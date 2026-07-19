//! Canonicalization for function identity (Kernel AST §5, de-Bruijn half).
//!
//! A lambda's identity should be independent of its bound-variable *names*
//! (α-equivalence) and should incorporate the *values* of its free variables
//! (captures). We produce a canonical `Lambda` by:
//!
//! - renaming every bound variable to a positional canonical name (`$0`, `$1`, …
//!   in binding order — a de-Bruijn-style scheme), and
//! - replacing each free-variable reference with the constant it captured (an
//!   immutable value) or a location marker (a Box slot — location identity
//!   participates in function identity, B1).
//!
//! If any free variable is not yet resolvable (a self/mutual reference under
//! initialization — the μ case), canonicalization **bails** (`None`) and the
//! caller falls back to opaque identity. That is the deferred half (§7 group
//! identity / DECISIONS.md); it is always sound (it only fails to merge).

use std::collections::HashMap;

use crate::ast::*; // LocationId, Ref, BindingRef, Lambda, Expr, …
use crate::env::{Binding, Env, SlotId};

/// Produce the canonical form of `lambda` closed over `env`, or `None` if a free
/// variable cannot be resolved yet (recursion / forward reference).
pub(super) fn canonicalize(lambda: &Lambda, env: &Env) -> Option<Lambda> {
    let mut c = Canon { env, scopes: Vec::new(), counter: 0 };
    c.lambda(lambda)
}

struct Canon<'e> {
    env: &'e Env,
    /// Bound-variable scopes (innermost last): original name → canonical name.
    scopes: Vec<HashMap<String, String>>,
    counter: u32,
}

impl Canon<'_> {
    fn fresh(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("${n}")
    }

    fn bind(&mut self, name: &str) -> String {
        let canonical = self.fresh();
        self.scopes.last_mut().expect("a scope is open").insert(name.to_string(), canonical.clone());
        canonical
    }

    fn lookup_bound(&self, name: &str) -> Option<&String> {
        self.scopes.iter().rev().find_map(|s| s.get(name))
    }

    fn lambda(&mut self, l: &Lambda) -> Option<Lambda> {
        self.scopes.push(HashMap::new());
        let params = self.pattern(&l.params)?;
        let body = self.expr(&l.body)?;
        self.scopes.pop();
        Some(Lambda { params, body: Box::new(body), act_kind: l.act_kind })
    }

    fn expr(&mut self, e: &Expr) -> Option<Expr> {
        Some(match e {
            Expr::Const(v) => Expr::Const(v.clone()),
            Expr::Ref(r) => self.reference(r)?,
            Expr::Lambda(l) => Expr::Lambda(self.lambda(l)?),
            Expr::Apply { callee, args } => Expr::Apply {
                callee: Box::new(self.expr(callee)?),
                args: args.iter().map(|a| self.arg(a)).collect::<Option<_>>()?,
            },
            Expr::PrimOp { op, args } => Expr::PrimOp {
                op: *op,
                args: args.iter().map(|a| self.expr(a)).collect::<Option<_>>()?,
            },
            Expr::Match(m) => Expr::Match(self.match_expr(m)?),
            Expr::TupleCons(elems) => {
                Expr::TupleCons(elems.iter().map(|el| self.element(el)).collect::<Option<_>>()?)
            }
            Expr::RecordCons(fields) => {
                Expr::RecordCons(fields.iter().map(|f| self.field(f)).collect::<Option<_>>()?)
            }
            Expr::Access { target, form, total } => Expr::Access {
                target: Box::new(self.expr(target)?),
                form: self.access_form(form)?,
                total: *total,
            },
            Expr::Template(parts) => Expr::Template(
                parts.iter().map(|p| self.template_part(p)).collect::<Option<_>>()?,
            ),
            Expr::Write { slot, value } => Expr::Write {
                slot: self.slot_ref(slot)?,
                value: Box::new(self.expr(value)?),
            },
        })
    }

    /// The heart of it: a bound reference becomes its canonical name; a free
    /// reference is replaced by its captured value (a const) or location.
    fn reference(&mut self, r: &Ref) -> Option<Expr> {
        let name = match r {
            Ref::Immutable(BindingRef::Name(n)) => n,
            // Already-canonical / non-name refs shouldn't appear pre-canon; bail.
            _ => return None,
        };
        if let Some(canonical) = self.lookup_bound(name) {
            return Some(Expr::Ref(Ref::Immutable(BindingRef::Name(canonical.clone()))));
        }
        match self.env.lookup(name) {
            Some(Binding::Value(v)) => Some(Expr::Const(v)),
            Some(Binding::Slot(slot)) => {
                Some(Expr::Ref(Ref::Location(loc(slot))))
            }
            // Under-initialization / unbound: the μ case — bail to opaque.
            _ => None,
        }
    }

    fn slot_ref(&mut self, slot: &SlotRef) -> Option<SlotRef> {
        match slot {
            SlotRef::Location(l) => Some(SlotRef::Location(*l)),
            SlotRef::Name(name) => {
                if let Some(canonical) = self.lookup_bound(name) {
                    return Some(SlotRef::Name(canonical.clone()));
                }
                match self.env.lookup(name) {
                    Some(Binding::Slot(slot)) => Some(SlotRef::Location(loc(slot))),
                    _ => None,
                }
            }
        }
    }

    fn match_expr(&mut self, m: &Match) -> Option<Match> {
        let scrutinee = match &m.scrutinee {
            Some(e) => Some(Box::new(self.expr(e)?)),
            None => None,
        };
        self.scopes.push(HashMap::new()); // binds accumulate here
        let mut items = Vec::with_capacity(m.items.len());
        for item in &m.items {
            items.push(match item {
                MatchItem::Bind(b) => {
                    // Evaluate order: value is canonicalized before its name binds
                    // (a self/forward reference is therefore free ⇒ bails).
                    let value = self.expr(&b.value)?;
                    let target = self.bind_target(&b.target)?;
                    MatchItem::Bind(Bind { target, value, exported: b.exported })
                }
                MatchItem::Stmt(e) => MatchItem::Stmt(self.expr(e)?),
                MatchItem::Arm(arm) => {
                    self.scopes.push(HashMap::new()); // arm-local bindings
                    let pattern = match &arm.pattern {
                        Some(p) => Some(self.pattern(p)?),
                        None => None,
                    };
                    let guard = match &arm.guard {
                        Some(g) => Some(self.expr(g)?),
                        None => None,
                    };
                    let result = self.expr(&arm.result)?;
                    self.scopes.pop();
                    MatchItem::Arm(Arm { pattern, guard, result })
                }
            });
        }
        self.scopes.pop();
        Some(Match { scrutinee, items })
    }

    fn bind_target(&mut self, t: &BindTarget) -> Option<BindTarget> {
        Some(match t {
            BindTarget::Name(n) => BindTarget::Name(self.bind(n)),
            BindTarget::Pattern(p) => BindTarget::Pattern(self.pattern(p)?),
        })
    }

    fn arg(&mut self, a: &Arg) -> Option<Arg> {
        Some(match a {
            Arg::Expr(e) => Arg::Expr(self.expr(e)?),
            Arg::Spread(e) => Arg::Spread(self.expr(e)?),
        })
    }

    fn element(&mut self, el: &Element) -> Option<Element> {
        Some(match el {
            Element::Expr(e) => Element::Expr(self.expr(e)?),
            Element::Spread(e) => Element::Spread(self.expr(e)?),
        })
    }

    fn field(&mut self, f: &Field) -> Option<Field> {
        Some(match f {
            Field::Field { key, value } => Field::Field { key: key.clone(), value: self.expr(value)? },
            Field::Computed { key, value } => {
                Field::Computed { key: self.expr(key)?, value: self.expr(value)? }
            }
            Field::Spread(e) => Field::Spread(self.expr(e)?),
        })
    }

    fn access_form(&mut self, form: &AccessForm) -> Option<AccessForm> {
        Some(match form {
            AccessForm::Field(n) => AccessForm::Field(n.clone()),
            AccessForm::Index(e) => AccessForm::Index(Box::new(self.expr(e)?)),
            AccessForm::Slice { lo, hi } => AccessForm::Slice {
                lo: match lo {
                    Some(e) => Some(Box::new(self.expr(e)?)),
                    None => None,
                },
                hi: match hi {
                    Some(e) => Some(Box::new(self.expr(e)?)),
                    None => None,
                },
            },
        })
    }

    fn template_part(&mut self, p: &TemplatePart) -> Option<TemplatePart> {
        Some(match p {
            TemplatePart::Segment(s) => TemplatePart::Segment(s.clone()),
            TemplatePart::Interp(e) => TemplatePart::Interp(self.expr(e)?),
        })
    }

    // Patterns bind names into the current scope.
    fn pattern(&mut self, p: &Pat) -> Option<Pat> {
        Some(match p {
            Pat::Const(v) => Pat::Const(v.clone()),
            Pat::Wild => Pat::Wild,
            Pat::Bind(n) => Pat::Bind(self.bind(n)),
            Pat::Tuple(elems) => {
                Pat::Tuple(elems.iter().map(|e| self.pat_elem(e)).collect::<Option<_>>()?)
            }
            Pat::Record { fields, exact } => Pat::Record {
                fields: fields.iter().map(|f| self.pat_field(f)).collect::<Option<_>>()?,
                exact: *exact,
            },
            // A contract name is a stable global identifier — keep it as-is.
            Pat::Contract(r) => Pat::Contract(r.clone()),
        })
    }

    fn pat_elem(&mut self, e: &PatElem) -> Option<PatElem> {
        Some(match e {
            PatElem::Pat(p) => PatElem::Pat(self.pattern(p)?),
            PatElem::Rest(Some(n)) => PatElem::Rest(Some(self.bind(n))),
            PatElem::Rest(None) => PatElem::Rest(None),
        })
    }

    fn pat_field(&mut self, f: &PatField) -> Option<PatField> {
        Some(match f {
            PatField::Field { key, pat } => {
                PatField::Field { key: key.clone(), pat: self.pattern(pat)? }
            }
            PatField::Rest(Some(n)) => PatField::Rest(Some(self.bind(n))),
            PatField::Rest(None) => PatField::Rest(None),
        })
    }
}

/// Map a runtime slot to the AST location marker (same underlying index).
fn loc(slot: SlotId) -> LocationId {
    LocationId(slot.0)
}
