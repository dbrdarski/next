//! Function **shape** canonicalization (μ-Canonicalization Spec v0.1, algorithm A,
//! the α + capture-slot layer).
//!
//! A closure's identity is its rational tree = `node(canonical-code, captures)`
//! (law 6). This module computes the **canonical code** (shape): the lambda body
//! with bound variables α-renamed to positional canonical names (`$0`, `$1`, … —
//! de-Bruijn order) and free variables replaced by positional **capture slots**
//! (`@cap0`, `@cap1`, …, first-occurrence order). Captures are *not* inlined — the
//! shape is capture-independent; the actual captured values are compared
//! separately by bisimulation (algorithm B, `equal.rs`).
//!
//! The shape is a finite term (recursion lives in the captures, never in the
//! code), so shape identity is ordinary structural equality of the canonical
//! `Lambda`. The full μ-binder minimization (SCC grouping, laws 1–5) refines the
//! *code* identity used by layer-2 cache keys and ships with the analyzer; layer-1
//! `==` needs only this shape plus algorithm B, which already collapses symmetric
//! recursion coinductively.

use std::collections::HashMap;

use crate::ast::*;
use crate::interner::Interner;

/// A canonical function shape: the α/capture-normalized code and the ordered
/// names of its free variables (capture slots).
pub(super) struct Shape {
    pub code: Lambda,
    pub free_vars: Vec<String>,
}

/// Prefix for canonical bound-variable names (never collides with user names,
/// which are `$`/`@`-free alphanumerics).
const BOUND: &str = "$";
/// Prefix for canonical capture-slot names.
const CAP: &str = "@cap";

/// Canonicalize a lambda into its shape. Always succeeds: free variables become
/// capture slots regardless of whether they are yet bound (resolution is B's job).
/// After α/capture normalization, arithmetic subterms are put into polynomial
/// normal form (the frozen `==`-set item H-05) — hence the interner (for the
/// coefficient/constant values it produces).
pub(super) fn canonicalize(lambda: &Lambda, interner: &mut Interner) -> Shape {
    let mut c = Canon {
        scopes: Vec::new(),
        counter: 0,
        free: Vec::new(),
        free_index: HashMap::new(),
    };
    let code = c.lambda(lambda);
    let code = super::poly::normalize_lambda(&code, interner);
    Shape { code, free_vars: c.free }
}

struct Canon {
    /// Bound-variable scopes (innermost last): original name → canonical name.
    scopes: Vec<HashMap<String, String>>,
    counter: u32,
    /// Free-variable names in first-occurrence order (the capture slots).
    free: Vec<String>,
    free_index: HashMap<String, u32>,
}

impl Canon {
    fn fresh_bound(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("{BOUND}{n}")
    }

    fn bind(&mut self, name: &str) -> String {
        let canonical = self.fresh_bound();
        self.scopes.last_mut().expect("a scope is open").insert(name.to_string(), canonical.clone());
        canonical
    }

    fn lookup_bound(&self, name: &str) -> Option<&String> {
        self.scopes.iter().rev().find_map(|s| s.get(name))
    }

    /// Assign (or reuse) a capture slot for a free variable.
    fn capture_slot(&mut self, name: &str) -> String {
        let idx = *self.free_index.entry(name.to_string()).or_insert_with(|| {
            let i = self.free.len() as u32;
            self.free.push(name.to_string());
            i
        });
        format!("{CAP}{idx}")
    }

    fn lambda(&mut self, l: &Lambda) -> Lambda {
        self.scopes.push(HashMap::new());
        let params = self.pattern(&l.params);
        let body = self.expr(&l.body);
        self.scopes.pop();
        Lambda { params, body: Box::new(body), act_kind: l.act_kind }
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::Const(v) => Expr::Const(v.clone()),
            Expr::Ref(r) => self.reference(r),
            Expr::Lambda(l) => Expr::Lambda(self.lambda(l)),
            Expr::Apply { callee, args } => Expr::Apply {
                callee: Box::new(self.expr(callee)),
                args: args.iter().map(|a| self.arg(a)).collect(),
            },
            Expr::PrimOp { op, args } => Expr::PrimOp {
                op: *op,
                args: args.iter().map(|a| self.expr(a)).collect(),
            },
            Expr::Match(m) => Expr::Match(self.match_expr(m)),
            Expr::TupleCons(elems) => Expr::TupleCons(elems.iter().map(|el| self.element(el)).collect()),
            Expr::RecordCons(fields) => Expr::RecordCons(fields.iter().map(|f| self.field(f)).collect()),
            Expr::Access { target, form, total } => Expr::Access {
                target: Box::new(self.expr(target)),
                form: self.access_form(form),
                total: *total,
            },
            Expr::Template(parts) => Expr::Template(parts.iter().map(|p| self.template_part(p)).collect()),
            Expr::Write { slot, value } => Expr::Write {
                slot: self.slot_ref(slot),
                value: Box::new(self.expr(value)),
            },
        }
    }

    fn reference(&mut self, r: &Ref) -> Expr {
        let name = match r {
            Ref::Immutable(BindingRef::Name(n)) => n,
            // Already-canonical / location / μ refs: keep them (idempotence).
            other => return Expr::Ref(other.clone()),
        };
        let canonical = match self.lookup_bound(name) {
            Some(bound) => bound.clone(),
            None => self.capture_slot(name),
        };
        Expr::Ref(Ref::Immutable(BindingRef::Name(canonical)))
    }

    fn slot_ref(&mut self, slot: &SlotRef) -> SlotRef {
        match slot {
            SlotRef::Location(l) => SlotRef::Location(*l),
            SlotRef::Name(name) => {
                let canonical = match self.lookup_bound(name) {
                    Some(bound) => bound.clone(),
                    None => self.capture_slot(name),
                };
                SlotRef::Name(canonical)
            }
        }
    }

    fn match_expr(&mut self, m: &Match) -> Match {
        let scrutinee = m.scrutinee.as_ref().map(|e| Box::new(self.expr(e)));
        self.scopes.push(HashMap::new());
        let mut items = Vec::with_capacity(m.items.len());
        for item in &m.items {
            items.push(match item {
                MatchItem::Bind(b) => {
                    let value = self.expr(&b.value);
                    let target = self.bind_target(&b.target);
                    MatchItem::Bind(Bind { target, value, exported: b.exported })
                }
                MatchItem::Stmt(e) => MatchItem::Stmt(self.expr(e)),
                MatchItem::Arm(arm) => {
                    self.scopes.push(HashMap::new());
                    let pattern = arm.pattern.as_ref().map(|p| self.pattern(p));
                    let guard = arm.guard.as_ref().map(|g| self.expr(g));
                    let result = self.expr(&arm.result);
                    self.scopes.pop();
                    MatchItem::Arm(Arm { pattern, guard, result })
                }
            });
        }
        self.scopes.pop();
        Match { scrutinee, items }
    }

    fn bind_target(&mut self, t: &BindTarget) -> BindTarget {
        match t {
            BindTarget::Name(n) => BindTarget::Name(self.bind(n)),
            BindTarget::Pattern(p) => BindTarget::Pattern(self.pattern(p)),
        }
    }

    fn arg(&mut self, a: &Arg) -> Arg {
        match a {
            Arg::Expr(e) => Arg::Expr(self.expr(e)),
            Arg::Spread(e) => Arg::Spread(self.expr(e)),
        }
    }

    fn element(&mut self, el: &Element) -> Element {
        match el {
            Element::Expr(e) => Element::Expr(self.expr(e)),
            Element::Spread(e) => Element::Spread(self.expr(e)),
        }
    }

    fn field(&mut self, f: &Field) -> Field {
        match f {
            Field::Field { key, value } => Field::Field { key: key.clone(), value: self.expr(value) },
            Field::Computed { key, value } => {
                Field::Computed { key: self.expr(key), value: self.expr(value) }
            }
            Field::Spread(e) => Field::Spread(self.expr(e)),
        }
    }

    fn access_form(&mut self, form: &AccessForm) -> AccessForm {
        match form {
            AccessForm::Field(n) => AccessForm::Field(n.clone()),
            AccessForm::Index(e) => AccessForm::Index(Box::new(self.expr(e))),
            AccessForm::Slice { lo, hi } => AccessForm::Slice {
                lo: lo.as_ref().map(|e| Box::new(self.expr(e))),
                hi: hi.as_ref().map(|e| Box::new(self.expr(e))),
            },
        }
    }

    fn template_part(&mut self, p: &TemplatePart) -> TemplatePart {
        match p {
            TemplatePart::Segment(s) => TemplatePart::Segment(s.clone()),
            TemplatePart::Interp(e) => TemplatePart::Interp(self.expr(e)),
        }
    }

    fn pattern(&mut self, p: &Pat) -> Pat {
        match p {
            Pat::Const(v) => Pat::Const(v.clone()),
            Pat::Wild => Pat::Wild,
            Pat::Bind(n) => Pat::Bind(self.bind(n)),
            Pat::Tuple(elems) => Pat::Tuple(elems.iter().map(|e| self.pat_elem(e)).collect()),
            Pat::Record { fields, exact } => Pat::Record {
                fields: fields.iter().map(|f| self.pat_field(f)).collect(),
                exact: *exact,
            },
            // Contract names are stable global identifiers — keep them.
            Pat::Contract(r) => Pat::Contract(r.clone()),
        }
    }

    fn pat_elem(&mut self, e: &PatElem) -> PatElem {
        match e {
            PatElem::Pat(p) => PatElem::Pat(self.pattern(p)),
            PatElem::Rest(Some(n)) => PatElem::Rest(Some(self.bind(n))),
            PatElem::Rest(None) => PatElem::Rest(None),
        }
    }

    fn pat_field(&mut self, f: &PatField) -> PatField {
        match f {
            PatField::Field { key, pat } => PatField::Field { key: key.clone(), pat: self.pattern(pat) },
            PatField::Rest(Some(n)) => PatField::Rest(Some(self.bind(n))),
            PatField::Rest(None) => PatField::Rest(None),
        }
    }
}
