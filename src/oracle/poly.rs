//! Narrow arithmetic normalization for function-shape identity
//! (μ-Canonicalization Spec v0.5, §8 — the enumerated, frozen `==`-slice).
//!
//! **Only** three rewrites are permitted, because a shape-level rewrite must
//! preserve the produced value, completion-vs-divergence, operation-safety
//! demands, and the accepted domain:
//!
//! - commutative/associative **reordering** of retained operands,
//! - **literal constant folding** (no variable erased),
//! - **like-term coefficient combining** where every variable survives with its
//!   demand (`x + x → 2*x` — the standing H-05 commitment).
//!
//! **Permanently excluded** (MU-10, asserted *not* to fire): zero-annihilation
//! (`0*e`), cancellation (`e-e`), demand-dropping identity elimination (`x+0`,
//! `x*1`), distribution, and any rewrite erasing a call / diverging operand. A
//! normalization that would do any of these **aborts** — the node is rebuilt with
//! normalized children but is otherwise left unrewritten. Evaluation is
//! unaffected (shapes drive identity only; closures run their original body).

use std::collections::BTreeMap;

use crate::ast::*;
use crate::interner::Interner;
use crate::rational::Rational;

/// Normalize the arithmetic subterms of a lambda shape.
pub(super) fn normalize_lambda(l: &Lambda, interner: &mut Interner) -> Lambda {
    let mut n = Norm { interner };
    Lambda {
        params: l.params.clone(),
        body: Box::new(n.normalize(&l.body)),
        act_kind: l.act_kind,
    }
}

struct Norm<'a> {
    interner: &'a mut Interner,
}

impl Norm<'_> {
    fn normalize(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::PrimOp { op: PrimOp::Add | PrimOp::Sub, args } if args.len() == 2 => self.norm_add(e),
            Expr::PrimOp { op: PrimOp::Neg, args } if args.len() == 1 => self.norm_add(e),
            Expr::PrimOp { op: PrimOp::Mul, args } if args.len() == 2 => self.norm_mul(e),
            _ => self.norm_children(e),
        }
    }

    // ── Additive chains ──────────────────────────────────────────────────────

    fn norm_add(&mut self, e: &Expr) -> Expr {
        let mut flat: Vec<(bool, Expr)> = Vec::new();
        self.flatten_add(e, true, &mut flat);

        // Group non-constant terms by base; accumulate the constant separately.
        let mut groups: BTreeMap<String, (Rational, Expr)> = BTreeMap::new();
        let mut constant = Rational::from(0);
        let mut had_constant = false;
        for (positive, term) in flat {
            let (mut coeff, base) = decompose(&term);
            if !positive {
                coeff = -coeff;
            }
            match base {
                None => {
                    constant = constant + coeff;
                    had_constant = true;
                }
                Some(b) => {
                    let entry = groups.entry(key(&b)).or_insert((Rational::from(0), b));
                    entry.0 = entry.0.clone() + coeff;
                }
            }
        }

        // Abort on cancellation (a base combined to zero) — but still reorder, so
        // commutative spellings (`x - x` vs `-x + x`) stay equal.
        if groups.values().any(|(c, _)| c.is_zero()) {
            return self.reorder_only_add(e);
        }
        // Abort if the result would be a single bare base (demand drop).
        if groups.len() == 1 && !had_constant && is_one(&groups.values().next().unwrap().0) {
            return self.reorder_only_add(e);
        }

        // Emit: variable terms (canonical key order) then the constant.
        let mut out: Vec<Expr> = groups.into_values().map(|(c, b)| self.term(c, b)).collect();
        if had_constant {
            out.push(Expr::Const(self.interner.number(constant)));
        }
        out.into_iter().reduce(|a, b| prim(PrimOp::Add, a, b)).expect("non-empty chain")
    }

    /// Flatten a `+`/`-`/unary-`-` chain into signed, normalized leaf terms.
    fn flatten_add(&mut self, e: &Expr, positive: bool, out: &mut Vec<(bool, Expr)>) {
        match e {
            Expr::PrimOp { op: PrimOp::Add, args } if args.len() == 2 => {
                self.flatten_add(&args[0], positive, out);
                self.flatten_add(&args[1], positive, out);
            }
            Expr::PrimOp { op: PrimOp::Sub, args } if args.len() == 2 => {
                self.flatten_add(&args[0], positive, out);
                self.flatten_add(&args[1], !positive, out);
            }
            Expr::PrimOp { op: PrimOp::Neg, args } if args.len() == 1 => {
                self.flatten_add(&args[0], !positive, out);
            }
            _ => out.push((positive, self.normalize(e))),
        }
    }

    // ── Multiplicative chains ────────────────────────────────────────────────

    fn norm_mul(&mut self, e: &Expr) -> Expr {
        let mut factors: Vec<Expr> = Vec::new();
        self.flatten_mul(e, &mut factors);

        // Fold literal factors into one coefficient; reorder the rest.
        let mut coeff = Rational::from(1);
        let mut had_literal = false;
        let mut rest: Vec<Expr> = Vec::new();
        for f in factors {
            match &f {
                Expr::Const(v) if v.as_number().is_some() => {
                    coeff = coeff * v.as_number().unwrap().clone();
                    had_literal = true;
                }
                _ => rest.push(f),
            }
        }
        rest.sort_by_cached_key(key);
        if rest.is_empty() {
            return Expr::Const(self.interner.number(coeff));
        }
        let product = rest.into_iter().reduce(|a, b| prim(PrimOp::Mul, a, b)).unwrap();
        // Keep the coefficient as a factor even when 0 or 1 — dropping it would
        // annihilate (`0·x`) or drop a demand (`x·1`), both excluded. Omit it only
        // when there was no literal factor at all.
        if had_literal {
            prim(PrimOp::Mul, Expr::Const(self.interner.number(coeff)), product)
        } else {
            product
        }
    }

    /// Reorder (and fold literal constants) an additive chain without combining
    /// like terms — the abort fallback, so commutative spellings stay equal.
    fn reorder_only_add(&mut self, e: &Expr) -> Expr {
        let mut flat: Vec<(bool, Expr)> = Vec::new();
        self.flatten_add(e, true, &mut flat);
        let mut pos: Vec<Expr> = Vec::new();
        let mut neg: Vec<Expr> = Vec::new();
        let mut constant = Rational::from(0);
        let mut had_constant = false;
        for (positive, t) in flat {
            match &t {
                Expr::Const(v) if v.as_number().is_some() => {
                    let n = v.as_number().unwrap().clone();
                    constant = if positive { constant + n } else { constant - n };
                    had_constant = true;
                }
                _ if positive => pos.push(t),
                _ => neg.push(t),
            }
        }
        pos.sort_by_cached_key(key);
        neg.sort_by_cached_key(key);

        let mut result: Option<Expr> = None;
        for p in pos {
            result = Some(match result {
                None => p,
                Some(acc) => prim(PrimOp::Add, acc, p),
            });
        }
        for n in neg {
            result = Some(match result {
                None => Expr::PrimOp { op: PrimOp::Neg, args: vec![n] },
                Some(acc) => prim(PrimOp::Sub, acc, n),
            });
        }
        if had_constant {
            let c = Expr::Const(self.interner.number(constant));
            result = Some(match result {
                None => c,
                Some(acc) => prim(PrimOp::Add, acc, c),
            });
        }
        result.unwrap_or_else(|| Expr::Const(self.interner.number(Rational::from(0))))
    }

    fn flatten_mul(&mut self, e: &Expr, out: &mut Vec<Expr>) {
        match e {
            Expr::PrimOp { op: PrimOp::Mul, args } if args.len() == 2 => {
                self.flatten_mul(&args[0], out);
                self.flatten_mul(&args[1], out);
            }
            _ => out.push(self.normalize(e)),
        }
    }

    /// A `coeff · base` term (coeff already known non-zero).
    fn term(&mut self, coeff: Rational, base: Expr) -> Expr {
        if is_one(&coeff) {
            base
        } else {
            prim(PrimOp::Mul, Expr::Const(self.interner.number(coeff)), base)
        }
    }

    // ── Structural recursion for everything else (and abort fallbacks) ────────

    fn norm_children(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::Const(_) | Expr::Ref(_) => e.clone(),
            Expr::Lambda(l) => Expr::Lambda(Lambda {
                params: l.params.clone(),
                body: Box::new(self.normalize(&l.body)),
                act_kind: l.act_kind,
            }),
            Expr::Apply { callee, args } => Expr::Apply {
                callee: Box::new(self.normalize(callee)),
                args: args.iter().map(|a| self.arg(a)).collect(),
            },
            Expr::PrimOp { op, args } => Expr::PrimOp {
                op: *op,
                args: args.iter().map(|a| self.normalize(a)).collect(),
            },
            Expr::Match(m) => Expr::Match(self.mtch(m)),
            Expr::TupleCons(elems) => Expr::TupleCons(elems.iter().map(|el| self.elem(el)).collect()),
            Expr::RecordCons(fields) => Expr::RecordCons(fields.iter().map(|f| self.field(f)).collect()),
            Expr::Access { target, form, total } => Expr::Access {
                target: Box::new(self.normalize(target)),
                form: self.form(form),
                total: *total,
            },
            Expr::Template(parts) => Expr::Template(
                parts
                    .iter()
                    .map(|p| match p {
                        TemplatePart::Segment(s) => TemplatePart::Segment(s.clone()),
                        TemplatePart::Interp(e) => TemplatePart::Interp(self.normalize(e)),
                    })
                    .collect(),
            ),
            Expr::Write { slot, value } => Expr::Write {
                slot: slot.clone(),
                value: Box::new(self.normalize(value)),
            },
        }
    }

    fn arg(&mut self, a: &Arg) -> Arg {
        match a {
            Arg::Expr(e) => Arg::Expr(self.normalize(e)),
            Arg::Spread(e) => Arg::Spread(self.normalize(e)),
        }
    }
    fn elem(&mut self, el: &Element) -> Element {
        match el {
            Element::Expr(e) => Element::Expr(self.normalize(e)),
            Element::Spread(e) => Element::Spread(self.normalize(e)),
        }
    }
    fn field(&mut self, f: &Field) -> Field {
        match f {
            Field::Field { key, value } => Field::Field { key: key.clone(), value: self.normalize(value) },
            Field::Computed { key, value } => {
                Field::Computed { key: self.normalize(key), value: self.normalize(value) }
            }
            Field::Spread(e) => Field::Spread(self.normalize(e)),
        }
    }
    fn form(&mut self, form: &AccessForm) -> AccessForm {
        match form {
            AccessForm::Field(n) => AccessForm::Field(n.clone()),
            AccessForm::Index(e) => AccessForm::Index(Box::new(self.normalize(e))),
            AccessForm::Slice { lo, hi } => AccessForm::Slice {
                lo: lo.as_ref().map(|e| Box::new(self.normalize(e))),
                hi: hi.as_ref().map(|e| Box::new(self.normalize(e))),
            },
        }
    }
    fn mtch(&mut self, m: &Match) -> Match {
        Match {
            scrutinee: m.scrutinee.as_ref().map(|e| Box::new(self.normalize(e))),
            items: m
                .items
                .iter()
                .map(|item| match item {
                    MatchItem::Bind(b) => MatchItem::Bind(Bind {
                        target: b.target.clone(),
                        value: self.normalize(&b.value),
                        exported: b.exported,
                    }),
                    MatchItem::Stmt(e) => MatchItem::Stmt(self.normalize(e)),
                    MatchItem::Arm(arm) => MatchItem::Arm(Arm {
                        pattern: arm.pattern.clone(),
                        guard: arm.guard.as_ref().map(|g| self.normalize(g)),
                        result: self.normalize(&arm.result),
                    }),
                })
                .collect(),
        }
    }
}

fn prim(op: PrimOp, a: Expr, b: Expr) -> Expr {
    Expr::PrimOp { op, args: vec![a, b] }
}

fn is_one(r: &Rational) -> bool {
    *r == Rational::from(1)
}

/// Decompose a normalized additive operand into `(coefficient, base)`; a pure
/// numeric literal has base `None`.
fn decompose(e: &Expr) -> (Rational, Option<Expr>) {
    match e {
        Expr::Const(v) if v.as_number().is_some() => (v.as_number().unwrap().clone(), None),
        Expr::PrimOp { op: PrimOp::Mul, args } if args.len() == 2 => match &args[0] {
            Expr::Const(v) if v.as_number().is_some() => {
                (v.as_number().unwrap().clone(), Some(args[1].clone()))
            }
            _ => (Rational::from(1), Some(e.clone())),
        },
        _ => (Rational::from(1), Some(e.clone())),
    }
}

// ── Canonical serialization for grouping / ordering ──────────────────────────

fn key(e: &Expr) -> String {
    let mut s = String::new();
    ser(e, &mut s);
    s
}

fn ser(e: &Expr, out: &mut String) {
    match e {
        Expr::Const(v) => out.push_str(&format!("c{};", v.addr())),
        Expr::Ref(Ref::Immutable(BindingRef::Name(n))) => out.push_str(&format!("r{n};")),
        Expr::Ref(r) => out.push_str(&format!("R{r:?};")),
        Expr::PrimOp { op, args } => {
            out.push_str(&format!("P{op:?}("));
            for a in args {
                ser(a, out);
            }
            out.push(')');
        }
        Expr::Apply { callee, args } => {
            out.push_str("A(");
            ser(callee, out);
            for a in args {
                match a {
                    Arg::Expr(e) | Arg::Spread(e) => ser(e, out),
                }
            }
            out.push(')');
        }
        Expr::Access { target, form, total } => {
            out.push_str(&format!("X{total}("));
            ser(target, out);
            match form {
                AccessForm::Field(n) => out.push_str(&format!(".{n}")),
                AccessForm::Index(e) => ser(e, out),
                AccessForm::Slice { lo, hi } => {
                    if let Some(e) = lo {
                        ser(e, out);
                    }
                    out.push('~');
                    if let Some(e) = hi {
                        ser(e, out);
                    }
                }
            }
            out.push(')');
        }
        // Other node kinds are compared structurally via a debug rendering — they
        // appear as opaque factors, never distributed into.
        other => out.push_str(&format!("O{other:?}")),
    }
}
