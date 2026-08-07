//! The arithmetic rule of the normalization phase (μ-Canonicalization Spec v0.5,
//! §8 — the enumerated, frozen `==`-slice).
//!
//! This is a **local** rewrite: the phase ([`super`]) owns the recursion and
//! hands each node here already normalized in its children, so flattening an
//! additive or multiplicative chain never has to re-descend.
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
//! normalization that would do any of these **aborts** — the node is left with
//! its normalized children but is otherwise unrewritten.
//!
//! ## Anchoring: what the master law costs the reordering rule
//!
//! Operands evaluate strictly left to right, so **reordering is not free**. If
//! two operands can each diverge, trap, or touch the world, swapping them can
//! change which one happens — and the master law names *completion vs
//! divergence* explicitly. An operand that can **call** (`Apply`) or **write**
//! (`Write`) is therefore **anchored**: it keeps its position relative to the
//! other anchored operands, and it is never merged into a coefficient (that
//! would erase a call, the named exclusion). Only call-free operands move and
//! combine — which is exactly the H-05 commitment's scope, `x + x → 2 * x`
//! over *variable occurrences*.
//!
//! Anchoring deliberately does **not** cover plain trapping. Two call-free
//! arithmetic operands may both be ill-typed, and reordering can change which
//! trap class is reported — but only on inputs the program already rejects, so
//! the accepted domain, the produced value, the demands, and completion vs
//! divergence are all preserved. The master law lists those four; which trap
//! fires among already-rejected inputs is not among them. `// [ask-author]`:
//! this reading is mine, and it is what keeps `2*x + 3*y == 3*y + 2*x`.

use std::collections::BTreeMap;

use crate::ast::*;
use crate::interner::Interner;
use crate::rational::Rational;

/// Apply the arithmetic rule to one node whose children are already normalized.
/// Any other node is returned untouched.
pub(super) fn rewrite(e: &Expr, interner: &mut Interner) -> Expr {
    let mut n = Norm { interner };
    match e {
        Expr::PrimOp {
            op: PrimOp::Add | PrimOp::Sub,
            args,
        } if args.len() == 2 => n.norm_add(e),
        Expr::PrimOp {
            op: PrimOp::Neg,
            args,
        } if args.len() == 1 => n.norm_add(e),
        Expr::PrimOp {
            op: PrimOp::Mul,
            args,
        } if args.len() == 2 => n.norm_mul(e),
        _ => e.clone(),
    }
}

struct Norm<'a> {
    interner: &'a mut Interner,
}

impl Norm<'_> {
    // ── Additive chains ──────────────────────────────────────────────────────

    fn norm_add(&mut self, e: &Expr) -> Expr {
        let mut flat: Vec<(bool, Expr)> = Vec::new();
        flatten_add(e, true, &mut flat);

        // Anchored terms hold their source order and never combine; the rest
        // group by base, with the constant accumulated separately.
        let mut anchored: Vec<(bool, Expr)> = Vec::new();
        let mut groups: BTreeMap<String, (Rational, Expr)> = BTreeMap::new();
        let mut constant = Rational::from(0);
        let mut had_constant = false;
        for (positive, term) in flat {
            if anchored_operand(&term) {
                anchored.push((positive, term));
                continue;
            }
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
        // Abort if the free part would collapse to a single bare base: `2*x - x`
        // → `x` drops x's Number demand, and so does `f() + 2*x - x`.
        if groups.len() == 1 && !had_constant && is_one(&groups.values().next().unwrap().0) {
            return self.reorder_only_add(e);
        }

        // Emit: anchored terms in source order, then variable terms (canonical
        // key order), then the constant.
        let mut result: Option<Expr> = None;
        for (positive, t) in anchored {
            result = Some(signed(result, positive, t));
        }
        for term in groups.into_values().map(|(c, b)| self.term(c, b)) {
            result = Some(signed(result, true, term));
        }
        if had_constant {
            let c = Expr::Const(self.interner.number(constant));
            result = Some(signed(result, true, c));
        }
        result.expect("non-empty chain")
    }

    // ── Multiplicative chains ────────────────────────────────────────────────

    fn norm_mul(&mut self, e: &Expr) -> Expr {
        let mut factors: Vec<Expr> = Vec::new();
        flatten_mul(e, &mut factors);

        // Fold literal factors into one coefficient; reorder the rest, except
        // that anchored factors hold their source order relative to each other.
        let mut coeff = Rational::from(1);
        let mut had_literal = false;
        let mut anchored: Vec<Expr> = Vec::new();
        let mut rest: Vec<Expr> = Vec::new();
        for f in factors {
            match &f {
                Expr::Const(v) if v.as_number().is_some() => {
                    coeff = coeff * v.as_number().unwrap().clone();
                    had_literal = true;
                }
                _ if anchored_operand(&f) => anchored.push(f),
                _ => rest.push(f),
            }
        }
        rest.sort_by_cached_key(key);
        if anchored.is_empty() && rest.is_empty() {
            return Expr::Const(self.interner.number(coeff));
        }
        let product = anchored
            .into_iter()
            .chain(rest)
            .reduce(|a, b| prim(PrimOp::Mul, a, b))
            .expect("non-empty chain");
        // Keep the coefficient as a factor even when 0 or 1 — dropping it would
        // annihilate (`0·x`) or drop a demand (`x·1`), both excluded. Omit it only
        // when there was no literal factor at all.
        if had_literal {
            prim(
                PrimOp::Mul,
                Expr::Const(self.interner.number(coeff)),
                product,
            )
        } else {
            product
        }
    }

    /// Reorder (and fold literal constants) an additive chain without combining
    /// like terms — the abort fallback, so commutative spellings stay equal.
    ///
    /// A term's sign lives in two places at once: the chain's own `+`/`-`/unary
    /// `-`, and a negative coefficient, because the phase normalizes children
    /// first and `-x` reaches this point already rewritten to `(-1)·x`. Both must
    /// read as the same negation, or `-x + x` and `x - x` stop agreeing.
    fn reorder_only_add(&mut self, e: &Expr) -> Expr {
        let mut flat: Vec<(bool, Expr)> = Vec::new();
        flatten_add(e, true, &mut flat);
        let mut anchored: Vec<(bool, Expr)> = Vec::new();
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
                _ if anchored_operand(&t) => anchored.push((positive, t)),
                _ => {
                    let (mut coeff, base) = decompose(&t);
                    if !positive {
                        coeff = -coeff;
                    }
                    let base = base.expect("a numeric literal took the Const arm");
                    let negative = coeff < Rational::from(0);
                    let term = self.term(if negative { -coeff } else { coeff }, base);
                    if negative {
                        neg.push(term)
                    } else {
                        pos.push(term)
                    }
                }
            }
        }
        pos.sort_by_cached_key(key);
        neg.sort_by_cached_key(key);

        let mut result: Option<Expr> = None;
        for (positive, t) in anchored {
            result = Some(signed(result, positive, t));
        }
        for p in pos {
            result = Some(signed(result, true, p));
        }
        for n in neg {
            result = Some(signed(result, false, n));
        }
        if had_constant {
            let c = Expr::Const(self.interner.number(constant));
            result = Some(signed(result, true, c));
        }
        result.unwrap_or_else(|| Expr::Const(self.interner.number(Rational::from(0))))
    }

    /// A `coeff · base` term (coeff already known non-zero).
    fn term(&mut self, coeff: Rational, base: Expr) -> Expr {
        if is_one(&coeff) {
            base
        } else {
            prim(PrimOp::Mul, Expr::Const(self.interner.number(coeff)), base)
        }
    }
}

/// Flatten a `+`/`-`/unary-`-` chain into signed leaf terms, left to right.
fn flatten_add(e: &Expr, positive: bool, out: &mut Vec<(bool, Expr)>) {
    match e {
        Expr::PrimOp {
            op: PrimOp::Add,
            args,
        } if args.len() == 2 => {
            flatten_add(&args[0], positive, out);
            flatten_add(&args[1], positive, out);
        }
        Expr::PrimOp {
            op: PrimOp::Sub,
            args,
        } if args.len() == 2 => {
            flatten_add(&args[0], positive, out);
            flatten_add(&args[1], !positive, out);
        }
        Expr::PrimOp {
            op: PrimOp::Neg,
            args,
        } if args.len() == 1 => {
            flatten_add(&args[0], !positive, out);
        }
        _ => out.push((positive, e.clone())),
    }
}

/// Flatten a `*` chain into its factors, left to right.
fn flatten_mul(e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::PrimOp {
            op: PrimOp::Mul,
            args,
        } if args.len() == 2 => {
            flatten_mul(&args[0], out);
            flatten_mul(&args[1], out);
        }
        _ => out.push(e.clone()),
    }
}

fn prim(op: PrimOp, a: Expr, b: Expr) -> Expr {
    Expr::PrimOp {
        op,
        args: vec![a, b],
    }
}

/// Append a signed term to an additive chain being rebuilt.
fn signed(acc: Option<Expr>, positive: bool, t: Expr) -> Expr {
    match (acc, positive) {
        (None, true) => t,
        (None, false) => Expr::PrimOp {
            op: PrimOp::Neg,
            args: vec![t],
        },
        (Some(acc), true) => prim(PrimOp::Add, acc, t),
        (Some(acc), false) => prim(PrimOp::Sub, acc, t),
    }
}

/// Does this operand pin its own evaluation position? True when it can **call**
/// or **write** — the only ways an operand can diverge or touch the world, and
/// so the only ways its position is observable. A `Lambda` is not entered: making
/// a closure runs no body, so its contents never anchor.
fn anchored_operand(e: &Expr) -> bool {
    match e {
        Expr::Apply { .. } | Expr::Write { .. } => true,
        Expr::Const(_) | Expr::Ref(_) | Expr::Lambda(_) => false,
        Expr::PrimOp { args, .. } => args.iter().any(anchored_operand),
        Expr::TupleCons(elems) => elems.iter().any(|el| match el {
            Element::Expr(e) | Element::Spread(e) => anchored_operand(e),
        }),
        Expr::RecordCons(fields) => fields.iter().any(|f| match f {
            Field::Field { value, .. } => anchored_operand(value),
            Field::Computed { key, value } => anchored_operand(key) || anchored_operand(value),
            Field::Spread(e) => anchored_operand(e),
        }),
        Expr::Access { target, form, .. } => {
            anchored_operand(target)
                || match form {
                    AccessForm::Field(_) => false,
                    AccessForm::Index(e) => anchored_operand(e),
                    AccessForm::Slice { lo, hi } => {
                        lo.iter().chain(hi).any(|e| anchored_operand(e))
                    }
                }
        }
        Expr::Template(parts) => parts.iter().any(|p| match p {
            TemplatePart::Segment(_) => false,
            TemplatePart::Interp(e) => anchored_operand(e),
        }),
        Expr::Match(m) => {
            m.scrutinee.iter().any(|e| anchored_operand(e))
                || m.items.iter().any(|item| match item {
                    MatchItem::Bind(b) => anchored_operand(&b.value),
                    MatchItem::Stmt(e) => anchored_operand(e),
                    MatchItem::Arm(arm) => {
                        arm.guard.iter().any(anchored_operand) || anchored_operand(&arm.result)
                    }
                })
        }
    }
}

fn is_one(r: &Rational) -> bool {
    *r == Rational::from(1)
}

/// Decompose a normalized additive operand into `(coefficient, base)`; a pure
/// numeric literal has base `None`.
fn decompose(e: &Expr) -> (Rational, Option<Expr>) {
    match e {
        Expr::Const(v) if v.as_number().is_some() => (v.as_number().unwrap().clone(), None),
        Expr::PrimOp {
            op: PrimOp::Mul,
            args,
        } if args.len() == 2 => match &args[0] {
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
        Expr::Access {
            target,
            form,
            total,
        } => {
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
