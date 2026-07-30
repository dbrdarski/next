//! Grounding — the recursion **termination** judgment (`next-grounding-specification-v0-5.md`,
//! v0.5 §§1–7; DRAFT, ACCEPTED pending the author's stamp — the judgment rules are stable;
//! only the unproven-*consequence* (P-1, warn-vs-reject) is an open policy pick).
//!
//! Grounding proves a recursive call over an input domain is **well-founded** — it
//! descends toward a base and lands there (GR-05) — so the domain-indexed body check may
//! stop unfolding a recursion instead of chasing a domain that grows without end. This is
//! the specified replacement for the old machine's widening as the analysis's termination
//! bound. It is a *termination* judgment, **not** a safe-input-domain deriver.
//!
//! **Scope of this increment (G-1) — the numeric constant-drift descent certificate**
//! (GR-05), for a single-parameter self-recursive numeric function whose every recursive
//! call steps the parameter by a **constant**. Both GR-05 components are required:
//!
//!  1. **Well-founded descent** — every recursive step's drift is a *negative constant*
//!     (an exposed strictly-positive Progress floor `δ = |drift|`). `GT(0)`-only progress
//!     (Zeno, specimen 1) exposes no floor → unproven.
//!  2. **Landing** (GR-05(2)) — the descending chain reaches the base without skipping it:
//!     a **downward half-line** base (`k <= 1`) lands structurally; a **point** base
//!     (`n == 0`) needs grid alignment — handled here for the clean unit-drift integer
//!     lattice (`countDown` / `factorial` on `GE(0) ∧ Mod(1,0)`).
//!
//! Candidate-locality (GR-04): outside this candidate's applicability it concludes
//! **nothing** — [`Verdict::Unproven`], always sound. Refutation (§7 drift-away / closed
//! orbit), variable drift (§6), lexicographic (§5), exact-singleton chains (§4) and the
//! WorldDecided classifier (§8) are later increments. **Not yet wired** into the body
//! check — same discipline as `region.rs` / `bodycheck.rs`: build standalone, prove
//! green, integrate after.

use num_bigint::BigInt;

use crate::analyzer::region::region_table;
use crate::ast::{
    AccessForm, Arg, Bind, BindingRef, Element, Expr, Field, MatchItem, Pat, PatElem, PrimOp, Ref,
    TemplatePart,
};
use crate::contract::{Contract, ContractEnv, Verdict as Sub, subcontract};
use crate::env::Binding;
use crate::interner::Interner;
use crate::rational::Rational;
use crate::value::{Closure, ValueRef};

/// A grounding verdict (GR-04 / GR-28).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// Well-founded descent **and** landing proven — the recursion terminates on this
    /// domain, so the analysis may stop unfolding it.
    Grounded,
    /// A represented witness forces nontermination (§7) — never minted in G-1.
    Refuted,
    /// No candidate proved and no witness refuted (GR-04) — the sound default.
    Unproven,
}

/// Judge whether `callee` recursing over input `domain` is grounded (terminates).
pub fn ground(callee: &ValueRef, domain: &Contract, cenv: &ContractEnv, interner: &mut Interner) -> Verdict {
    numeric_descent(callee, domain, cenv, interner).unwrap_or(Verdict::Unproven)
}

/// The numeric constant-drift descent certificate (GR-05). `None` ⇒ this candidate does
/// not apply (→ `Unproven`); `Some(Grounded)` ⇒ both components proven.
fn numeric_descent(callee: &ValueRef, domain: &Contract, cenv: &ContractEnv, interner: &mut Interner) -> Option<Verdict> {
    let closure = callee.as_closure()?;
    let param = single_param(&closure.lambda.params)?;
    let rows = region_table(&closure.lambda.body, &param, cenv);

    // Split arms: a row whose result contains a self-call is *recursive* (read each call's
    // drift on the parameter); the rest are *base* rows.
    let mut drifts: Vec<Rational> = Vec::new();
    let mut bases: Vec<Contract> = Vec::new();
    for row in &rows {
        let mut calls = Vec::new();
        collect_self_calls(&row.result, &closure, callee, &mut calls);
        if calls.is_empty() {
            bases.push(row.region.clone());
        } else {
            for arg in &calls {
                drifts.push(constant_drift(arg, &param)?); // non-constant drift ⇒ inapplicable
            }
        }
    }
    if drifts.is_empty() {
        return None; // not self-recursive here — candidate inapplicable
    }

    // (1) Well-founded descent: every drift a strictly negative constant.
    let zero = Rational::from(0);
    if !drifts.iter().all(|d| *d < zero) {
        return None;
    }

    // (2) Landing: a single base row, of a shape the descent provably reaches.
    let [base] = bases.as_slice() else { return None };
    lands(base, &drifts, domain, interner).then_some(Verdict::Grounded)
}

/// Whether a strictly-decreasing integer chain over `domain` provably reaches `base`
/// (GR-05(2)). Integer lattice required (dense measures are deferred).
fn lands(base: &Contract, drifts: &[Rational], domain: &Contract, interner: &mut Interner) -> bool {
    let integers = Contract::Mod { n: BigInt::from(1), r: BigInt::from(0) };
    if !matches!(subcontract(domain, &integers, interner), Sub::Proven) {
        return false;
    }
    match point_value(base) {
        // Point base `b`: grid-aligned only for the clean single unit step over `≥ b`.
        // A wider or non-unit step may straddle the point (specimen 12) — deferred.
        Some(b) => {
            drifts.len() == 1
                && drifts[0] == Rational::from(-1)
                && matches!(subcontract(domain, &Contract::GreaterEq(b), interner), Sub::Proven)
        }
        // Downward half-line base (`k <= b`): a strictly-decreasing integer chain must
        // eventually enter it, from any start (structural landing).
        None => matches!(base, Contract::LessEq(_) | Contract::Less(_)),
    }
}

// ── Reading the shape ─────────────────────────────────────────────────────────

/// The single bound parameter name (`(n)`), or `None` for any other parameter shape.
fn single_param(params: &Pat) -> Option<String> {
    let Pat::Tuple(elems) = params else { return None };
    match elems.as_slice() {
        [PatElem::Pat(Pat::Bind(n))] => Some(n.clone()),
        _ => None,
    }
}

/// The constant drift of a recursive call's argument on `param`: `param - c → -c`,
/// `param + c → +c`. Anything else (`param * c`, a non-parameter carrier, a compound) is
/// not a constant drift — `None`, ending this candidate (GR-04).
fn constant_drift(arg: &Expr, param: &str) -> Option<Rational> {
    let Expr::PrimOp { op, args } = arg else { return None };
    if args.len() != 2 {
        return None;
    }
    match op {
        PrimOp::Sub if is_param(&args[0], param) => const_num(&args[1]).map(|c| -c),
        PrimOp::Add if is_param(&args[0], param) => const_num(&args[1]),
        PrimOp::Add if is_param(&args[1], param) => const_num(&args[0]),
        _ => None,
    }
}

/// A point contract's value (`Equals(v)`, or a degenerate `Range(v, v)` — the form a
/// `== v` guard regionalizes to), else `None`.
fn point_value(c: &Contract) -> Option<Rational> {
    match c {
        Contract::Range(lo, hi) if lo == hi => Some(lo.clone()),
        Contract::Equals(v) => v.as_number().cloned(),
        _ => None,
    }
}

/// Every self-call argument in `e` — the applications whose callee resolves (through the
/// closure's captured environment) to the recursing closure `cv`. Descends every
/// subexpression except nested lambdas (distinct instances); mirrors `bodywalk`'s walk so
/// no self-call is missed (an unread self-call could otherwise be a false proof).
fn collect_self_calls(e: &Expr, closure: &Closure, cv: &ValueRef, out: &mut Vec<Expr>) {
    match e {
        Expr::Const(_) | Expr::Ref(_) => {}
        Expr::Lambda(_) => {} // a distinct instance — not this body's recursion
        Expr::Apply { callee, args } => {
            if resolves_to_self(callee, closure, cv)
                && let Some(Arg::Expr(a)) = args.first()
            {
                out.push(a.clone());
            }
            collect_self_calls(callee, closure, cv, out);
            for a in args {
                match a {
                    Arg::Expr(x) | Arg::Spread(x) => collect_self_calls(x, closure, cv, out),
                }
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                collect_self_calls(a, closure, cv, out);
            }
        }
        Expr::Match(m) => {
            if let Some(s) = &m.scrutinee {
                collect_self_calls(s, closure, cv, out);
            }
            for item in &m.items {
                match item {
                    MatchItem::Bind(Bind { value, .. }) => collect_self_calls(value, closure, cv, out),
                    MatchItem::Stmt(x) => collect_self_calls(x, closure, cv, out),
                    MatchItem::Arm(arm) => {
                        if let Some(g) = &arm.guard {
                            collect_self_calls(g, closure, cv, out);
                        }
                        collect_self_calls(&arm.result, closure, cv, out);
                    }
                }
            }
        }
        Expr::TupleCons(els) => {
            for el in els {
                match el {
                    Element::Expr(x) | Element::Spread(x) => collect_self_calls(x, closure, cv, out),
                }
            }
        }
        Expr::RecordCons(fs) => {
            for f in fs {
                match f {
                    Field::Field { value, .. } | Field::Spread(value) => collect_self_calls(value, closure, cv, out),
                    Field::Computed { key, value } => {
                        collect_self_calls(key, closure, cv, out);
                        collect_self_calls(value, closure, cv, out);
                    }
                }
            }
        }
        Expr::Access { target, form, .. } => {
            collect_self_calls(target, closure, cv, out);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(x) => collect_self_calls(x, closure, cv, out),
                AccessForm::Slice { lo, hi } => {
                    if let Some(x) = lo {
                        collect_self_calls(x, closure, cv, out);
                    }
                    if let Some(x) = hi {
                        collect_self_calls(x, closure, cv, out);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    collect_self_calls(x, closure, cv, out);
                }
            }
        }
        Expr::Write { value, .. } => collect_self_calls(value, closure, cv, out),
    }
}

/// Whether `callee` is a reference that resolves, through `closure`'s captured
/// environment, to the recursing closure `cv` (pointer identity — the self-capture is the
/// same allocation).
fn resolves_to_self(callee: &Expr, closure: &Closure, cv: &ValueRef) -> bool {
    let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = callee else { return false };
    matches!(closure.env.lookup(n), Some(Binding::Value(v)) if &v == cv)
}

fn is_param(e: &Expr, param: &str) -> bool {
    matches!(e, Expr::Ref(Ref::Immutable(BindingRef::Name(n))) if n == param)
}

fn const_num(e: &Expr) -> Option<Rational> {
    match e {
        Expr::Const(v) => v.as_number().cloned(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::harness::run_source_in;

    /// `GE(0) ∧ Mod(1,0)` — the non-negative integers, factorial's / countDown's domain.
    fn nonneg_ints() -> Contract {
        Contract::Intersection(
            Box::new(Contract::GreaterEq(Rational::from(0))),
            Box::new(Contract::Mod { n: BigInt::from(1), r: BigInt::from(0) }),
        )
    }

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    #[test]
    fn count_down_grounds_over_nonneg_integers() {
        // Point base `n == 0`, unit drift −1, integer domain → grid-aligned landing.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        assert_eq!(ground(&cd, &nonneg_ints(), &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn factorial_grounds_over_nonneg_integers() {
        // The self-call `f(n - 1)` is nested under `n * _`; the walk still reads its drift.
        let mut i = Interner::new();
        let fact = f("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf", &mut i);
        assert_eq!(ground(&fact, &nonneg_ints(), &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn half_line_base_grounds_structurally() {
        // Downward half-line base `k <= 1` — the descending chain enters it; no grid needed.
        let mut i = Interner::new();
        let g = f("g = (k) => k <= 1 ? k : g(k - 1)\ng", &mut i);
        assert_eq!(ground(&g, &nonneg_ints(), &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn ascending_drift_is_unproven() {
        // `n + 1` is not descent — no floor. Candidate inapplicable → Unproven (sound).
        let mut i = Interner::new();
        let up = f("f = (n) => n == 0 ? 0 : f(n + 1)\nf", &mut i);
        assert_eq!(ground(&up, &nonneg_ints(), &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    #[test]
    fn off_grid_point_base_is_unproven_in_g1() {
        // Drift −2 to point base 0: parity-straddling (specimen 12 — refuted later, not now).
        // G-1 defers the non-unit grid check → Unproven (never a false proof).
        let mut i = Interner::new();
        let step2 = f("f = (n) => n == 0 ? 0 : f(n - 2)\nf", &mut i);
        assert_eq!(ground(&step2, &nonneg_ints(), &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    #[test]
    fn non_integer_domain_is_unproven() {
        // Without the integer lattice the dense-measure landing is deferred → Unproven.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        assert_eq!(ground(&cd, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }
}
