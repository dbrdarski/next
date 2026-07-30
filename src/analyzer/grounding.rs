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
//! **Refutation (G-2, §7)** — the **drift-away** certificate (GR-23a): from an *admitted*
//! represented-exact start written at the call (GR-22, e.g. `f(1)`), a single forced
//! linear descent whose forward lattice provably misses every base region diverges →
//! [`Verdict::Refuted`]. A broad (non-represented-exact) domain admits no witness → stays
//! `Unproven` (GR-21; specimen 3c). The **closed-orbit** refutation form (GR-11) is a
//! later increment.
//!
//! **Program-expressed linear-measure descent (G-3/G-4, §6 GR-15a/16)** — a base arm's
//! half-line stop `E ⋈ c` whose varying side `E` is a *linear* measure over the parameters
//! (`n`; `2a + b`). Its drift per recursive call is read by **substitute-and-normalize**
//! (GR-16): substitute the call's arguments into `E`, normalize as a linear form, subtract
//! — a nonzero constant of a single sign facing the stop is a floored monotone measure;
//! coefficient-0 positions are carried freely (`(n, acc) => n <= 0 ? acc : f(n-1, acc+n)`;
//! `(a, b) => 2a+b <= 0 ? d : f(a-1, b+1)`). Structural, domain-independent landing.
//! Subsumes the bare-argument counter. Point (`==`) stops (grid, GR-05(2)/GR-18) and
//! nonlinear measures are later increments; two-varying-side relational stops are
//! **[permanent]** unprovable by this route (GR-18).
//!
//! Candidate-locality (GR-04): outside applicability each candidate concludes **nothing**
//! — [`Verdict::Unproven`], always sound. The lexicographic certificate (§5), exact-
//! singleton chains (§4) and the WorldDecided classifier (§8) are later increments. **Not
//! yet wired** into the body check — same discipline as `region.rs` / `bodycheck.rs`:
//! build standalone, prove green, integrate after.

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
    /// A represented-exact witness forces nontermination (§7) — minted by the drift-away
    /// certificate (GR-23a); the closed-orbit form (GR-11) is a later increment.
    Refuted,
    /// No candidate proved and no witness refuted (GR-04) — the sound default.
    Unproven,
}

/// Judge whether `callee` recursing over input `domain` is grounded (terminates).
///
/// A candidate may prove groundedness (GR-05); failing that, an **admitted witness** — a
/// represented-exact start actually written at the call (GR-22) — may **refute** via
/// drift-away (GR-23a). No witness ⇒ procedure-relative `Unproven` (GR-04/GR-21). Grounded
/// is judged first: a proven descent is never also a divergence.
pub fn ground(callee: &ValueRef, domain: &Contract, cenv: &ContractEnv, interner: &mut Interner) -> Verdict {
    if matches!(numeric_descent(callee, domain, cenv, interner), Some(Verdict::Grounded))
        || measure_descent(callee)
    {
        return Verdict::Grounded;
    }
    if let Some(start) = point_value(domain)
        && drift_away(callee, &start, cenv)
    {
        return Verdict::Refuted;
    }
    Verdict::Unproven
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
            for arglist in &calls {
                let arg = arglist.first()?; // spread / zero-arg self-call ⇒ inapplicable
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

/// The GR-23a **drift-away** refutation from a represented-exact start `start`: a single
/// forced *linear* recursion (one recursive row, one self-call, constant negative drift)
/// whose forward lattice `{ start + drift·k : k ≥ 0 }` provably misses **every** base
/// region — a denotationally forced infinite descent (GR-20/23). Because the lattice
/// includes the start (`k = 0`), a start that already sits in a base is not a valid
/// recursive start and is correctly rejected. Sound: `true` only when the miss is certain.
fn drift_away(callee: &ValueRef, start: &Rational, cenv: &ContractEnv) -> bool {
    let Some(closure) = callee.as_closure() else { return false };
    let Some(param) = single_param(&closure.lambda.params) else { return false };
    let rows = region_table(&closure.lambda.body, &param, cenv);

    let mut bases = Vec::new();
    let mut drift = None;
    let mut rec_rows = 0;
    for row in &rows {
        let mut calls = Vec::new();
        collect_self_calls(&row.result, &closure, callee, &mut calls);
        if calls.is_empty() {
            bases.push(row.region.clone());
        } else {
            rec_rows += 1;
            if calls.len() != 1 {
                return false; // branching recursion — not a single forced path
            }
            let Some(arg) = calls[0].first() else { return false };
            match constant_drift(arg, &param) {
                Some(d) => drift = Some(d),
                None => return false,
            }
        }
    }
    let Some(d) = drift else { return false };
    if rec_rows != 1 || d >= Rational::from(0) {
        return false; // not a single strictly-descending forced path
    }
    // Forced descent that misses every base ⇒ never lands ⇒ diverges. `!reaches` over the
    // whole lattice is both base-disjointness (v) and transition closure (vi).
    bases.iter().all(|b| !reaches(start, &d, b))
}

/// Whether the descending lattice `{ start + d·k : k ≥ 0 }` (`d < 0`) reaches `base`.
/// Conservative: an unrecognized base shape returns `true`, blocking a refutation.
fn reaches(start: &Rational, d: &Rational, base: &Contract) -> bool {
    // A point `p` lies on the lattice iff `(start − p) / |d|` is a non-negative integer.
    if let Some(p) = point_value(base) {
        let q = (start.clone() - p) / -d.clone();
        return q.is_integer() && q >= Rational::from(0);
    }
    match base {
        // An unbounded descent always crosses into a downward half-line.
        Contract::LessEq(_) | Contract::Less(_) => true,
        // An upward half-line is reached only if the start already lies in it (`k = 0`);
        // every later state only descends further away.
        Contract::GreaterEq(b) => start >= b,
        Contract::Greater(b) => start > b,
        _ => true, // unknown base shape — block the refutation (sound)
    }
}

/// **Program-expressed linear-measure descent** (§6 GR-15a/16). A base arm — reached
/// **before** any recursive arm — stops on a **half-line** test `E ⋈ c` whose varying side
/// `E` is a *linear* combination of the parameters (GR-15a: the canonicalized expression
/// the base tests; `n`, `2a + b`). Its drift across each recursive call is read by
/// **substitute-and-normalize** (GR-16): substitute the call's argument expressions into
/// `E`, normalize as a linear form, subtract — a nonzero constant of a single sign facing
/// the stop is a floored monotone measure. Positions with coefficient 0 are carried
/// freely. Landing is **structural** (a floored step crosses a half-line in finitely many
/// steps — Archimedean), so no domain or range (GR-18) is needed. Subsumes the
/// bare-argument counter (`E = n`). Point (`==`) stops need the grid (GR-05(2)/GR-18) and
/// stay with `numeric_descent` / a later increment; two-varying-side (relational) stops
/// contribute nothing (GR-15a).
fn measure_descent(callee: &ValueRef) -> bool {
    let Some(closure) = callee.as_closure() else { return false };
    let Some(params) = param_names(&closure.lambda.params) else { return false };
    let Expr::Match(m) = &*closure.lambda.body else { return false };

    // Classify arms in order: a base arm (no self-call) offers its guard as a stop; a
    // recursive arm offers each self-call's positional argument list.
    let mut stops: Vec<Expr> = Vec::new();
    let mut rec_calls: Vec<Vec<Expr>> = Vec::new();
    let mut first_rec = usize::MAX;
    for (idx, item) in m.items.iter().enumerate() {
        let MatchItem::Arm(arm) = item else { continue };
        let mut calls = Vec::new();
        collect_self_calls(&arm.result, &closure, callee, &mut calls);
        if calls.is_empty() {
            // A stop is only sound if it is tested *before* any recursion can fire.
            if let Some(g) = &arm.guard
                && idx < first_rec
            {
                stops.push(g.clone());
            }
        } else {
            rec_calls.extend(calls);
            first_rec = first_rec.min(idx);
        }
    }
    if rec_calls.is_empty() {
        return false;
    }
    stops.iter().any(|g| measure_ok(g, &params, &rec_calls))
}

/// Whether the half-line stop `g` reads as `E ⋈ c` for a linear measure `E` that drifts by
/// a nonzero constant of a single sign facing the stop across every recursive call.
fn measure_ok(g: &Expr, params: &[String], rec_calls: &[Vec<Expr>]) -> bool {
    let Expr::PrimOp { op, args } = g else { return false };
    if args.len() != 2 {
        return false;
    }
    let (Some(l), Some(r)) = (linear_form(&args[0], params), linear_form(&args[1], params)) else {
        return false;
    };
    // GR-15a: exactly one varying side. The measure `E` is it; orient the op as `E ⋈ c`.
    let (e, op) = match (l.is_constant(), r.is_constant()) {
        (false, true) => (l, *op),
        (true, false) => (r, flip(*op)),
        _ => return false, // both constant, or both varying (relational — [permanent])
    };
    let mut ascending: Option<bool> = None;
    for call in rec_calls {
        let Some(d) = drift_on(&e, call, params) else { return false };
        if d.is_zero() {
            return false; // no progress on this measure
        }
        let up = d > Rational::from(0);
        match ascending {
            None => ascending = Some(up),
            Some(prev) if prev != up => return false, // mixed directions — not monotone
            _ => {}
        }
    }
    let Some(ascending) = ascending else { return false };
    matches!(
        (op, ascending),
        (PrimOp::Le | PrimOp::Lt, false) | (PrimOp::Ge | PrimOp::Gt, true)
    )
}

/// The drift of measure `e` across one recursive call — `E[args] − E` by substitute-and-
/// normalize (GR-16): substitute each parameter with its argument's linear form, sum, and
/// subtract. `Some(δ)` only when the result is a **constant** (correlation-preserving);
/// otherwise the drift is relational and this route concludes nothing (GR-18).
fn drift_on(e: &LinComb, call: &[Expr], params: &[String]) -> Option<Rational> {
    let mut substituted = LinComb::constant(e.constant.clone(), params.len());
    for (i, ci) in e.coeffs.iter().enumerate() {
        if ci.is_zero() {
            continue; // a coefficient-0 position is carried freely — its argument is irrelevant
        }
        let arg = call.get(i)?;
        substituted = substituted.add(&linear_form(arg, params)?.scale(ci));
    }
    let drift = substituted.sub(e);
    drift.is_constant().then_some(drift.constant)
}

/// A linear combination `Σ coeffs[i]·paramᵢ + constant` over the parameter list.
#[derive(Clone)]
struct LinComb {
    coeffs: Vec<Rational>,
    constant: Rational,
}

impl LinComb {
    fn constant(constant: Rational, n: usize) -> LinComb {
        LinComb { coeffs: vec![Rational::from(0); n], constant }
    }
    fn is_constant(&self) -> bool {
        self.coeffs.iter().all(Rational::is_zero)
    }
    fn add(&self, o: &LinComb) -> LinComb {
        LinComb {
            coeffs: self.coeffs.iter().zip(&o.coeffs).map(|(a, b)| a.clone() + b.clone()).collect(),
            constant: self.constant.clone() + o.constant.clone(),
        }
    }
    fn sub(&self, o: &LinComb) -> LinComb {
        LinComb {
            coeffs: self.coeffs.iter().zip(&o.coeffs).map(|(a, b)| a.clone() - b.clone()).collect(),
            constant: self.constant.clone() - o.constant.clone(),
        }
    }
    fn scale(&self, k: &Rational) -> LinComb {
        LinComb {
            coeffs: self.coeffs.iter().map(|a| a.clone() * k.clone()).collect(),
            constant: self.constant.clone() * k.clone(),
        }
    }
}

/// Parse `e` as a [`LinComb`] over `params`; `None` if it is nonlinear (`param·param`,
/// division by a variable) or mentions a non-parameter reference.
fn linear_form(e: &Expr, params: &[String]) -> Option<LinComb> {
    match e {
        Expr::Const(v) => Some(LinComb::constant(v.as_number()?.clone(), params.len())),
        Expr::Ref(Ref::Immutable(BindingRef::Name(n))) => {
            let i = params.iter().position(|p| p == n)?;
            let mut lc = LinComb::constant(Rational::from(0), params.len());
            lc.coeffs[i] = Rational::from(1);
            Some(lc)
        }
        Expr::PrimOp { op: PrimOp::Add, args } if args.len() == 2 => {
            Some(linear_form(&args[0], params)?.add(&linear_form(&args[1], params)?))
        }
        Expr::PrimOp { op: PrimOp::Sub, args } if args.len() == 2 => {
            Some(linear_form(&args[0], params)?.sub(&linear_form(&args[1], params)?))
        }
        Expr::PrimOp { op: PrimOp::Neg, args } if args.len() == 1 => {
            Some(LinComb::constant(Rational::from(0), params.len()).sub(&linear_form(&args[0], params)?))
        }
        Expr::PrimOp { op: PrimOp::Mul, args } if args.len() == 2 => {
            let (a, b) = (linear_form(&args[0], params)?, linear_form(&args[1], params)?);
            if a.is_constant() {
                Some(b.scale(&a.constant))
            } else if b.is_constant() {
                Some(a.scale(&b.constant))
            } else {
                None // param · param — nonlinear
            }
        }
        _ => None,
    }
}

/// The comparison with operands swapped (`a < b` ⇔ `b > a`); `==`/`!=` are symmetric.
fn flip(op: PrimOp) -> PrimOp {
    match op {
        PrimOp::Lt => PrimOp::Gt,
        PrimOp::Gt => PrimOp::Lt,
        PrimOp::Le => PrimOp::Ge,
        PrimOp::Ge => PrimOp::Le,
        other => other,
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

/// Every bound parameter name in a flat parameter tuple (`(n, acc)` → `["n", "acc"]`), or
/// `None` if any element is not a bare binding (a rest or nested pattern).
fn param_names(params: &Pat) -> Option<Vec<String>> {
    let Pat::Tuple(elems) = params else { return None };
    elems
        .iter()
        .map(|e| match e {
            PatElem::Pat(Pat::Bind(n)) => Some(n.clone()),
            _ => None,
        })
        .collect()
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

/// Every self-call's **positional argument list** in `e` — the applications whose callee
/// resolves (through the closure's captured environment) to the recursing closure `cv`.
/// Descends every subexpression except nested lambdas (distinct instances); mirrors
/// `bodywalk`'s walk so no self-call is missed (an unread self-call could otherwise be a
/// false proof). A self-call carrying a spread argument has no reliable positional mapping
/// and is recorded as an **empty** list — every candidate then rejects it.
fn collect_self_calls(e: &Expr, closure: &Closure, cv: &ValueRef, out: &mut Vec<Vec<Expr>>) {
    match e {
        Expr::Const(_) | Expr::Ref(_) => {}
        Expr::Lambda(_) => {} // a distinct instance — not this body's recursion
        Expr::Apply { callee, args } => {
            if resolves_to_self(callee, closure, cv) {
                let mut positional = Vec::new();
                let mut clean = true;
                for a in args {
                    match a {
                        Arg::Expr(x) => positional.push(x.clone()),
                        Arg::Spread(_) => clean = false,
                    }
                }
                out.push(if clean { positional } else { Vec::new() });
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
    fn off_grid_point_base_over_broad_domain_is_unproven() {
        // Drift −2 to point base 0 over the *broad* domain: descent isn't proved (non-unit)
        // and there is no admitted represented-exact witness (GR-22) → Unproven. The
        // divergent inputs are only refuted from an *exact* start (next test; specimen 3c).
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

    // ── G-2: drift-away refutation (GR-23a) ──────────────────────────────────

    #[test]
    fn drift_away_refutes_off_grid_from_odd_witness() {
        // Specimen 12: `f(n-2)` from the written argument 1 — the odd lattice 1, −1, −3, …
        // misses the even point base 0 → forced infinite descent → refuted, witness 1.
        let mut i = Interner::new();
        let step2 = f("f = (n) => n == 0 ? 0 : f(n - 2)\nf", &mut i);
        let one = Contract::Equals(i.integer(1));
        assert_eq!(ground(&step2, &one, &ContractEnv::new(), &mut i), Verdict::Refuted);
    }

    #[test]
    fn even_witness_of_the_same_function_is_not_refuted() {
        // From 2 the lattice 2, 0, … *hits* the base 0 → terminates → not refuted (and the
        // non-unit descent isn't proved either) → Unproven. Same function, opposite fate by
        // witness parity.
        let mut i = Interner::new();
        let step2 = f("f = (n) => n == 0 ? 0 : f(n - 2)\nf", &mut i);
        let two = Contract::Equals(i.integer(2));
        assert_eq!(ground(&step2, &two, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    #[test]
    fn exact_witness_where_descent_proves_grounds_not_refutes() {
        // From an exact start where descent *does* prove (unit drift), Grounded wins — a
        // proven descent is never also a divergence.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert_eq!(ground(&cd, &five, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    // ── G-3/G-4: program-expressed linear-measure descent (§6 GR-15a/16) ─────

    #[test]
    fn compound_measure_grounds_when_no_single_arg_descends() {
        // `2a + b` drifts −1 under `f(a-1, b+1)` — but neither `a` nor `b` alone is a
        // monotone counter (b ascends). Substitute-and-normalize reads the linear measure.
        let mut i = Interner::new();
        let s = f("f = (a, b) => 2 * a + b <= 0 ? a : f(a - 1, b + 1)\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn relational_two_varying_stop_is_unproven() {
        // `a <= b` — both sides vary; the correlation is relational ([permanent]) and this
        // route concludes nothing (GR-15a/18), even though it happens to terminate.
        let mut i = Interner::new();
        let s = f("f = (a, b) => a <= b ? a : f(a - 1, b)\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    #[test]
    fn accumulator_counter_grounds_descending() {
        // `n` is the counter (drift −1 toward the `n <= 0` stop); `acc` is carried freely.
        // Structural landing — the (broad) domain is irrelevant.
        let mut i = Interner::new();
        let s = f("f = (n, acc) => n <= 0 ? acc : f(n - 1, acc + n)\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn accumulator_counter_grounds_ascending() {
        // Ascending counter toward an upper stop `n >= 100` (drift +1) — the mirror case.
        let mut i = Interner::new();
        let s = f("f = (n, acc) => n >= 100 ? acc : f(n + 1, acc + n)\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn counter_moving_away_from_the_stop_is_unproven() {
        // Drift +1 but the stop `n <= 0` is a *lower* half-line — the counter moves away,
        // never crossing it. No matching stop → Unproven (it genuinely diverges for n > 0).
        let mut i = Interner::new();
        let s = f("f = (n, acc) => n <= 0 ? acc : f(n + 1, acc)\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    #[test]
    fn a_carried_only_recursion_has_no_counter() {
        // Neither position moves toward its stop: `n` is carried and the stop is on the
        // carried `acc`. No floored counter → Unproven (sound — it can diverge).
        let mut i = Interner::new();
        let s = f("f = (n, acc) => acc <= 0 ? n : f(n, acc)\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }
}
