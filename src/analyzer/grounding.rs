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
//! **Refutation (G-2/G-7, §7)** — the **constant-drift** certificate (GR-20/23): from an
//! *admitted* represented-exact start written at the call (GR-22, e.g. `f(1)`), a single
//! forced linear recursion whose forward orbit `{ start + drift·k }` provably misses every
//! base region diverges → [`Verdict::Refuted`]. Covers `drift < 0` (GR-23a drift-away),
//! `drift > 0` (ascending mirror), and `drift == 0` (a **period-1 closed orbit** — GR-11's
//! degenerate case, `f(n)` on itself). A broad (non-represented-exact) domain admits no
//! witness → stays `Unproven` (GR-21; specimen 3c). The general closed-orbit form (a
//! required-dependency cycle, GR-11) is a later increment.
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
//! **Lexicographic descent (G-5, §5 GR-13/14)** — an ordered dictionary of argument
//! positions that lex-decreases on every recursive call: the first changing position
//! decreases, and every decreasing position is bounded below on that call's path (a guard
//! gates its decrease — component-grain landing, `(a, b) => a <= 0 ? b : b <= 0 ?
//! f(a-1, 10) : f(a, b-1)`). v1 positions are arguments only, components **descending**;
//! ascending components and `==`/point-stop floors (Ackermann's — grid + domain) are later.
//!
//! **Structural descent (G-6, §2b)** — recursion that peels a tuple parameter
//! (`l :: { [] => …, [h, ...rest] => f(rest) }`): the recursive arm's pattern removes ≥1
//! element and the call passes the remainder, so the parameter's length (intrinsically
//! `GE(0) ∧ Mod(1, 0)`) strictly decreases and is bounded below by 0 — terminates
//! regardless of the base, no domain needed.
//!
//! **Mutual recursion (G-8, §5 GR-07)** — the reachable closure group forms the mutual SCC;
//! if every cross-call decreases a shared single-parameter measure and every recursive member
//! has a descending half-line base, every cycle composes to a decrease so the group terminates
//! (`isEven`/`isOdd` on `n <= 0`). The enumeration-free sufficient case; mixed-sign
//! oscillator cycles need the full composition — later.
//!
//! Candidate-locality (GR-04): outside applicability each candidate concludes **nothing**
//! — [`Verdict::Unproven`], always sound. Point-base/Ackermann (grid + domain, GR-18),
//! exact-singleton chains (§4) and the WorldDecided classifier (§8) are later increments.
//! **Not yet wired** into the body check — same discipline as `region.rs` / `bodycheck.rs`:
//! build standalone, prove green, integrate after.

use num_bigint::BigInt;

use crate::analyzer::bodywalk::reachable_closures;
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
    /// A represented-exact witness forces nontermination (§7) — minted by the constant-drift
    /// certificate (GR-23a drift-away, its ascending mirror, and the period-1 closed orbit).
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
        || lex_descent(callee)
        || structural_descent(callee)
        || mutual_descent(callee)
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

/// The **constant-drift refutation** from a represented-exact start `start` (GR-20/23): a
/// single forced *linear* recursion (one recursive row, one self-call, **any** constant
/// drift) whose forward orbit `{ start + drift·k : k ≥ 0 }` provably misses **every** base
/// region — a denotationally forced infinite path. `drift < 0` is the GR-23a drift-away
/// (descending), `drift > 0` its ascending mirror, and `drift == 0` a **period-1 closed
/// orbit** (GR-11's degenerate case — `f(n)` recurring on itself). Because the orbit
/// includes the start (`k = 0`), a start already in a base is correctly rejected. Sound:
/// `true` only when the miss is certain.
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
            match position_drift(arg, &param) {
                Some(d) => drift = Some(d),
                None => return false,
            }
        }
    }
    let Some(d) = drift else { return false };
    if rec_rows != 1 {
        return false; // not a single forced path
    }
    // A forced orbit that misses every base ⇒ never lands ⇒ diverges. `!reaches` over the
    // whole orbit is both base-disjointness (v) and transition closure (vi).
    bases.iter().all(|b| !reaches(start, &d, b))
}

/// Whether the arithmetic progression `{ start + d·k : k ≥ 0 }` reaches `base` — the forward
/// orbit of a constant-drift recursion (`d < 0` descends, `d > 0` ascends, `d == 0` is a
/// period-1 fixed point). Conservative: an unrecognized base shape returns `true`, blocking
/// a refutation.
fn reaches(start: &Rational, d: &Rational, base: &Contract) -> bool {
    // A point `p` is on the orbit iff `k = (p − start)/d` is a non-negative integer (or, when
    // the orbit is a fixed point, `p == start`).
    if let Some(p) = point_value(base) {
        if d.is_zero() {
            return &p == start;
        }
        let q = (start.clone() - p) / -d.clone(); // = (p − start)/d, the step count k
        return q.is_integer() && q >= Rational::from(0);
    }
    let zero = Rational::from(0);
    match base {
        // Reached iff some orbit value falls in the half-line: a descent always crosses a
        // downward half-line; otherwise the extreme value is the start.
        Contract::LessEq(b) => *d < zero || start <= b,
        Contract::Less(b) => *d < zero || start < b,
        Contract::GreaterEq(b) => *d > zero || start >= b,
        Contract::Greater(b) => *d > zero || start > b,
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

// ── Lexicographic descent (§5 GR-13/14) ───────────────────────────────────────

/// Lexicographic descent (§5 GR-13/14, single-function / one-cycle case). Some ordered
/// sequence of argument positions (the *dictionary*) lex-decreases on every recursive
/// call: reading the dictionary in order, the first position that changes does so by a
/// **decrease**, and every position that decreases on a call is **bounded below on that
/// call's path** (a lower-bound guard gates its decreasing transition — landing at
/// component grain, GR-14 domain closure), so each component is well-founded. v1 dictionary
/// positions are argument positions only (GR-14); components are **descending**. Ascending
/// components and `==`/point-stop floors (Ackermann's — needing the grid + domain) are
/// later increments.
fn lex_descent(callee: &ValueRef) -> bool {
    let Some(closure) = callee.as_closure() else { return false };
    let Some(params) = param_names(&closure.lambda.params) else { return false };
    let mut calls = Vec::new();
    walk(&closure.lambda.body, &closure, std::slice::from_ref(callee), &params, &vec![false; params.len()], &mut calls);
    if calls.is_empty() {
        return false;
    }
    let positions: Vec<usize> = (0..params.len()).collect();
    injective_seqs(&positions)
        .into_iter()
        .filter(|dict| dict.len() >= 2) // length-1 dictionaries are `measure_descent`'s job
        .any(|dict| calls.iter().all(|(args, lb)| lex_call_ok(&dict, args, lb, &params)))
}

/// One recursive call lex-decreases under `dict`: reading the dictionary in order the first
/// changed position decreases (a later increase/reset is fine once a decrease is fixed), and
/// **every** decreasing position is lower-bounded on this call's path (`lb`).
fn lex_call_ok(dict: &[usize], args: &[Expr], lb: &[bool], params: &[String]) -> bool {
    let mut decreaser_found = false;
    for &i in dict {
        let Some(arg) = args.get(i) else { return false };
        match position_drift(arg, &params[i]) {
            Some(d) if d < Rational::from(0) => {
                if !lb.get(i).copied().unwrap_or(false) {
                    return false; // an ungated decrease — component not bounded below
                }
                decreaser_found = true; // the first decrease is the lex-decreaser (earlier were 0)
            }
            Some(d) if d > Rational::from(0) => {
                if !decreaser_found {
                    return false; // first change is an increase → not a lex decrease
                }
            }
            Some(_) => {} // zero — carried, look further down the dictionary
            None => {
                if !decreaser_found {
                    return false; // first change is an unreadable reset → cannot order
                }
            }
        }
    }
    decreaser_found
}

/// The drift of parameter `param` in a recursive call's argument: `param → 0` (carried),
/// `param ± c → ±c`, else `None`.
fn position_drift(arg: &Expr, param: &str) -> Option<Rational> {
    if is_param(arg, param) {
        return Some(Rational::from(0));
    }
    constant_drift(arg, param)
}

/// If guard `g` (optionally `negated`) is a **lower bound** on a bare parameter — `p > c` /
/// `p >= c`, or the negation of `p <= c` / `p < c` — its parameter index, else `None`.
fn guard_lb(g: &Expr, negated: bool, params: &[String]) -> Option<usize> {
    let Expr::PrimOp { op, args } = g else { return None };
    if args.len() != 2 {
        return None;
    }
    let (idx, op) = if let (Some(i), true) = (param_index(&args[0], params), const_num(&args[1]).is_some()) {
        (i, *op)
    } else if let (Some(i), true) = (param_index(&args[1], params), const_num(&args[0]).is_some()) {
        (i, flip(*op))
    } else {
        return None;
    };
    let op = if negated { negate_cmp(op) } else { op };
    matches!(op, PrimOp::Gt | PrimOp::Ge).then_some(idx)
}

/// The index of a bare parameter reference in `params`, else `None`.
fn param_index(e: &Expr, params: &[String]) -> Option<usize> {
    let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = e else { return None };
    params.iter().position(|p| p == n)
}

/// The logical negation of a comparison operator.
fn negate_cmp(op: PrimOp) -> PrimOp {
    match op {
        PrimOp::Lt => PrimOp::Ge,
        PrimOp::Le => PrimOp::Gt,
        PrimOp::Gt => PrimOp::Le,
        PrimOp::Ge => PrimOp::Lt,
        PrimOp::Eq => PrimOp::Ne,
        PrimOp::Ne => PrimOp::Eq,
        other => other,
    }
}

/// Every non-empty ordered injective sequence of `items` (subsets × orderings) — the
/// GR-14 dictionary enumeration, finite and bounded by arity.
fn injective_seqs(items: &[usize]) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let head = rest.remove(i);
        out.push(vec![head]);
        for mut tail in injective_seqs(&rest) {
            let mut seq = vec![head];
            seq.append(&mut tail);
            out.push(seq);
        }
    }
    out
}

// ── Structural descent (§2b) ──────────────────────────────────────────────────

/// **Structural descent** (§2b) — recursion that **peels** a tuple parameter. The body
/// pattern-matches the parameter (`l :: { [] => …, [h, ...rest] => … f(rest) … }`); every
/// recursive arm's pattern removes ≥1 element and binds the remainder, and every self-call
/// passes that remainder back in the parameter's position. The parameter's **length** is
/// intrinsically `GE(0) ∧ Mod(1, 0)` (a non-negative integer — tuple Λ-semantics) and drops
/// by the peel count each step: strictly decreasing and bounded below by 0, so the recursion
/// terminates **regardless of the base** (a length that undershoots the peel pattern simply
/// stops matching it — exhaustiveness is E10's concern, not grounding's). Landing is
/// intrinsic; no domain needed. Multi-parameter: the peeled position descends, others carried.
fn structural_descent(callee: &ValueRef) -> bool {
    let Some(closure) = callee.as_closure() else { return false };
    let Some(params) = param_names(&closure.lambda.params) else { return false };
    let Expr::Match(m) = &*closure.lambda.body else { return false };
    let Some(scrut) = &m.scrutinee else { return false };
    let Some(pos) = param_index(scrut, &params) else { return false };

    let mut has_recursive = false;
    for item in &m.items {
        let MatchItem::Arm(arm) = item else { continue };
        let mut calls = Vec::new();
        collect_self_calls(&arm.result, &closure, callee, &mut calls);
        if calls.is_empty() {
            continue; // a base arm
        }
        // A recursive arm must peel the scrutinee and recurse on the remainder.
        let Some(rest) = arm.pattern.as_ref().and_then(peel_binding) else {
            return false;
        };
        for call in &calls {
            let Some(arg) = call.get(pos) else { return false };
            if !is_param(arg, &rest) {
                return false; // the peeled position must carry the remainder
            }
        }
        has_recursive = true;
    }
    has_recursive
}

/// The remainder binding of a **peeling** tuple pattern — `[e₁ … eₖ, ...rest]` (rest at any
/// position) with **k ≥ 1** fixed elements and a single *named* rest → `rest`. `None` if
/// there is no named rest, more than one rest, or nothing is peeled (`[...all]`).
fn peel_binding(pat: &Pat) -> Option<String> {
    let Pat::Tuple(elems) = pat else { return None };
    let mut peeled = 0;
    let mut rest = None;
    for e in elems {
        match e {
            PatElem::Pat(_) => peeled += 1,
            PatElem::Rest(Some(name)) => {
                if rest.is_some() {
                    return None; // one rest per level
                }
                rest = Some(name.clone());
            }
            PatElem::Rest(None) => return None, // unnamed rest — nothing to recurse on
        }
    }
    if peeled >= 1 { rest } else { None }
}

// ── Mutual recursion (GR-07) ──────────────────────────────────────────────────

/// Mutual-recursion descent (§5 GR-07, the enumeration-free sufficient sub-case). The
/// reachable closure group is the mutual SCC; if **every** cross-call in the group decreases
/// a shared single-parameter measure by a constant and every recursive member has a
/// descending half-line base on it, then every simple cycle composes to a strict decrease
/// (a sum of negatives) and the measure is bounded below — so the whole group terminates.
/// This discharges GR-07's per-cycle obligation by the stronger per-edge condition (no cycle
/// enumeration); landing is structural (domain-independent). A composed measure that only
/// descends over a *mixed-sign* cycle (the oscillator specimen) needs the full composition —
/// a later increment.
fn mutual_descent(callee: &ValueRef) -> bool {
    let group = reachable_closures(callee.clone());
    if group.len() < 2 {
        return false; // single function — the self-recursion candidates handle it
    }
    group.iter().all(|f| member_descends(f, &group))
}

/// A group member is compatible with mutual descent: it makes no group call (a non-recursive
/// leaf), or every group call decreases its parameter by a constant and it has a descending
/// half-line base on that parameter.
fn member_descends(f: &ValueRef, group: &[ValueRef]) -> bool {
    let Some(closure) = f.as_closure() else { return false };
    let Some(param) = single_param(&closure.lambda.params) else { return false };
    let Expr::Match(m) = &*closure.lambda.body else { return false };

    let mut stops = Vec::new();
    let mut calls: Vec<Vec<Expr>> = Vec::new();
    let mut first_call = usize::MAX;
    for (idx, item) in m.items.iter().enumerate() {
        let MatchItem::Arm(arm) = item else { continue };
        let mut gc = Vec::new();
        walk(&arm.result, &closure, group, &[], &[], &mut gc);
        if gc.is_empty() {
            if let Some(g) = &arm.guard
                && idx < first_call
            {
                stops.push(g.clone());
            }
        } else {
            calls.extend(gc.into_iter().map(|(args, _)| args));
            first_call = first_call.min(idx);
        }
    }
    if calls.is_empty() {
        return true; // a non-recursive member — contributes no cycle edge
    }
    let decreases = calls.iter().all(|call| {
        call.first()
            .and_then(|arg| constant_drift(arg, &param))
            .is_some_and(|d| d < Rational::from(0))
    });
    decreases && stops.iter().any(|g| descending_stop(g, &param))
}

/// Whether guard `g` is a **descending** half-line stop on `param` — `param <= c` /
/// `param < c` (or the flipped `c >= param` / `c > param`) — the floor a decreasing measure
/// lands in.
fn descending_stop(g: &Expr, param: &str) -> bool {
    let Expr::PrimOp { op, args } = g else { return false };
    if args.len() != 2 {
        return false;
    }
    let op = if is_param(&args[0], param) && const_num(&args[1]).is_some() {
        *op
    } else if is_param(&args[1], param) && const_num(&args[0]).is_some() {
        flip(*op)
    } else {
        return false;
    };
    matches!(op, PrimOp::Le | PrimOp::Lt)
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

/// Every self-call's **positional argument list** in `e` (paths discarded) — the shape
/// [`numeric_descent`] / [`measure_descent`] read. Thin wrapper over [`walk`].
fn collect_self_calls(e: &Expr, closure: &Closure, cv: &ValueRef, out: &mut Vec<Vec<Expr>>) {
    let mut full = Vec::new();
    walk(e, closure, std::slice::from_ref(cv), &[], &[], &mut full);
    out.extend(full.into_iter().map(|(args, _)| args));
}

/// Every call in `e` to a member of the **target group** `cv`, paired with its **path
/// lower-bound vector** — `lb[i] = true` iff parameter `i` is bounded below on the path that
/// reaches this call (a `pᵢ > c` / `pᵢ >= c` guard, or the negation of an earlier `pᵢ <= c`
/// / `pᵢ < c`). The applications whose callee resolves through `closure`'s captured
/// environment to any group member (`[cv]` is the self-recursion case; the reachable group
/// is the mutual case); descends every subexpression except nested lambdas (distinct
/// instances); mirrors `bodywalk` so no call is missed (an unread one could be a false
/// proof). A spread argument (no reliable positional mapping) records an **empty** list.
/// With empty `params`/`lb` the lower-bound tracking is inert (the arg-only wrappers).
fn walk(e: &Expr, closure: &Closure, cv: &[ValueRef], params: &[String], lb: &[bool], out: &mut Vec<(Vec<Expr>, Vec<bool>)>) {
    match e {
        Expr::Const(_) | Expr::Ref(_) => {}
        Expr::Lambda(_) => {} // a distinct instance — not this body's recursion
        Expr::Apply { callee, args } => {
            if resolves_to_target(callee, closure, cv) {
                let mut positional = Vec::new();
                let mut clean = true;
                for a in args {
                    match a {
                        Arg::Expr(x) => positional.push(x.clone()),
                        Arg::Spread(_) => clean = false,
                    }
                }
                out.push((if clean { positional } else { Vec::new() }, lb.to_vec()));
            }
            walk(callee, closure, cv, params, lb, out);
            for a in args {
                match a {
                    Arg::Expr(x) | Arg::Spread(x) => walk(x, closure, cv, params, lb, out),
                }
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                walk(a, closure, cv, params, lb, out);
            }
        }
        Expr::Match(m) => {
            if let Some(s) = &m.scrutinee {
                walk(s, closure, cv, params, lb, out);
            }
            // First-match: arm `k`'s result runs under the earlier guards negated plus its
            // own guard — accumulate the lower bounds each contributes.
            let mut acc = lb.to_vec();
            for item in &m.items {
                match item {
                    MatchItem::Bind(Bind { value, .. }) => walk(value, closure, cv, params, &acc, out),
                    MatchItem::Stmt(x) => walk(x, closure, cv, params, &acc, out),
                    MatchItem::Arm(arm) => {
                        let mut branch = acc.clone();
                        if let Some(g) = &arm.guard {
                            walk(g, closure, cv, params, &acc, out);
                            if let Some(i) = guard_lb(g, false, params) {
                                branch[i] = true;
                            }
                        }
                        walk(&arm.result, closure, cv, params, &branch, out);
                        if let Some(g) = &arm.guard
                            && let Some(i) = guard_lb(g, true, params)
                        {
                            acc[i] = true;
                        }
                    }
                }
            }
        }
        Expr::TupleCons(els) => {
            for el in els {
                match el {
                    Element::Expr(x) | Element::Spread(x) => walk(x, closure, cv, params, lb, out),
                }
            }
        }
        Expr::RecordCons(fs) => {
            for f in fs {
                match f {
                    Field::Field { value, .. } | Field::Spread(value) => walk(value, closure, cv, params, lb, out),
                    Field::Computed { key, value } => {
                        walk(key, closure, cv, params, lb, out);
                        walk(value, closure, cv, params, lb, out);
                    }
                }
            }
        }
        Expr::Access { target, form, .. } => {
            walk(target, closure, cv, params, lb, out);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(x) => walk(x, closure, cv, params, lb, out),
                AccessForm::Slice { lo, hi } => {
                    if let Some(x) = lo {
                        walk(x, closure, cv, params, lb, out);
                    }
                    if let Some(x) = hi {
                        walk(x, closure, cv, params, lb, out);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    walk(x, closure, cv, params, lb, out);
                }
            }
        }
        Expr::Write { value, .. } => walk(value, closure, cv, params, lb, out),
    }
}

/// Whether `callee` is a reference that resolves, through `closure`'s captured environment,
/// to a member of the target group `targets` (pointer identity — a self- or mutual-capture
/// is the same allocation).
fn resolves_to_target(callee: &Expr, closure: &Closure, targets: &[ValueRef]) -> bool {
    let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = callee else { return false };
    matches!(closure.env.lookup(n), Some(Binding::Value(v)) if targets.contains(&v))
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
    fn self_loop_is_a_period_1_closed_orbit() {
        // `f(n)` recurs on itself with drift 0. From witness 5 (∉ the base {0}) the orbit is
        // {5} forever → refuted (GR-11 degenerate closed orbit).
        let mut i = Interner::new();
        let s = f("f = (n) => n == 0 ? 0 : f(n)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert_eq!(ground(&s, &five, &ContractEnv::new(), &mut i), Verdict::Refuted);
    }

    #[test]
    fn ascending_drift_away_refutes_from_a_witness() {
        // `f(n+1)` ascends; from witness 5 the orbit 5, 6, 7, … never meets the point base 0
        // → refuted. (Over a broad domain the same function is only Unproven — no witness.)
        let mut i = Interner::new();
        let s = f("f = (n) => n == 0 ? 0 : f(n + 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert_eq!(ground(&s, &five, &ContractEnv::new(), &mut i), Verdict::Refuted);
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
    fn baseless_divergent_recursions_are_unproven_not_grounded() {
        // The analyzer's two growing-domain *termination* tests are non-terminating
        // PROGRAMS (no base case). Grounding correctly declines them (Unproven), so a
        // grounding verdict cannot bound the analyzer's unfolding of them — their bound is
        // the finite-domain abstraction (domain_admitted + widening / the row-set lattice),
        // which is a *different* mechanism than grounding. (Records the wiring finding.)
        let mut i = Interner::new();
        let g1 = f("f = (x, y) => f(x + y, y)\nf", &mut i);
        assert_eq!(ground(&g1, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
        let g2 = f("f = (x, b) => f(b ? x : 0, b)\nf", &mut i);
        assert_eq!(ground(&g2, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    // ── G-8: mutual recursion (§5 GR-07) ─────────────────────────────────────

    #[test]
    fn mutual_even_odd_grounds() {
        // The cycle isEven → isOdd → isEven decreases `n` by 1 on every edge; both members
        // have the descending half-line base `n <= 0`, so every round trip descends.
        let mut i = Interner::new();
        let src = "isEven = (n) => n <= 0 ? true : isOdd(n - 1)\n\
                   isOdd = (n) => n <= 0 ? false : isEven(n - 1)\n\
                   isEven";
        let ev = f(src, &mut i);
        assert_eq!(ground(&ev, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn mutual_recursion_that_does_not_descend_is_unproven() {
        // The `ping`→`pong`→`ping` cycle carries `n` unchanged — no descent → Unproven.
        let mut i = Interner::new();
        let src = "ping = (n) => n <= 0 ? 0 : pong(n)\n\
                   pong = (n) => n <= 0 ? 0 : ping(n)\n\
                   ping";
        let p = f(src, &mut i);
        assert_eq!(ground(&p, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    // ── G-6: structural descent (§2b, tuple peel) ────────────────────────────

    #[test]
    fn list_peel_recursion_grounds_structurally() {
        // Classic list recursion: `rest` is one element shorter than `l`, so the length
        // strictly descends to the empty base. No domain, no numeric measure.
        let mut i = Interner::new();
        let s = f("f = (l) => l :: {\n [] => 0\n [h, ...rest] => 1 + f(rest)\n }\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn peel_recursion_with_accumulator_grounds() {
        // Multi-parameter: the peeled tuple position descends; the accumulator is carried.
        let mut i = Interner::new();
        let s = f("f = (l, acc) => l :: {\n [] => acc\n [h, ...rest] => f(rest, acc + h)\n }\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn recursing_on_the_whole_tuple_is_unproven() {
        // The recursive call rebuilds and passes the *whole* tuple (`[h, ...rest]`), not the
        // shorter remainder — no length descent → Unproven (it diverges).
        let mut i = Interner::new();
        let s = f("f = (l) => l :: {\n [] => 0\n [h, ...rest] => f([h, ...rest])\n }\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Unproven);
    }

    // ── G-5: lexicographic descent (§5 GR-13/14) ─────────────────────────────

    #[test]
    fn lexicographic_reset_grounds() {
        // Dictionary [a, b]: `f(a-1, 10)` drops a (gated by a>0), resetting b; `f(a, b-1)`
        // holds a and drops b (gated by b>0). Neither argument descends monotonically — the
        // lex order does. Both floors come from the path guards, not the domain.
        let mut i = Interner::new();
        let s = f("f = (a, b) => a <= 0 ? b : b <= 0 ? f(a - 1, 10) : f(a, b - 1)\nf", &mut i);
        assert_eq!(ground(&s, &Contract::Top, &ContractEnv::new(), &mut i), Verdict::Grounded);
    }

    #[test]
    fn lexicographic_with_a_relational_floor_is_unproven() {
        // `a` descends toward the stop `a == b`, but that stop is relational — it puts no
        // constant lower bound on `a`, so the decrease is ungated. Sound Unproven (it does
        // terminate, but this route cannot prove a floor).
        let mut i = Interner::new();
        let s = f("f = (a, b) => a == b ? a : f(a - 1, b)\nf", &mut i);
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
