//! Grounding — the recursion **termination** judgment (`next-grounding-specification-v0-5.md`,
//! v0.5 §§1–7; DRAFT, ACCEPTED pending the author's stamp — the judgment rules are stable;
//! only the unproven-*consequence* (P-1, warn-vs-reject) is an open policy pick).
//!
//! Grounding proves a recursive call over an input domain is **well-founded** — it
//! descends toward a base and lands there (GR-05). It is a **behavioural judgment about the
//! program's recursion**, and a *termination* judgment, **not** a safe-input-domain deriver.
//!
//! **It does NOT bound or terminate the analyzer's own unfolding** [corrected 2026-07-31 —
//! the previous claim that grounding "lets the body check stop unfolding" and "replaces
//! widening as the analysis's termination bound" was superseded and is removed]. C§13.3
//! bounds the symbolic procedure independently of whether any runtime recursion is grounded;
//! a non-terminating program is simply *Unproven* here, so grounding could not serve as an
//! analysis cutoff even in principle. Using it as one is forbidden
//! (`IMPLEMENTATION-STATUS.md` §5).
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
//! **Not yet wired** into application safety: build standalone, prove green, integrate
//! only when the exact-chain and broader grounding consumers are authorized.

use num_bigint::BigInt;

use crate::analyzer::bodywalk::{callee_targets, reachable_closures};
use crate::analyzer::region::region_table;
use crate::ast::{
    AccessForm, ActKind, Arg, Bind, BindingRef, Element, Expr, Field, Match, MatchItem, Pat,
    PatElem, PrimOp, Ref, TemplatePart,
};
use crate::contract::{Contract, ContractEnv, Verdict as Sub, subcontract};
use crate::env::Binding;
use crate::interner::Interner;
use crate::rational::Rational;
use crate::value::{Closure, ValueRef};

/// The **persistent evidence a refutation must carry** (§7 / GR-23): the admitted
/// represented-exact **root witness** the forced orbit starts from, plus the certificate
/// that the orbit misses every base. A refutation without this cannot be diagnosed or
/// re-checked, so the verdict carries it rather than recomputing or discarding it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Refutation {
    /// The admitted represented-exact start, taken from the call's own written argument
    /// domain — never synthesized (the constructed-witness inventory is ruled empty).
    pub witness: Rational,
    /// The forced constant drift of the single admitted recursive transition.
    pub drift: Rational,
    /// The base regions the forward orbit `{witness + drift·k : k ≥ 0}` provably misses.
    pub missed_bases: Vec<Contract>,
}

/// A grounding verdict (GR-04 / GR-28).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// Well-founded descent **and** landing proven — the recursion terminates on this domain.
    /// (This is a statement about the *program*; it does not license any analyzer cutoff.)
    Grounded,
    /// A represented-exact witness forces nontermination (§7), carrying its [`Refutation`]
    /// certificate — minted by the constant-drift certificate (GR-23a drift-away, its
    /// ascending mirror, and the period-1 closed orbit).
    Refuted(Refutation),
    /// No candidate proved and no witness refuted (GR-04) — the sound default.
    Unproven,
}

/// Judge whether `callee` recursing over input `domain` is grounded (terminates).
///
/// A candidate may prove groundedness (GR-05); failing that, an **admitted witness** — a
/// represented-exact start actually written at the call (GR-22) — may **refute** via
/// drift-away (GR-23a). No witness ⇒ procedure-relative `Unproven` (GR-04/GR-21). Grounded
/// is judged first: a proven descent is never also a divergence.
pub fn ground(
    callee: &ValueRef,
    domain: &Contract,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Verdict {
    if matches!(
        numeric_descent(callee, domain, cenv, interner),
        Some(Verdict::Grounded)
    ) || measure_descent(callee)
        || lex_descent(callee)
        || structural_descent(callee)
        || mutual_descent(callee)
        || nested_zone_descent(callee, domain, cenv, interner)
    {
        return Verdict::Grounded;
    }
    // The domain-aware mutual grid: the group orbit's own derivation *is* the
    // two-component certificate over this start (all-negative constant cross-steps;
    // a landing the descending chain must enter — half-line, or a shared point base
    // the start provably sits above on the lattice). Grid 7's same-bases pair.
    {
        let group = reachable_closures(callee.clone());
        if group
            .iter()
            .any(|g| g != callee && callee_targets(g).contains(callee))
            && group_orbit_domain(callee, &group, domain, interner).is_some()
        {
            return Verdict::Grounded;
        }
    }
    if let Some(start) = point_value(domain)
        && let Some(refutation) = drift_away(callee, &start, cenv, interner)
    {
        return Verdict::Refuted(refutation);
    }
    Verdict::Unproven
}

/// The numeric constant-drift descent certificate (GR-05). `None` ⇒ this candidate does
/// not apply (→ `Unproven`); `Some(Grounded)` ⇒ both components proven.
fn numeric_descent(
    callee: &ValueRef,
    domain: &Contract,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Verdict> {
    let closure = callee.as_closure()?;
    let param = single_param(&closure.lambda.params)?;
    let rows = region_table(&closure.lambda.body, &param, cenv, interner);

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
    let [base] = bases.as_slice() else {
        return None;
    };
    lands(base, &drifts, domain, interner).then_some(Verdict::Grounded)
}

/// Whether a strictly-decreasing integer chain over `domain` provably reaches `base`
/// (GR-05(2)). Integer lattice required (dense measures are deferred).
fn lands(base: &Contract, drifts: &[Rational], domain: &Contract, interner: &mut Interner) -> bool {
    let integers = Contract::Mod {
        n: BigInt::from(1),
        r: BigInt::from(0),
    };
    if !matches!(subcontract(domain, &integers, interner), Sub::Proven) {
        return false;
    }
    match point_value(base) {
        // Point base `b` — GR-18's grid: when every step is the same constant `−d`,
        // the forced chain from any admitted start stays on the lattice `b + d·k`, so
        // it lands exactly when the whole domain sits on that lattice at or above `b`
        // (`6 → 4 → 2 → 0` lands; `5 → 3 → 1 → −1` is the drift-away's business,
        // specimen 12). The unit step is the `d = 1` case. Mixed step sizes may
        // straddle the point and stay out.
        Some(b) => {
            let Some(first) = drifts.first() else {
                return false;
            };
            if !drifts.iter().all(|d| d == first) || !b.is_integer() {
                return false;
            }
            let step = -first.clone();
            if !step.is_integer() {
                return false;
            }
            let above = matches!(
                subcontract(domain, &Contract::GreaterEq(b.clone()), interner),
                Sub::Proven
            );
            let n = step.as_ratio().numer().clone();
            let r = {
                let base_n = b.as_ratio().numer().clone();
                ((base_n % &n) + &n) % &n
            };
            let aligned = matches!(
                subcontract(domain, &Contract::Mod { n, r }, interner),
                Sub::Proven
            );
            above && aligned
        }
        // Downward half-line base (`k <= b`): a strictly-decreasing integer chain must
        // eventually enter it, from any start (structural landing).
        None => matches!(base, Contract::LessEq(_) | Contract::Less(_)),
    }
}

/// The **derived orbit envelope** [author, 2026-08-03]: for a self-recursion whose
/// constant negative integer drifts land (exactly GR-05's own license — nothing beyond
/// it), the domain the recursion visits from an exact start is composed from the
/// program's own drift arithmetic: `Range(floor, start) ∧ Mod(g, start mod g)`, with `g`
/// the gcd of the step sizes and `floor` read from the landing base. `countDown(5)`
/// derives `Range(0, 5) ∧ Mod(1, 0)`. This is C§13.3(1)'s "derived grounding contracts":
/// the derivation **proposes** a fact domain — the ordinary induction must still prove
/// the fact over it — and it is never a Kind menu; where no certificate applies there is
/// no envelope and the caller keeps its honest cutoff.
pub(crate) fn derived_orbit_domain(
    callee: &ValueRef,
    start: &Contract,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Contract> {
    // A genuinely mutual group derives the **group orbit** instead: one shared
    // envelope covering every member's visited values.
    let group = reachable_closures(callee.clone());
    if group
        .iter()
        .any(|g| g != callee && callee_targets(g).contains(callee))
    {
        return group_orbit_domain(callee, &group, start, interner);
    }

    // The **ascending-stop zone envelope** — the derived domain of the grid-§6 closed
    // form (and its simple non-nested ascent): from any numeric start below the stop,
    // climbs stay within `T + d` and feed-back arguments within the return zone, so
    // every visited argument lies in `LessEq(T + d + max(s, 0))`, composed from the
    // written constants alone. The derivation proposes; the ordinary vector induction
    // must still prove the fact over it — a divergent-but-safe variant proving *safety*
    // over the envelope is correct (safety is not termination). Tried first because the
    // descending reader below bails on any non-constant call argument (the feed-back
    // call), which is exactly this shape.
    {
        let zero = Rational::from(0);
        if let Some(shape) = nested_zone_shape(callee)
            && shape.climb > zero
        {
            let mut hi = shape.boundary + shape.climb;
            if shape.shift > zero {
                hi = hi + shape.shift;
            }
            let env = Contract::LessEq(hi);
            if matches!(subcontract(start, &env, interner), Sub::Proven) {
                return Some(env);
            }
        }
    }

    // `lands` requires the start on the integer lattice; the envelope handles point
    // and non-point starts (a declared `GreaterEq` domain derives `GreaterEq(floor)`).
    let closure = callee.as_closure()?;
    let param = single_param(&closure.lambda.params)?;
    let rows = region_table(&closure.lambda.body, &param, cenv, interner);

    let mut drifts: Vec<Rational> = Vec::new();
    let mut bases: Vec<Contract> = Vec::new();
    for row in &rows {
        let mut calls = Vec::new();
        collect_self_calls(&row.result, &closure, callee, &mut calls);
        if calls.is_empty() {
            bases.push(row.region.clone());
        } else {
            for arglist in &calls {
                let arg = arglist.first()?;
                drifts.push(constant_drift(arg, &param)?);
            }
        }
    }
    let zero = Rational::from(0);
    if drifts.is_empty() || !drifts.iter().all(|d| *d < zero && d.is_integer()) {
        return None;
    }
    let [base] = bases.as_slice() else {
        return None;
    };
    if !lands(base, &drifts, start, interner) {
        return None;
    }

    // Floor from the landing base; overshoot bounded by the largest step.
    let max_step = drifts
        .iter()
        .map(|d| -d.clone())
        .max()
        .expect("at least one drift");
    let floor = match point_value(base) {
        // `lands` admits a point base only when the chain is grid-aligned with it, so
        // the chain stops exactly on `b`.
        Some(b) => b,
        None => match base {
            Contract::LessEq(c) | Contract::Less(c) => c.clone() - max_step,
            _ => return None,
        },
    };

    // Every reachable value is `start − Σ kᵢ·|dᵢ| ≡ start (mod g)`, g = gcd of the steps.
    let mut g = BigInt::from(0);
    for d in &drifts {
        let step = (-d.clone()).as_ratio().numer().clone();
        g = gcd_bigint(g, step);
    }
    envelope(start, floor, g, interner)
}

/// The envelope a landing orbit derives: bounded-above starts give
/// `Range(floor, hi)`; an unbounded start (a declared `GreaterEq` domain — grid 1's
/// `where` cases) gives `GreaterEq(floor)`. The congruence facet needs a uniform
/// class: a point start carries its own class; otherwise only the unit lattice is
/// uniform (v1).
fn envelope(
    start: &Contract,
    floor: Rational,
    g: BigInt,
    interner: &mut Interner,
) -> Option<Contract> {
    let cong = if let Some(s) = point_value(start) {
        let n = s.as_ratio().numer().clone();
        Contract::Mod {
            r: ((n % &g) + &g) % &g,
            n: g,
        }
    } else if g == BigInt::from(1) {
        Contract::Mod {
            n: g,
            r: BigInt::from(0),
        }
    } else {
        return None;
    };
    let extent = match upper_bound(start) {
        Some(hi) => {
            // A start already at or inside the base has the trivial orbit `{start}`.
            let floor = if floor > hi { hi.clone() } else { floor };
            Contract::Range(floor, hi)
        }
        None => Contract::GreaterEq(floor),
    };
    Some(Contract::intersection(extent, cong, interner))
}

/// The **group orbit envelope** — the mutual form of the derivation. When every
/// member's group calls drift by constant negative integer steps on its single
/// parameter and every recursive member stops on a descending half-line
/// (`member_descends`' own reading), the group's visited values from a bounded start
/// all live in `Range(min_boundary − max_step, start_hi)` on the shared lattice.
/// Half-line bases only in v1 — a point base's grid alignment across members is the
/// parity ping-pong, deferred. The derivation proposes; the joint induction proves.
fn group_orbit_domain(
    callee: &ValueRef,
    group: &[ValueRef],
    start: &Contract,
    interner: &mut Interner,
) -> Option<Contract> {
    let mut steps: Vec<Rational> = Vec::new();
    let mut half_line_boundaries: Vec<Rational> = Vec::new();
    let mut point_bases: Vec<Rational> = Vec::new();
    let mut callee_point_base: Option<Rational> = None;
    let mut partner_point_base: Option<Rational> = None;
    for f in group {
        let closure = f.as_closure()?;
        let param = single_param(&closure.lambda.params)?;
        let Expr::Match(m) = &*closure.lambda.body else {
            return None; // a forwarder-shaped member — no stop to read (v1)
        };
        let mut member_calls: Vec<Vec<Expr>> = Vec::new();
        let mut member_half_lines: Vec<Rational> = Vec::new();
        let mut member_points: Vec<Rational> = Vec::new();
        let mut first_call = usize::MAX;
        for (idx, item) in m.items.iter().enumerate() {
            let MatchItem::Arm(arm) = item else { continue };
            let mut gc = Vec::new();
            walk(&arm.result, &closure, group, &[], &[], &mut gc);
            if gc.is_empty() {
                if idx < first_call {
                    if let Some(g) = &arm.guard {
                        if let Some(b) = stop_boundary(g, &param) {
                            member_half_lines.push(b);
                        }
                    } else if let Some(Pat::Const(v)) = &arm.pattern
                        && let Some(b) = v.as_number()
                    {
                        member_points.push(b.clone());
                    }
                }
            } else {
                member_calls.extend(gc.into_iter().map(|(args, _)| args));
                first_call = first_call.min(idx);
            }
        }
        if member_calls.is_empty() {
            continue; // a non-recursive leaf — no cycle edge, no boundary owed
        }
        for call in &member_calls {
            let d = call.first().and_then(|arg| constant_drift(arg, &param))?;
            if d >= Rational::from(0) || !d.is_integer() {
                return None;
            }
            steps.push(-d);
        }
        if let Some(b) = member_half_lines.into_iter().min() {
            half_line_boundaries.push(b);
        } else {
            // A recursive member with no readable stop derives nothing.
            let b = member_points.into_iter().min()?;
            if f == callee {
                callee_point_base = Some(b.clone());
            } else {
                partner_point_base = Some(b.clone());
            }
            point_bases.push(b);
        }
    }
    if steps.is_empty() {
        return None;
    }
    let max_step = steps.iter().cloned().max()?;
    // Half-line stops pad by the largest step. Point bases across a group are exact
    // only in the unit-step, same-value case: consecutive descent visits every
    // integer down to `b`, and whichever member holds `b` stops there — grid 7's
    // same-bases pair. Different base values are the threading example (per-exit
    // parity grids) and stay out; so do mixed stop kinds (v1).
    let floor = match (half_line_boundaries.is_empty(), point_bases.is_empty()) {
        (false, true) => half_line_boundaries.into_iter().min()? - max_step,
        (true, false) => {
            let one = Rational::from(1);
            if !steps.iter().all(|s| *s == one) {
                return None;
            }
            let first = point_bases[0].clone();
            if !point_bases.iter().all(|b| *b == first) {
                // **The threading lattices** (grid 7's different-bases pair): with two
                // recursive members on unit hops, after `k` hops the state is
                // `(member_k, n − k)`, so an exit needs `n − k = b_target` with the
                // hop parity selecting the member. A start wholly on the callee's own
                // lattice (`n ≡ b_self (mod 2)`, `n ≥ b_self`) exits through its own
                // base; wholly on the partner-parity lattice
                // (`n ≡ b_other + 1 (mod 2)`, `n ≥ b_other + 1`) through the
                // partner's. Either way the member's visited values stay on that
                // lattice down to its floor — the per-member envelope. Off both
                // lattices the recursion threads between the bases forever
                // (`isEven(3)`), and no envelope exists.
                if point_bases.len() != 2 {
                    return None;
                }
                let (b_self, b_other) = (callee_point_base?, partner_point_base?);
                if !b_self.is_integer() || !b_other.is_integer() {
                    return None;
                }
                let hi = upper_bound(start)?;
                let two = BigInt::from(2);
                let lattice = |anchor: &Rational, interner: &mut Interner| {
                    let r = {
                        let n = anchor.as_ratio().numer().clone();
                        ((n % &two) + &two) % &two
                    };
                    Contract::intersection(
                        Contract::GreaterEq(anchor.clone()),
                        Contract::Mod { n: two.clone(), r },
                        interner,
                    )
                };
                let own = lattice(&b_self, interner);
                if matches!(subcontract(start, &own, interner), Sub::Proven) {
                    return Some(Contract::intersection(
                        Contract::Range(b_self, hi),
                        match own {
                            Contract::Intersection(_, m) => (*m).clone(),
                            _ => unreachable!("built as an intersection"),
                        },
                        interner,
                    ));
                }
                let partner_entry = b_other.clone() + Rational::from(1);
                let partner = lattice(&partner_entry, interner);
                if matches!(subcontract(start, &partner, interner), Sub::Proven) {
                    return Some(Contract::intersection(
                        Contract::Range(partner_entry, hi),
                        match partner {
                            Contract::Intersection(_, m) => (*m).clone(),
                            _ => unreachable!("built as an intersection"),
                        },
                        interner,
                    ));
                }
                return None;
            }
            // A point base is entered only from at-or-above on the integer lattice:
            // consecutive unit descent visits every integer down to `b`. Below the
            // base nothing lands (isEven(−1) diverges), so the start must sit inside.
            let integers = Contract::Mod {
                n: BigInt::from(1),
                r: BigInt::from(0),
            };
            let above = matches!(
                subcontract(start, &Contract::GreaterEq(first.clone()), interner),
                Sub::Proven
            );
            let lattice = matches!(subcontract(start, &integers, interner), Sub::Proven);
            if !above || !lattice {
                return None;
            }
            first
        }
        _ => return None,
    };
    let mut g = BigInt::from(0);
    for s in &steps {
        g = gcd_bigint(g, s.as_ratio().numer().clone());
    }
    envelope(start, floor, g, interner)
}

/// The boundary of a **descending** half-line stop guard on `param` (`param <= c` /
/// `param < c`, either operand order), or `None`.
fn stop_boundary(g: &Expr, param: &str) -> Option<Rational> {
    let Expr::PrimOp { op, args } = g else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (op, c) = if is_param(&args[0], param) {
        (*op, const_num(&args[1])?)
    } else if is_param(&args[1], param) {
        (flip(*op), const_num(&args[0])?)
    } else {
        return None;
    };
    matches!(op, PrimOp::Le | PrimOp::Lt).then_some(c)
}

/// The least upper bound a contract spells directly (`Equals`, `Range`, `LessEq`,
/// intersections thereof), or `None` — the group orbit's bounded-start reader.
fn upper_bound(c: &Contract) -> Option<Rational> {
    match c {
        Contract::Equals(v) => v.as_number().cloned(),
        Contract::Range(_, h) | Contract::LessEq(h) => Some(h.clone()),
        Contract::Intersection(a, b) => match (upper_bound(a), upper_bound(b)) {
            (Some(x), Some(y)) => Some(if x < y { x } else { y }),
            (x, y) => x.or(y),
        },
        _ => None,
    }
}

fn gcd_bigint(a: BigInt, b: BigInt) -> BigInt {
    let (mut a, mut b) = (a.max(BigInt::from(0)), b.max(BigInt::from(0)));
    while b != BigInt::from(0) {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// The **constant-drift refutation** from a represented-exact start `start` (GR-20/23): a
/// single forced *linear* recursion (one recursive row, one self-call, **any** constant
/// drift) whose forward orbit `{ start + drift·k : k ≥ 0 }` provably misses **every** base
/// region — a denotationally forced infinite path. `drift < 0` is the GR-23a drift-away
/// (descending), `drift > 0` its ascending mirror, and `drift == 0` a **period-1 closed
/// orbit** (GR-11's degenerate case — `f(n)` recurring on itself). Because the orbit
/// includes the start (`k = 0`), a start already in a base is correctly rejected. Sound:
/// `true` only when the miss is certain.
fn drift_away(
    callee: &ValueRef,
    start: &Rational,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Refutation> {
    let closure = callee.as_closure()?;
    let param = single_param(&closure.lambda.params)?;
    let rows = region_table(&closure.lambda.body, &param, cenv, interner);

    let mut bases = Vec::new();
    let mut drift = None;
    let mut rec_rows = 0;
    for row in &rows {
        // **Forced-path selection (GR-23).** A recursive transition may be admitted only
        // when the path to it is *forced*; syntactic presence of a self-call is not
        // sufficient. `forced_self_calls` collects only calls reached under no unproven
        // selection, and reports when one was found *behind* a nested conditional — in
        // which case this candidate declines outright rather than treating a conditional
        // edge as taken (which produced a **false refutation** of a terminating program).
        let mut calls = Vec::new();
        if !forced_self_calls(&row.result, &closure, callee, &mut calls) {
            return None; // a self-call behind an unproven selection — transition not forced
        }
        if calls.is_empty() {
            bases.push(row.region.clone());
        } else {
            rec_rows += 1;
            if calls.len() != 1 {
                return None; // branching recursion — not a single forced path
            }
            let arg = calls[0].first()?;
            drift = Some(position_drift(arg, &param)?);
        }
    }
    let d = drift?;
    if rec_rows != 1 {
        return None; // not a single forced path
    }
    // A forced orbit that misses every base ⇒ never lands ⇒ diverges. `!reaches` over the
    // whole orbit is both base-disjointness (v) and transition closure (vi).
    if !bases.iter().all(|b| !reaches(start, &d, b)) {
        return None;
    }
    Some(Refutation {
        witness: start.clone(),
        drift: d,
        missed_bases: bases,
    })
}

/// Collect the self-calls in `e` that lie on the **forced path** — those reached under no
/// unproven selection — returning `false` when a self-call was found *off* it.
///
/// GR-23 admits a recursive transition only under exact selection (or another applicable
/// must-condition) at **every** step. A call inside a nested `Match`'s items is taken only
/// if that arm is selected, which this layer does not prove, so its presence makes the
/// transition unforced. A `Match` **scrutinee** is always evaluated and stays on the forced
/// path. Everything else evaluates unconditionally and recurses normally.
///
/// Note this discipline is required only for **refutation** (which must exhibit a forced
/// divergent path). The descent side is unaffected: a merely *conditional* recursive call
/// still has to descend when taken, so `numeric_descent` continues to read every
/// syntactically present self-call.
fn forced_self_calls(e: &Expr, closure: &Closure, cv: &ValueRef, out: &mut Vec<Vec<Expr>>) -> bool {
    let mut forced = true;
    match e {
        Expr::Const(_) | Expr::Ref(_) => {}
        Expr::Lambda(_) => {} // a distinct instance — not this body's recursion
        Expr::Apply { callee, args } => {
            if resolves_to_target(callee, closure, std::slice::from_ref(cv)) {
                let mut positional = Vec::new();
                for a in args {
                    match a {
                        Arg::Expr(x) => positional.push(x.clone()),
                        Arg::Spread(_) => return false, // no positional mapping — decline
                    }
                }
                out.push(positional);
            }
            forced &= forced_self_calls(callee, closure, cv, out);
            for a in args {
                let (Arg::Expr(x) | Arg::Spread(x)) = a;
                forced &= forced_self_calls(x, closure, cv, out);
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                forced &= forced_self_calls(a, closure, cv, out);
            }
        }
        Expr::Match(m) => {
            // The scrutinee always evaluates — still forced.
            if let Some(s) = &m.scrutinee {
                forced &= forced_self_calls(s, closure, cv, out);
            }
            // The items are selection-dependent: any self-call inside is NOT forced.
            for item in &m.items {
                let mut probe = Vec::new();
                for sub in item_exprs(item) {
                    collect_self_calls(sub, closure, cv, &mut probe);
                }
                if !probe.is_empty() {
                    forced = false;
                }
            }
        }
        Expr::TupleCons(els) => {
            for el in els {
                let (Element::Expr(x) | Element::Spread(x)) = el;
                forced &= forced_self_calls(x, closure, cv, out);
            }
        }
        Expr::RecordCons(fs) => {
            for f in fs {
                match f {
                    Field::Field { value, .. } | Field::Spread(value) => {
                        forced &= forced_self_calls(value, closure, cv, out);
                    }
                    Field::Computed { key, value } => {
                        forced &= forced_self_calls(key, closure, cv, out);
                        forced &= forced_self_calls(value, closure, cv, out);
                    }
                }
            }
        }
        Expr::Access { target, form, .. } => {
            forced &= forced_self_calls(target, closure, cv, out);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(x) => forced &= forced_self_calls(x, closure, cv, out),
                AccessForm::Slice { lo, hi } => {
                    for x in [lo, hi].into_iter().flatten() {
                        forced &= forced_self_calls(x, closure, cv, out);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    forced &= forced_self_calls(x, closure, cv, out);
                }
            }
        }
        Expr::Write { value, .. } => forced &= forced_self_calls(value, closure, cv, out),
    }
    forced
}

/// The sub-expressions of a `Match` item (all selection-dependent).
fn item_exprs(item: &MatchItem) -> Vec<&Expr> {
    match item {
        MatchItem::Bind(b) => vec![&b.value],
        MatchItem::Stmt(x) => vec![x],
        MatchItem::Arm(a) => match &a.guard {
            Some(g) => vec![g, &a.result],
            None => vec![&a.result],
        },
    }
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
    let Some(closure) = callee.as_closure() else {
        return false;
    };
    let Some(params) = param_names(&closure.lambda.params) else {
        return false;
    };
    let Expr::Match(m) = &*closure.lambda.body else {
        return false;
    };

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
    let Expr::PrimOp { op, args } = g else {
        return false;
    };
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
        let Some(d) = drift_on(&e, call, params) else {
            return false;
        };
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
    let Some(ascending) = ascending else {
        return false;
    };
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

/// The **nested landing-zone certificate** — the worked-examples grid §6 closed form
/// ("McCarthy 91 — landing zones; point vs range bases"), the C§10-core landing-zone
/// route GR specimen 7 consumes. The admitted shape, read from the written program:
///
/// ```text
/// m = (n) => n > T ? n + s : … m(m(n + d)) …
/// ```
///
/// — a single-parameter self-recursion with **one** base arm whose guard is an
/// **ascending half-line stop** (`n > T` / `n >= T`; GR-15a's admitted region base
/// **above**, so landing is structural and no grid condition arises — the grid's
/// "derived input contract: none — all reals") and whose result is a **pure shift**
/// `n + s`; every self-call is either a **climb** `m(n + d)` (one shared written drift
/// `d > 0`) or a **feed-back** call whose argument is exactly one inner self-call of
/// climb shape — one nesting level only: the k-fold generalization (`m(m(m(n+d)))`)
/// is *not* this closed form and diverges for McCarthy's own constants, so a nested
/// inner argument declines the candidate (GR-04 — no conclusion).
///
/// The closed form's three steps, mechanized from the written constants:
/// 1. **Landing zone** `(T, T+d]` — every climb from below first lands there.
/// 2. **Candidate return** = the exit shift applied to the zone: `(T+s, T+d+s]`.
/// 3. **Feed-back check** — "one F(C) ⊑ C induction": the ordinary return-fact
///    machinery must prove the return over `LE(T+d)` (every inner argument from the
///    recursive region lies there) inside the candidate zone, which is what licenses
///    every feed-back argument to land in it.
///
/// Termination then follows the grid's own count: climbs are finite (constant `+d`
/// toward a half-line above — Archimedean, no grid), and feed-back laps net `d + s`
/// per lap ("net +1 per lap" for McCarthy's 11 − 10), so `d + s > 0` is required —
/// `d + s <= 0` is the exact-self-loop family (`n − 11` against `+11` laps forever)
/// and proves nothing. Real-valued `T`, `d`, `s` are all admitted; the domain must
/// only be numeric.
fn nested_zone_descent(
    callee: &ValueRef,
    domain: &Contract,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> bool {
    if !matches!(
        subcontract(
            domain,
            &Contract::Kind(crate::contract::Kind::Number),
            interner
        ),
        Sub::Proven
    ) {
        return false;
    }
    let Some(shape) = nested_zone_shape(callee) else {
        return false;
    };
    let zero = Rational::from(0);
    if !shape.feedback || shape.climb <= zero || shape.climb.clone() + shape.shift.clone() <= zero {
        return false; // no nested call, climbs not ascending, or laps not progressing
    }

    // Step 3 — the feed-back induction, through the ordinary return-fact machinery.
    // Interval openness follows the stop: a strict stop (`n > T`) gives the closed-top
    // zone `(T, T+d]`; a weak stop (`n >= T`) the half-open `[T, T+d)`.
    let hi = shape.boundary.clone() + shape.climb.clone();
    let (inner_domain, zone_lo, zone_hi) = match shape.op {
        PrimOp::Gt => (
            Contract::LessEq(hi.clone()),
            Contract::Greater(shape.boundary + shape.shift.clone()),
            Contract::LessEq(hi + shape.shift),
        ),
        PrimOp::Ge => (
            Contract::Less(hi.clone()),
            Contract::GreaterEq(shape.boundary + shape.shift.clone()),
            Contract::Less(hi + shape.shift),
        ),
        _ => return false,
    };
    let Some(ret) = crate::analyzer::induction::infer_return_fact(
        callee,
        Some(std::slice::from_ref(&inner_domain)),
        cenv,
        interner,
    ) else {
        return false;
    };
    let zone_return = Contract::intersection(zone_lo, zone_hi, interner);
    matches!(subcontract(&ret, &zone_return, interner), Sub::Proven)
}

/// The written constants of the ascending-stop shape, read off the body.
struct ZoneShape {
    /// The stop comparison — `Gt` (`n > T`) or `Ge` (`n >= T`).
    op: PrimOp,
    /// The stop boundary `T`.
    boundary: Rational,
    /// The exit branch's shift `s` (`n + s`).
    shift: Rational,
    /// The one shared climb drift `d` (`m(n + d)`).
    climb: Rational,
    /// Whether a feed-back call (`m(m(n + d))`) is present.
    feedback: bool,
}

/// Read the ascending-stop closed-form shape: one base arm `n ⋈ T` (`>`/`>=`) tested
/// before any recursion, exit result a pure shift `n + s`, and every self-call either a
/// climb `m(n + d)` (one shared `d`) or a one-level feed-back `m(m(n + d))`. `None`
/// wherever the written program departs from the form — candidate-locality (GR-04)
/// turns every departure into "no conclusion", never a guess.
fn nested_zone_shape(callee: &ValueRef) -> Option<ZoneShape> {
    let closure = callee.as_closure()?;
    let param = single_param(&closure.lambda.params)?;
    let params = vec![param];
    let Expr::Match(m) = &*closure.lambda.body else {
        return None;
    };

    let one = Rational::from(1);
    let zero = Rational::from(0);
    let mut exit: Option<(PrimOp, Rational, Rational)> = None;
    let mut climb: Option<Rational> = None;
    let mut feedback = false;
    let mut first_rec = usize::MAX;
    for (idx, item) in m.items.iter().enumerate() {
        let MatchItem::Arm(arm) = item else {
            return None; // interleaved binds/statements — outside this closed form
        };
        let mut calls = Vec::new();
        collect_self_calls(&arm.result, &closure, callee, &mut calls);
        if calls.is_empty() {
            // The one base arm, tested before any recursion can fire (§6 discipline).
            if exit.is_some() || idx > first_rec {
                return None;
            }
            let Some(Expr::PrimOp { op, args }) = arm.guard.as_ref() else {
                return None;
            };
            if args.len() != 2 {
                return None;
            }
            let (l, r) = (
                linear_form(&args[0], &params)?,
                linear_form(&args[1], &params)?,
            );
            let (e, c, op) = match (l.is_constant(), r.is_constant()) {
                (false, true) => (l, r.constant, *op),
                (true, false) => (r, l.constant, flip(*op)),
                _ => return None,
            };
            // The varying side must be the bare parameter, the stop above it.
            if e.coeffs != vec![one.clone()] || e.constant != zero {
                return None;
            }
            if !matches!(op, PrimOp::Gt | PrimOp::Ge) {
                return None;
            }
            // The exit branch must be the pure shift `n + s`.
            let res = linear_form(&arm.result, &params)?;
            if res.coeffs != vec![one.clone()] {
                return None;
            }
            exit = Some((op, c, res.constant));
        } else {
            first_rec = first_rec.min(idx);
            for arglist in &calls {
                let [arg] = arglist.as_slice() else {
                    return None;
                };
                if let Some(lin) = linear_form(arg, &params) {
                    // A climb call `m(n + d)` — one shared written drift.
                    if lin.coeffs != vec![one.clone()] {
                        return None;
                    }
                    match &climb {
                        None => climb = Some(lin.constant),
                        Some(d) if *d == lin.constant => {}
                        Some(_) => return None,
                    }
                } else if let Expr::Apply {
                    callee: inner,
                    args: inner_args,
                } = arg
                {
                    // A feed-back call: exactly one inner self-call whose own argument
                    // is linear — one nesting level only (the k-fold generalization
                    // `m(m(m(n+d)))` diverges for McCarthy's own constants and is not
                    // this closed form). The inner call is also collected separately
                    // and validated as a climb there.
                    if !resolves_to_target(inner, &closure, std::slice::from_ref(callee)) {
                        return None;
                    }
                    let [Arg::Expr(a2)] = inner_args.as_slice() else {
                        return None;
                    };
                    linear_form(a2, &params)?;
                    feedback = true;
                } else {
                    return None;
                }
            }
        }
    }
    let (Some((op, boundary, shift)), Some(climb)) = (exit, climb) else {
        return None;
    };
    Some(ZoneShape {
        op,
        boundary,
        shift,
        climb,
        feedback,
    })
}

/// A linear combination `Σ coeffs[i]·paramᵢ + constant` over the parameter list.
#[derive(Clone)]
struct LinComb {
    coeffs: Vec<Rational>,
    constant: Rational,
}

impl LinComb {
    fn constant(constant: Rational, n: usize) -> LinComb {
        LinComb {
            coeffs: vec![Rational::from(0); n],
            constant,
        }
    }
    fn is_constant(&self) -> bool {
        self.coeffs.iter().all(Rational::is_zero)
    }
    fn add(&self, o: &LinComb) -> LinComb {
        LinComb {
            coeffs: self
                .coeffs
                .iter()
                .zip(&o.coeffs)
                .map(|(a, b)| a.clone() + b.clone())
                .collect(),
            constant: self.constant.clone() + o.constant.clone(),
        }
    }
    fn sub(&self, o: &LinComb) -> LinComb {
        LinComb {
            coeffs: self
                .coeffs
                .iter()
                .zip(&o.coeffs)
                .map(|(a, b)| a.clone() - b.clone())
                .collect(),
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
        Expr::PrimOp {
            op: PrimOp::Add,
            args,
        } if args.len() == 2 => {
            Some(linear_form(&args[0], params)?.add(&linear_form(&args[1], params)?))
        }
        Expr::PrimOp {
            op: PrimOp::Sub,
            args,
        } if args.len() == 2 => {
            Some(linear_form(&args[0], params)?.sub(&linear_form(&args[1], params)?))
        }
        Expr::PrimOp {
            op: PrimOp::Neg,
            args,
        } if args.len() == 1 => Some(
            LinComb::constant(Rational::from(0), params.len()).sub(&linear_form(&args[0], params)?),
        ),
        Expr::PrimOp {
            op: PrimOp::Mul,
            args,
        } if args.len() == 2 => {
            let (a, b) = (
                linear_form(&args[0], params)?,
                linear_form(&args[1], params)?,
            );
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

// ── The joint lexicographic certificate over point floors (§5 GR-13/14) ───────
//
// Ackermann's shape (GR specimen 5): a flat multi-parameter self-recursion whose
// positions are floored by `param == k` **point guards** (the arm order is the gate:
// a recursive call sits below the negation of its position's point test, so on an
// integer lattice at or above the floor the position is ≥ floor + 1 and a unit
// decrease lands back at or above the floor), whose recursive arguments per position
// are the same parameter with a constant drift, an admitted integer constant, or a
// **nested self-call** whose value obtains domain membership from the induction
// hypothesis's *return half* (GR-13: the joint `(terminates ∧ returns ⊑ R)`
// induction — mechanically, the proven return fact over the envelope must sit inside
// the position's envelope). One fixed dictionary — an injective sequence of argument
// positions (GR-14's advance enumeration) — must pass every recursive call: reading
// in order, positions strictly decrease (gated, unit steps in v1) or are carried
// unchanged, and any reset (constant / nested-call) position is admitted only after
// the strict decrease. Candidate-locality throughout (GR-04): any departure
// contributes no conclusion.

/// The per-position **point floors** read off the body: every `param == k` guard
/// constant (integer k), per position. A position with no point test derives no
/// floor and the certificate declines.
fn point_floors(body: &Expr, params: &[String]) -> Vec<Vec<Rational>> {
    fn scan(e: &Expr, params: &[String], out: &mut Vec<Vec<Rational>>) {
        if let Expr::PrimOp {
            op: PrimOp::Eq,
            args,
        } = e
            && args.len() == 2
        {
            for (idx, p) in params.iter().enumerate() {
                let hit = (is_param(&args[0], p), const_num(&args[1]));
                let flipped = (is_param(&args[1], p), const_num(&args[0]));
                if let (true, Some(k)) = hit {
                    out[idx].push(k);
                } else if let (true, Some(k)) = flipped {
                    out[idx].push(k);
                }
            }
        }
        for_each_child(e, &mut |child| scan(child, params, out));
    }
    let mut out = vec![Vec::new(); params.len()];
    scan(body, params, &mut out);
    out
}

/// The **lex orbit envelope**: `GE(floor_p) ∧ Mod(1, 0)` per position, from the
/// program's own point tests — the least `== k` constant each position is tested
/// against. `None` when a position has no integer point test or a recursive
/// argument departs from the admitted shapes (same-position constant drift,
/// integer constant, nested self-call). The derivation **proposes**; safety and
/// completion facts over it are still proven by the ordinary vector induction.
pub(crate) fn lex_envelope(callee: &ValueRef, interner: &mut Interner) -> Option<Vec<Contract>> {
    let closure = callee.as_closure()?;
    let params = crate::analyzer::region::flat_params(&closure.lambda.params)?;
    if params.len() < 2 {
        return None;
    }
    let mut calls = Vec::new();
    collect_self_calls(&closure.lambda.body, &closure, callee, &mut calls);
    if calls.is_empty() {
        return None;
    }
    let floors = point_floors(&closure.lambda.body, &params);
    let mut envelope = Vec::new();
    for f in &floors {
        let b = f.iter().min()?.clone();
        if !b.is_integer() {
            return None;
        }
        envelope.push(Contract::intersection(
            Contract::GreaterEq(b),
            Contract::Mod {
                n: BigInt::from(1),
                r: BigInt::from(0),
            },
            interner,
        ));
    }
    // Every recursive argument must be one of the admitted shapes.
    for arglist in &calls {
        if arglist.len() != params.len() {
            return None;
        }
        for (idx, arg) in arglist.iter().enumerate() {
            let admitted = position_drift(arg, &params[idx]).is_some()
                || const_num(arg).is_some_and(|k| k.is_integer())
                || matches!(arg, Expr::Apply { callee: c, .. }
                    if resolves_to_target(c, &closure, std::slice::from_ref(callee)));
            if !admitted {
                return None;
            }
        }
    }
    Some(envelope)
}

/// One recursive call with the **negated point tests** in force on its path: `gates[p]`
/// holds every constant `k` such that the path passed the `false` side of a
/// `param_p == k` test. Later arms of a `Match` run under the negation of every
/// earlier arm's point guard — the E9 remainder, read for this one gate shape.
fn lex_calls_with_gates(
    e: &Expr,
    closure: &Closure,
    cv: &ValueRef,
    params: &[String],
    gates: &[Vec<Rational>],
    out: &mut Vec<(Vec<Expr>, Vec<Vec<Rational>>)>,
) {
    match e {
        Expr::Const(_) | Expr::Ref(_) | Expr::Lambda(_) => {}
        Expr::Apply { callee, args } => {
            if resolves_to_target(callee, closure, std::slice::from_ref(cv)) {
                let mut positional = Vec::new();
                let mut clean = true;
                for a in args {
                    match a {
                        Arg::Expr(x) => positional.push(x.clone()),
                        Arg::Spread(_) => clean = false,
                    }
                }
                if clean {
                    out.push((positional, gates.to_vec()));
                } else {
                    out.push((Vec::new(), gates.to_vec()));
                }
            }
            lex_calls_with_gates(callee, closure, cv, params, gates, out);
            for a in args {
                let (Arg::Expr(x) | Arg::Spread(x)) = a;
                lex_calls_with_gates(x, closure, cv, params, gates, out);
            }
        }
        Expr::Match(m) => {
            if let Some(s) = &m.scrutinee {
                lex_calls_with_gates(s, closure, cv, params, gates, out);
            }
            let mut acc = gates.to_vec();
            for item in &m.items {
                match item {
                    MatchItem::Bind(Bind { value, .. }) => {
                        lex_calls_with_gates(value, closure, cv, params, &acc, out)
                    }
                    MatchItem::Stmt(x) => lex_calls_with_gates(x, closure, cv, params, &acc, out),
                    MatchItem::Arm(arm) => {
                        if let Some(g) = &arm.guard {
                            lex_calls_with_gates(g, closure, cv, params, &acc, out);
                        }
                        lex_calls_with_gates(&arm.result, closure, cv, params, &acc, out);
                        // After this arm, its point guard is negated for later items.
                        if let Some(Expr::PrimOp {
                            op: PrimOp::Eq,
                            args,
                        }) = arm.guard.as_ref()
                            && args.len() == 2
                        {
                            for (idx, p) in params.iter().enumerate() {
                                if is_param(&args[0], p)
                                    && let Some(k) = const_num(&args[1])
                                {
                                    acc[idx].push(k);
                                } else if is_param(&args[1], p)
                                    && let Some(k) = const_num(&args[0])
                                {
                                    acc[idx].push(k);
                                }
                            }
                        }
                    }
                }
            }
        }
        other => {
            for_each_child(other, &mut |child| {
                lex_calls_with_gates(child, closure, cv, params, gates, out)
            });
        }
    }
}

/// The joint lexicographic certificate (GR-13/14) over `args`. Proves `Grounded`
/// when: the lex envelope derives and contains `args`; the **return half** — the
/// proven return fact over the envelope — sits inside every position that receives
/// a nested self-call or that the envelope must re-admit; and one fixed dictionary
/// passes every recursive call: strict unit decreases gated by the position's
/// negated point test, earlier positions carried unchanged, resets (constants and
/// nested calls, both proven inside the position's envelope) only after the strict
/// decrease.
pub(crate) fn lex_grounded(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> bool {
    let Some(closure) = callee.as_closure() else {
        return false;
    };
    let Some(params) = crate::analyzer::region::flat_params(&closure.lambda.params) else {
        return false;
    };
    if params.len() != args.len() {
        return false;
    }
    // Self-recursion only in v1 — a genuine mutual group needs GR-07's full cycle
    // inventory for the fixed-candidate rule.
    let group = reachable_closures(callee.clone());
    if group
        .iter()
        .any(|g| g != callee && callee_targets(g).contains(callee))
    {
        return false;
    }
    let Some(envelope) = lex_envelope(callee, interner) else {
        return false;
    };
    for (a, e) in args.iter().zip(&envelope) {
        if !matches!(subcontract(a, e, interner), Sub::Proven) {
            return false;
        }
    }
    let floors: Vec<Rational> = point_floors(&closure.lambda.body, &params)
        .iter()
        .map(|f| f.iter().min().cloned().expect("envelope derived"))
        .collect();

    let mut calls = Vec::new();
    lex_calls_with_gates(
        &closure.lambda.body,
        &closure,
        callee,
        &params,
        &vec![Vec::new(); params.len()],
        &mut calls,
    );
    if calls.is_empty() || calls.iter().any(|(a, _)| a.len() != params.len()) {
        return false;
    }

    // GR-13's return half, once per certificate: the nested call's value must sit
    // inside the envelope of the position that receives it.
    let needs_return = calls.iter().any(|(a, _)| {
        a.iter().any(|arg| {
            matches!(arg, Expr::Apply { callee: c, .. }
            if resolves_to_target(c, &closure, std::slice::from_ref(callee)))
        })
    });
    let returned = if needs_return {
        match crate::analyzer::induction::infer_return_fact(callee, Some(&envelope), cenv, interner)
        {
            Some(r) => Some(r),
            None => return false,
        }
    } else {
        None
    };

    let zero = Rational::from(0);
    let one = Rational::from(1);

    // **Domain closure at every position** (GR-14), dictionary-independent: every
    // argument of every recursive call must stay inside its position's envelope.
    // A decreasing drift needs its gate (unit step below the negated point floor:
    // `p != floor` on the integer lattice at or above the floor means
    // `p ≥ floor + 1`, so `p − 1` lands at or above it); carries and increases stay
    // inside a `GE` envelope freely; constants and nested-call values must be proven
    // inside the envelope (the nested value through GR-13's return half).
    let closed = calls.iter().all(|(cargs, gates)| {
        cargs.iter().enumerate().all(|(i, arg)| {
            if let Some(d) = position_drift(arg, &params[i]) {
                d >= zero || (d == -one.clone() && gates[i].contains(&floors[i]))
            } else {
                match arg {
                    Expr::Apply { callee: c, .. }
                        if resolves_to_target(c, &closure, std::slice::from_ref(callee)) =>
                    {
                        returned.as_ref().is_some_and(|r| {
                            matches!(subcontract(r, &envelope[i], interner), Sub::Proven)
                        })
                    }
                    _ => const_num(arg).is_some_and(|k| {
                        matches!(
                            subcontract(
                                &Contract::Equals(interner.number(k)),
                                &envelope[i],
                                interner
                            ),
                            Sub::Proven
                        )
                    }),
                }
            }
        })
    });
    if !closed {
        return false;
    }

    // **The descent scan** — one fixed dictionary must pass every call: reading in
    // order, carried positions (drift 0) pass through, and the first *changed*
    // position must be a strict (already gate-validated) decrease. An increase or a
    // reset (constant / nested call) before the decrease fails the dictionary; a
    // call with no dictionary decrease at all is a potential same-state loop and
    // fails too.
    let positions: Vec<usize> = (0..params.len()).collect();
    injective_seqs(&positions).into_iter().any(|dict| {
        calls.iter().all(|(cargs, _)| {
            for &i in &dict {
                match position_drift(&cargs[i], &params[i]) {
                    Some(d) if d.is_zero() => continue,
                    Some(d) if d < zero => return true,
                    _ => return false, // increase or reset before the decrease
                }
            }
            false // every dictionary position carried — no decrease
        })
    })
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
    let Some(closure) = callee.as_closure() else {
        return false;
    };
    let Some(params) = param_names(&closure.lambda.params) else {
        return false;
    };
    let mut calls = Vec::new();
    walk(
        &closure.lambda.body,
        &closure,
        std::slice::from_ref(callee),
        &params,
        &vec![false; params.len()],
        &mut calls,
    );
    if calls.is_empty() {
        return false;
    }
    let positions: Vec<usize> = (0..params.len()).collect();
    injective_seqs(&positions)
        .into_iter()
        .filter(|dict| dict.len() >= 2) // length-1 dictionaries are `measure_descent`'s job
        .any(|dict| {
            calls
                .iter()
                .all(|(args, lb)| lex_call_ok(&dict, args, lb, &params))
        })
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
    let Expr::PrimOp { op, args } = g else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (idx, op) = if let (Some(i), true) =
        (param_index(&args[0], params), const_num(&args[1]).is_some())
    {
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
    let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = e else {
        return None;
    };
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
    let Some(closure) = callee.as_closure() else {
        return false;
    };
    let Some(params) = param_names(&closure.lambda.params) else {
        return false;
    };
    let Expr::Match(m) = &*closure.lambda.body else {
        return false;
    };
    let Some(scrut) = &m.scrutinee else {
        return false;
    };
    let Some(pos) = param_index(scrut, &params) else {
        return false;
    };

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
            let Some(arg) = call.get(pos) else {
                return false;
            };
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

// ── The WorldDecided classifier (§8 GR-24, v1 subset) ────────────────────────

/// The **WorldDecided certificate**, v1 (GR-24) — the sound recognizer the D-α/D-β
/// rulings owe. Effect-world recursion is excused from **exactly one** obligation — a
/// bound on the number of world-driven iterations — when every recursive cycle
/// observes the world afresh and every observation has a represented completing
/// alternative to select. Judged per self-recursive Effect instance; the seat
/// **consumes** the certificate (GR-26's row), never establishes it.
///
/// v1 admission (GR-24(c): syntax plus dataflow already read; no taint metadata):
/// - the callee is an **Effect** closure whose recursion is direct self-recursion —
///   mutual world-driven groups stay unclassified, honestly unproven;
/// - a parameter position is **refreshed** when every self-call passes a direct
///   effect application there (`loop(read())`);
/// - every self-call site is **world-guarded**: a test on its selection path (match
///   scrutinee, or a guard at or before its arm) contains a current-activation
///   effect application (`readFile(q) :: { … }`) or reads refreshed parameters
///   only — a stale-carried parameter (`loop(msg)` tested on `msg`) qualifies
///   nothing (specimen 13);
/// - every match that guards recursion owns a **completing arm** — an arm whose
///   result contains no self-call — GR-24(b)'s seed; the decorative branch
///   (`bit ? loop() : loop()`) seeds nothing and dies (specimen 16).
pub(crate) fn world_decided(callee: &ValueRef) -> bool {
    let Some(closure) = callee.as_closure() else {
        return false;
    };
    if closure.lambda.act_kind != ActKind::Effect {
        return false;
    }
    // Direct self-recursion only: no other reachable closure may close a cycle back.
    let group = reachable_closures(callee.clone());
    if group
        .iter()
        .any(|g| g != callee && callee_targets(g).contains(callee))
    {
        return false;
    }
    if !callee_targets(callee).contains(callee) {
        return false; // not recursive — nothing to classify
    }

    let mut sites: Vec<Vec<Expr>> = Vec::new();
    collect_self_calls(&closure.lambda.body, &closure, callee, &mut sites);
    let params = param_names(&closure.lambda.params).unwrap_or_default();
    let refreshed: Vec<String> = params
        .iter()
        .enumerate()
        .filter(|(i, _)| {
            !sites.is_empty()
                && sites.iter().all(|args| {
                    args.get(*i)
                        .is_some_and(|a| is_effect_application(a, &closure))
                })
        })
        .map(|(_, name)| name.clone())
        .collect();

    let mut w = WorldWalk {
        closure: &closure,
        callee,
        params: &params,
        refreshed: &refreshed,
        ok: true,
    };
    w.expr(&closure.lambda.body, false);
    w.ok
}

struct WorldWalk<'a> {
    closure: &'a Closure,
    callee: &'a ValueRef,
    params: &'a [String],
    refreshed: &'a [String],
    ok: bool,
}

impl WorldWalk<'_> {
    /// Walk `e`; `guarded` means this position's selection already depends on a
    /// current-activation world observation.
    fn expr(&mut self, e: &Expr, guarded: bool) {
        if !self.ok {
            return;
        }
        match e {
            Expr::Const(_) | Expr::Ref(_) => {}
            Expr::Lambda(_) => {} // a distinct instance — not this body's recursion
            Expr::Apply { callee, args } => {
                if !guarded
                    && resolves_to_target(callee, self.closure, std::slice::from_ref(self.callee))
                {
                    self.ok = false; // an unguarded cycle — the internal graph cycles
                    return;
                }
                self.expr(callee, guarded);
                for a in args {
                    let (Arg::Expr(x) | Arg::Spread(x)) = a;
                    self.expr(x, guarded);
                }
            }
            Expr::Match(m) => self.match_node(m, guarded),
            Expr::PrimOp { args, .. } => {
                for a in args {
                    self.expr(a, guarded);
                }
            }
            Expr::TupleCons(els) => {
                for el in els {
                    let (Element::Expr(x) | Element::Spread(x)) = el;
                    self.expr(x, guarded);
                }
            }
            Expr::RecordCons(fs) => {
                for f in fs {
                    match f {
                        Field::Field { value, .. } | Field::Spread(value) => {
                            self.expr(value, guarded)
                        }
                        Field::Computed { key, value } => {
                            self.expr(key, guarded);
                            self.expr(value, guarded);
                        }
                    }
                }
            }
            Expr::Access { target, form, .. } => {
                self.expr(target, guarded);
                match form {
                    AccessForm::Field(_) => {}
                    AccessForm::Index(x) => self.expr(x, guarded),
                    AccessForm::Slice { lo, hi } => {
                        if let Some(x) = lo {
                            self.expr(x, guarded);
                        }
                        if let Some(x) = hi {
                            self.expr(x, guarded);
                        }
                    }
                }
            }
            Expr::Template(parts) => {
                for p in parts {
                    if let TemplatePart::Interp(x) = p {
                        self.expr(x, guarded);
                    }
                }
            }
            Expr::Write { value, .. } => self.expr(value, guarded),
        }
    }

    fn match_node(&mut self, m: &Match, guarded: bool) {
        let scrutinee_q = m
            .scrutinee
            .as_deref()
            .is_some_and(|s| self.qualifying_test(s));
        if let Some(s) = m.scrutinee.as_deref() {
            self.expr(s, guarded); // a self-call in the scrutinee is not arm-selected
        }
        // First-match semantics: arm `k` is selected under its own guard *and* the
        // negations of the earlier ones, so any earlier qualifying guard makes the
        // later arms' selection world-dependent too.
        let mut seen_qualifying_guard = false;
        let mut guards_recursion = false;
        let mut completing_arm = false;
        for item in &m.items {
            match item {
                MatchItem::Bind(Bind { value, .. }) => self.expr(value, guarded),
                MatchItem::Stmt(x) => self.expr(x, guarded),
                MatchItem::Arm(arm) => {
                    let guard_q = arm.guard.as_ref().is_some_and(|g| self.qualifying_test(g));
                    if let Some(g) = &arm.guard {
                        self.expr(g, guarded);
                    }
                    let world_selected = scrutinee_q || guard_q || seen_qualifying_guard;
                    seen_qualifying_guard |= guard_q;
                    let recursive_arm = contains_self_call(&arm.result, self.closure, self.callee);
                    if recursive_arm {
                        if world_selected {
                            guards_recursion = true;
                        }
                        // An unguarded recursive arm fails inside `expr` below.
                    } else {
                        completing_arm = true;
                    }
                    self.expr(&arm.result, guarded || world_selected);
                }
            }
        }
        if guards_recursion && !completing_arm {
            self.ok = false; // decorative: no completing transition seeds the closure
        }
    }

    /// A test qualifies as a current-activation world observation when it contains an
    /// effect application outright, or reads refreshed parameters (and no stale ones,
    /// and no other bindings — captures could carry stale world data).
    fn qualifying_test(&self, e: &Expr) -> bool {
        if contains_effect_application(e, self.closure) {
            return true;
        }
        let mut refreshed = false;
        let mut stale = false;
        self.read_refs(e, &mut refreshed, &mut stale);
        refreshed && !stale
    }

    fn read_refs(&self, e: &Expr, refreshed: &mut bool, stale: &mut bool) {
        if let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = e {
            if self.refreshed.contains(n) {
                *refreshed = true;
            } else if self.params.contains(n) || self.closure.env.lookup(n).is_some() {
                *stale = true;
            }
            return;
        }
        for_each_child(e, &mut |c| self.read_refs(c, refreshed, stale));
    }
}

/// Whether `e` **is** a direct effect application (`read()` in `loop(read())`) — the
/// refreshed-parameter form's syntactic admission.
fn is_effect_application(e: &Expr, closure: &Closure) -> bool {
    let Expr::Apply { callee, .. } = e else {
        return false;
    };
    let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = &**callee else {
        return false;
    };
    let Some(Binding::Value(v)) = closure.env.lookup(n) else {
        return false;
    };
    v.as_native().is_some()
        || v.as_closure()
            .is_some_and(|c| c.lambda.act_kind == ActKind::Effect)
}

/// Whether `e` contains an application of an effect-kind callee resolvable through
/// `closure`'s environment — an `@effect` closure, or a native (every current native is
/// an effect primitive; B6's total-return column is theirs).
fn contains_effect_application(e: &Expr, closure: &Closure) -> bool {
    if let Expr::Apply { callee, .. } = e
        && let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = &**callee
        && let Some(Binding::Value(v)) = closure.env.lookup(n)
        && (v.as_native().is_some()
            || v.as_closure()
                .is_some_and(|c| c.lambda.act_kind == ActKind::Effect))
    {
        return true;
    }
    let mut found = false;
    for_each_child(e, &mut |c| {
        found = found || contains_effect_application(c, closure);
    });
    found
}

/// Whether `e` contains a call to `callee` (outside nested lambdas).
fn contains_self_call(e: &Expr, closure: &Closure, callee: &ValueRef) -> bool {
    let mut sites = Vec::new();
    collect_self_calls(e, closure, callee, &mut sites);
    !sites.is_empty()
}

/// Structural recursion over an expression's immediate children, skipping nested
/// lambdas (distinct instances).
fn for_each_child(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    match e {
        Expr::Const(_) | Expr::Ref(_) | Expr::Lambda(_) => {}
        Expr::Apply { callee, args } => {
            f(callee);
            for a in args {
                let (Arg::Expr(x) | Arg::Spread(x)) = a;
                f(x);
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                f(a);
            }
        }
        Expr::Match(m) => {
            if let Some(s) = &m.scrutinee {
                f(s);
            }
            for item in &m.items {
                match item {
                    MatchItem::Bind(Bind { value, .. }) => f(value),
                    MatchItem::Stmt(x) => f(x),
                    MatchItem::Arm(arm) => {
                        if let Some(g) = &arm.guard {
                            f(g);
                        }
                        f(&arm.result);
                    }
                }
            }
        }
        Expr::TupleCons(els) => {
            for el in els {
                let (Element::Expr(x) | Element::Spread(x)) = el;
                f(x);
            }
        }
        Expr::RecordCons(fs) => {
            for fld in fs {
                match fld {
                    Field::Field { value, .. } | Field::Spread(value) => f(value),
                    Field::Computed { key, value } => {
                        f(key);
                        f(value);
                    }
                }
            }
        }
        Expr::Access { target, form, .. } => {
            f(target);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(x) => f(x),
                AccessForm::Slice { lo, hi } => {
                    if let Some(x) = lo {
                        f(x);
                    }
                    if let Some(x) = hi {
                        f(x);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    f(x);
                }
            }
        }
        Expr::Write { value, .. } => f(value),
    }
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
    let Some(closure) = f.as_closure() else {
        return false;
    };
    let Some(param) = single_param(&closure.lambda.params) else {
        return false;
    };
    let Expr::Match(m) = &*closure.lambda.body else {
        return false;
    };

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
    let Expr::PrimOp { op, args } = g else {
        return false;
    };
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
    let Pat::Tuple(elems) = params else {
        return None;
    };
    match elems.as_slice() {
        [PatElem::Pat(Pat::Bind(n))] => Some(n.clone()),
        _ => None,
    }
}

/// Every bound parameter name in a flat parameter tuple (`(n, acc)` → `["n", "acc"]`), or
/// `None` if any element is not a bare binding (a rest or nested pattern).
fn param_names(params: &Pat) -> Option<Vec<String>> {
    let Pat::Tuple(elems) = params else {
        return None;
    };
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
    let Expr::PrimOp { op, args } = arg else {
        return None;
    };
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
pub(crate) fn collect_self_calls(
    e: &Expr,
    closure: &Closure,
    cv: &ValueRef,
    out: &mut Vec<Vec<Expr>>,
) {
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
fn walk(
    e: &Expr,
    closure: &Closure,
    cv: &[ValueRef],
    params: &[String],
    lb: &[bool],
    out: &mut Vec<(Vec<Expr>, Vec<bool>)>,
) {
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
                    MatchItem::Bind(Bind { value, .. }) => {
                        walk(value, closure, cv, params, &acc, out)
                    }
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
                    Field::Field { value, .. } | Field::Spread(value) => {
                        walk(value, closure, cv, params, lb, out)
                    }
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
    let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = callee else {
        return false;
    };
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
    pub(super) fn nonneg_ints(i: &mut Interner) -> Contract {
        Contract::intersection(
            Contract::GreaterEq(Rational::from(0)),
            Contract::Mod {
                n: BigInt::from(1),
                r: BigInt::from(0),
            },
            i,
        )
    }

    pub(super) fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    #[test]
    fn count_down_grounds_over_nonneg_integers() {
        // Point base `n == 0`, unit drift −1, integer domain → grid-aligned landing.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        assert_eq!(
            ground(&cd, &nonneg_ints(&mut i), &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn ackermann_grounds_by_the_joint_lex_certificate() {
        // GR-13/14 (specimen 5): dictionary (m, n); point floors from the `== 0`
        // guards; each unit decrease gated by its negated point test; the nested
        // `ack(m, n − 1)` value obtains membership from the return half over the
        // `[Nat, Nat]` envelope.
        let mut i = Interner::new();
        let ack = f(
            "ack = (m, n) => m == 0 ? n + 1 : (n == 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)))\nack",
            &mut i,
        );
        let nat2 = vec![nonneg_ints(&mut i), nonneg_ints(&mut i)];
        assert_eq!(
            ground_args(&ack, &nat2, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
        let two = Contract::Equals(i.integer(2));
        assert_eq!(
            ground_args(&ack, &[two.clone(), two], &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn the_lex_certificate_declines_ascent_and_missing_floors() {
        // The ascending-inner twin genuinely diverges (`f(1, 1)` climbs n forever):
        // the descent scan finds no dictionary whose first change is a decrease.
        let mut i = Interner::new();
        let up = f(
            "f = (m, n) => m == 0 ? n : (n == 0 ? f(m - 1, 1) : f(m - 1, f(m, n + 1)))\nf",
            &mut i,
        );
        let nat2 = vec![nonneg_ints(&mut i), nonneg_ints(&mut i)];
        assert_eq!(
            ground_args(&up, &nat2, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );

        // A decrease with no point test anywhere on its position derives no floor —
        // the envelope declines and the candidate contributes nothing (honest, even
        // though this variant happens to terminate on Nat through `n`).
        let unfloored = f("f = (m, n) => n == 0 ? 0 : f(m - 1, n - 1)\nf", &mut i);
        let nat2 = vec![nonneg_ints(&mut i), nonneg_ints(&mut i)];
        assert_eq!(
            ground_args(&unfloored, &nat2, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    #[test]
    fn mccarthy_grounds_over_all_reals_by_the_zone_certificate() {
        // Grid §6's closed form (GR specimen 7): ascending half-line stop above,
        // climbs +11, exit shift −10, one-level feed-back; laps net +1. The region
        // base means no grid condition — the whole numeric Kind grounds, including
        // non-integer starts.
        let mut i = Interner::new();
        let m = f("m = (n) => n > 100 ? n - 10 : m(m(n + 11))\nm", &mut i);
        assert_eq!(
            ground(
                &m,
                &Contract::Kind(crate::contract::Kind::Number),
                &ContractEnv::new(),
                &mut i
            ),
            Verdict::Grounded
        );
    }

    #[test]
    fn the_zone_certificate_requires_progressing_laps_and_one_nesting_level() {
        // Lap net `d + s = 0` is the exact self-loop family (`m(100)` recurs on itself);
        // triple nesting is Knuth's k-fold generalization, divergent for these constants.
        // Neither may ground; neither has a represented witness here, so both are the
        // honest third voice.
        let mut i = Interner::new();
        let num = Contract::Kind(crate::contract::Kind::Number);
        let lap_zero = f("m = (n) => n > 100 ? n - 11 : m(m(n + 11))\nm", &mut i);
        assert_eq!(
            ground(&lap_zero, &num, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
        let k3 = f("m = (n) => n > 100 ? n - 10 : m(m(m(n + 11)))\nm", &mut i);
        assert_eq!(
            ground(&k3, &num, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    #[test]
    fn factorial_grounds_over_nonneg_integers() {
        // The self-call `f(n - 1)` is nested under `n * _`; the walk still reads its drift.
        let mut i = Interner::new();
        let fact = f("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf", &mut i);
        assert_eq!(
            ground(&fact, &nonneg_ints(&mut i), &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn half_line_base_grounds_structurally() {
        // Downward half-line base `k <= 1` — the descending chain enters it; no grid needed.
        let mut i = Interner::new();
        let g = f("g = (k) => k <= 1 ? k : g(k - 1)\ng", &mut i);
        assert_eq!(
            ground(&g, &nonneg_ints(&mut i), &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn ascending_drift_is_unproven() {
        // `n + 1` is not descent — no floor. Candidate inapplicable → Unproven (sound).
        let mut i = Interner::new();
        let up = f("f = (n) => n == 0 ? 0 : f(n + 1)\nf", &mut i);
        assert_eq!(
            ground(&up, &nonneg_ints(&mut i), &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    #[test]
    fn off_grid_point_base_over_broad_domain_is_unproven() {
        // Drift −2 to point base 0 over the *broad* domain: descent isn't proved (non-unit)
        // and there is no admitted represented-exact witness (GR-22) → Unproven. The
        // divergent inputs are only refuted from an *exact* start (next test; specimen 3c).
        let mut i = Interner::new();
        let step2 = f("f = (n) => n == 0 ? 0 : f(n - 2)\nf", &mut i);
        assert_eq!(
            ground(&step2, &nonneg_ints(&mut i), &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    #[test]
    fn non_integer_domain_is_unproven() {
        // Without the integer lattice the dense-measure landing is deferred → Unproven.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        assert_eq!(
            ground(&cd, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    // ── G-2: drift-away refutation (GR-23a) ──────────────────────────────────

    #[test]
    fn drift_away_refutes_off_grid_from_odd_witness() {
        // Specimen 12: `f(n-2)` from the written argument 1 — the odd lattice 1, −1, −3, …
        // misses the even point base 0 → forced infinite descent → refuted, witness 1.
        let mut i = Interner::new();
        let step2 = f("f = (n) => n == 0 ? 0 : f(n - 2)\nf", &mut i);
        let one = Contract::Equals(i.integer(1));
        assert!(matches!(
            ground(&step2, &one, &ContractEnv::new(), &mut i),
            Verdict::Refuted(_)
        ));
    }

    #[test]
    fn even_witness_of_the_same_function_grounds_on_the_grid() {
        // From 2 the lattice 2, 0 *hits* the base 0 → terminates. Pre-grid this was the
        // conservative Unproven; GR-18's grid now proves it (2 ≡ 0 mod 2, at or above
        // the base). Same function, opposite fate by witness parity — and never, in
        // either era, a refutation.
        let mut i = Interner::new();
        let step2 = f("f = (n) => n == 0 ? 0 : f(n - 2)\nf", &mut i);
        let two = Contract::Equals(i.integer(2));
        assert_eq!(
            ground(&step2, &two, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn self_loop_is_a_period_1_closed_orbit() {
        // `f(n)` recurs on itself with drift 0. From witness 5 (∉ the base {0}) the orbit is
        // {5} forever → refuted (GR-11 degenerate closed orbit).
        let mut i = Interner::new();
        let s = f("f = (n) => n == 0 ? 0 : f(n)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert!(matches!(
            ground(&s, &five, &ContractEnv::new(), &mut i),
            Verdict::Refuted(_)
        ));
    }

    #[test]
    fn ascending_drift_away_refutes_from_a_witness() {
        // `f(n+1)` ascends; from witness 5 the orbit 5, 6, 7, … never meets the point base 0
        // → refuted. (Over a broad domain the same function is only Unproven — no witness.)
        let mut i = Interner::new();
        let s = f("f = (n) => n == 0 ? 0 : f(n + 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert!(matches!(
            ground(&s, &five, &ContractEnv::new(), &mut i),
            Verdict::Refuted(_)
        ));
    }

    #[test]
    fn exact_witness_where_descent_proves_grounds_not_refutes() {
        // From an exact start where descent *does* prove (unit drift), Grounded wins — a
        // proven descent is never also a divergence.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert_eq!(
            ground(&cd, &five, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    // ── G-3/G-4: program-expressed linear-measure descent (§6 GR-15a/16) ─────

    #[test]
    fn compound_measure_grounds_when_no_single_arg_descends() {
        // `2a + b` drifts −1 under `f(a-1, b+1)` — but neither `a` nor `b` alone is a
        // monotone counter (b ascends). Substitute-and-normalize reads the linear measure.
        let mut i = Interner::new();
        let s = f(
            "f = (a, b) => 2 * a + b <= 0 ? a : f(a - 1, b + 1)\nf",
            &mut i,
        );
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn relational_two_varying_stop_is_unproven() {
        // `a <= b` — both sides vary; the correlation is relational ([permanent]) and this
        // route concludes nothing (GR-15a/18), even though it happens to terminate.
        let mut i = Interner::new();
        let s = f("f = (a, b) => a <= b ? a : f(a - 1, b)\nf", &mut i);
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
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
        assert_eq!(
            ground(&g1, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
        let g2 = f("f = (x, b) => f(b ? x : 0, b)\nf", &mut i);
        assert_eq!(
            ground(&g2, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
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
        assert_eq!(
            ground(&ev, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn mutual_recursion_that_does_not_descend_is_unproven() {
        // The `ping`→`pong`→`ping` cycle carries `n` unchanged — no descent → Unproven.
        let mut i = Interner::new();
        let src = "ping = (n) => n <= 0 ? 0 : pong(n)\n\
                   pong = (n) => n <= 0 ? 0 : ping(n)\n\
                   ping";
        let p = f(src, &mut i);
        assert_eq!(
            ground(&p, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    // ── G-6: structural descent (§2b, tuple peel) ────────────────────────────

    #[test]
    fn list_peel_recursion_grounds_structurally() {
        // Classic list recursion: `rest` is one element shorter than `l`, so the length
        // strictly descends to the empty base. No domain, no numeric measure.
        let mut i = Interner::new();
        let s = f(
            "f = (l) => l :: {\n [] => 0\n [h, ...rest] => 1 + f(rest)\n }\nf",
            &mut i,
        );
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn peel_recursion_with_accumulator_grounds() {
        // Multi-parameter: the peeled tuple position descends; the accumulator is carried.
        let mut i = Interner::new();
        let s = f(
            "f = (l, acc) => l :: {\n [] => acc\n [h, ...rest] => f(rest, acc + h)\n }\nf",
            &mut i,
        );
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn recursing_on_the_whole_tuple_is_unproven() {
        // The recursive call rebuilds and passes the *whole* tuple (`[h, ...rest]`), not the
        // shorter remainder — no length descent → Unproven (it diverges).
        let mut i = Interner::new();
        let s = f(
            "f = (l) => l :: {\n [] => 0\n [h, ...rest] => f([h, ...rest])\n }\nf",
            &mut i,
        );
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    // ── G-5: lexicographic descent (§5 GR-13/14) ─────────────────────────────

    #[test]
    fn lexicographic_reset_grounds() {
        // Dictionary [a, b]: `f(a-1, 10)` drops a (gated by a>0), resetting b; `f(a, b-1)`
        // holds a and drops b (gated by b>0). Neither argument descends monotonically — the
        // lex order does. Both floors come from the path guards, not the domain.
        let mut i = Interner::new();
        let s = f(
            "f = (a, b) => a <= 0 ? b : b <= 0 ? f(a - 1, 10) : f(a, b - 1)\nf",
            &mut i,
        );
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn lexicographic_with_a_relational_floor_is_unproven() {
        // `a` descends toward the stop `a == b`, but that stop is relational — it puts no
        // constant lower bound on `a`, so the decrease is ungated. Sound Unproven (it does
        // terminate, but this route cannot prove a floor).
        let mut i = Interner::new();
        let s = f("f = (a, b) => a == b ? a : f(a - 1, b)\nf", &mut i);
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    #[test]
    fn accumulator_counter_grounds_descending() {
        // `n` is the counter (drift −1 toward the `n <= 0` stop); `acc` is carried freely.
        // Structural landing — the (broad) domain is irrelevant.
        let mut i = Interner::new();
        let s = f(
            "f = (n, acc) => n <= 0 ? acc : f(n - 1, acc + n)\nf",
            &mut i,
        );
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn accumulator_counter_grounds_ascending() {
        // Ascending counter toward an upper stop `n >= 100` (drift +1) — the mirror case.
        let mut i = Interner::new();
        let s = f(
            "f = (n, acc) => n >= 100 ? acc : f(n + 1, acc + n)\nf",
            &mut i,
        );
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Grounded
        );
    }

    #[test]
    fn counter_moving_away_from_the_stop_is_unproven() {
        // Drift +1 but the stop `n <= 0` is a *lower* half-line — the counter moves away,
        // never crossing it. No matching stop → Unproven (it genuinely diverges for n > 0).
        let mut i = Interner::new();
        let s = f("f = (n, acc) => n <= 0 ? acc : f(n + 1, acc)\nf", &mut i);
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }

    #[test]
    fn a_carried_only_recursion_has_no_counter() {
        // Neither position moves toward its stop: `n` is carried and the stop is on the
        // carried `acc`. No floored counter → Unproven (sound — it can diverge).
        let mut i = Interner::new();
        let s = f("f = (n, acc) => acc <= 0 ? n : f(n, acc)\nf", &mut i);
        assert_eq!(
            ground(&s, &Contract::Top, &ContractEnv::new(), &mut i),
            Verdict::Unproven
        );
    }
}

#[cfg(test)]
mod review_gates {
    use super::tests::{f, nonneg_ints};
    use super::*;

    #[test]
    fn forced_path_discipline_is_narrow_not_blanket() {
        // The forced-path rule must not simply refuse every recursion. A self-call that IS
        // the row result is on the forced path, so the legitimate refutations still stand
        // (checked by the G-2 tests above) — and grounding a descent is unaffected, because
        // the descent side reads every syntactically present call (a conditional call must
        // still descend when taken).
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        assert_eq!(
            ground(&cd, &nonneg_ints(&mut i), &ContractEnv::new(), &mut i),
            Verdict::Grounded,
            "descent is unaffected by the refutation-side forced-path rule"
        );
        // And a *conditionally* recursive body still grounds when it descends.
        let g = f(
            "flag = true\ng = (n) => n <= 0 ? 0 : (flag ? g(n - 1) : 0)\ng",
            &mut i,
        );
        assert_ne!(
            ground(&g, &nonneg_ints(&mut i), &ContractEnv::new(), &mut i),
            Verdict::Unproven,
            "a descending conditional recursion is still judged, not abandoned"
        );
    }

    #[test]
    fn refutation_carries_its_witness_and_certificate() {
        // §7: a refutation must persist its admitted represented-exact root witness and the
        // certificate (drift + the bases the orbit misses), not recompute or discard them.
        let mut i = Interner::new();
        let step2 = f("f = (n) => n == 0 ? 0 : f(n - 2)\nf", &mut i);
        let one = Contract::Equals(i.integer(1));
        match ground(&step2, &one, &ContractEnv::new(), &mut i) {
            Verdict::Refuted(r) => {
                assert_eq!(r.witness, Rational::from(1), "the admitted written start");
                assert_eq!(r.drift, Rational::from(-2), "the forced constant drift");
                assert!(
                    !r.missed_bases.is_empty(),
                    "the bases the orbit provably misses"
                );
            }
            other => panic!("expected a witness-bearing refutation, got {other:?}"),
        }
    }

    #[test]
    fn captured_false_guard_must_not_refute() {
        // `flag` is false, so at f(1) the recursive edge is NEVER taken:
        // n != 0 -> flag false -> 0. The program TERMINATES.
        // The walker still sees one self-call in the recursive row; drift -2 from the
        // witness 1 walks 1, -1, -3, ... missing the point base 0 -> refutes.
        let mut i = Interner::new();
        let src = "flag = false\nf = (n) => n == 0 ? 0 : (flag ? f(n - 2) : 0)\nf";
        let fv = f(src, &mut i);
        let one = Contract::Equals(i.integer(1));
        assert!(
            !matches!(
                ground(&fv, &one, &ContractEnv::new(), &mut i),
                Verdict::Refuted(_)
            ),
            "FALSE REFUTATION: f(1) terminates because the guard `flag` is false"
        );
    }
}

// ── The modulo-descent certificate (gcd's shape) ─────────────────────────────

/// The seat entry taking the full argument vector: the single-domain candidates run
/// first (`ground`), and a multi-parameter recursion may then ground by
/// **modulo descent** — strictly decreasing non-negative integers at one position.
pub(crate) fn ground_args(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Verdict {
    let single = match args {
        [one] => one.clone(),
        _ => Contract::Top,
    };
    let v = ground(callee, &single, cenv, interner);
    if !matches!(v, Verdict::Unproven) {
        return v;
    }
    if args.len() >= 2 && mod_descent_shape(callee, args.len(), interner).is_some() {
        let nat = nat_contract(interner);
        if args
            .iter()
            .all(|a| matches!(subcontract(a, &nat, interner), Sub::Proven))
        {
            return Verdict::Grounded;
        }
    }
    // The joint lexicographic certificate over point floors (GR-13/14; Ackermann).
    if args.len() >= 2 && lex_grounded(callee, args, cenv, interner) {
        return Verdict::Grounded;
    }
    Verdict::Unproven
}

fn nat_contract(interner: &mut Interner) -> Contract {
    Contract::intersection(
        Contract::GreaterEq(Rational::from(0)),
        Contract::Mod {
            n: BigInt::from(1),
            r: BigInt::from(0),
        },
        interner,
    )
}

/// The **modulo-descent shape** (Euclid's): a flat multi-parameter self-recursion whose
/// every self-call passes, at some position `p`, `param % param_p` — and bare parameter
/// references everywhere else — with a preceding base row pinning position `p` to `0`.
/// Over non-negative integer starts: every position stays a non-negative integer (a
/// truncated remainder of naturals lies in `[0, divisor)`), and position `p` strictly
/// decreases while the recursion continues (`p ≥ 1` off the base row), so the chain is
/// finite. Returns `p`.
fn mod_descent_shape(callee: &ValueRef, arity: usize, interner: &mut Interner) -> Option<usize> {
    let closure = callee.as_closure()?;
    let params = crate::analyzer::region::flat_params(&closure.lambda.params)?;
    if params.len() != arity {
        return None;
    }
    let table =
        crate::analyzer::region::region_table_multi(&closure.lambda.body, &params, interner)?;

    // Gather self-call argument lists and the index of the first recursive row.
    let mut calls: Vec<Vec<Expr>> = Vec::new();
    let mut first_recursive = usize::MAX;
    let mut base_zero_positions: Vec<(usize, usize)> = Vec::new(); // (row, position)
    for (idx, row) in table.iter().enumerate() {
        let mut gc = Vec::new();
        collect_self_calls(&row.result, &closure, callee, &mut gc);
        if gc.is_empty() {
            for (pos, region) in row.regions.iter().enumerate() {
                if matches!(point_value(region), Some(v) if v == Rational::from(0)) {
                    base_zero_positions.push((idx, pos));
                }
            }
        } else {
            calls.extend(gc);
            first_recursive = first_recursive.min(idx);
        }
    }
    if calls.is_empty() {
        return None;
    }

    // A candidate position: pinned to zero by a base row before any recursive row.
    'position: for &(row, p) in &base_zero_positions {
        if row > first_recursive {
            continue;
        }
        for call in &calls {
            if call.len() != arity {
                continue 'position;
            }
            for (pos, arg) in call.iter().enumerate() {
                let ok = if pos == p {
                    is_param_rem(arg, &params, &params[p])
                } else {
                    is_any_param(arg, &params)
                };
                if !ok {
                    continue 'position;
                }
            }
        }
        return Some(p);
    }
    None
}

/// `param % param_p` — the descending position's required argument form.
fn is_param_rem(e: &Expr, params: &[String], divisor: &str) -> bool {
    let Expr::PrimOp {
        op: PrimOp::Rem,
        args,
    } = e
    else {
        return false;
    };
    matches!(&args[..], [x, d]
        if is_any_param(x, params) && is_param(d, divisor))
}

fn is_any_param(e: &Expr, params: &[String]) -> bool {
    params.iter().any(|p| is_param(e, p))
}

/// The modulo-descent **orbit envelope** for exact/bounded non-negative integer
/// starts: bare-reference positions carry existing values and remainder positions
/// shrink, so everything the recursion visits lies in `Range(0, max_start) ∧ Mod(1,0)`
/// at every position.
pub(crate) fn mod_orbit_domain(
    callee: &ValueRef,
    args: &[Contract],
    interner: &mut Interner,
) -> Option<Vec<Contract>> {
    if args.len() < 2 {
        return None;
    }
    mod_descent_shape(callee, args.len(), interner)?;
    let nat = nat_contract(interner);
    if !args
        .iter()
        .all(|a| matches!(subcontract(a, &nat, interner), Sub::Proven))
    {
        return None;
    }
    let mut hi: Option<Rational> = None;
    for a in args {
        let h = upper_bound(a)?;
        hi = Some(match hi {
            Some(cur) if cur >= h => cur,
            _ => h,
        });
    }
    let hi = hi?;
    let envelope = Contract::intersection(
        Contract::Range(Rational::from(0), hi),
        Contract::Mod {
            n: BigInt::from(1),
            r: BigInt::from(0),
        },
        interner,
    );
    Some(vec![envelope; args.len()])
}
