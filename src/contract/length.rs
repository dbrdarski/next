//! The length derivation — Λ-semantics with exactness stamps (tuple-length family
//! §2).
//!
//! `Λ(T) = { |t| : t ∈ ⟦T⟧ }` is the set of tuple lengths a contract admits.
//! [`len`] returns a **stamped** pair: a Number contract bounding Λ, plus a
//! [`Stamp`]. The soundness law holds always —
//!
//! ```text
//! Λ(T) ⊆ ⟦len(T).contract⟧
//! ```
//!
//! — and `Exact` additionally claims `⟦len(T).contract⟧ = Λ(T)`, provenly. An
//! uninhabited `T` has `Λ(T) = ∅`, hence `len(T) = (Bottom, Exact)`: impossible
//! shapes are never realizable lengths.
//!
//! Recursion is solved as a **weighted graph** over the SCC (§2, rebuilt round 2).
//! Each member is a state; each recursive alternative is an edge weighted by its
//! nonrecursive length contribution; base alternatives contribute accepting lengths
//! at their own state. The eventual period is the **gcd of closed-walk weights**
//! (equivalently the SCC-wide cycle-weight gcd) — **never** the gcd of individual
//! transition weights, which would erase parity (TL-19's R/S counterexample). The
//! saturation bound is computed in advance from the finite label sets (Principle 7).
//!
//! Exactness is forfeited — dropping to a sound `(GE(minimum), Approx)` — when an
//! alternative is nonlinear (more than one own-SCC reference) or when the label
//! boundary fails (an increment or base that is not a finite exact length set).

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;

use super::recursive::{self, Emptiness, RecGroup};
use super::{Contract, Kind};
use crate::interner::Interner;
use crate::rational::Rational;

/// Whether a derived length contract is provably *equal* to Λ, or merely a sound
/// upper bound.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Stamp {
    /// `⟦contract⟧ = Λ(T)`, provenly.
    Exact,
    /// `Λ(T) ⊆ ⟦contract⟧` only.
    Approx,
}

/// A length contract with its exactness stamp.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Len {
    pub contract: Contract,
    pub stamp: Stamp,
}

impl Len {
    fn exact(contract: Contract) -> Len {
        Len { contract, stamp: Stamp::Exact }
    }
    fn approx(contract: Contract) -> Len {
        Len { contract, stamp: Stamp::Approx }
    }
    /// Weaken to `Approx` (used when any operand or applied rule is approximate).
    fn weakened(self) -> Len {
        Len { contract: self.contract, stamp: Stamp::Approx }
    }
    pub fn is_exact(&self) -> bool {
        self.stamp == Stamp::Exact
    }
}

/// The singleton length `k`. `Range(k, k)` is `Equals(k)` over numbers (C§4) and
/// needs no interner, so length contracts stay constructible without one.
fn eq_len(k: u64) -> Contract {
    let r = Rational::from_integer(BigInt::from(k));
    Contract::Range(r.clone(), r)
}

fn ge(k: u64) -> Contract {
    Contract::GreaterEq(Rational::from_integer(BigInt::from(k)))
}

fn union_all(mut parts: Vec<Contract>) -> Contract {
    match parts.len() {
        0 => Contract::Bottom,
        1 => parts.pop().expect("len 1"),
        _ => parts
            .into_iter()
            .reduce(|a, b| Contract::Union(Box::new(a), Box::new(b)))
            .expect("non-empty"),
    }
}

// ── The derivation ───────────────────────────────────────────────────────────

/// Derive the stamped length of `c` under `group`.
pub fn len(group: &RecGroup, c: &Contract, interner: &mut Interner) -> Len {
    // An uninhabited shape has no realizable lengths at all.
    if matches!(recursive::contract_emptiness(group, c, interner), Emptiness::Empty) {
        return Len::exact(Contract::Bottom);
    }
    match c {
        Contract::Bottom => Len::exact(Contract::Bottom),

        // Exact tuples and records: the count is fixed; the stamp follows
        // inhabitation (an unproven shape may be empty, so `Equals(k)` is only an
        // upper bound until inhabitation is proven).
        Contract::Tuple(elems) => stamped_count(group, c, elems.len() as u64, false, interner),
        Contract::Record(fields) => stamped_count(group, c, fields.len() as u64, false, interner),
        // Open records: at least the named fields, with arbitrary further distinct
        // fields assumed constructible.
        Contract::HasField(_) => stamped_count(group, c, 1, true, interner),

        Contract::Concat(segs) => {
            // The C§7 sum of segment lengths; `Exact` only if every operand and
            // every applied rule is exact.
            let mut acc = Len::exact(eq_len(0));
            for s in segs {
                let l = len(group, s, interner);
                acc = sum_len(&acc, &l);
            }
            acc
        }

        Contract::Union(a, b) => {
            let (la, lb) = (len(group, a, interner), len(group, b, interner));
            let stamp = if la.is_exact() && lb.is_exact() { Stamp::Exact } else { Stamp::Approx };
            // The union of exact sets is exact.
            Len {
                contract: union_all(vec![la.contract, lb.contract]),
                stamp,
            }
        }

        // Any tuple/record shape at all.
        Contract::Top | Contract::Kind(Kind::Tuple) | Contract::Kind(Kind::Record) => {
            Len::exact(ge(0))
        }

        Contract::Equals(v) => match v.as_tuple() {
            Some(t) => Len::exact(eq_len(t.len() as u64)),
            None => match v.as_record() {
                Some(r) => Len::exact(eq_len(r.len() as u64)),
                None => Len::exact(Contract::Bottom), // not a length-bearing value
            },
        },

        Contract::Ref(name) if group.defs.contains_key(name) => solve(group, name, interner),

        // Intersection/Difference: sound bounds only.
        Contract::Intersection(a, b) => {
            let (la, lb) = (len(group, a, interner), len(group, b, interner));
            Len::approx(Contract::Intersection(Box::new(la.contract), Box::new(lb.contract)))
        }
        Contract::Difference(base, _) => len(group, base, interner).weakened(),

        // Anything else carries no tuple length.
        _ => Len::exact(Contract::Bottom),
    }
}

/// A fixed field/element count, stamped by inhabitation (§2). `open` widens to
/// `GE(n)` for open records.
fn stamped_count(
    group: &RecGroup,
    c: &Contract,
    n: u64,
    open: bool,
    interner: &mut Interner,
) -> Len {
    let contract = if open { ge(n) } else { eq_len(n) };
    match recursive::contract_emptiness(group, c, interner) {
        Emptiness::Empty => Len::exact(Contract::Bottom),
        Emptiness::NonEmpty(_) => Len::exact(contract),
        Emptiness::Unproven => Len::approx(contract),
    }
}

/// The C§7 sum of two length contracts. Exact only when both operands are exact
/// **and** the applied rule is exact for the pair (a coarsening rule stamps
/// `Approx`).
fn sum_len(a: &Len, b: &Len) -> Len {
    let stamp = if a.is_exact() && b.is_exact() { Stamp::Exact } else { Stamp::Approx };
    // Bottom + anything = Bottom (no realizable length).
    if matches!(a.contract, Contract::Bottom) || matches!(b.contract, Contract::Bottom) {
        return Len::exact(Contract::Bottom);
    }
    let contract = match (finite_lengths(&a.contract), finite_lengths(&b.contract)) {
        // Two finite exact sets sum pointwise — exact.
        (Some(xs), Some(ys)) => {
            let sums: BTreeSet<u64> = xs.iter().flat_map(|x| ys.iter().map(move |y| x + y)).collect();
            union_all(sums.into_iter().map(eq_len).collect())
        }
        // Otherwise fall back to the minima — a sound lower bound, coarsening.
        _ => return Len { contract: ge(min_of(&a.contract) + min_of(&b.contract)), stamp: Stamp::Approx },
    };
    Len { contract, stamp }
}

/// Extract a **finite exact** length set from a length contract, or `None` when the
/// label is not finite-exact (the family's label boundary: `Equals` and bounded
/// `Range` qualify after enumeration; `GE` and nonfinite modular labels do not).
fn finite_lengths(c: &Contract) -> Option<Vec<u64>> {
    fn go(c: &Contract, out: &mut BTreeSet<u64>) -> Option<()> {
        match c {
            Contract::Range(lo, hi) => {
                let (l, h) = (to_nat(lo)?, to_nat(hi)?);
                if h < l || h.saturating_sub(l) > 1024 {
                    return None; // empty or unmanageably wide
                }
                for v in l..=h {
                    out.insert(v);
                }
                Some(())
            }
            Contract::Union(a, b) => {
                go(a, out)?;
                go(b, out)
            }
            Contract::Bottom => Some(()),
            _ => None,
        }
    }
    let mut set = BTreeSet::new();
    go(c, &mut set).map(|_| set.into_iter().collect())
}

fn to_nat(r: &Rational) -> Option<u64> {
    if !r.is_integer() {
        return None;
    }
    let n = r.as_ratio().numer();
    u64::try_from(n.clone()).ok()
}

/// A sound lower bound on a length contract.
fn min_of(c: &Contract) -> u64 {
    match c {
        Contract::Range(lo, _) => to_nat(lo).unwrap_or(0),
        Contract::GreaterEq(m) => to_nat(m).unwrap_or(0),
        Contract::Greater(m) => to_nat(m).map(|v| v + 1).unwrap_or(0),
        Contract::Union(a, b) => min_of(a).min(min_of(b)),
        Contract::Intersection(a, b) => min_of(a).max(min_of(b)),
        _ => 0,
    }
}

// ── The recursive solver: a weighted graph over the SCC (§2) ─────────────────

/// One alternative of a member's definition.
enum Alt {
    /// No own-SCC reference: contributes accepting lengths at this state.
    Base(Vec<u64>),
    /// Exactly one own-SCC reference, reached after consuming these lengths.
    Edge { to: String, weights: Vec<u64> },
    /// Not solvable exactly — nonlinear, or a label outside the finite-exact
    /// boundary.
    Opaque,
}

/// Solve `Λ(name)` over its SCC.
fn solve(group: &RecGroup, name: &str, interner: &mut Interner) -> Len {
    let scc = strongly_connected(group, name);

    // Decompose every member's definition into alternatives.
    let mut alts: BTreeMap<String, Vec<Alt>> = BTreeMap::new();
    for m in &scc {
        let def = group.defs.get(m).expect("member");
        let mut list = Vec::new();
        for branch in branches(def) {
            list.push(classify(group, &scc, branch, interner));
        }
        alts.insert(m.clone(), list);
    }

    // Any opaque alternative forfeits exactness for the whole system.
    let exact_system = alts.values().flatten().all(|a| !matches!(a, Alt::Opaque));
    if !exact_system {
        let min = super::min_extent(group.defs.get(name).expect("member"));
        return Len::approx(ge(min as u64));
    }

    // Saturate achievable lengths, bounded in advance by the finite label sets.
    let bound = saturation_bound(&alts);
    let reach = saturate(&alts, bound);
    let achievable = reach.get(name).cloned().unwrap_or_default();
    if achievable.is_empty() {
        return Len::exact(Contract::Bottom);
    }

    // The eventual period is the gcd of CLOSED-WALK weights — the SCC-wide
    // cycle-weight gcd — never the gcd of individual edges (TL-19).
    let period = cycle_weight_gcd(&alts);
    Len::exact(periodic_form(&achievable, period, bound))
}

/// Split a definition into its union alternatives.
fn branches(c: &Contract) -> Vec<&Contract> {
    match c {
        Contract::Union(a, b) => {
            let mut v = branches(a);
            v.extend(branches(b));
            v
        }
        other => vec![other],
    }
}

/// Classify one alternative as a base, an edge, or opaque.
fn classify(group: &RecGroup, scc: &BTreeSet<String>, alt: &Contract, interner: &mut Interner) -> Alt {
    // Collect own-SCC references and the surrounding non-recursive segments.
    let segs: Vec<&Contract> = match alt {
        Contract::Concat(s) => s.iter().collect(),
        other => vec![other],
    };
    let mut target: Option<String> = None;
    let mut weight = Len::exact(eq_len(0));
    for s in segs {
        match s {
            Contract::Ref(n) if scc.contains(n) => {
                if target.is_some() {
                    return Alt::Opaque; // nonlinear: more than one own-SCC reference
                }
                target = Some(n.clone());
            }
            other => {
                // An own-SCC reference on a **length-relevant** path inside the
                // segment (under Union/Concat/Intersection/Difference — where
                // `len` recurses) is outside the linear fragment, and following it
                // would re-enter `solve` on this SCC without progress. Decline to
                // Opaque. Refs inside Tuple elements / Record fields are harmless:
                // arity never recurses into element lengths (`R = Tuple(E, Ref R)`
                // stays exactly 2).
                if length_path_hits(other, scc) {
                    return Alt::Opaque;
                }
                let l = len(group, other, interner);
                if !l.is_exact() {
                    return Alt::Opaque; // label outside the finite-exact boundary
                }
                weight = sum_len(&weight, &l);
            }
        }
    }
    let Some(weights) = finite_lengths(&weight.contract) else {
        return Alt::Opaque;
    };
    match target {
        None => Alt::Base(weights),
        Some(to) => Alt::Edge { to, weights },
    }
}

/// Whether an own-SCC reference is reachable along a path `len` itself recurses
/// through (Union/Concat/Intersection/Difference/Ref) — the paths where following
/// it would loop. Tuple elements and Record fields are *not* length-relevant.
fn length_path_hits(c: &Contract, scc: &BTreeSet<String>) -> bool {
    match c {
        Contract::Ref(n) => scc.contains(n),
        Contract::Union(a, b) | Contract::Intersection(a, b) | Contract::Difference(a, b) => {
            length_path_hits(a, scc) || length_path_hits(b, scc)
        }
        Contract::Concat(segs) => segs.iter().any(|s| length_path_hits(s, scc)),
        _ => false,
    }
}

/// The SCC containing `name`: the members mutually reachable with it.
fn strongly_connected(group: &RecGroup, name: &str) -> BTreeSet<String> {
    let reach = |from: &str| -> BTreeSet<String> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![from.to_string()];
        while let Some(n) = stack.pop() {
            if !seen.insert(n.clone()) {
                continue;
            }
            if let Some(def) = group.defs.get(&n) {
                let mut refs = BTreeSet::new();
                collect_refs(def, &mut refs);
                stack.extend(refs);
            }
        }
        seen
    };
    let forward = reach(name);
    forward
        .iter()
        .filter(|m| reach(m).contains(name))
        .cloned()
        .collect()
}

fn collect_refs(c: &Contract, out: &mut BTreeSet<String>) {
    match c {
        Contract::Ref(n) => {
            out.insert(n.clone());
        }
        Contract::Union(a, b) | Contract::Intersection(a, b) | Contract::Difference(a, b) => {
            collect_refs(a, out);
            collect_refs(b, out);
        }
        Contract::Tuple(v) | Contract::Concat(v) => v.iter().for_each(|x| collect_refs(x, out)),
        Contract::Record(f) => f.iter().for_each(|(_, x)| collect_refs(x, out)),
        _ => {}
    }
}

/// An advance-computed saturation bound from the finite label sets (Principle 7):
/// beyond the conductor of the numerical semigroup the increments generate, the
/// achievable set is purely periodic.
fn saturation_bound(alts: &BTreeMap<String, Vec<Alt>>) -> u64 {
    let mut max_w = 1u64;
    let mut max_b = 0u64;
    for a in alts.values().flatten() {
        match a {
            Alt::Base(ws) => max_b = max_b.max(ws.iter().copied().max().unwrap_or(0)),
            Alt::Edge { weights, .. } => {
                max_w = max_w.max(weights.iter().copied().max().unwrap_or(0).max(1))
            }
            Alt::Opaque => {}
        }
    }
    let states = alts.len().max(1) as u64;
    max_b + (max_w * states) * (max_w * states) + max_w * states + 2
}

/// Achievable lengths per state, up to `bound` — a least fixpoint over the graph.
fn saturate(alts: &BTreeMap<String, Vec<Alt>>, bound: u64) -> BTreeMap<String, BTreeSet<u64>> {
    let mut set: BTreeMap<String, BTreeSet<u64>> =
        alts.keys().map(|k| (k.clone(), BTreeSet::new())).collect();
    // Seed with bases.
    for (state, list) in alts {
        for a in list {
            if let Alt::Base(ws) = a {
                for w in ws {
                    if *w <= bound {
                        set.get_mut(state).expect("state").insert(*w);
                    }
                }
            }
        }
    }
    // Propagate along edges until stable.
    loop {
        let mut changed = false;
        for (state, list) in alts {
            for a in list {
                let Alt::Edge { to, weights } = a else { continue };
                let targets: Vec<u64> = set.get(to).cloned().unwrap_or_default().into_iter().collect();
                for t in targets {
                    for w in weights {
                        let v = t + w;
                        if v <= bound && set.get_mut(state).expect("state").insert(v) {
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    set
}

/// The gcd of all closed-walk weights in the SCC, via edge potentials: assign
/// `pot` by traversal, then every edge `u →w v` contributes `pot[u] + w − pot[v]`.
/// This is the cycle-weight gcd, **not** the edge-weight gcd (TL-19).
fn cycle_weight_gcd(alts: &BTreeMap<String, Vec<Alt>>) -> u64 {
    let mut pot: BTreeMap<&str, i64> = BTreeMap::new();
    let Some(root) = alts.keys().next() else { return 1 };
    pot.insert(root.as_str(), 0);

    // Propagate potentials (the graph is strongly connected within an SCC).
    let mut changed = true;
    while changed {
        changed = false;
        for (state, list) in alts {
            let Some(&ps) = pot.get(state.as_str()) else { continue };
            for a in list {
                let Alt::Edge { to, weights } = a else { continue };
                let Some(&w) = weights.first() else { continue };
                if !pot.contains_key(to.as_str()) {
                    pot.insert(to.as_str(), ps + w as i64);
                    changed = true;
                }
            }
        }
    }

    let mut g: u64 = 0;
    for (state, list) in alts {
        let Some(&ps) = pot.get(state.as_str()) else { continue };
        for a in list {
            let Alt::Edge { to, weights } = a else { continue };
            let Some(&pt) = pot.get(to.as_str()) else { continue };
            for w in weights {
                let d = (ps + *w as i64 - pt).unsigned_abs();
                g = gcd(g, d);
            }
        }
    }
    if g == 0 { 1 } else { g }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// Render an ultimately-periodic achievable set as a contract: for each residue
/// class mod `period`, the smallest point from which the class is complete becomes
/// a `Mod ∩ GE` tail; everything below stays an explicit exceptional value.
fn periodic_form(achievable: &BTreeSet<u64>, period: u64, bound: u64) -> Contract {
    let mut parts: Vec<Contract> = Vec::new();
    let mut covered: BTreeSet<u64> = BTreeSet::new();

    for r in 0..period {
        // The smallest x ≡ r (mod period) from which every member of the class up
        // to `bound` is achievable.
        let class: Vec<u64> = (r..=bound).step_by(period as usize).collect();
        let mut start: Option<u64> = None;
        for (i, v) in class.iter().enumerate() {
            if class[i..].iter().all(|x| achievable.contains(x)) {
                start = Some(*v);
                break;
            }
        }
        let Some(start) = start else { continue };
        parts.push(if period == 1 {
            ge(start)
        } else {
            Contract::Intersection(
                Box::new(Contract::Mod {
                    n: BigInt::from(period),
                    r: BigInt::from(start % period),
                }),
                Box::new(ge(start)),
            )
        });
        covered.extend(class.into_iter().filter(|v| *v >= start));
    }

    // Exceptional values below their class's tail.
    for v in achievable.iter().filter(|v| !covered.contains(v)) {
        parts.push(eq_len(*v));
    }
    parts.sort_by_key(min_of);
    union_all(parts)
}
