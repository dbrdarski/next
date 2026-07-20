//! Three-valued subcontract `A ⊑ B` (Compendium C§8).
//!
//! Returns [`Verdict::Proven`] (`⟦A⟧ ⊆ ⟦B⟧`), [`Verdict::Refuted`] with a concrete
//! witness in `⟦A⟧ \ ⟦B⟧`, or [`Verdict::Unproven`] (the honest shrug). Soundness
//! is the invariant and is brute-tested against the denotational membership
//! ([`Contract::contains`]) — the truth source — in `tests.rs`:
//!
//! - `Proven` ⇒ no value is in `A` but not `B`,
//! - `Refuted(w)` ⇒ `w ∈ ⟦A⟧ \ ⟦B⟧`.
//!
//! The proof side uses sound structural rules (Union/Intersection/Difference) plus
//! decidable atom rules (Kind, interval containment, Mod lattice, exact Record,
//! Tuple, `Equals` via membership). The refutation side samples members of `A` and
//! checks them against `B`. Anything neither proved nor refuted is `Unproven`
//! (never guessed). Recursive contracts (C§9) are a later layer on top of this.

use num_bigint::BigInt;
use num_traits::Zero;

use super::{Contract, Kind as VKind};
use crate::interner::Interner;
use crate::rational::Rational;
use crate::value::ValueRef;

/// The three-valued subcontract verdict.
#[derive(Clone, Debug)]
pub enum Verdict {
    Proven,
    Refuted(ValueRef),
    Unproven,
}

/// Decide `A ⊑ B`.
pub fn subcontract(a: &Contract, b: &Contract, interner: &mut Interner) -> Verdict {
    if provable(a, b) {
        return Verdict::Proven;
    }
    if let Some(w) = refute(a, b, interner) {
        return Verdict::Refuted(w);
    }
    Verdict::Unproven
}

// ── Proof side (sound; `true` only when `⟦A⟧ ⊆ ⟦B⟧`) ─────────────────────────

fn provable(a: &Contract, b: &Contract) -> bool {
    use Contract::*;

    // Bottom (or a provably-empty source) is a subcontract of everything.
    if is_empty(a) {
        return true;
    }

    // Structure of B first — the "and-like" rules are complete for proof.
    match b {
        Top => return true,
        Intersection(b1, b2) => return provable(a, b1) && provable(a, b2),
        Difference(bb, e) => return provable(a, bb) && disjoint(a, e),
        _ => {}
    }

    // Complete rules on the shape of A.
    match a {
        Bottom => return true,
        Union(a1, a2) => return provable(a1, b) && provable(a2, b),
        // `A \ E ⊑ B` if `A ⊑ B` (sound, incomplete — E may remove the bad part).
        Difference(aa, _) if provable(aa, b) => return true,
        // `Equals(v) ⊑ B` is decidable: `v ∈ ⟦B⟧`.
        Equals(v) => return b.contains(v),
        _ => {}
    }

    // Sound-but-incomplete "or" rules: A ⊑ (B1∪B2) if A⊑B1 or A⊑B2; (A1∩A2) ⊑ B
    // if A1⊑B or A2⊑B.
    let or_rule = match (a, b) {
        (_, Union(b1, b2)) => provable(a, b1) || provable(a, b2),
        (Intersection(a1, a2), _) => provable(a1, b) || provable(a2, b),
        _ => false,
    };
    if or_rule {
        return true;
    }

    if a == b {
        return true; // reflexivity
    }
    atom_provable(a, b)
}

fn atom_provable(a: &Contract, b: &Contract) -> bool {
    use Contract::*;
    match (a, b) {
        (Kind(k1), Kind(k2)) => k1 == k2,
        // Every numeric atom is a Number.
        (Range(..) | Greater(_) | GreaterEq(_) | Less(_) | LessEq(_) | Mod { .. } | Geo { .. }, Kind(VKind::Number)) => true,
        // A structured contract inhabits its kind.
        (Tuple(_), Kind(VKind::Tuple)) => true,
        (Record(_) | HasField(_), Kind(VKind::Record)) => true,
        (Mod { n: n1, r: r1 }, Mod { n: n2, r: r2 }) => mod_subset(n1, r1, n2, r2),
        (HasField(k1), HasField(k2)) => k1 == k2,
        // An exact record having field `k` is a subcontract of `HasField(k)`.
        (Record(fields), HasField(k)) => fields.iter().any(|(key, _)| key == k),
        (Record(fa), Record(fb)) => record_subset(fa, fb),
        (Tuple(ea), Tuple(eb)) => ea.len() == eb.len() && ea.iter().zip(eb).all(|(x, y)| provable(x, y)),
        (Indeterminate(f1), Indeterminate(f2)) => f1 == f2,
        _ => match (interval_of(a), interval_of(b)) {
            (Some(ia), Some(ib)) => interval_subset(&ia, &ib),
            _ => false,
        },
    }
}

/// `Record` is exact: `A ⊑ B` iff same key set and each field's contract is a
/// subcontract of `B`'s.
fn record_subset(fa: &[(String, Contract)], fb: &[(String, Contract)]) -> bool {
    fa.len() == fb.len()
        && fa.iter().all(|(key, ca)| match fb.iter().find(|(k, _)| k == key) {
            Some((_, cb)) => provable(ca, cb),
            None => false,
        })
}

/// `Mod(n1,r1) ⊑ Mod(n2,r2)` iff every `x ≡ r1 (mod n1)` also has `x ≡ r2 (mod n2)`
/// — i.e. `n2 | n1` and `r1 ≡ r2 (mod n2)`.
fn mod_subset(n1: &BigInt, r1: &BigInt, n2: &BigInt, r2: &BigInt) -> bool {
    !n2.is_zero() && (n1 % n2).is_zero() && ((r1 - r2) % n2).is_zero()
}

// ── Intervals ────────────────────────────────────────────────────────────────

/// A numeric interval as `(low, high)` bounds; `None` = unbounded.
struct Interval {
    low: Bound,
    high: Bound,
}
enum Bound {
    Unbounded,
    /// inclusive
    Incl(Rational),
    /// exclusive
    Excl(Rational),
}

fn interval_of(c: &Contract) -> Option<Interval> {
    Some(match c {
        Contract::Range(lo, hi) => Interval { low: Bound::Incl(lo.clone()), high: Bound::Incl(hi.clone()) },
        Contract::Greater(m) => Interval { low: Bound::Excl(m.clone()), high: Bound::Unbounded },
        Contract::GreaterEq(m) => Interval { low: Bound::Incl(m.clone()), high: Bound::Unbounded },
        Contract::Less(m) => Interval { low: Bound::Unbounded, high: Bound::Excl(m.clone()) },
        Contract::LessEq(m) => Interval { low: Bound::Unbounded, high: Bound::Incl(m.clone()) },
        // Landing zones: an intersection of intervals is their meet (C§4).
        Contract::Intersection(a, b) => meet(interval_of(a)?, interval_of(b)?),
        _ => return None,
    })
}

/// The meet (intersection) of two intervals: highest low, lowest high.
fn meet(a: Interval, b: Interval) -> Interval {
    let low = if low_ge(&a.low, &b.low) { a.low } else { b.low };
    let high = if high_le(&a.high, &b.high) { a.high } else { b.high };
    Interval { low, high }
}

/// `A ⊆ B` for intervals: A's low is no lower than B's, and A's high no higher.
fn interval_subset(a: &Interval, b: &Interval) -> bool {
    low_ge(&a.low, &b.low) && high_le(&a.high, &b.high)
}

/// A's lower bound starts at or above B's lower bound.
fn low_ge(a: &Bound, b: &Bound) -> bool {
    match (a, b) {
        (_, Bound::Unbounded) => true,        // B extends infinitely down
        (Bound::Unbounded, _) => false,       // A extends below B
        (a, b) => {
            let (va, sa) = bound_parts(a);
            let (vb, sb) = bound_parts(b);
            // ok iff A's lowest allowed value ≥ B's lowest allowed value.
            va > vb || (va == vb && (sa || !sb)) // equal: bad only if A inclusive & B exclusive
        }
    }
}

/// A's upper bound ends at or below B's upper bound.
fn high_le(a: &Bound, b: &Bound) -> bool {
    match (a, b) {
        (_, Bound::Unbounded) => true,
        (Bound::Unbounded, _) => false,
        (a, b) => {
            let (va, sa) = bound_parts(a);
            let (vb, sb) = bound_parts(b);
            va < vb || (va == vb && (sa || !sb))
        }
    }
}

/// `(value, strict)` for a finite bound.
fn bound_parts(b: &Bound) -> (&Rational, bool) {
    match b {
        Bound::Incl(v) => (v, false),
        Bound::Excl(v) => (v, true),
        Bound::Unbounded => unreachable!(),
    }
}

// ── Disjointness and emptiness (sound; `true` only when provable) ─────────────

/// Shared with the recursive layer (C§9), which needs leaf-level disjointness to
/// bottom out product-graph intersection emptiness.
pub(crate) fn disjoint(a: &Contract, b: &Contract) -> bool {
    use Contract::*;
    match (a, b) {
        (Bottom, _) | (_, Bottom) => true,
        (Equals(v), other) | (other, Equals(v)) => !other.contains(v),
        (Kind(k1), Kind(k2)) => k1 != k2,
        // A numeric interval is disjoint from a non-numeric kind.
        (Kind(k), other) | (other, Kind(k)) if *k != VKind::Number && is_numeric(other) => true,
        // A record contract is disjoint from any non-Record kind.
        (Kind(k), Record(_) | HasField(_)) | (Record(_) | HasField(_), Kind(k)) if *k != VKind::Record => true,
        // A tuple contract is disjoint from any non-Tuple kind.
        (Kind(k), Tuple(_)) | (Tuple(_), Kind(k)) if *k != VKind::Tuple => true,
        // An exact record lacking field `k` can never have it.
        (Record(fields), HasField(k)) | (HasField(k), Record(fields)) => !fields.iter().any(|(key, _)| key == k),
        (Union(a1, a2), other) | (other, Union(a1, a2)) => disjoint(a1, other) && disjoint(a2, other),
        (Intersection(a1, a2), other) | (other, Intersection(a1, a2)) => {
            disjoint(a1, other) || disjoint(a2, other)
        }
        _ => match (interval_of(a), interval_of(b)) {
            (Some(ia), Some(ib)) => intervals_disjoint(&ia, &ib),
            _ => false,
        },
    }
}

fn intervals_disjoint(a: &Interval, b: &Interval) -> bool {
    // Disjoint iff a is entirely below b, or entirely above b.
    below(&a.high, &b.low) || below(&b.high, &a.low)
}

/// `high` bound is strictly below `low` bound (no overlap point).
fn below(high: &Bound, low: &Bound) -> bool {
    match (high, low) {
        (Bound::Unbounded, _) | (_, Bound::Unbounded) => false,
        (h, l) => {
            let (vh, sh) = bound_parts(h);
            let (vl, sl) = bound_parts(l);
            vh < vl || (vh == vl && (sh || sl)) // touching point excluded by either side
        }
    }
}

fn half() -> Rational {
    Rational::new(BigInt::from(1), BigInt::from(2))
}

fn is_numeric(c: &Contract) -> bool {
    matches!(
        c,
        Contract::Range(..)
            | Contract::Greater(_)
            | Contract::GreaterEq(_)
            | Contract::Less(_)
            | Contract::LessEq(_)
            | Contract::Mod { .. }
            | Contract::Geo { .. }
    )
}

fn is_empty(c: &Contract) -> bool {
    use Contract::*;
    match c {
        Bottom => true,
        Range(lo, hi) => lo > hi,
        Intersection(a, b) => is_empty(a) || is_empty(b) || disjoint(a, b),
        Union(a, b) => is_empty(a) && is_empty(b),
        Difference(a, _) => is_empty(a),
        _ => false,
    }
}

// ── Refutation side (sound; witness verified in `⟦A⟧ \ ⟦B⟧`) ──────────────────

fn refute(a: &Contract, b: &Contract, interner: &mut Interner) -> Option<ValueRef> {
    // A sample must genuinely inhabit A (a valid witness) and be outside B.
    sample(a, interner).into_iter().find(|s| a.contains(s) && !b.contains(s))
}

/// Candidate members of `⟦c⟧` (best-effort; the caller re-checks membership).
/// Shared with the operation rules (C§7), which sample operands to hunt for
/// safety-refuting witness tuples.
pub(crate) fn sample(c: &Contract, interner: &mut Interner) -> Vec<ValueRef> {
    use Contract::*;
    let nums = |i: &mut Interner, vs: &[i64]| vs.iter().map(|&n| i.integer(n)).collect::<Vec<_>>();
    match c {
        Top => nums(interner, &[0, 1, -1]),
        Bottom => vec![],
        Kind(k) => match k {
            VKind::Number => nums(interner, &[0, 1, -1, 2, 100]),
            VKind::String => vec![interner.string(""), interner.string("a")],
            VKind::Boolean => vec![interner.boolean(true), interner.boolean(false)],
            VKind::Null => vec![interner.null()],
            VKind::Tuple => vec![interner.tuple(vec![])],
            VKind::Record => vec![interner.record_str(vec![])],
            VKind::Function => vec![],
        },
        Equals(v) => vec![v.clone()],
        Range(lo, hi) => {
            let mid = (lo.clone() + hi.clone()) / Rational::from(2);
            vec![interner.number(lo.clone()), interner.number(hi.clone()), interner.number(mid)]
        }
        // Include a fractional near-bound point — the rationals are dense, so a
        // half-step witnesses gaps that integer steps miss.
        Greater(m) => vec![
            interner.number(m.clone() + Rational::from(1)),
            interner.number(m.clone() + half()),
        ],
        GreaterEq(m) => vec![interner.number(m.clone()), interner.number(m.clone() + half())],
        Less(m) => vec![
            interner.number(m.clone() - Rational::from(1)),
            interner.number(m.clone() - half()),
        ],
        LessEq(m) => vec![interner.number(m.clone()), interner.number(m.clone() - half())],
        Mod { n, r } => {
            let base = Rational::from_integer(r.clone());
            let step = Rational::from_integer(n.clone());
            vec![
                interner.number(base.clone()),
                interner.number(base.clone() + step.clone()),
                interner.number(base - step),
            ]
        }
        Geo { b, r } => {
            vec![interner.number(b.clone()), interner.number(b.clone() * r.clone())]
        }
        Indeterminate(f) => vec![interner.indeterminate(*f)],
        // A bare reference is unsampleable without its group; recursive sampling
        // lives in `recursive`.
        Ref(_) => vec![],
        Union(a1, a2) => {
            let mut v = sample(a1, interner);
            v.extend(sample(a2, interner));
            v
        }
        Intersection(a1, a2) => {
            let mut v = sample(a1, interner);
            v.extend(sample(a2, interner));
            v.retain(|s| a1.contains(s) && a2.contains(s));
            v
        }
        Difference(base, ex) => {
            let mut v = sample(base, interner);
            v.retain(|s| !ex.contains(s));
            v
        }
        HasField(key) => {
            let val = interner.integer(0);
            vec![interner.record_str(vec![(key.as_str(), val)])]
        }
        Record(fields) => {
            // Build one record picking the first sample of each field; if any
            // field is unsampleable, produce no witness.
            let mut pairs = Vec::new();
            for (key, contract) in fields {
                match sample(contract, interner).into_iter().next() {
                    Some(s) => pairs.push((key.encode_utf16().collect(), s)),
                    None => return vec![],
                }
            }
            vec![interner.record(pairs)]
        }
        Tuple(elems) => {
            let mut items = Vec::new();
            for contract in elems {
                match sample(contract, interner).into_iter().next() {
                    Some(s) => items.push(s),
                    None => return vec![],
                }
            }
            vec![interner.tuple(items)]
        }
    }
}
