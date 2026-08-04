//! The shared numeric abstraction behind the bound family — `Range` (closed,
//! bounded) and the four half-lines (`Greater`/`GreaterEq`/`Less`/`LessEq`) are one
//! shape: an interval with an optional, possibly-strict endpoint on each side.
//!
//! Extracted from `subcontract.rs` so the subcontract/disjointness reasoning and the
//! C§7 operation transfer rules share **one** encoding rather than two parallel ones.
//!
//! ## The direction asymmetry — normative, and the reason there are two conversions
//!
//! A contract may be read into an interval in two different directions, and they are
//! **not** interchangeable:
//!
//! - [`interval_exact`] — the interval **denotes exactly** `⟦c⟧` (for the forms it
//!   accepts). Required for **subset/disjointness testing**, where widening the
//!   right-hand side would make `⊑` wrongly *true*. It therefore returns `None` for a
//!   form whose extent it cannot state exactly — notably `Mod`, whose members are the
//!   integers `≡ r (mod n)`: reading it as "unbounded" would make
//!   `GreaterEq(0) ⊑ Mod(1,0)` come out **Proven**, which is false (`0.5` is ≥ 0 and
//!   not an integer).
//! - a widening conversion (owed with the C§7 image rules) — the interval **contains**
//!   `⟦c⟧`. Sound for an **image over-approximation**, where widening an input only
//!   widens the image, so `Mod`/`Geo` *may* read as unbounded there.
//!
//! Keep them separate and keep this note with them.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, Zero};

use super::{Contract, Kind};
use crate::ast::PrimOp;
use crate::interner::Interner;
use crate::rational::Rational;

/// A numeric interval as `(low, high)` bounds.
#[derive(Clone, Debug)]
pub(crate) struct Interval {
    pub low: Bound,
    pub high: Bound,
}

/// One endpoint of an [`Interval`].
#[derive(Clone, Debug)]
pub(crate) enum Bound {
    Unbounded,
    /// inclusive
    Incl(Rational),
    /// exclusive
    Excl(Rational),
}

impl Bound {
    fn value(&self) -> Option<&Rational> {
        match self {
            Bound::Incl(v) | Bound::Excl(v) => Some(v),
            Bound::Unbounded => None,
        }
    }
    fn is_incl(&self) -> bool {
        matches!(self, Bound::Incl(_))
    }
}

impl Interval {
    pub fn unbounded() -> Interval {
        Interval {
            low: Bound::Unbounded,
            high: Bound::Unbounded,
        }
    }
    pub fn point(v: Rational) -> Interval {
        Interval {
            low: Bound::Incl(v.clone()),
            high: Bound::Incl(v),
        }
    }
    /// Proven empty — the bounds cross, or meet at a point one side excludes.
    fn is_empty(&self) -> bool {
        match (self.low.value(), self.high.value()) {
            (Some(l), Some(h)) => l > h || (l == h && !(self.low.is_incl() && self.high.is_incl())),
            _ => false,
        }
    }
}

/// Which side of zero an interval is confined to — the only fact `×` and `/` need
/// when an endpoint is unbounded.
#[derive(PartialEq, Clone, Copy)]
enum SignClass {
    NonNeg,
    NonPos,
    Unknown,
}

fn sign_class(iv: &Interval) -> SignClass {
    let zero = Rational::from(0);
    if iv.low.value().is_some_and(|l| *l >= zero) {
        return SignClass::NonNeg;
    }
    if iv.high.value().is_some_and(|h| *h <= zero) {
        return SignClass::NonPos;
    }
    SignClass::Unknown
}

/// Whether `0 ∈ ⟦iv⟧` — a divisor containing zero has no numeric bound (and yields
/// an Indeterminate value, handled by the caller).
fn contains_zero(iv: &Interval) -> bool {
    let zero = Rational::from(0);
    let above_low = match &iv.low {
        Bound::Unbounded => true,
        Bound::Incl(l) => *l <= zero,
        Bound::Excl(l) => *l < zero,
    };
    let below_high = match &iv.high {
        Bound::Unbounded => true,
        Bound::Incl(h) => *h >= zero,
        Bound::Excl(h) => *h > zero,
    };
    above_low && below_high
}

// ── Congruence — the integer-lattice facet ───────────────────────────────────

/// `x ≡ r (mod n)`. **`n = 0` encodes an exact integer** (`x = r`) — which makes the
/// `gcd`-based composition rules below uniform: `gcd(0, m) = m`, so an exact operand
/// composes with a lattice operand exactly as it should (`Equals(2) + Mod(2,0)` stays
/// `Mod(2,0)` — even + 2 is even), and integrality survives `±` (the non-negative
/// integers minus 1 are still integers).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Congruence {
    pub n: BigInt,
    pub r: BigInt,
}

impl Congruence {
    fn new(n: BigInt, r: BigInt) -> Congruence {
        let n = n.abs();
        let r = if n.is_zero() { r } else { r.mod_floor(&n) };
        Congruence { n, r }
    }
    fn exact(v: BigInt) -> Congruence {
        Congruence {
            n: BigInt::zero(),
            r: v,
        }
    }

    fn add(&self, o: &Congruence) -> Congruence {
        Congruence::new(self.n.gcd(&o.n), &self.r + &o.r)
    }
    fn sub(&self, o: &Congruence) -> Congruence {
        Congruence::new(self.n.gcd(&o.n), &self.r - &o.r)
    }
    fn neg(&self) -> Congruence {
        Congruence::new(self.n.clone(), -&self.r)
    }
    /// Scaling by an exact integer (C§7's *scaling*): `x ≡ r (mod n) ⇒ cx ≡ cr (mod cn)`.
    fn scale(&self, c: &BigInt) -> Congruence {
        Congruence::new(&self.n * c, &self.r * c)
    }

    /// The tightest congruence containing both — CRT. `None` when the two are
    /// incompatible (their intersection is empty).
    fn meet(&self, o: &Congruence) -> Option<Congruence> {
        let g = self.n.gcd(&o.n);
        if !g.is_zero() && !((&self.r - &o.r) % &g).is_zero() {
            return None; // incompatible residues
        }
        if self.n.is_zero() {
            return Some(self.clone()); // already exact
        }
        if o.n.is_zero() {
            return Some(o.clone());
        }
        let lcm = self.n.lcm(&o.n);
        // Search one lcm window: finite (lcm/n steps) and exact.
        let mut cand = self.r.clone();
        while cand < lcm {
            if (&cand - &o.r).mod_floor(&o.n).is_zero() {
                return Some(Congruence::new(lcm, cand));
            }
            cand += &self.n;
        }
        None
    }

    /// The coarsest congruence containing both — the join used for a union hull.
    fn join(&self, o: &Congruence) -> Congruence {
        let g = self.n.gcd(&o.n).gcd(&(&self.r - &o.r));
        Congruence::new(g, self.r.clone())
    }
}

// ── NumAbs — the two facets together ─────────────────────────────────────────

/// The numeric abstraction: an interval and (when known) an integer-lattice
/// congruence. This is the shape every numeric contract form projects onto.
#[derive(Clone, Debug)]
pub(crate) struct NumAbs {
    pub iv: Interval,
    pub cong: Option<Congruence>,
}

impl NumAbs {
    fn of(iv: Interval) -> NumAbs {
        NumAbs { iv, cong: None }
    }
}

/// The **widening** conversion — the interval/congruence pair *containing* `⟦c⟧`,
/// returned only when `⟦c⟧ ⊆ Numbers`. Sound for an **image over-approximation**
/// only; see the module note (`Mod`/`Geo` read as unbounded here, which would be
/// unsound for subset testing).
pub(crate) fn num_abs(c: &Contract) -> Option<NumAbs> {
    Some(match c {
        Contract::Kind(Kind::Number) => NumAbs::of(Interval::unbounded()),
        Contract::Range(l, h) => NumAbs::of(Interval {
            low: Bound::Incl(l.clone()),
            high: Bound::Incl(h.clone()),
        }),
        Contract::Greater(m) => NumAbs::of(Interval {
            low: Bound::Excl(m.clone()),
            high: Bound::Unbounded,
        }),
        Contract::GreaterEq(m) => NumAbs::of(Interval {
            low: Bound::Incl(m.clone()),
            high: Bound::Unbounded,
        }),
        Contract::Less(m) => NumAbs::of(Interval {
            low: Bound::Unbounded,
            high: Bound::Excl(m.clone()),
        }),
        Contract::LessEq(m) => NumAbs::of(Interval {
            low: Bound::Unbounded,
            high: Bound::Incl(m.clone()),
        }),
        Contract::Equals(v) => {
            let q = v.as_number()?.clone();
            let cong = q
                .is_integer()
                .then(|| Congruence::exact(q.as_ratio().numer().clone()));
            NumAbs {
                iv: Interval::point(q),
                cong,
            }
        }
        // The lattice: unbounded extent, exact congruence.
        Contract::Mod { n, r } => NumAbs {
            iv: Interval::unbounded(),
            cong: Some(Congruence::new(n.clone(), r.clone())),
        },
        // `b, b·r, b·r², …` with `r > 1` — bounded on the side `b` sits.
        Contract::Geo { b, .. } => {
            let zero = Rational::from(0);
            let iv = if *b > zero {
                Interval {
                    low: Bound::Incl(b.clone()),
                    high: Bound::Unbounded,
                }
            } else {
                Interval {
                    low: Bound::Unbounded,
                    high: Bound::Incl(b.clone()),
                }
            };
            NumAbs::of(iv)
        }
        Contract::Intersection(a, b) => {
            let (x, y) = (num_abs(a), num_abs(b));
            match (x, y) {
                (Some(x), Some(y)) => {
                    let cong = match (&x.cong, &y.cong) {
                        (Some(p), Some(q)) => p.meet(q),
                        (Some(p), None) => Some(p.clone()),
                        (None, q) => q.clone(),
                    };
                    NumAbs {
                        iv: meet(x.iv, y.iv),
                        cong,
                    }
                }
                // `⟦A ∩ B⟧ ⊆ ⟦A⟧`, so one side alone already contains the meet.
                (Some(x), None) | (None, Some(x)) => x,
                (None, None) => return None,
            }
        }
        Contract::Union(a, b) => {
            let (x, y) = (num_abs(a)?, num_abs(b)?);
            let cong = match (&x.cong, &y.cong) {
                (Some(p), Some(q)) => Some(p.join(q)),
                _ => None,
            };
            NumAbs {
                iv: hull(x.iv, y.iv),
                cong,
            }
        }
        // Dropping the exclusion only widens (sound) — but a **singleton exclusion sitting
        // on an endpoint** tightens that endpoint instead of being lost: `[0,∞) ∖ {0}` is
        // `(0,∞)`. This is what makes a guarded recursive step land back inside its domain
        // (`n ≥ 0 ∧ n ≠ 0 ⇒ n ≥ 1 ⇒ n-1 ≥ 0`).
        Contract::Difference(a, b) => {
            let mut x = num_abs(a)?;
            if let Some(q) = as_point(b) {
                if matches!(&x.iv.low, Bound::Incl(l) if *l == q) {
                    x.iv.low = Bound::Excl(q.clone());
                }
                if matches!(&x.iv.high, Bound::Incl(h) if *h == q) {
                    x.iv.high = Bound::Excl(q);
                }
            }
            // A **half-line exclusion** bounds the remainder outright: whatever
            // survives `∖ {x ≤ c}` is `> c` (and dually), so the abstraction meets the
            // complement half-line — unconditionally sound, no endpoint condition
            // needed. `snap_to_lattice` then turns `> 0` into `≥ 1` on an integer
            // lattice: the `n <= 0` guard's remainder landing `n - 1` back inside its
            // domain, exactly as the point guard's does.
            let complement = match &**b {
                Contract::LessEq(c) => Some(Interval {
                    low: Bound::Excl(c.clone()),
                    high: Bound::Unbounded,
                }),
                Contract::Less(c) => Some(Interval {
                    low: Bound::Incl(c.clone()),
                    high: Bound::Unbounded,
                }),
                Contract::GreaterEq(c) => Some(Interval {
                    low: Bound::Unbounded,
                    high: Bound::Excl(c.clone()),
                }),
                Contract::Greater(c) => Some(Interval {
                    low: Bound::Unbounded,
                    high: Bound::Incl(c.clone()),
                }),
                _ => None,
            };
            if let Some(complement) = complement {
                x.iv = meet(x.iv, complement);
            }
            snap_to_lattice(x)
        }
        _ => return None,
    })
}

/// A numeric contract denoting exactly one value — `Equals(v)` or the `Range(v, v)` the
/// spec says normalizes to it (that normalization is not enforced at construction, so both
/// spellings reach here).
fn as_point(c: &Contract) -> Option<Rational> {
    match c {
        Contract::Equals(v) => v.as_number().cloned(),
        Contract::Range(l, h) if l == h => Some(l.clone()),
        _ => None,
    }
}

/// **Grid alignment.** An exclusive bound on an integer lattice snaps to the next lattice
/// point and becomes inclusive: over the integers, `> -1` *is* `≥ 0`. Without this the
/// interval and congruence facets disagree — the interval says "above −1", the lattice says
/// "an integer" — and their conjunction cannot be recognised as `≥ 0`. (Same idea as
/// grounding's landing/grid step, applied to the abstraction rather than to a descent.)
fn snap_to_lattice(mut a: NumAbs) -> NumAbs {
    let Some(c) = a.cong.clone().filter(|c| !c.n.is_zero()) else {
        return a;
    };
    if let Bound::Excl(q) = &a.iv.low
        && let Some(next) = next_on_lattice(q, &c, true)
    {
        a.iv.low = Bound::Incl(next);
    }
    if let Bound::Excl(q) = &a.iv.high
        && let Some(prev) = next_on_lattice(q, &c, false)
    {
        a.iv.high = Bound::Incl(prev);
    }
    a
}

/// The nearest lattice member strictly above (`up`) or below `q`, when `q` is an integer.
fn next_on_lattice(q: &Rational, c: &Congruence, up: bool) -> Option<Rational> {
    if !q.is_integer() {
        return None;
    }
    let qi = q.as_ratio().numer().clone();
    let step = if up {
        BigInt::from(1)
    } else {
        BigInt::from(-1)
    };
    let mut v = &qi + &step;
    // At most `n` steps to the next residue-matching integer.
    for _ in 0..c.n.to_u32_digits().1.first().copied().unwrap_or(1).max(1) {
        if (&v - &c.r).mod_floor(&c.n).is_zero() {
            return Some(Rational::from_integer(v));
        }
        v += &step;
    }
    None
}

/// The hull (union) of two intervals: lowest low, highest high.
pub(crate) fn hull(a: Interval, b: Interval) -> Interval {
    let low = if low_ge(&a.low, &b.low) { b.low } else { a.low };
    let high = if high_le(&a.high, &b.high) {
        b.high
    } else {
        a.high
    };
    Interval { low, high }
}

/// Render a [`NumAbs`] back into the contract algebra — **canonically**, so the same
/// set always yields the same syntactic form and downstream form-matching is stable:
/// `Bottom` when empty · `Equals` for a singleton · a half-line when one side is
/// unbounded · closed `Range` when both endpoints are inclusive · an `Intersection`
/// of two half-lines for genuine mixed strictness · a trailing `∧ Mod` conjunct when
/// a congruence survived · `Kind(Number)` when nothing is known.
pub(crate) fn to_contract(a: NumAbs, interner: &mut Interner) -> Contract {
    if a.iv.is_empty() {
        return Contract::Bottom;
    }
    // An exact congruence pins the value; if the interval admits it, that is the set.
    if let Some(c) = a.cong.as_ref().filter(|c| c.n.is_zero()) {
        let q = Rational::from_integer(c.r.clone());
        return Contract::Equals(interner.number(q));
    }
    let base = match (&a.iv.low, &a.iv.high) {
        (Bound::Unbounded, Bound::Unbounded) => None,
        (Bound::Incl(l), Bound::Unbounded) => Some(Contract::GreaterEq(l.clone())),
        (Bound::Excl(l), Bound::Unbounded) => Some(Contract::Greater(l.clone())),
        (Bound::Unbounded, Bound::Incl(h)) => Some(Contract::LessEq(h.clone())),
        (Bound::Unbounded, Bound::Excl(h)) => Some(Contract::Less(h.clone())),
        (lo, hi) => {
            let (l, h) = (lo.value().unwrap().clone(), hi.value().unwrap().clone());
            if lo.is_incl() && hi.is_incl() {
                if l == h {
                    return Contract::Equals(interner.number(l));
                }
                Some(Contract::Range(l, h))
            } else {
                let lo_c = if lo.is_incl() {
                    Contract::GreaterEq(l)
                } else {
                    Contract::Greater(l)
                };
                let hi_c = if hi.is_incl() {
                    Contract::LessEq(h)
                } else {
                    Contract::Less(h)
                };
                Some(Contract::intersection(lo_c, hi_c, interner))
            }
        }
    };
    let lattice = a
        .cong
        .filter(|c| !c.n.is_zero())
        .map(|c| Contract::Mod { n: c.n, r: c.r });
    match (base, lattice) {
        (None, None) => Contract::Kind(Kind::Number),
        (Some(b), None) => b,
        (None, Some(m)) => m,
        (Some(b), Some(m)) => Contract::intersection(b, m, interner),
    }
}

// ── Transfer rules (C§7) ─────────────────────────────────────────────────────

/// `[a,b] + [c,d] = [a+c, b+d]`; an endpoint is inclusive only when both are.
pub(crate) fn abs_add(x: &NumAbs, y: &NumAbs) -> NumAbs {
    NumAbs {
        iv: Interval {
            low: combine(&x.iv.low, &y.iv.low, |p, q| p + q),
            high: combine(&x.iv.high, &y.iv.high, |p, q| p + q),
        },
        cong: both(&x.cong, &y.cong, |p, q| p.add(q)),
    }
}

/// `[a,b] − [c,d] = [a−d, b−c]` — each result bound pairs with the subtrahend's
/// **opposite** bound.
pub(crate) fn abs_sub(x: &NumAbs, y: &NumAbs) -> NumAbs {
    NumAbs {
        iv: Interval {
            low: combine(&x.iv.low, &y.iv.high, |p, q| p - q),
            high: combine(&x.iv.high, &y.iv.low, |p, q| p - q),
        },
        cong: both(&x.cong, &y.cong, |p, q| p.sub(q)),
    }
}

/// `−[a,b] = [−b, −a]`.
pub(crate) fn abs_neg(x: &NumAbs) -> NumAbs {
    let flip = |b: &Bound| match b {
        Bound::Unbounded => Bound::Unbounded,
        Bound::Incl(v) => Bound::Incl(-v.clone()),
        Bound::Excl(v) => Bound::Excl(-v.clone()),
    };
    NumAbs {
        iv: Interval {
            low: flip(&x.iv.high),
            high: flip(&x.iv.low),
        },
        cong: x.cong.as_ref().map(Congruence::neg),
    }
}

/// `×` — exact corner products when every endpoint is finite; otherwise the sign
/// classes still fix one side. Computed endpoints are emitted **inclusive** (sound:
/// at most one point wider than the true image). The congruence survives only for
/// **scaling** by an exact integer (C§7).
pub(crate) fn abs_mul(x: &NumAbs, y: &NumAbs) -> NumAbs {
    let cong = match (&x.cong, &y.cong) {
        (Some(p), Some(q)) if q.n.is_zero() => Some(p.scale(&q.r)),
        (Some(p), Some(q)) if p.n.is_zero() => Some(q.scale(&p.r)),
        _ => None,
    };
    NumAbs {
        iv: mul_iv(&x.iv, &y.iv),
        cong,
    }
}

/// An endpoint under **extended arithmetic** — a finite rational or a signed
/// infinity. Deriving the ordering gives `NegInf < Fin(..) < PosInf` for free, which
/// is exactly what the corner min/max needs.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Ext {
    NegInf,
    Fin(Rational),
    PosInf,
}

fn low_ext(b: &Bound) -> Ext {
    b.value().map_or(Ext::NegInf, |v| Ext::Fin(v.clone()))
}
fn high_ext(b: &Bound) -> Ext {
    b.value().map_or(Ext::PosInf, |v| Ext::Fin(v.clone()))
}

fn sign_of(e: &Ext) -> i32 {
    let zero = Rational::from(0);
    match e {
        Ext::NegInf => -1,
        Ext::PosInf => 1,
        Ext::Fin(q) if *q > zero => 1,
        Ext::Fin(q) if *q < zero => -1,
        Ext::Fin(_) => 0,
    }
}

/// `x · y` extended. **`0 · ∞ = 0`** — sound here because a zero endpoint really is
/// attained, so the product genuinely reaches 0 (this is what makes `[0,∞) · [0,∞)`
/// come out `[0,∞)` rather than unbounded).
fn mul_ext(a: &Ext, b: &Ext) -> Ext {
    let (sa, sb) = (sign_of(a), sign_of(b));
    if sa == 0 || sb == 0 {
        return Ext::Fin(Rational::from(0));
    }
    match (a, b) {
        (Ext::Fin(x), Ext::Fin(y)) => Ext::Fin(x.clone() * y.clone()),
        _ if sa * sb > 0 => Ext::PosInf,
        _ => Ext::NegInf,
    }
}

/// `x / y` extended. `None` when the corner is genuinely indeterminate — `∞/∞`, or a
/// **zero divisor endpoint**: an interval may exclude `0` as a *value* while still
/// having it as an endpoint (`Greater(0)` is `(0, ∞)`), and quotients then run off to
/// infinity, so the caller widens to unbounded. (Precision note: this also gives up on
/// the bounded side of e.g. `[1,2] / (0,∞)`; recorded as deliberately unproven.)
fn div_ext(a: &Ext, b: &Ext) -> Option<Ext> {
    let sb = sign_of(b);
    if sb == 0 {
        return None; // zero divisor endpoint — quotients are unbounded
    }
    Some(match (a, b) {
        (Ext::Fin(x), Ext::Fin(y)) => Ext::Fin(x.clone() / y.clone()),
        // finite / ±∞ → 0
        (Ext::Fin(_), _) => Ext::Fin(Rational::from(0)),
        // ±∞ / finite keeps or flips sign
        (Ext::PosInf, Ext::Fin(_)) => {
            if sb > 0 {
                Ext::PosInf
            } else {
                Ext::NegInf
            }
        }
        (Ext::NegInf, Ext::Fin(_)) => {
            if sb > 0 {
                Ext::NegInf
            } else {
                Ext::PosInf
            }
        }
        _ => return None, // ∞/∞
    })
}

/// Build an interval from extended corner results. A finite endpoint is emitted
/// **inclusive** — sound (at most one point wider than the true image); recovering
/// exact strictness through `×`/`/` is deliberately not attempted.
fn from_corners(corners: &[Ext]) -> Interval {
    let lo = corners.iter().min().unwrap();
    let hi = corners.iter().max().unwrap();
    let bound = |e: &Ext, unbounded_side: bool| match e {
        Ext::Fin(q) => Bound::Incl(q.clone()),
        _ => {
            let _ = unbounded_side;
            Bound::Unbounded
        }
    };
    Interval {
        low: bound(lo, true),
        high: bound(hi, false),
    }
}

/// The four corner products under extended arithmetic — total, and exact on the
/// bounded case (no sign-class special-casing needed: the signs fall out).
fn mul_iv(a: &Interval, b: &Interval) -> Interval {
    let (al, ah) = (low_ext(&a.low), high_ext(&a.high));
    let (bl, bh) = (low_ext(&b.low), high_ext(&b.high));
    let corners = [
        mul_ext(&al, &bl),
        mul_ext(&al, &bh),
        mul_ext(&ah, &bl),
        mul_ext(&ah, &bh),
    ];
    from_corners(&corners)
}

/// `/` — the numeric part of the image. A divisor that may be zero has no bound (the
/// caller adds the operation's Indeterminate form; division itself is total).
pub(crate) fn abs_div(x: &NumAbs, y: &NumAbs) -> NumAbs {
    if contains_zero(&y.iv) {
        return NumAbs::of(Interval::unbounded());
    }
    let (al, ah) = (low_ext(&x.iv.low), high_ext(&x.iv.high));
    let (bl, bh) = (low_ext(&y.iv.low), high_ext(&y.iv.high));
    let corners: Option<Vec<Ext>> = [(&al, &bl), (&al, &bh), (&ah, &bl), (&ah, &bh)]
        .iter()
        .map(|(p, q)| div_ext(p, q))
        .collect();
    match corners {
        Some(cs) => NumAbs::of(from_corners(&cs)),
        None => NumAbs::of(Interval::unbounded()), // ∞/∞ — genuinely indeterminate
    }
}

/// `%` — `|r| < |y|` with the **sign following the dividend** (truncation toward
/// zero, matching the oracle's `eval_rem`).
pub(crate) fn abs_rem(x: &NumAbs, y: &NumAbs) -> NumAbs {
    let zero = Rational::from(0);
    let bound = max_abs(&y.iv);
    let (lo, hi) = match sign_class(&x.iv) {
        SignClass::NonNeg => (
            Bound::Incl(zero),
            bound.map(Bound::Excl).unwrap_or(Bound::Unbounded),
        ),
        SignClass::NonPos => (
            bound.map(|q| Bound::Excl(-q)).unwrap_or(Bound::Unbounded),
            Bound::Incl(zero),
        ),
        SignClass::Unknown => (
            bound
                .clone()
                .map(|q| Bound::Excl(-q))
                .unwrap_or(Bound::Unbounded),
            bound.map(Bound::Excl).unwrap_or(Bound::Unbounded),
        ),
    };
    NumAbs::of(Interval { low: lo, high: hi })
}

/// The largest `|v|` over an interval, when both endpoints are finite.
fn max_abs(iv: &Interval) -> Option<Rational> {
    let (l, h) = (iv.low.value()?, iv.high.value()?);
    let (la, ha) = (abs_rat(l), abs_rat(h));
    Some(if la > ha { la } else { ha })
}

fn abs_rat(v: &Rational) -> Rational {
    if *v < Rational::from(0) {
        -v.clone()
    } else {
        v.clone()
    }
}

/// `**` — sign facts only (the exact image needs the exponent, which the singleton
/// fast path already folds). A non-negative base, or an even exact exponent, gives a
/// non-negative result.
pub(crate) fn abs_pow(x: &NumAbs, y: &NumAbs) -> NumAbs {
    let zero = Rational::from(0);
    let even_exponent = y
        .cong
        .as_ref()
        .is_some_and(|c| c.n.is_zero() && (&c.r % BigInt::from(2)).is_zero());
    if sign_class(&x.iv) == SignClass::NonNeg || even_exponent {
        return NumAbs::of(Interval {
            low: Bound::Incl(zero),
            high: Bound::Unbounded,
        });
    }
    NumAbs::of(Interval::unbounded())
}

/// Whether the operands' bounds **settle** an ordering comparison: `Some(true)` when
/// it holds for every pair, `Some(false)` when it holds for none, `None` when the
/// ranges overlap so both outcomes are live. This is the precise image of the
/// comparison, and it is what lets a tested seat / guard resolve.
pub(crate) fn compare_decided(op: PrimOp, x: &NumAbs, y: &NumAbs) -> Option<bool> {
    // `x < y` for **all** pairs iff x's high is below y's low.
    let always_lt = below(&x.iv.high, &y.iv.low);
    let always_gt = below(&y.iv.high, &x.iv.low);
    // `x <= y` for all pairs iff x's high never exceeds y's low.
    let always_le = always_lt || touching(&x.iv.high, &y.iv.low);
    let always_ge = always_gt || touching(&y.iv.high, &x.iv.low);
    match op {
        PrimOp::Lt if always_lt => Some(true),
        PrimOp::Lt if always_ge => Some(false),
        PrimOp::Le if always_le => Some(true),
        PrimOp::Le if always_gt => Some(false),
        PrimOp::Gt if always_gt => Some(true),
        PrimOp::Gt if always_le => Some(false),
        PrimOp::Ge if always_ge => Some(true),
        PrimOp::Ge if always_lt => Some(false),
        _ => None,
    }
}

/// The two bounds meet at one shared, mutually-included point (so `≤` holds
/// everywhere while `<` does not).
fn touching(high: &Bound, low: &Bound) -> bool {
    match (high.value(), low.value()) {
        (Some(h), Some(l)) => h == l && high.is_incl() && low.is_incl(),
        _ => false,
    }
}

/// Combine two bounds pointwise; unbounded on either side stays unbounded, and an
/// endpoint is inclusive only when **both** contributing endpoints are.
fn combine(a: &Bound, b: &Bound, f: impl Fn(Rational, Rational) -> Rational) -> Bound {
    match (a.value(), b.value()) {
        (Some(p), Some(q)) => {
            let v = f(p.clone(), q.clone());
            if a.is_incl() && b.is_incl() {
                Bound::Incl(v)
            } else {
                Bound::Excl(v)
            }
        }
        _ => Bound::Unbounded,
    }
}

fn both(
    a: &Option<Congruence>,
    b: &Option<Congruence>,
    f: impl Fn(&Congruence, &Congruence) -> Congruence,
) -> Option<Congruence> {
    match (a, b) {
        (Some(p), Some(q)) => Some(f(p, q)),
        _ => None,
    }
}

/// The interval **exactly denoting** `c`, or `None` when this form's extent cannot be
/// stated exactly as an interval. Sound for subset and disjointness testing — see the
/// module note on the direction asymmetry before reusing it for images.
pub(crate) fn interval_exact(c: &Contract) -> Option<Interval> {
    Some(match c {
        Contract::Range(lo, hi) => Interval {
            low: Bound::Incl(lo.clone()),
            high: Bound::Incl(hi.clone()),
        },
        Contract::Greater(m) => Interval {
            low: Bound::Excl(m.clone()),
            high: Bound::Unbounded,
        },
        Contract::GreaterEq(m) => Interval {
            low: Bound::Incl(m.clone()),
            high: Bound::Unbounded,
        },
        Contract::Less(m) => Interval {
            low: Bound::Unbounded,
            high: Bound::Excl(m.clone()),
        },
        Contract::LessEq(m) => Interval {
            low: Bound::Unbounded,
            high: Bound::Incl(m.clone()),
        },
        // Landing zones: an intersection of intervals is their meet (C§4).
        Contract::Intersection(a, b) => meet(interval_exact(a)?, interval_exact(b)?),
        _ => return None,
    })
}

/// The meet (intersection) of two intervals: highest low, lowest high.
pub(crate) fn meet(a: Interval, b: Interval) -> Interval {
    let low = if low_ge(&a.low, &b.low) { a.low } else { b.low };
    let high = if high_le(&a.high, &b.high) {
        a.high
    } else {
        b.high
    };
    Interval { low, high }
}

/// `A ⊆ B` for intervals: A's low is no lower than B's, and A's high no higher.
pub(crate) fn interval_subset(a: &Interval, b: &Interval) -> bool {
    low_ge(&a.low, &b.low) && high_le(&a.high, &b.high)
}

/// Disjoint iff one interval lies entirely below the other.
pub(crate) fn intervals_disjoint(a: &Interval, b: &Interval) -> bool {
    below(&a.high, &b.low) || below(&b.high, &a.low)
}

/// A's lower bound starts at or above B's lower bound.
pub(crate) fn low_ge(a: &Bound, b: &Bound) -> bool {
    match (a, b) {
        (_, Bound::Unbounded) => true,  // B extends infinitely down
        (Bound::Unbounded, _) => false, // A extends below B
        (a, b) => {
            let (va, sa) = bound_parts(a);
            let (vb, sb) = bound_parts(b);
            // ok iff A's lowest allowed value ≥ B's lowest allowed value.
            va > vb || (va == vb && (sa || !sb)) // equal: bad only if A inclusive & B exclusive
        }
    }
}

/// A's upper bound ends at or below B's upper bound.
pub(crate) fn high_le(a: &Bound, b: &Bound) -> bool {
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

/// Whether `high` lies strictly below `low` (a gap, so no value sits between them).
pub(crate) fn below(high: &Bound, low: &Bound) -> bool {
    match (high, low) {
        (Bound::Unbounded, _) | (_, Bound::Unbounded) => false,
        (h, l) => {
            let (vh, sh) = bound_parts(h);
            let (vl, sl) = bound_parts(l);
            vh < vl || (vh == vl && (sh || sl)) // touching point excluded by either side
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
