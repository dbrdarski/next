//! Contracts — the algebra of value properties (Compendium C§4) and their
//! denotational membership (C§16: `⟦C⟧ ⊆ Values`).
//!
//! A `Contract` denotes a set of values; [`Contract::contains`] decides whether a
//! concrete value is in that set. This membership is the **denotational kernel**
//! the whole analyzer is grounded on and tested against — per Part I, every
//! contract rule is brute-tested against the oracle's values. Membership is
//! decidable for every constructor here; **named recursive contracts (C§9) are
//! owed** and not yet represented.
//!
//! This is analysis-layer code — legitimate now that the oracle + normalization
//! harness are green (CLAUDE.md hard rule 1).

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Zero;

use crate::oracle::values_equal;
use crate::rational::Rational;
use crate::value::{ValueData, ValueRef};

#[cfg(test)]
mod tests;

/// The seven value kinds a `Kind` contract can name (C§4). Indeterminate values
/// are matched by [`Contract::Indeterminate`], not by a `Kind`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    Number,
    String,
    Boolean,
    Null,
    Function,
    Tuple,
    Record,
}

/// A contract — a bounded algebraic property of values (C§4).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Contract {
    /// All values.
    Top,
    /// No values (empty intersections normalize here).
    Bottom,
    /// Values of a given kind.
    Kind(Kind),
    /// Exactly one value (`Equals(v)`); `NotEquals(v) ≡ Difference(Top, Equals(v))`.
    Equals(ValueRef),
    /// A closed numeric interval `[min, max]`; `Range(v, v)` means `Equals(v)`.
    Range(Rational, Rational),
    /// Strict/loose numeric bounds.
    Greater(Rational),
    GreaterEq(Rational),
    Less(Rational),
    LessEq(Rational),
    /// Integers `x` with `x ≡ r (mod n)` (rational moduli clear to integer
    /// lattices — C§3.1); `n > 0`.
    Mod { n: BigInt, r: BigInt },
    /// The geometric sequence `b, b·r, b·r², …` (`r > 1`, `b ≠ 0`; `Geo(0, r)`
    /// normalizes to `Equals(0)`).
    Geo { b: Rational, r: Rational },
    /// Union / Intersection / Difference (the sole negative form, C§6).
    Union(Box<Contract>, Box<Contract>),
    Intersection(Box<Contract>, Box<Contract>),
    Difference(Box<Contract>, Box<Contract>),
    /// A record having **exactly** the named fields (no others), each satisfying
    /// its contract (exact — matching exact-by-default patterns, E9). The open
    /// "has at least this field" case is [`HasField`].
    Record(Vec<(String, Contract)>),
    /// A record having a given field (any value) — the open partial form.
    HasField(String),
    /// A tuple of exactly these element contracts, positionally.
    Tuple(Vec<Contract>),
    /// An Indeterminate value of a given form.
    Indeterminate(crate::value::IndetForm),
}

/// The kind of a value, or `None` for an Indeterminate value.
fn value_kind(v: &ValueRef) -> Option<Kind> {
    Some(match v.data() {
        ValueData::Number(_) => Kind::Number,
        ValueData::Str(_) => Kind::String,
        ValueData::Boolean(_) => Kind::Boolean,
        ValueData::Null => Kind::Null,
        ValueData::Function(_) | ValueData::Native(_) => Kind::Function,
        ValueData::Tuple(_) => Kind::Tuple,
        ValueData::Record(_) => Kind::Record,
        ValueData::Indeterminate(_) => return None,
    })
}

impl Contract {
    /// Denotational membership (C§16): whether `v ∈ ⟦self⟧`.
    pub fn contains(&self, v: &ValueRef) -> bool {
        match self {
            Contract::Top => true,
            Contract::Bottom => false,
            Contract::Kind(k) => value_kind(v) == Some(*k),
            Contract::Equals(x) => values_equal(v, x),
            Contract::Range(lo, hi) => num(v).is_some_and(|n| lo <= n && n <= hi),
            Contract::Greater(m) => num(v).is_some_and(|n| n > m),
            Contract::GreaterEq(m) => num(v).is_some_and(|n| n >= m),
            Contract::Less(m) => num(v).is_some_and(|n| n < m),
            Contract::LessEq(m) => num(v).is_some_and(|n| n <= m),
            Contract::Mod { n, r } => in_mod(v, n, r),
            Contract::Geo { b, r } => in_geo(v, b, r),
            Contract::Union(a, b) => a.contains(v) || b.contains(v),
            Contract::Intersection(a, b) => a.contains(v) && b.contains(v),
            Contract::Difference(base, ex) => base.contains(v) && !ex.contains(v),
            Contract::Record(fields) => record_contains(v, fields),
            Contract::HasField(key) => has_field(v, key),
            Contract::Tuple(elems) => tuple_contains(v, elems),
            Contract::Indeterminate(f) => v.as_indeterminate() == Some(*f),
        }
    }
}

fn num(v: &ValueRef) -> Option<&Rational> {
    v.as_number()
}

fn in_mod(v: &ValueRef, n: &BigInt, r: &BigInt) -> bool {
    let Some(x) = num(v) else { return false };
    if !x.is_integer() || n.is_zero() {
        return false;
    }
    let numer = x.as_ratio().numer();
    (numer - r).mod_floor(n).is_zero()
}

fn in_geo(v: &ValueRef, b: &Rational, r: &Rational) -> bool {
    let Some(x) = num(v) else { return false };
    // Solve x = b·r^k for some integer k ≥ 0. With r > 1, dividing by r strictly
    // shrinks |q|, so the search terminates.
    let one = Rational::from(1);
    if r <= &one || b.is_zero() {
        return false; // ill-formed Geo (normalized away by construction)
    }
    let mut q = x.clone() / b.clone(); // q must equal r^k ≥ 1
    if q < one {
        return false;
    }
    loop {
        if q == one {
            return true;
        }
        q = q / r.clone();
        if q < one {
            return false;
        }
    }
}

fn has_field(v: &ValueRef, key: &str) -> bool {
    let Some(entries) = v.as_record() else { return false };
    let ku: Vec<u16> = key.encode_utf16().collect();
    entries.iter().any(|e| e.key == ku)
}

fn record_contains(v: &ValueRef, fields: &[(String, Contract)]) -> bool {
    let Some(entries) = v.as_record() else { return false };
    // Exact: the record's key set equals the contract's, and each field's value
    // satisfies its contract. Keys are unique on both sides, so equal counts plus
    // all-fields-present ⇒ equal key sets (no un-listed fields).
    entries.len() == fields.len()
        && fields.iter().all(|(key, contract)| {
            let ku: Vec<u16> = key.encode_utf16().collect();
            match entries.iter().find(|e| e.key == ku) {
                Some(e) => contract.contains(&e.value),
                None => false,
            }
        })
}

fn tuple_contains(v: &ValueRef, elems: &[Contract]) -> bool {
    let Some(items) = v.as_tuple() else { return false };
    items.len() == elems.len() && items.iter().zip(elems).all(|(item, c)| c.contains(item))
}
