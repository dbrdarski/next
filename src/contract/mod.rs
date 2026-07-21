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

mod expr;
pub mod length;
mod operation;
pub mod recursive;
mod subcontract;
pub use expr::{ContractEnv, build_contract_env, eval_contract};
pub use length::{Len, Stamp, len};
pub use operation::{OpResult, OpSafety, analyze_operation};
pub use recursive::{DefError, Emptiness, RecGroup, admissible};
pub use subcontract::{Verdict, subcontract};

/// Whether two contracts are provably disjoint (`⟦a⟧ ∩ ⟦b⟧ = ∅`) — sound, so
/// `true` only when provable. Used by the analyzer's access demands (E6).
pub fn disjoint(a: &Contract, b: &Contract) -> bool {
    subcontract::disjoint(a, b)
}

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
    /// **Tuple concatenation** — a tuple that splits into consecutive segments,
    /// each satisfying its segment contract (tuple-length family §1). Positive in
    /// every segment. `Concat()` denotes the empty tuple; normal forms flatten
    /// nested Concats, erase the empty-tuple segment, and Bottom-normalize when any
    /// segment is uninhabited (erasing an uninhabited segment would turn an empty
    /// contract into an inhabited one).
    Concat(Vec<Contract>),
    /// An Indeterminate value of a given form.
    Indeterminate(crate::value::IndetForm),
    /// A late-bound reference to a named contract in the ambient recursive group
    /// (C§9). Meaningful only relative to a [`recursive::RecGroup`]; bare, it
    /// denotes nothing (`contains` is `false`) — recursive code resolves it first.
    Ref(String),
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
    /// Smart constructor for [`Contract::Concat`], applying the family's normal
    /// forms (§1): nested Concats flatten associatively; the canonical empty-tuple
    /// segment **erases** (a structural fact); an **uninhabited segment never
    /// erases** — it Bottom-normalizes the whole Concat, since erasing it would
    /// turn an empty contract into an inhabited one; adjacent exact segments fuse.
    ///
    /// Uninhabitance here uses only *permanent* structural facts, never temporary
    /// analysis state (family §1; RC §6 supplies the productivity verdicts).
    pub fn concat(segments: impl IntoIterator<Item = Contract>) -> Contract {
        // Flatten associatively.
        let mut flat: Vec<Contract> = Vec::new();
        for s in segments {
            match s {
                Contract::Concat(inner) => flat.extend(inner),
                other => flat.push(other),
            }
        }
        // An uninhabited segment empties the whole concatenation.
        if flat.iter().any(structurally_uninhabited) {
            return Contract::Bottom;
        }
        // Erase empty-tuple segments.
        flat.retain(|s| !matches!(s, Contract::Tuple(e) if e.is_empty()));

        // Fuse adjacent exact segments.
        let mut out: Vec<Contract> = Vec::with_capacity(flat.len());
        for s in flat {
            let fused = match (out.last_mut(), s) {
                (Some(Contract::Tuple(prev)), Contract::Tuple(cur)) => {
                    prev.extend(cur);
                    None
                }
                (_, s) => Some(s),
            };
            if let Some(s) = fused {
                out.push(s);
            }
        }
        match out.len() {
            0 => Contract::Tuple(vec![]), // the empty tuple
            1 => out.pop().expect("length 1"),
            _ => Contract::Concat(out),
        }
    }

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
            Contract::Concat(segs) => match v.as_tuple() {
                Some(items) => concat_matches(segs, items),
                None => false,
            },
            Contract::Indeterminate(f) => v.as_indeterminate() == Some(*f),
            // A bare reference has no ambient group to resolve against; recursive
            // membership goes through `recursive::contains`.
            Contract::Ref(_) => false,
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

/// Whether `items` splits into consecutive windows satisfying `segs` in order.
///
/// A segment with a **proven exact arity** consumes exactly that many positions;
/// anything else is variable and is searched over. The search is a straightforward
/// backtrack — the denotational reference, not the analyzer's alignment procedure
/// (tuple-family §4), which decides the *contract* question without enumerating.
fn concat_matches(segs: &[Contract], items: &[ValueRef]) -> bool {
    match segs.split_first() {
        None => items.is_empty(),
        Some((first, rest)) => {
            // A fixed-arity segment admits exactly one split; otherwise try each.
            if let Some(k) = exact_arity(first) {
                return k <= items.len()
                    && first.contains_tuple_window(&items[..k])
                    && concat_matches(rest, &items[k..]);
            }
            (0..=items.len()).any(|k| {
                first.contains_tuple_window(&items[..k]) && concat_matches(rest, &items[k..])
            })
        }
    }
}

/// Uninhabited by **structure alone** — sound and permanent, so it is safe for the
/// Concat normal form (which may not consult temporary analysis state).
fn structurally_uninhabited(c: &Contract) -> bool {
    match c {
        Contract::Bottom => true,
        Contract::Range(lo, hi) => lo > hi,
        Contract::Tuple(elems) => elems.iter().any(structurally_uninhabited),
        Contract::Concat(segs) => segs.iter().any(structurally_uninhabited),
        Contract::Record(fields) => fields.iter().any(|(_, c)| structurally_uninhabited(c)),
        Contract::Union(a, b) => structurally_uninhabited(a) && structurally_uninhabited(b),
        Contract::Intersection(a, b) => {
            structurally_uninhabited(a) || structurally_uninhabited(b)
        }
        _ => false,
    }
}

/// A proven lower bound on the tuple length a contract admits, from **segment-local
/// structure only** — exact-tuple arities and non-recursive minima, never the
/// productivity of a group under admission (the family's non-circularity clause,
/// §1). A reference contributes `0`, so the bound stays valid.
pub(crate) fn min_extent(c: &Contract) -> usize {
    match c {
        Contract::Tuple(elems) => elems.len(),
        Contract::Concat(segs) => segs.iter().map(min_extent).sum(),
        Contract::Union(a, b) => min_extent(a).min(min_extent(b)),
        Contract::Intersection(a, b) => min_extent(a).max(min_extent(b)),
        Contract::Equals(v) => v.as_tuple().map(|t| t.len()).unwrap_or(0),
        _ => 0,
    }
}

/// The arity a segment always consumes, when that is structurally fixed.
fn exact_arity(c: &Contract) -> Option<usize> {
    match c {
        Contract::Tuple(elems) => Some(elems.len()),
        Contract::Concat(segs) => segs.iter().map(exact_arity).sum::<Option<usize>>(),
        _ => None,
    }
}

impl Contract {
    /// Whether the tuple formed from `window` satisfies this contract. Segments are
    /// contracts over *tuples*, so a window is re-wrapped before testing.
    fn contains_tuple_window(&self, window: &[ValueRef]) -> bool {
        match self {
            Contract::Tuple(elems) => {
                elems.len() == window.len()
                    && elems.iter().zip(window).all(|(c, v)| c.contains(v))
            }
            Contract::Concat(segs) => concat_matches(segs, window),
            Contract::Union(a, b) => {
                a.contains_tuple_window(window) || b.contains_tuple_window(window)
            }
            Contract::Intersection(a, b) => {
                a.contains_tuple_window(window) && b.contains_tuple_window(window)
            }
            Contract::Difference(base, ex) => {
                base.contains_tuple_window(window) && !ex.contains_tuple_window(window)
            }
            Contract::Top => true,
            Contract::Bottom => false,
            Contract::Kind(Kind::Tuple) => true,
            // Any other contract can only admit a window by naming the tuple value
            // itself; `contains` decides that once the window is materialized.
            _ => false,
        }
    }
}

fn tuple_contains(v: &ValueRef, elems: &[Contract]) -> bool {
    let Some(items) = v.as_tuple() else { return false };
    items.len() == elems.len() && items.iter().zip(elems).all(|(item, c)| c.contains(item))
}
