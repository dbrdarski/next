//! Recursive contracts — the C§9 package (spec v0.2).
//!
//! A recursive contract is an ordinary named binding mentioning itself or its
//! mutual group ([`RecGroup`]); references are [`Contract::Ref`]. Four subsystems,
//! each grounded on the finite canonical graph (never a materialized unfolding):
//!
//! 1. **Admissibility** ([`admissible`], §1): positivity (no recursion through a
//!    negative `Difference` exclusion) + structural guardedness (every reference
//!    cycle crosses a `Tuple`/`Record` constructor). Violations are *definition
//!    errors* — `Bad = Difference(Top, Bad)` and `R = R` / `R = Union(Number, R)`
//!    are rejected.
//! 2. **Membership** ([`contains`], §3): inductive, over finite acyclic values —
//!    references resolve to their group definitions and the value strictly shrinks
//!    at each structural descent, so it terminates on admissible groups.
//! 3. **Emptiness** ([`emptiness`], §6): a monotone *productivity* closure over the
//!    group's finite state space — each state flips at most once (no iteration
//!    budget). Productive ⇒ non-empty *with a witness*; unproductive with every
//!    reachable leaf exact ⇒ empty; a dependence on an opaque leaf ⇒ unproven.
//! 4. **Subcontract** ([`subcontract`], §5): progress-guarded pair induction — a
//!    revisited pair closes as *holds* only at strictly greater source depth
//!    (per-hypothesis, depth-stamped; a global progress flag is non-conforming).
//!    Empty sources short-circuit to proven; leaf pairs delegate to the C.2 check.
//!
//! Every witness produced anywhere here is a finite concrete value (C§16).

use std::collections::{BTreeMap, HashMap, HashSet};

use super::{Contract, Kind, Verdict};
use crate::interner::Interner;
use crate::rational::Rational;
use crate::value::ValueRef;

/// A mutual group of named contracts. `Ref(name)` within a definition resolves
/// against `defs`.
#[derive(Clone, Debug)]
pub struct RecGroup {
    pub defs: BTreeMap<String, Contract>,
}

impl RecGroup {
    pub fn new(defs: impl IntoIterator<Item = (String, Contract)>) -> RecGroup {
        RecGroup { defs: defs.into_iter().collect() }
    }

    fn get(&self, name: &str) -> &Contract {
        self.defs.get(name).expect("reference to a name outside its group")
    }

    fn is_member(&self, name: &str) -> bool {
        self.defs.contains_key(name)
    }
}

// ── 1. Admissibility (§1) ─────────────────────────────────────────────────────

/// A definition error — the contract group does not denote a least fixpoint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefError {
    /// A recursive reference occurs at negative polarity (under a `Difference`
    /// exclusion) — the operator is antitone and no least fixpoint exists.
    NegativeOccurrence { name: String },
    /// A reference cycle crosses no `Tuple`/`Record` constructor — inclusion
    /// induction is not well-founded. `hint` carries the spec's rewrite advice.
    Unguarded { name: String, hint: String },
}

/// Check both admissibility laws over the whole group.
pub fn admissible(group: &RecGroup) -> Result<(), DefError> {
    for def in group.defs.values() {
        check_positive(group, def, true)?;
    }
    check_guarded(group)?;
    Ok(())
}

/// (a) Positivity: a group reference may not appear at negative polarity.
fn check_positive(group: &RecGroup, c: &Contract, positive: bool) -> Result<(), DefError> {
    match c {
        Contract::Ref(name) if group.is_member(name) => {
            if positive {
                Ok(())
            } else {
                Err(DefError::NegativeOccurrence { name: name.clone() })
            }
        }
        Contract::Union(a, b) | Contract::Intersection(a, b) => {
            check_positive(group, a, positive)?;
            check_positive(group, b, positive)
        }
        // `Difference(B, E)`: positive in B, negative in E.
        Contract::Difference(b, e) => {
            check_positive(group, b, positive)?;
            check_positive(group, e, !positive)
        }
        Contract::Tuple(elems) => {
            elems.iter().try_for_each(|e| check_positive(group, e, positive))
        }
        Contract::Record(fields) => {
            fields.iter().try_for_each(|(_, e)| check_positive(group, e, positive))
        }
        // `Concat` is positive in every segment (declared by the tuple family per
        // §1a's future-constructor rule).
        Contract::Concat(segs) => {
            segs.iter().try_for_each(|s| check_positive(group, s, positive))
        }
        _ => Ok(()),
    }
}

/// (b) Structural guardedness: no reference cycle avoids a `Tuple`/`Record`
/// constructor. Build the unguarded-reachability graph and reject any cycle.
fn check_guarded(group: &RecGroup) -> Result<(), DefError> {
    // Unguarded successors: names reachable without crossing a structural
    // constructor (Tuple element / Record field).
    let succ: BTreeMap<&str, HashSet<String>> = group
        .defs
        .iter()
        .map(|(name, def)| {
            let mut out = HashSet::new();
            collect_unguarded(group, def, &mut out);
            (name.as_str(), out)
        })
        .collect();

    for name in group.defs.keys() {
        if reaches_self(name, &succ) {
            let hint = guardedness_hint(group, name);
            return Err(DefError::Unguarded { name: name.clone(), hint });
        }
    }
    Ok(())
}

fn collect_unguarded(group: &RecGroup, c: &Contract, out: &mut HashSet<String>) {
    match c {
        Contract::Ref(name) if group.is_member(name) => {
            out.insert(name.clone());
        }
        Contract::Union(a, b) | Contract::Intersection(a, b) => {
            collect_unguarded(group, a, out);
            collect_unguarded(group, b, out);
        }
        // Only B is reachable without a constructor; E is recursion-free (§1a).
        Contract::Difference(b, _) => collect_unguarded(group, b, out),
        // A `Concat` edge guards a segment when some *sibling* segment has a
        // permanently proven structural minimum length ≥ 1 — the traversal then
        // consumes at least one element (RC §1b, integration). The proof is
        // segment-local (`min_extent`), never the productivity of the group being
        // admitted, so it stays non-circular.
        Contract::Concat(segs) => {
            for (i, s) in segs.iter().enumerate() {
                let sibling_extent: usize = segs
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other)| super::min_extent(other))
                    .sum();
                if sibling_extent == 0 {
                    collect_unguarded(group, s, out); // nothing certainly consumed
                }
            }
        }
        // Tuple / Record are structural progress — stop; references beneath them
        // are guarded.
        _ => {}
    }
}

fn reaches_self(start: &str, succ: &BTreeMap<&str, HashSet<String>>) -> bool {
    let mut stack: Vec<&str> = succ.get(start).into_iter().flatten().map(String::as_str).collect();
    let mut seen = HashSet::new();
    while let Some(n) = stack.pop() {
        if n == start {
            return true;
        }
        if seen.insert(n) {
            stack.extend(succ.get(n).into_iter().flatten().map(String::as_str));
        }
    }
    false
}

/// Spec-mandated rewrite hints (§1b, RC-10).
fn guardedness_hint(group: &RecGroup, name: &str) -> String {
    // `R = Union(Number, R)` already denotes its non-recursive branch.
    if let Contract::Union(a, b) = group.get(name) {
        let refs_self = |c: &Contract| matches!(c, Contract::Ref(n) if n == name);
        if refs_self(a) {
            return format!("`{name}` denotes `{b:?}` — write that");
        }
        if refs_self(b) {
            return format!("`{name}` denotes `{a:?}` — write that");
        }
    }
    format!("cycle through `{name}` crosses no Tuple/Record constructor")
}

// ── 2. Membership (§3) ────────────────────────────────────────────────────────

/// Inductive membership `v ∈ ⟦c⟧` with `Ref`s resolved against `group`. Assumes
/// `group` is admissible (else may not terminate).
pub fn contains(group: &RecGroup, c: &Contract, v: &ValueRef) -> bool {
    match c {
        Contract::Ref(name) if group.is_member(name) => contains(group, group.get(name), v),
        Contract::Union(a, b) => contains(group, a, v) || contains(group, b, v),
        Contract::Intersection(a, b) => contains(group, a, v) && contains(group, b, v),
        Contract::Difference(b, e) => contains(group, b, v) && !contains(group, e, v),
        Contract::Tuple(elems) => match v.as_tuple() {
            Some(items) => {
                items.len() == elems.len()
                    && items.iter().zip(elems).all(|(item, ce)| contains(group, ce, item))
            }
            None => false,
        },
        Contract::Record(fields) => match v.as_record() {
            Some(entries) => {
                entries.len() == fields.len()
                    && fields.iter().all(|(key, ce)| {
                        let ku: Vec<u16> = key.encode_utf16().collect();
                        match entries.iter().find(|e| e.key == ku) {
                            Some(e) => contains(group, ce, &e.value),
                            None => false,
                        }
                    })
            }
            None => false,
        },
        Contract::Concat(segs) => match v.as_tuple() {
            Some(items) => concat_contains(group, segs, items),
            None => false,
        },
        // Non-recursive leaves: the ordinary denotational membership.
        _ => c.contains(v),
    }
}

/// Group-aware Concat membership: does `items` split into consecutive windows
/// satisfying `segs` in order? References resolve against the group, so a
/// recursive segment (`Repeat`) is followed. Terminates on admissible groups —
/// guardedness makes every reference cycle consume at least one element.
fn concat_contains(group: &RecGroup, segs: &[Contract], items: &[ValueRef]) -> bool {
    match segs.split_first() {
        None => items.is_empty(),
        Some((first, rest)) => (0..=items.len()).any(|k| {
            window_contains(group, first, &items[..k]) && concat_contains(group, rest, &items[k..])
        }),
    }
}

/// Whether the tuple formed from `window` satisfies `c`, resolving group
/// references. Structural, so no interner is needed to materialize the window.
fn window_contains(group: &RecGroup, c: &Contract, window: &[ValueRef]) -> bool {
    match c {
        Contract::Ref(name) if group.is_member(name) => {
            window_contains(group, group.get(name), window)
        }
        Contract::Tuple(elems) => {
            elems.len() == window.len()
                && elems.iter().zip(window).all(|(e, v)| contains(group, e, v))
        }
        Contract::Concat(segs) => concat_contains(group, segs, window),
        Contract::Union(a, b) => {
            window_contains(group, a, window) || window_contains(group, b, window)
        }
        Contract::Intersection(a, b) => {
            window_contains(group, a, window) && window_contains(group, b, window)
        }
        Contract::Difference(b, e) => {
            window_contains(group, b, window) && !window_contains(group, e, window)
        }
        Contract::Top | Contract::Kind(Kind::Tuple) => true,
        _ => false,
    }
}

// ── 3. Emptiness (§6) — bounded productivity closure ──────────────────────────

/// Three-voiced emptiness verdict (C§16 witness discipline).
#[derive(Clone, Debug)]
pub enum Emptiness {
    Empty,
    NonEmpty(ValueRef),
    Unproven,
}

/// Exactness voice used internally while propagating.
#[derive(Clone, Copy, PartialEq, Eq)]
enum E3 {
    Empty,
    NonEmpty,
    Unproven,
}

/// The productivity/exactness environment for a group (computed once).
struct EmptyEnv {
    /// `Some(witness)` ⇔ the name is *productive* (non-empty).
    productive: BTreeMap<String, Option<ValueRef>>,
    /// For unproductive names: `Empty` or `Unproven`.
    verdict: BTreeMap<String, E3>,
}

impl EmptyEnv {
    fn analyze(group: &RecGroup, interner: &mut Interner) -> EmptyEnv {
        let productive = productivity(group, interner);
        let verdict = exactness(group, &productive, interner);
        EmptyEnv { productive, verdict }
    }

    /// The emptiness voice of an arbitrary contract under this environment.
    fn voice(&self, group: &RecGroup, c: &Contract, interner: &mut Interner) -> E3 {
        exact_eval(group, c, &self.productive, &self.verdict, interner)
    }
}

/// Least-fixpoint productivity: each state flips to `Some(witness)` at most once.
fn productivity(group: &RecGroup, interner: &mut Interner) -> BTreeMap<String, Option<ValueRef>> {
    let mut states: BTreeMap<String, Option<ValueRef>> =
        group.defs.keys().map(|n| (n.clone(), None)).collect();

    loop {
        let mut changed = false;
        let names: Vec<String> = states.iter().filter(|(_, s)| s.is_none()).map(|(n, _)| n.clone()).collect();
        for name in names {
            let def = group.get(&name).clone();
            if let Some(w) = prod_eval(group, &def, &states, interner) {
                states.insert(name, Some(w));
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    states
}

/// A productive witness for `c` this round, or `None` if not yet productive.
fn prod_eval(
    group: &RecGroup,
    c: &Contract,
    states: &BTreeMap<String, Option<ValueRef>>,
    interner: &mut Interner,
) -> Option<ValueRef> {
    match c {
        Contract::Ref(name) if group.is_member(name) => states.get(name).cloned().flatten(),
        Contract::Top => Some(interner.null()),
        Contract::Bottom => None,
        Contract::Kind(k) => kind_witness(*k, interner),
        Contract::Equals(v) => Some(v.clone()),
        Contract::Range(lo, hi) => (lo <= hi).then(|| interner.number(lo.clone())),
        Contract::Greater(m) => Some(interner.number(m.clone() + Rational::from(1))),
        Contract::GreaterEq(m) => Some(interner.number(m.clone())),
        Contract::Less(m) => Some(interner.number(m.clone() - Rational::from(1))),
        Contract::LessEq(m) => Some(interner.number(m.clone())),
        Contract::Mod { r, .. } => Some(interner.number(Rational::from_integer(r.clone()))),
        Contract::Geo { b, .. } => Some(interner.number(b.clone())),
        Contract::Indeterminate(f) => Some(interner.indeterminate(*f)),
        Contract::HasField(key) => {
            let val = interner.integer(0);
            Some(interner.record_str(vec![(key.as_str(), val)]))
        }
        Contract::Union(a, b) => {
            prod_eval(group, a, states, interner).or_else(|| prod_eval(group, b, states, interner))
        }
        Contract::Intersection(a, b) => {
            // Non-emptiness of a recursive intersection = productivity over the
            // finite product graph (§6). A `NonEmpty` verdict carries a witness.
            match intersection_emptiness(group, a, b, interner) {
                Emptiness::NonEmpty(w) => Some(w),
                _ => None,
            }
        }
        Contract::Difference(b, e) => match prod_eval(group, b, states, interner) {
            Some(w) if !contains(group, e, &w) => Some(w),
            _ => None,
        },
        // Every segment is required, so a Concat is productive exactly when all of
        // them are; the witness is their concatenation. An uninhabited segment
        // therefore makes the whole Concat empty (it never erases — family §1).
        Contract::Concat(segs) => {
            let mut items: Vec<ValueRef> = Vec::new();
            for s in segs {
                let w = prod_eval(group, s, states, interner)?;
                let part = w.as_tuple()?.to_vec();
                items.extend(part);
            }
            Some(interner.tuple(items))
        }
        Contract::Tuple(elems) => {
            let mut items = Vec::with_capacity(elems.len());
            for ce in elems {
                items.push(prod_eval(group, ce, states, interner)?);
            }
            Some(interner.tuple(items))
        }
        Contract::Record(fields) => {
            let mut pairs: Vec<(Vec<u16>, ValueRef)> = Vec::with_capacity(fields.len());
            for (key, ce) in fields {
                let w = prod_eval(group, ce, states, interner)?;
                pairs.push((key.encode_utf16().collect(), w));
            }
            Some(interner.record(pairs))
        }
        // Reference to a name outside the group — treat as opaque (no witness).
        Contract::Ref(_) => None,
    }
}

fn kind_witness(k: Kind, interner: &mut Interner) -> Option<ValueRef> {
    Some(match k {
        Kind::Number => interner.integer(0),
        Kind::String => interner.string(""),
        Kind::Boolean => interner.boolean(true),
        Kind::Null => interner.null(),
        Kind::Tuple => interner.tuple(vec![]),
        Kind::Record => interner.record_str(vec![]),
        // No constructible finite witness — opaque for productivity.
        Kind::Function => return None,
    })
}

/// For unproductive names, decide `Empty` (exact) vs `Unproven` (opaque
/// dependence). Monotone: a name only moves `Empty → Unproven`.
fn exactness(
    group: &RecGroup,
    productive: &BTreeMap<String, Option<ValueRef>>,
    interner: &mut Interner,
) -> BTreeMap<String, E3> {
    let mut verdict: BTreeMap<String, E3> = productive
        .iter()
        .map(|(n, s)| (n.clone(), if s.is_some() { E3::NonEmpty } else { E3::Empty }))
        .collect();

    loop {
        let mut changed = false;
        for name in group.defs.keys().cloned().collect::<Vec<_>>() {
            if verdict[&name] == E3::NonEmpty {
                continue;
            }
            let def = group.get(&name).clone();
            let v = exact_eval(group, &def, productive, &verdict, interner);
            if v == E3::Unproven && verdict[&name] != E3::Unproven {
                verdict.insert(name, E3::Unproven);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    verdict
}

/// The emptiness voice of `c`, reading name states/verdicts (no recursion into
/// reference bodies — references are leaves here). `Intersection` bottoms out in
/// the product-graph closure ([`intersection_emptiness`]).
fn exact_eval(
    group: &RecGroup,
    c: &Contract,
    productive: &BTreeMap<String, Option<ValueRef>>,
    verdict: &BTreeMap<String, E3>,
    interner: &mut Interner,
) -> E3 {
    match c {
        Contract::Ref(name) if group.is_member(name) => {
            if productive[name].is_some() {
                E3::NonEmpty
            } else {
                verdict[name]
            }
        }
        Contract::Bottom => E3::Empty,
        Contract::Kind(Kind::Function) => E3::Unproven, // opaque leaf
        Contract::Range(lo, hi) => {
            if lo > hi {
                E3::Empty
            } else {
                E3::NonEmpty
            }
        }
        Contract::Union(a, b) => {
            let va = exact_eval(group, a, productive, verdict, interner);
            let vb = exact_eval(group, b, productive, verdict, interner);
            join_union(va, vb)
        }
        Contract::Intersection(a, b) => match intersection_emptiness(group, a, b, interner) {
            Emptiness::Empty => E3::Empty,
            Emptiness::NonEmpty(_) => E3::NonEmpty,
            Emptiness::Unproven => E3::Unproven,
        },
        Contract::Difference(b, _) => {
            if exact_eval(group, b, productive, verdict, interner) == E3::Empty {
                E3::Empty
            } else {
                E3::Unproven
            }
        }
        Contract::Tuple(elems) => {
            let voices: Vec<E3> =
                elems.iter().map(|e| exact_eval(group, e, productive, verdict, interner)).collect();
            join_product(voices.into_iter())
        }
        Contract::Record(fields) => {
            let voices: Vec<E3> = fields
                .iter()
                .map(|(_, e)| exact_eval(group, e, productive, verdict, interner))
                .collect();
            join_product(voices.into_iter())
        }
        // Every remaining leaf (Top, non-Function Kind, bounds, Mod, Geo, Equals,
        // Indeterminate, HasField) is inhabited.
        _ => E3::NonEmpty,
    }
}

/// Union: `NonEmpty` if either branch is; `Empty` only if both are.
fn join_union(a: E3, b: E3) -> E3 {
    match (a, b) {
        (E3::NonEmpty, _) | (_, E3::NonEmpty) => E3::NonEmpty,
        (E3::Empty, E3::Empty) => E3::Empty,
        _ => E3::Unproven,
    }
}

/// Product (Tuple/Record): `Empty` if any component is; `NonEmpty` only if all
/// are; else `Unproven`.
fn join_product(parts: impl Iterator<Item = E3>) -> E3 {
    let mut all_nonempty = true;
    for p in parts {
        match p {
            E3::Empty => return E3::Empty,
            E3::Unproven => all_nonempty = false,
            E3::NonEmpty => {}
        }
    }
    if all_nonempty { E3::NonEmpty } else { E3::Unproven }
}

/// The emptiness verdict of every group member.
pub fn emptiness(group: &RecGroup, interner: &mut Interner) -> BTreeMap<String, Emptiness> {
    let env = EmptyEnv::analyze(group, interner);
    group
        .defs
        .keys()
        .map(|name| {
            let e = match &env.productive[name] {
                Some(w) => Emptiness::NonEmpty(w.clone()),
                None => match env.verdict[name] {
                    E3::Empty => Emptiness::Empty,
                    _ => Emptiness::Unproven,
                },
            };
            (name.clone(), e)
        })
        .collect()
}

/// Emptiness of `⟦a⟧ ∩ ⟦b⟧` as *productivity over the finite product graph* (§6,
/// RC-14). Product states are pairs `(a, b)`; a revisited pair is cut as not-yet
/// productive (the least fixpoint — an intersection inhabited only *through* a
/// cycle has no finite witness and is empty). Unions distribute, `Record`/`Tuple`
/// descend into paired components, `Equals` decides exactly by membership, and
/// leaf pairs bottom out in disjointness plus a sampled common witness.
#[allow(clippy::mutable_key_type)] // keys embed immutable interned values (stable hash/eq)
fn intersection_emptiness(group: &RecGroup, a: &Contract, b: &Contract, interner: &mut Interner) -> Emptiness {
    let mut visiting: HashSet<(Contract, Contract)> = HashSet::new();
    inter(group, a, b, &mut visiting, interner)
}

#[allow(clippy::mutable_key_type)]
fn inter(
    group: &RecGroup,
    a: &Contract,
    b: &Contract,
    visiting: &mut HashSet<(Contract, Contract)>,
    interner: &mut Interner,
) -> Emptiness {
    use Contract::*;

    // Singletons decide exactly: `Equals(v) ∩ B` is `{v}` if `v ∈ B`, else empty.
    if let Equals(v) = a {
        return if contains(group, b, v) { Emptiness::NonEmpty(v.clone()) } else { Emptiness::Empty };
    }
    if let Equals(v) = b {
        return if contains(group, a, v) { Emptiness::NonEmpty(v.clone()) } else { Emptiness::Empty };
    }

    // Reference resolution introduces a product state; cut a revisited pair.
    let is_ref = |c: &Contract| matches!(c, Ref(n) if group.is_member(n));
    if is_ref(a) || is_ref(b) {
        let key = (a.clone(), b.clone());
        if visiting.contains(&key) {
            return Emptiness::Empty; // cycle with no base case ⇒ no finite witness
        }
        visiting.insert(key.clone());
        let ra = match a {
            Ref(n) if group.is_member(n) => group.get(n),
            _ => a,
        };
        let rb = match b {
            Ref(n) if group.is_member(n) => group.get(n),
            _ => b,
        };
        let r = inter(group, ra, rb, visiting, interner);
        visiting.remove(&key);
        return r;
    }

    match (a, b) {
        // Union distributes over intersection.
        (Union(a1, a2), _) => {
            let r1 = inter(group, a1, b, visiting, interner);
            if let Emptiness::NonEmpty(w) = r1 {
                return Emptiness::NonEmpty(w);
            }
            let r2 = inter(group, a2, b, visiting, interner);
            join_empty(r1, r2)
        }
        (_, Union(b1, b2)) => {
            let r1 = inter(group, a, b1, visiting, interner);
            if let Emptiness::NonEmpty(w) = r1 {
                return Emptiness::NonEmpty(w);
            }
            let r2 = inter(group, a, b2, visiting, interner);
            join_empty(r1, r2)
        }
        // Exact records: same key set, and each paired field-intersection inhabited.
        (Record(fa), Record(fb)) => {
            if fa.len() != fb.len() {
                return Emptiness::Empty;
            }
            let mut pairs: Vec<(Vec<u16>, ValueRef)> = Vec::with_capacity(fa.len());
            let mut any_unproven = false;
            for (key, ca) in fa {
                let Some((_, cb)) = fb.iter().find(|(k, _)| k == key) else {
                    return Emptiness::Empty; // key absent on the other side
                };
                match inter(group, ca, cb, visiting, interner) {
                    Emptiness::Empty => return Emptiness::Empty,
                    Emptiness::Unproven => any_unproven = true,
                    Emptiness::NonEmpty(w) => pairs.push((key.encode_utf16().collect(), w)),
                }
            }
            if any_unproven {
                Emptiness::Unproven
            } else {
                Emptiness::NonEmpty(interner.record(pairs))
            }
        }
        (Tuple(ea), Tuple(eb)) => {
            if ea.len() != eb.len() {
                return Emptiness::Empty;
            }
            let mut items = Vec::with_capacity(ea.len());
            let mut any_unproven = false;
            for (ca, cb) in ea.iter().zip(eb) {
                match inter(group, ca, cb, visiting, interner) {
                    Emptiness::Empty => return Emptiness::Empty,
                    Emptiness::Unproven => any_unproven = true,
                    Emptiness::NonEmpty(w) => items.push(w),
                }
            }
            if any_unproven {
                Emptiness::Unproven
            } else {
                Emptiness::NonEmpty(interner.tuple(items))
            }
        }
        // Leaf-ish pairs: exact disjointness, then a sampled common witness.
        _ => {
            if super::subcontract::disjoint(a, b) {
                return Emptiness::Empty;
            }
            let common = super::subcontract::sample(a, interner)
                .into_iter()
                .chain(super::subcontract::sample(b, interner))
                .find(|v| contains(group, a, v) && contains(group, b, v));
            match common {
                Some(w) => Emptiness::NonEmpty(w),
                None => Emptiness::Unproven,
            }
        }
    }
}

/// Combine two emptiness verdicts disjunctively (a union of the two sides).
fn join_empty(a: Emptiness, b: Emptiness) -> Emptiness {
    match (a, b) {
        (Emptiness::NonEmpty(w), _) | (_, Emptiness::NonEmpty(w)) => Emptiness::NonEmpty(w),
        (Emptiness::Empty, Emptiness::Empty) => Emptiness::Empty,
        _ => Emptiness::Unproven,
    }
}

// ── 4. Subcontract (§5) — progress-guarded pair induction ─────────────────────

/// Bound on how deep the refutation search unfolds recursive references. A
/// counterexample to `A ⊑ B`, if one exists, is a finite source value; the
/// minimal one is shallow, so a small bound suffices in practice (§5.3: no
/// derivable bound ⇒ unproven, never a cap on a *proof*).
const REFUTE_DEPTH: usize = 4;

/// Decide `A ⊑ B` over the recursive group. Sound: `Proven` only when
/// `⟦A⟧ ⊆ ⟦B⟧`; `Refuted(w)` only with a finite `w ∈ ⟦A⟧ ∖ ⟦B⟧` (§5.3 — an
/// assembled source witness, never a bare component mismatch). Empty sources are
/// `Proven` (step 0) and yield no inhabitants, so are never refuted.
// `Contract` keys embed interned `ValueRef`s. Interned values are immutable, so
// their hash/eq are stable — the `mutable_key_type` lint's concern does not apply.
#[allow(clippy::mutable_key_type)]
pub fn subcontract(group: &RecGroup, a: &Contract, b: &Contract, interner: &mut Interner) -> Verdict {
    let env = EmptyEnv::analyze(group, interner);
    let mut assumed: HashMap<(Contract, Contract), usize> = HashMap::new();
    if prove(group, &env, a, b, 0, &mut assumed, interner) {
        return Verdict::Proven;
    }
    // Refutation: assemble a finite inhabitant of A that B rejects.
    if let Some(w) = refute(group, a, b, interner) {
        return Verdict::Refuted(w);
    }
    // Otherwise unproven — deferred to the non-recursive check, which is sound
    // (Unproven for recursive shapes, and complete for concrete ref-free pairs).
    super::subcontract(a, b, interner)
}

/// Search for a finite `w ∈ ⟦A⟧ ∖ ⟦B⟧` by enumerating inhabitants of `A` at
/// increasing unfolding depth. Every returned witness is re-checked against both
/// sides, so the verdict is sound (bounded, hence incomplete — a deeper-only
/// counterexample stays `Unproven`).
fn refute(group: &RecGroup, a: &Contract, b: &Contract, interner: &mut Interner) -> Option<ValueRef> {
    for depth in 0..=REFUTE_DEPTH {
        let candidates = inhabitants(group, a, depth, interner);
        if let Some(w) = candidates.into_iter().find(|w| contains(group, a, w) && !contains(group, b, w)) {
            return Some(w);
        }
    }
    None
}

/// A bounded set of finite inhabitants of `c`, unfolding references up to `depth`.
/// References past the budget contribute nothing (that branch simply yields fewer
/// witnesses — soundness is unaffected because every witness is re-verified).
fn inhabitants(group: &RecGroup, c: &Contract, depth: usize, interner: &mut Interner) -> Vec<ValueRef> {
    // Keep the per-node fan-out small; a counterexample needs only one witness.
    const FANOUT: usize = 3;
    match c {
        Contract::Ref(name) if group.is_member(name) => {
            if depth == 0 {
                vec![]
            } else {
                inhabitants(group, group.get(name), depth - 1, interner)
            }
        }
        Contract::Union(a, b) => {
            let mut v = inhabitants(group, a, depth, interner);
            v.extend(inhabitants(group, b, depth, interner));
            v
        }
        Contract::Difference(base, ex) => {
            let mut v = inhabitants(group, base, depth, interner);
            v.retain(|w| !contains(group, ex, w));
            v
        }
        Contract::Intersection(a, b) => {
            let mut v = inhabitants(group, a, depth, interner);
            v.retain(|w| contains(group, b, w));
            v
        }
        Contract::Tuple(elems) => {
            let per: Vec<Vec<ValueRef>> =
                elems.iter().map(|e| take(inhabitants(group, e, depth, interner), FANOUT)).collect();
            product_values(&per, interner, false, &[])
        }
        // A Concat inhabitant is a segment-wise choice, concatenated.
        Contract::Concat(segs) => {
            let per: Vec<Vec<ValueRef>> =
                segs.iter().map(|s| take(inhabitants(group, s, depth, interner), FANOUT)).collect();
            if per.iter().any(|c| c.is_empty()) {
                return vec![];
            }
            let mut out = Vec::new();
            for combo in product_values(&per, interner, false, &[]) {
                // Each component is itself a tuple; splice them.
                let parts = combo.as_tuple().expect("tuple of segments").to_vec();
                let mut items: Vec<ValueRef> = Vec::new();
                let mut ok = true;
                for p in parts {
                    match p.as_tuple() {
                        Some(t) => items.extend_from_slice(t),
                        None => ok = false,
                    }
                }
                if ok {
                    out.push(interner.tuple(items));
                }
            }
            out
        }
        Contract::Record(fields) => {
            let keys: Vec<Vec<u16>> = fields.iter().map(|(k, _)| k.encode_utf16().collect()).collect();
            let per: Vec<Vec<ValueRef>> =
                fields.iter().map(|(_, e)| take(inhabitants(group, e, depth, interner), FANOUT)).collect();
            product_values(&per, interner, true, &keys)
        }
        // Leaves — a few concrete samples, re-filtered by membership.
        _ => take(super::subcontract::sample(c, interner).into_iter().filter(|v| c.contains(v)).collect(), FANOUT),
    }
}

fn take(mut v: Vec<ValueRef>, n: usize) -> Vec<ValueRef> {
    v.truncate(n);
    v
}

/// Assemble tuple/record values from a per-component inhabitant grid (bounded
/// cartesian product). If any component is empty, there are no inhabitants.
fn product_values(per: &[Vec<ValueRef>], interner: &mut Interner, record: bool, keys: &[Vec<u16>]) -> Vec<ValueRef> {
    const CAP: usize = 12;
    if per.iter().any(|c| c.is_empty()) {
        return vec![];
    }
    let mut combos: Vec<Vec<ValueRef>> = vec![vec![]];
    for column in per {
        let mut next = Vec::new();
        for prefix in &combos {
            for item in column {
                let mut row = prefix.clone();
                row.push(item.clone());
                next.push(row);
                if next.len() >= CAP {
                    break;
                }
            }
        }
        combos = next;
    }
    combos
        .into_iter()
        .map(|row| {
            if record {
                let pairs: Vec<(Vec<u16>, ValueRef)> = keys.iter().cloned().zip(row).collect();
                interner.record(pairs)
            } else {
                interner.tuple(row)
            }
        })
        .collect()
}

#[allow(clippy::too_many_arguments, clippy::mutable_key_type)]
fn prove(
    group: &RecGroup,
    env: &EmptyEnv,
    a: &Contract,
    b: &Contract,
    source_progress: usize,
    assumed: &mut HashMap<(Contract, Contract), usize>,
    interner: &mut Interner,
) -> bool {
    // Step 0: an empty source is a subcontract of everything.
    if env.voice(group, a, interner) == E3::Empty {
        return true;
    }

    // Progress-guarded hypothesis: a revisit closes only at strictly greater
    // source depth (per-pair, depth-stamped — RC-16).
    let key = (a.clone(), b.clone());
    if let Some(&assumed_progress) = assumed.get(&key) {
        return source_progress > assumed_progress;
    }
    assumed.insert(key.clone(), source_progress);

    let result = prove_body(group, env, a, b, source_progress, assumed, interner);

    // Only the winning-path assumption persists; a failed pair must not poison a
    // sibling branch that could still close.
    if !result {
        assumed.remove(&key);
    }
    result
}

#[allow(clippy::too_many_arguments, clippy::mutable_key_type)]
fn prove_body(
    group: &RecGroup,
    env: &EmptyEnv,
    a: &Contract,
    b: &Contract,
    source_progress: usize,
    assumed: &mut HashMap<(Contract, Contract), usize>,
    interner: &mut Interner,
) -> bool {
    // μ-head traversal — resolve references without incrementing depth.
    match a {
        Contract::Ref(name) if group.is_member(name) => {
            return prove(group, env, group.get(name), b, source_progress, assumed, interner);
        }
        _ => {}
    }
    match b {
        Contract::Ref(name) if group.is_member(name) => {
            return prove(group, env, a, group.get(name), source_progress, assumed, interner);
        }
        _ => {}
    }

    match (a, b) {
        (_, Contract::Top) => true,
        // And-like rows on B (complete).
        (_, Contract::Intersection(b1, b2)) => {
            prove(group, env, a, b1, source_progress, assumed, interner)
                && prove(group, env, a, b2, source_progress, assumed, interner)
        }
        // Or/and rows on A (complete for Union-left).
        (Contract::Union(a1, a2), _) => {
            prove(group, env, a1, b, source_progress, assumed, interner)
                && prove(group, env, a2, b, source_progress, assumed, interner)
        }
        (_, Contract::Union(b1, b2)) => {
            prove(group, env, a, b1, source_progress, assumed, interner)
                || prove(group, env, a, b2, source_progress, assumed, interner)
        }
        (Contract::Intersection(a1, a2), _) => {
            prove(group, env, a1, b, source_progress, assumed, interner)
                || prove(group, env, a2, b, source_progress, assumed, interner)
        }
        // Aligned concatenation: compare segment-wise, and carry the source's
        // **consumed extent** as progress (RC §5, 0.2.2 — flat sequence recursion
        // licenses reuse by what the traversal consumed, not by nesting). This is
        // the aligned case only; the family's general alignment procedure (§4,
        // forced-boundary peeling over unequal segment counts) is a later increment,
        // and lands `unproven` here rather than guessing a split.
        (Contract::Concat(sa), Contract::Concat(sb)) if sa.len() == sb.len() => {
            let mut consumed = 0;
            for (x, y) in sa.iter().zip(sb) {
                if !prove(group, env, x, y, source_progress + consumed, assumed, interner) {
                    return false;
                }
                consumed += super::min_extent(x);
            }
            true
        }
        // Structural descent — increments source progress (the induction measure).
        (Contract::Tuple(ea), Contract::Tuple(eb)) => {
            ea.len() == eb.len()
                && ea
                    .iter()
                    .zip(eb)
                    .all(|(x, y)| prove(group, env, x, y, source_progress + 1, assumed, interner))
        }
        (Contract::Record(fa), Contract::Record(fb)) => {
            fa.len() == fb.len()
                && fa.iter().all(|(key, ca)| match fb.iter().find(|(k, _)| k == key) {
                    Some((_, cb)) => prove(group, env, ca, cb, source_progress + 1, assumed, interner),
                    None => false,
                })
        }
        // Leaf pair — neither side recursive here; the C.2 check is complete.
        _ => matches!(super::subcontract(a, b, interner), Verdict::Proven),
    }
}
