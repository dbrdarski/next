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
        // Non-recursive leaves: the ordinary denotational membership.
        _ => c.contains(v),
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
        let verdict = exactness(group, &productive);
        EmptyEnv { productive, verdict }
    }

    /// The emptiness voice of an arbitrary contract under this environment.
    fn voice(&self, group: &RecGroup, c: &Contract) -> E3 {
        exact_eval(group, c, &self.productive, &self.verdict)
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
            // A genuine common inhabitant: a witness of one side that the other admits.
            let admits = |w: &ValueRef, other: &Contract| contains(group, other, w);
            match prod_eval(group, a, states, interner) {
                Some(w) if admits(&w, b) => Some(w),
                _ => match prod_eval(group, b, states, interner) {
                    Some(w) if admits(&w, a) => Some(w),
                    _ => None,
                },
            }
        }
        Contract::Difference(b, e) => match prod_eval(group, b, states, interner) {
            Some(w) if !contains(group, e, &w) => Some(w),
            _ => None,
        },
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
) -> BTreeMap<String, E3> {
    let mut verdict: BTreeMap<String, E3> = productive
        .iter()
        .map(|(n, s)| (n.clone(), if s.is_some() { E3::NonEmpty } else { E3::Empty }))
        .collect();

    loop {
        let mut changed = false;
        for name in group.defs.keys() {
            if verdict[name] == E3::NonEmpty {
                continue;
            }
            let v = exact_eval(group, group.get(name), productive, &verdict);
            if v == E3::Unproven && verdict[name] != E3::Unproven {
                verdict.insert(name.clone(), E3::Unproven);
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
/// reference bodies — references are leaves here).
fn exact_eval(
    group: &RecGroup,
    c: &Contract,
    productive: &BTreeMap<String, Option<ValueRef>>,
    verdict: &BTreeMap<String, E3>,
) -> E3 {
    let go = |x: &Contract| exact_eval(group, x, productive, verdict);
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
        Contract::Union(a, b) => join_union(go(a), go(b)),
        Contract::Intersection(a, b) => {
            if go(a) == E3::Empty || go(b) == E3::Empty {
                E3::Empty
            } else {
                E3::Unproven // exact intersection emptiness (product graph) is owed
            }
        }
        Contract::Difference(b, _) => {
            if go(b) == E3::Empty {
                E3::Empty
            } else {
                E3::Unproven
            }
        }
        Contract::Tuple(elems) => join_product(elems.iter().map(&go)),
        Contract::Record(fields) => join_product(fields.iter().map(|(_, e)| go(e))),
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

// ── 4. Subcontract (§5) — progress-guarded pair induction ─────────────────────

/// Decide `A ⊑ B` over the recursive group. Sound: `Proven` only when
/// `⟦A⟧ ⊆ ⟦B⟧`. Recursive non-proofs are `Unproven`; ref-free leaf pairs delegate
/// to the C.2 check (which can additionally `Refute` with a witness).
// `Contract` keys embed interned `ValueRef`s. Interned values are immutable, so
// their hash/eq are stable — the `mutable_key_type` lint's concern does not apply.
#[allow(clippy::mutable_key_type)]
pub fn subcontract(group: &RecGroup, a: &Contract, b: &Contract, interner: &mut Interner) -> Verdict {
    let env = EmptyEnv::analyze(group, interner);
    let mut assumed: HashMap<(Contract, Contract), usize> = HashMap::new();
    if prove(group, &env, a, b, 0, &mut assumed, interner) {
        return Verdict::Proven;
    }
    // Fall back to the non-recursive check — sound (Unproven for recursive shapes,
    // possibly Refuted for concrete ones).
    super::subcontract(a, b, interner)
}

#[allow(clippy::too_many_arguments, clippy::mutable_key_type)]
fn prove(
    group: &RecGroup,
    env: &EmptyEnv,
    a: &Contract,
    b: &Contract,
    depth: usize,
    assumed: &mut HashMap<(Contract, Contract), usize>,
    interner: &mut Interner,
) -> bool {
    // Step 0: an empty source is a subcontract of everything.
    if env.voice(group, a) == E3::Empty {
        return true;
    }

    // Progress-guarded hypothesis: a revisit closes only at strictly greater
    // source depth (per-pair, depth-stamped — RC-16).
    let key = (a.clone(), b.clone());
    if let Some(&assumed_depth) = assumed.get(&key) {
        return depth > assumed_depth;
    }
    assumed.insert(key.clone(), depth);

    let result = prove_body(group, env, a, b, depth, assumed, interner);

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
    depth: usize,
    assumed: &mut HashMap<(Contract, Contract), usize>,
    interner: &mut Interner,
) -> bool {
    // μ-head traversal — resolve references without incrementing depth.
    match a {
        Contract::Ref(name) if group.is_member(name) => {
            return prove(group, env, group.get(name), b, depth, assumed, interner);
        }
        _ => {}
    }
    match b {
        Contract::Ref(name) if group.is_member(name) => {
            return prove(group, env, a, group.get(name), depth, assumed, interner);
        }
        _ => {}
    }

    match (a, b) {
        (_, Contract::Top) => true,
        // And-like rows on B (complete).
        (_, Contract::Intersection(b1, b2)) => {
            prove(group, env, a, b1, depth, assumed, interner)
                && prove(group, env, a, b2, depth, assumed, interner)
        }
        // Or/and rows on A (complete for Union-left).
        (Contract::Union(a1, a2), _) => {
            prove(group, env, a1, b, depth, assumed, interner)
                && prove(group, env, a2, b, depth, assumed, interner)
        }
        (_, Contract::Union(b1, b2)) => {
            prove(group, env, a, b1, depth, assumed, interner)
                || prove(group, env, a, b2, depth, assumed, interner)
        }
        (Contract::Intersection(a1, a2), _) => {
            prove(group, env, a1, b, depth, assumed, interner)
                || prove(group, env, a2, b, depth, assumed, interner)
        }
        // Structural descent — increments source depth (the induction measure).
        (Contract::Tuple(ea), Contract::Tuple(eb)) => {
            ea.len() == eb.len()
                && ea
                    .iter()
                    .zip(eb)
                    .all(|(x, y)| prove(group, env, x, y, depth + 1, assumed, interner))
        }
        (Contract::Record(fa), Contract::Record(fb)) => {
            fa.len() == fb.len()
                && fa.iter().all(|(key, ca)| match fb.iter().find(|(k, _)| k == key) {
                    Some((_, cb)) => prove(group, env, ca, cb, depth + 1, assumed, interner),
                    None => false,
                })
        }
        // Leaf pair — neither side recursive here; the C.2 check is complete.
        _ => matches!(super::subcontract(a, b, interner), Verdict::Proven),
    }
}
