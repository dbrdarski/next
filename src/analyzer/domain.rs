//! The **AnalysisContract** abstract domain — the analyzer core, §2 of the
//! Application & Induction package (v0.8.1), now in its **structural / correlated**
//! form (the checkpoint-review bridge).
//!
//! **Two-level semantics.** `erase(ac)` is the ordinary contract, whose language
//! denotation `⟦erase(ac)⟧` is untouched. **`γ(ac) ⊆ ⟦erase(ac)⟧`** is the analyzer
//! concretization: the runtime values the complete annotated contract represents,
//! metadata included. Function metadata now survives **structurally** — nested in a
//! tuple, a record field, or a correlated union alternative — so the joint operand
//! state `[callee, …args]` and a correlated union like `[numFn, 5] | [strFn, "hi"]`
//! keep their correlation and never synthesize a false cross-pair (`(numFn, "hi")`).
//!
//! The domain element:
//! - **`Leaf { contract, metadata }`** — a scalar/opaque position. A non-function
//!   member of `⟦contract⟧` is always in γ (metadata is vacuous off function
//!   positions); a function member is in γ iff the metadata admits it — every
//!   function under `Unknown`, or one **realizing** an instance under `Known(S)`.
//! - **`Tuple(elems)` / `Record(fields)`** — positional structure preserved; γ is the
//!   pointwise product, never flattened.
//! - **`Alt(alternatives)`** — a set of **correlated** alternatives; γ is their union,
//!   but each alternative keeps its internal correlation.
//! - **`Bottom`** — `γ = ∅`, the one canonical empty.
//!
//! `prove_subcontract_a` (⊑ᴬ, semantically `γ(a) ⊆ γ(b)`) and `intersect_a` (sound by
//! containment) recurse through the structure; both stay three-valued and
//! deliberately incomplete.

use crate::ast::Lambda;
use crate::contract::{Contract, Kind, Verdict, subcontract};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

/// An **analysis instance**: a function's μ-canonical shape (the node label,
/// compared structurally) plus its **annotated** captured environment — one
/// [`AnalysisContract`] per capture slot, in the shape's `free_vars` order.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Instance {
    pub shape: Lambda,
    pub env: Vec<AnalysisContract>,
}

impl Instance {
    /// Proven-empty when any captured position is bottom — no closure of this shape
    /// can realize it (metadata normalization, §2).
    pub fn is_empty(&self) -> bool {
        self.env.iter().any(AnalysisContract::is_bottom)
    }
}

/// The instance-metadata lattice element (§2). `Known(∅)` = no function possible
/// (a dead branch — feeds emptiness); `Unknown` = a function is possible, origins
/// coarsened away.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum InstanceMetadata {
    Known(Vec<Instance>),
    Unknown,
}

impl InstanceMetadata {
    /// Join (`∪`): `Known(S) ∪ Known(T) = Known(S ∪ T)`; `X ∪ Unknown = Unknown`.
    pub fn join(a: &InstanceMetadata, b: &InstanceMetadata) -> InstanceMetadata {
        match (a, b) {
            (InstanceMetadata::Known(s), InstanceMetadata::Known(t)) => {
                let mut out = s.clone();
                for i in t {
                    if !out.contains(i) {
                        out.push(i.clone());
                    }
                }
                InstanceMetadata::Known(out)
            }
            _ => InstanceMetadata::Unknown,
        }
    }
}

/// The structural / correlated abstract-domain element (§2, bridge form).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AnalysisContract {
    /// A scalar/opaque position: an ordinary contract with function-position metadata.
    Leaf { contract: Contract, metadata: InstanceMetadata },
    /// A tuple with positional annotated elements — structure preserved.
    Tuple(Vec<AnalysisContract>),
    /// A record with annotated fields (static string keys).
    Record(Vec<(String, AnalysisContract)>),
    /// A set of **correlated** alternatives — γ is their union; never flattened.
    Alt(Vec<AnalysisContract>),
    /// `γ = ∅` — the one canonical empty.
    Bottom,
}

impl AnalysisContract {
    /// The canonical empty concretization.
    pub fn bottom() -> AnalysisContract {
        AnalysisContract::Bottom
    }

    /// A leaf with coarsened metadata `(C, Unknown)`, normalized.
    pub fn of_contract(contract: Contract) -> AnalysisContract {
        AnalysisContract::leaf(contract, InstanceMetadata::Unknown)
    }

    /// A leaf, **normalized** to the one canonical bottom (§2): `(Bottom, _) →
    /// Bottom`, and `(C, Known(∅)) → Bottom` when `C` is function-only (its γ then has
    /// no members at all). Off function positions, `Known(∅)` is vacuous — a
    /// deliberate generalization of the spec's function-position statement (see
    /// `OwedItems`, the `Known(∅)` doc-integration mismatch).
    pub fn leaf(contract: Contract, metadata: InstanceMetadata) -> AnalysisContract {
        if matches!(contract, Contract::Bottom) {
            return AnalysisContract::Bottom;
        }
        if matches!(&metadata, InstanceMetadata::Known(s) if s.is_empty()) && is_function_only(&contract) {
            return AnalysisContract::Bottom;
        }
        AnalysisContract::Leaf { contract, metadata }
    }

    /// A correlated tuple; a bottom element makes the whole tuple bottom.
    pub fn tuple(elems: Vec<AnalysisContract>) -> AnalysisContract {
        if elems.iter().any(AnalysisContract::is_bottom) {
            return AnalysisContract::Bottom;
        }
        AnalysisContract::Tuple(elems)
    }

    /// A record; a bottom field makes the whole record bottom.
    pub fn record(fields: Vec<(String, AnalysisContract)>) -> AnalysisContract {
        if fields.iter().any(|(_, v)| v.is_bottom()) {
            return AnalysisContract::Bottom;
        }
        AnalysisContract::Record(fields)
    }

    /// A union of correlated alternatives, bottom branches dropped; an empty union is
    /// bottom, a singleton collapses.
    pub fn alt(alternatives: Vec<AnalysisContract>) -> AnalysisContract {
        let mut live: Vec<AnalysisContract> = alternatives.into_iter().filter(|a| !a.is_bottom()).collect();
        match live.len() {
            0 => AnalysisContract::Bottom,
            1 => live.pop().unwrap(),
            _ => AnalysisContract::Alt(live),
        }
    }

    /// `γ(ac) = ∅`.
    pub fn is_bottom(&self) -> bool {
        matches!(self, AnalysisContract::Bottom)
    }

    /// `erase(ac)` — the ordinary contract (the language denotation, metadata dropped).
    pub fn erase(&self, i: &mut Interner) -> Contract {
        match self {
            AnalysisContract::Bottom => Contract::Bottom,
            AnalysisContract::Leaf { contract, .. } => contract.clone(),
            AnalysisContract::Tuple(es) => {
                let elems: Vec<Contract> = es.iter().map(|e| e.erase(i)).collect();
                Contract::tuple(elems, i)
            }
            AnalysisContract::Record(fs) => {
                let fields: Vec<(String, Contract)> =
                    fs.iter().map(|(k, v)| (k.clone(), v.erase(i))).collect();
                Contract::record(fields, i)
            }
            AnalysisContract::Alt(alts) => {
                let parts: Vec<Contract> = alts.iter().map(|a| a.erase(i)).collect();
                parts
                    .into_iter()
                    .reduce(|a, b| Contract::union(a, b, i))
                    .unwrap_or(Contract::Bottom)
            }
        }
    }

    /// Whether the whole annotated contract carries **no** restrictive metadata — every
    /// leaf is `Unknown`. Then `γ(ac) = ⟦erase(ac)⟧`, so an erased-contract inclusion
    /// into it is a sound ⊑ᴬ proof.
    fn metadata_free(&self) -> bool {
        match self {
            AnalysisContract::Bottom => true,
            AnalysisContract::Leaf { metadata, .. } => matches!(metadata, InstanceMetadata::Unknown),
            AnalysisContract::Tuple(es) => es.iter().all(AnalysisContract::metadata_free),
            AnalysisContract::Record(fs) => fs.iter().all(|(_, v)| v.metadata_free()),
            AnalysisContract::Alt(alts) => alts.iter().all(AnalysisContract::metadata_free),
        }
    }
}

/// Whether `⟦c⟧ ⊆ Functions` — the only case where `Known(∅)` empties the whole
/// concretization (off function positions the metadata is vacuous).
fn is_function_only(c: &Contract) -> bool {
    match c {
        Contract::Kind(Kind::Function) | Contract::Bottom => true,
        Contract::Union(a, b) => is_function_only(a) && is_function_only(b),
        Contract::Intersection(a, b) => is_function_only(a) || is_function_only(b),
        Contract::Equals(v) => v.is_function(),
        _ => false,
    }
}

// ── γ concretization (membership) ────────────────────────────────────────────

/// Whether the closure value `v` **realizes** instance `i`: its μ-canonical shape
/// matches, and each captured value lies in the γ of the matching annotated capture
/// (recursively). A capture bound to a slot / under-init is treated conservatively as
/// unrealized (a sound under-approximation of γ for membership).
pub fn realizes(v: &ValueRef, i: &Instance, interner: &mut Interner) -> bool {
    let Some(f) = v.as_fn() else { return false };
    if f.shape() != &i.shape || f.free_vars().len() != i.env.len() {
        return false;
    }
    // Resolve capture values first, releasing the borrow on `v` before recursing.
    let mut captures: Vec<ValueRef> = Vec::with_capacity(i.env.len());
    for name in f.free_vars() {
        match f.closure().env.lookup(name) {
            Some(Binding::Value(cv)) => captures.push(cv),
            _ => return false,
        }
    }
    for (cap, cv) in i.env.iter().zip(&captures) {
        if !gamma_contains(cap, cv, interner) {
            return false;
        }
    }
    true
}

/// Whether `v ∈ γ(ac)`, recursing through the annotated structure.
pub fn gamma_contains(ac: &AnalysisContract, v: &ValueRef, interner: &mut Interner) -> bool {
    match ac {
        AnalysisContract::Bottom => false,
        AnalysisContract::Leaf { contract, metadata } => {
            if !contract.contains(v) {
                return false;
            }
            if !v.is_function() {
                return true; // metadata is vacuous off function positions
            }
            match metadata {
                InstanceMetadata::Unknown => true,
                InstanceMetadata::Known(s) => {
                    for i in s {
                        if realizes(v, i, interner) {
                            return true;
                        }
                    }
                    false
                }
            }
        }
        AnalysisContract::Tuple(es) => {
            let Some(items) = v.as_tuple() else {
                return false;
            };
            if items.len() != es.len() {
                return false;
            }
            let items: Vec<ValueRef> = items.to_vec();
            for (e, x) in es.iter().zip(&items) {
                if !gamma_contains(e, x, interner) {
                    return false;
                }
            }
            true
        }
        AnalysisContract::Record(fs) => {
            let Some(entries) = v.as_record() else {
                return false;
            };
            if entries.len() != fs.len() {
                return false;
            }
            let entries: Vec<(Vec<u16>, ValueRef)> = entries
                .iter()
                .map(|e| (e.key.clone(), e.value.clone()))
                .collect();
            for (k, ac) in fs {
                let ku: Vec<u16> = k.encode_utf16().collect();
                let Some((_, xv)) = entries.iter().find(|(ek, _)| *ek == ku) else {
                    return false;
                };
                let xv = xv.clone();
                if !gamma_contains(ac, &xv, interner) {
                    return false;
                }
            }
            true
        }
        AnalysisContract::Alt(alts) => {
            for a in alts {
                if gamma_contains(a, v, interner) {
                    return true;
                }
            }
            false
        }
    }
}

// ── intersectA / meetInstance ────────────────────────────────────────────────

/// The analyzer conjunction — sound by containment only: `γ(A) ∩ γ(B) ⊆
/// γ(intersect_a(A, B))`. Recurses through the structure (tuples pointwise, unions
/// distribute); leaf∩leaf uses the coverage-normalized metadata meet; a mixed
/// structural/leaf pair falls back to a leaf over the erased intersection (sound,
/// coarse). No lower-bound or idempotence reasoning may rest on the result.
pub fn intersect_a(a: &AnalysisContract, b: &AnalysisContract, interner: &mut Interner) -> AnalysisContract {
    match (a, b) {
        (AnalysisContract::Bottom, _) | (_, AnalysisContract::Bottom) => AnalysisContract::Bottom,
        (AnalysisContract::Alt(alts), other) | (other, AnalysisContract::Alt(alts)) => {
            let mut out = Vec::new();
            for alt in alts {
                out.push(intersect_a(alt, other, interner));
            }
            AnalysisContract::alt(out)
        }
        (AnalysisContract::Tuple(ea), AnalysisContract::Tuple(eb)) if ea.len() == eb.len() => {
            let mut elems = Vec::with_capacity(ea.len());
            for (x, y) in ea.iter().zip(eb) {
                elems.push(intersect_a(x, y, interner));
            }
            AnalysisContract::tuple(elems)
        }
        (AnalysisContract::Record(fa), AnalysisContract::Record(fb)) if same_keys(fa, fb) => {
            let mut fields = Vec::with_capacity(fa.len());
            for (k, va) in fa {
                let vb = &fb.iter().find(|(k2, _)| k2 == k).unwrap().1;
                fields.push((k.clone(), intersect_a(va, vb, interner)));
            }
            AnalysisContract::record(fields)
        }
        (
            AnalysisContract::Leaf {
                contract: ca,
                metadata: ma,
            },
            AnalysisContract::Leaf {
                contract: cb,
                metadata: mb,
            },
        ) => {
            let contract = Contract::intersection(ca.clone(), cb.clone(), interner);
            let metadata = meet_metadata(ma, mb, interner);
            AnalysisContract::leaf(contract, metadata)
        }
        _ => {
            let (ea, eb) = (a.erase(interner), b.erase(interner));
            AnalysisContract::leaf(
                Contract::intersection(ea, eb, interner),
                InstanceMetadata::Unknown,
            )
        }
    }
}

fn same_keys(fa: &[(String, AnalysisContract)], fb: &[(String, AnalysisContract)]) -> bool {
    fa.len() == fb.len() && fa.iter().all(|(k, _)| fb.iter().any(|(k2, _)| k2 == k))
}

/// The metadata meet (leaf level): `Unknown ∩ M = M`; `Known(S) ∩ Known(T)` is the
/// coverage-normalized same-shape meet (`s ⊑ t ⇒ s`, else the [`meet_instance`] of
/// overlapping environments).
fn meet_metadata(a: &InstanceMetadata, b: &InstanceMetadata, interner: &mut Interner) -> InstanceMetadata {
    match (a, b) {
        (InstanceMetadata::Unknown, m) | (m, InstanceMetadata::Unknown) => m.clone(),
        (InstanceMetadata::Known(s), InstanceMetadata::Known(t)) => {
            let mut out: Vec<Instance> = Vec::new();
            for si in s {
                for ti in t {
                    if si.shape != ti.shape {
                        continue;
                    }
                    let meet = if matches!(instance_covers(si, ti, interner), Verdict::Proven) {
                        Some(si.clone())
                    } else if matches!(instance_covers(ti, si, interner), Verdict::Proven) {
                        Some(ti.clone())
                    } else {
                        meet_instance(si, ti, interner)
                    };
                    match meet {
                        Some(m) if !m.is_empty() && !out.contains(&m) => out.push(m),
                        _ => {}
                    }
                }
            }
            InstanceMetadata::Known(out)
        }
    }
}

/// The same-shape environment meet. `None` when shapes differ, or when the
/// environment intersection is **proven** empty (a captured position becomes bottom).
pub fn meet_instance(i: &Instance, j: &Instance, interner: &mut Interner) -> Option<Instance> {
    if i.shape != j.shape || i.env.len() != j.env.len() {
        return None;
    }
    let mut env = Vec::with_capacity(i.env.len());
    for (a, b) in i.env.iter().zip(&j.env) {
        let m = intersect_a(a, b, interner);
        if m.is_bottom() {
            return None;
        }
        env.push(m);
    }
    Some(Instance { shape: i.shape.clone(), env })
}

// ── proveSubcontractA — the annotated three-valued subcontract ────────────────

/// The analyzer judgment for `AC₁ ⊑ᴬ AC₂` (semantically `γ(a) ⊆ γ(b)`) — sound,
/// deliberately incomplete, three-valued. Recurses through structure; a `Refuted`
/// witness must be γ-representable; a proof needs erased inclusion **and** either a
/// metadata-free target or leaf-level metadata coverage.
pub fn prove_subcontract_a(a: &AnalysisContract, b: &AnalysisContract, interner: &mut Interner) -> Verdict {
    match (a, b) {
        (AnalysisContract::Bottom, _) => Verdict::Proven, // ∅ ⊑ anything
        (AnalysisContract::Alt(alts), _) => {
            // γ(⋃ alts) ⊆ γ(b) ⟺ every alternative ⊑ b.
            for alt in alts {
                let v = prove_subcontract_a(alt, b, interner);
                if !matches!(v, Verdict::Proven) {
                    return v; // an alternative's Refuted/Unproven is the whole verdict
                }
            }
            Verdict::Proven
        }
        (_, AnalysisContract::Alt(alts)) => {
            // a ⊑ some alternative is sound (incomplete for genuine splits).
            for alt in alts {
                if matches!(prove_subcontract_a(a, alt, interner), Verdict::Proven) {
                    return Verdict::Proven;
                }
            }
            prove_by_erasure(a, b, interner)
        }
        (AnalysisContract::Tuple(ea), AnalysisContract::Tuple(eb)) if ea.len() == eb.len() => {
            for (x, y) in ea.iter().zip(eb) {
                if !matches!(prove_subcontract_a(x, y, interner), Verdict::Proven) {
                    return prove_by_erasure(a, b, interner);
                }
            }
            Verdict::Proven
        }
        (AnalysisContract::Record(fa), AnalysisContract::Record(fb)) if same_keys(fa, fb) => {
            for (k, va) in fa {
                let vb = &fb.iter().find(|(k2, _)| k2 == k).unwrap().1;
                if !matches!(prove_subcontract_a(va, vb, interner), Verdict::Proven) {
                    return prove_by_erasure(a, b, interner);
                }
            }
            Verdict::Proven
        }
        _ => prove_by_erasure(a, b, interner),
    }
}

/// The leaf/mixed path: refute through the erased contracts (γ-representable witness
/// only), else prove when erased inclusion holds and the target is metadata-free or
/// both sides are leaves with covering metadata.
fn prove_by_erasure(
    a: &AnalysisContract,
    b: &AnalysisContract,
    interner: &mut Interner,
) -> Verdict {
    let (ea, eb) = (a.erase(interner), b.erase(interner));
    let base = subcontract(&ea, &eb, interner);
    match &base {
        Verdict::Refuted(w) if gamma_contains(a, w, interner) => {
            return Verdict::Refuted(w.clone());
        }
        _ => {}
    }
    if matches!(base, Verdict::Proven) {
        if b.metadata_free() {
            return Verdict::Proven;
        }
        let leaf_covered = match (a, b) {
            (
                AnalysisContract::Leaf { metadata: ma, .. },
                AnalysisContract::Leaf { metadata: mb, .. },
            ) => matches!(covers(ma, mb, interner), Verdict::Proven),
            _ => false,
        };
        if leaf_covered {
            return Verdict::Proven;
        }
    }
    Verdict::Unproven
}

/// Metadata coverage — the `Known(S) ⊑ Known(T)` triage (§2, round 5). Proven-empty
/// sources ignored; every other source (uncertain inhabitance never silently skipped)
/// requires a same-shape target whose annotated environment covers it (⊑ᴬ recursively).
fn covers(s: &InstanceMetadata, t: &InstanceMetadata, interner: &mut Interner) -> Verdict {
    match (s, t) {
        (_, InstanceMetadata::Unknown) => Verdict::Proven,
        (InstanceMetadata::Unknown, InstanceMetadata::Known(_)) => Verdict::Unproven,
        (InstanceMetadata::Known(src), InstanceMetadata::Known(tgt)) => {
            for si in src {
                if si.is_empty() {
                    continue;
                }
                let covered = tgt.iter().any(|ti| matches!(instance_covers(si, ti, interner), Verdict::Proven));
                if !covered {
                    return Verdict::Unproven;
                }
            }
            Verdict::Proven
        }
    }
}

/// `instance s ⊑ᴬ instance t`: same shape, and each capture `s.env[k] ⊑ᴬ t.env[k]`.
fn instance_covers(s: &Instance, t: &Instance, interner: &mut Interner) -> Verdict {
    if s.shape != t.shape || s.env.len() != t.env.len() {
        return Verdict::Unproven;
    }
    for (a, b) in s.env.iter().zip(&t.env) {
        if !matches!(prove_subcontract_a(a, b, interner), Verdict::Proven) {
            return Verdict::Unproven;
        }
    }
    Verdict::Proven
}
