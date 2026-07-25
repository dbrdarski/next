//! The **AnalysisContract** abstract domain — the analyzer core, §2 of the
//! Application & Induction package (v0.8.1). This lands first: every analyzer-state
//! key is annotated, so the transfer rule (§1, the application rule) and the
//! induction machinery (§4/§6) are built over this domain.
//!
//! **Two-level semantics.** `erase(ac) = ac.contract` — the ordinary contract, whose
//! language denotation `⟦ac.contract⟧` is untouched. **`γ(ac) ⊆ ⟦ac.contract⟧`** is
//! the *analyzer concretization*: the runtime values the complete annotated contract
//! represents, metadata included. A **non-function** member of `⟦ac.contract⟧` is
//! always in γ (metadata is vacuous off function positions); a **function** member
//! is in γ only if the metadata admits it — *every* function under `Unknown`, or a
//! function **realizing** some instance under `Known(S)` (its μ-canonical shape
//! matches, and each captured value lies in the γ of the matching annotated capture,
//! recursively). Hence `Known(∅)` admits no function: `(C, Known(∅))` with `C`
//! function-only, and `(Bottom, _)`, both concretize to `∅` — normalized to the one
//! canonical bottom.
//!
//! **The metadata lattice.** `Known(∅)` = no function is possible here (a dead
//! branch — feeds emptiness); `Unknown` = a function is possible, origins coarsened
//! away. Join is `∪`; the analyzer conjunction is [`intersect_a`], sound by
//! containment (`γ(A) ∩ γ(B) ⊆ γ(intersect_a(A, B))`), returning an exact
//! representable meet **only when the fixed rules construct and certify one** (the
//! coverage-normalized same-shape [`meet_instance`]), else a conservative
//! over-approximation — never a semantic oracle. The annotated order is
//! `AC₁ ⊑ᴬ AC₂ ⇔ γ(AC₁) ⊆ γ(AC₂)`, decided by the three-valued, deliberately
//! incomplete [`prove_subcontract_a`] (ordinary inclusion × metadata coverage).

use crate::ast::Lambda;
use crate::contract::{Contract, Kind, Verdict, subcontract};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

/// An **analysis instance**: a function's μ-canonical shape (the node label,
/// compared structurally) plus its **annotated** captured environment — one
/// [`AnalysisContract`] per capture slot, in the shape's `free_vars` order.
/// Captures may themselves carry function metadata, so γ recurses through `env`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Instance {
    pub shape: Lambda,
    pub env: Vec<AnalysisContract>,
}

impl Instance {
    /// Proven-empty when any captured position is the canonical bottom — no closure
    /// of this shape can realize it (metadata normalization, §2).
    pub fn is_empty(&self) -> bool {
        self.env.iter().any(AnalysisContract::is_bottom)
    }
}

/// The instance-metadata lattice element (§2).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum InstanceMetadata {
    /// A finite set of instances — the functions possible here, with origins. The
    /// empty set is the dead branch (no function possible).
    Known(Vec<Instance>),
    /// A function is possible, origins coarsened away.
    Unknown,
}

/// A contract paired with function-position metadata — the abstract-domain element.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AnalysisContract {
    pub contract: Contract,
    pub metadata: InstanceMetadata,
}

impl AnalysisContract {
    /// The canonical bottom (`γ = ∅`): `(Bottom, Known(∅))`.
    pub fn bottom() -> AnalysisContract {
        AnalysisContract { contract: Contract::Bottom, metadata: InstanceMetadata::Known(vec![]) }
    }

    /// A plain contract with coarsened metadata `(C, Unknown)`, normalized.
    pub fn of_contract(contract: Contract) -> AnalysisContract {
        AnalysisContract::new(contract, InstanceMetadata::Unknown)
    }

    /// Construct and **normalize** to the one canonical key per empty concretization
    /// (§2): `(Bottom, _) → bottom`, and `(C, Known(∅)) → bottom` when `C` is
    /// function-only (its γ then has no members at all).
    pub fn new(contract: Contract, metadata: InstanceMetadata) -> AnalysisContract {
        if matches!(contract, Contract::Bottom) {
            return AnalysisContract::bottom();
        }
        if matches!(&metadata, InstanceMetadata::Known(s) if s.is_empty()) && is_function_only(&contract) {
            return AnalysisContract::bottom();
        }
        AnalysisContract { contract, metadata }
    }

    /// `γ(ac) = ∅` — the canonical bottom (contract `Bottom`).
    pub fn is_bottom(&self) -> bool {
        matches!(self.contract, Contract::Bottom)
    }
}

/// Whether `⟦c⟧ ⊆ Functions` — the only case where `Known(∅)` empties the whole
/// concretization (off function positions the metadata is vacuous).
fn is_function_only(c: &Contract) -> bool {
    // Value-free: no interner is needed to see a Kind/Bottom is function-only.
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
/// (recursively). A capture bound to a slot / under-init is treated conservatively
/// as unrealized (a sound under-approximation of γ for membership).
pub fn realizes(v: &ValueRef, i: &Instance, interner: &mut Interner) -> bool {
    let Some(f) = v.as_fn() else { return false };
    if f.shape() != &i.shape {
        return false;
    }
    if f.free_vars().len() != i.env.len() {
        return false;
    }
    for (name, cap) in f.free_vars().iter().zip(&i.env) {
        match f.closure().env.lookup(name) {
            Some(Binding::Value(cv)) => {
                if !gamma_contains(cap, &cv, interner) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// Whether `v ∈ γ(ac)`. Non-functions are governed by the ordinary contract alone;
/// functions must additionally be admitted by the metadata.
pub fn gamma_contains(ac: &AnalysisContract, v: &ValueRef, interner: &mut Interner) -> bool {
    if !ac.contract.contains(v) {
        return false;
    }
    if !v.is_function() {
        return true;
    }
    match &ac.metadata {
        InstanceMetadata::Unknown => true,
        InstanceMetadata::Known(s) => s.iter().any(|i| realizes(v, i, interner)),
    }
}

// ── The metadata lattice ─────────────────────────────────────────────────────

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

// ── intersectA / meetInstance ────────────────────────────────────────────────

/// The analyzer conjunction — sound by containment only: `γ(A) ∩ γ(B) ⊆
/// γ(intersect_a(A, B))`. Its result is an **exact representable meet only when the
/// fixed rules construct and certify one**; otherwise a conservative
/// over-approximation (no lower-bound or idempotence reasoning may be applied to it,
/// §2). The metadata meet:
/// - `Unknown ∩ M = M` (Unknown is the top);
/// - `Known(S) ∩ Known(T)` = the coverage-normalized same-shape meets — for each
///   compatible pair keep the covered instance (`s ⊑ t ⇒ s`, `t ⊑ s ⇒ t`), else the
///   [`meet_instance`] of genuinely overlapping environments.
pub fn intersect_a(a: &AnalysisContract, b: &AnalysisContract, interner: &mut Interner) -> AnalysisContract {
    let contract = Contract::Intersection(Box::new(a.contract.clone()), Box::new(b.contract.clone()));
    let metadata = match (&a.metadata, &b.metadata) {
        (InstanceMetadata::Unknown, m) | (m, InstanceMetadata::Unknown) => m.clone(),
        (InstanceMetadata::Known(s), InstanceMetadata::Known(t)) => {
            let mut out: Vec<Instance> = Vec::new();
            for si in s {
                for ti in t {
                    if si.shape != ti.shape {
                        continue;
                    }
                    let meet = if matches!(instance_covers(si, ti, interner), Verdict::Proven) {
                        Some(si.clone()) // s ⊑ t — the tighter instance is the meet
                    } else if matches!(instance_covers(ti, si, interner), Verdict::Proven) {
                        Some(ti.clone())
                    } else {
                        meet_instance(si, ti, interner) // genuine partial overlap
                    };
                    match meet {
                        Some(m) if !m.is_empty() && !out.contains(&m) => out.push(m),
                        _ => {}
                    }
                }
            }
            InstanceMetadata::Known(out)
        }
    };
    AnalysisContract::new(contract, metadata)
}

/// The same-shape environment meet. `None` when shapes differ, or when the
/// environment intersection is **proven** empty (a captured position becomes the
/// canonical bottom). Never mints a meet from a mere key mismatch (§2, round 5).
pub fn meet_instance(i: &Instance, j: &Instance, interner: &mut Interner) -> Option<Instance> {
    if i.shape != j.shape || i.env.len() != j.env.len() {
        return None;
    }
    let mut env = Vec::with_capacity(i.env.len());
    for (a, b) in i.env.iter().zip(&j.env) {
        let m = intersect_a(a, b, interner);
        if m.is_bottom() {
            return None; // environment intersection proven empty
        }
        env.push(m);
    }
    Some(Instance { shape: i.shape.clone(), env })
}

// ── proveSubcontractA — the annotated three-valued subcontract ────────────────

/// The analyzer judgment for `AC₁ ⊑ᴬ AC₂` (semantically `γ(AC₁) ⊆ γ(AC₂)`) —
/// sound, deliberately incomplete, three-valued. `Proven` requires ordinary-contract
/// inclusion **and** metadata coverage; a `Refuted` witness must be γ-representable
/// (a bare contract counterexample outside γ(AC₁) is downgraded to `Unproven`).
pub fn prove_subcontract_a(a: &AnalysisContract, b: &AnalysisContract, interner: &mut Interner) -> Verdict {
    // A refutation only counts when the witness is actually in γ(AC₁) ∖ γ(AC₂).
    let base = subcontract(&a.contract, &b.contract, interner);
    match &base {
        Verdict::Refuted(w) if gamma_contains(a, w, interner) => return Verdict::Refuted(w.clone()),
        _ => {}
    }
    if matches!(base, Verdict::Proven) && matches!(covers(&a.metadata, &b.metadata, interner), Verdict::Proven) {
        return Verdict::Proven;
    }
    Verdict::Unproven
}

/// Metadata coverage — the `Known(S) ⊑ Known(T)` triage (§2, round 5). Proven-empty
/// sources are ignored; every other source (including uncertain inhabitance, never
/// silently skipped) requires a target instance of the same shape whose annotated
/// environment covers it (`⊑ᴬ` recursively). Incomplete: an uncovered source yields
/// `Unproven`, never a manufactured refutation.
fn covers(s: &InstanceMetadata, t: &InstanceMetadata, interner: &mut Interner) -> Verdict {
    match (s, t) {
        (_, InstanceMetadata::Unknown) => Verdict::Proven, // Known(S) ⊑ Unknown; Unknown ⊑ Unknown
        (InstanceMetadata::Unknown, InstanceMetadata::Known(_)) => Verdict::Unproven,
        (InstanceMetadata::Known(src), InstanceMetadata::Known(tgt)) => {
            for si in src {
                if si.is_empty() {
                    continue; // proven-empty source ignored
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
/// So `instance(shape, Equals(1)) ⊑ instance(shape, Range(1,5))` despite distinct
/// keys — coverage is over γ, not over syntactic environment identity.
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
