//! The application transfer rule (§1) — the **outcome algebra**.
//!
//! `analyzeOperation(application, AC_operands)` combines the per-instance outcomes of
//! a call site into one seat verdict. This module is the algebra of that combination
//! — steps **1** (act-kind admission), **5** (the outcome summary), **6** (the
//! three-voiced completion demand), and **7** (union of callees) — as pure,
//! seat-applied combinators over the [`AnalysisContract`] domain.
//!
//! What is **not** here yet: computing a single instance's summary from its body
//! (steps 2–4 — instance resolution, the `E × A` input obligation, row selection).
//! That requires the constructed instance inventory (§4) and the candidate graph
//! (§6) so recursive callees are summarized soundly under the cutoff, and lands with
//! 8.1c. Until then the existing `analyze_apply` stays as the sound coarse path
//! (return `Top`); this algebra is unit-tested against synthetic per-instance
//! summaries, exactly as the domain layer was.

use crate::analyzer::domain::{AnalysisContract, InstanceMetadata};
use crate::ast::ActKind;
use crate::contract::{Contract, Verdict};
use crate::value::ValueRef;

/// Whether a **completed-without-value** (fall-through, E10) execution is present
/// (§1.5, tri-state — round 4). A Boolean erased the three-voice distinction between
/// a witnessed fall-through and a merely-undisproved live row.
#[derive(Clone, Debug)]
pub enum CompletionWithoutValue {
    /// `(E × A) ∩ Row = ∅` for every fall-through row — the product legitimately
    /// proves *absence*.
    ProvenAbsent,
    /// A fall-through is present, witnessed by a **jointly-represented** completing
    /// execution (never a synthesized cross-pair, §1.5 / AP-29).
    ProvenPresent(ValueRef),
    /// A live fall-through row whose intersection is not proven empty, but whose
    /// joint inhabitance is not proved — the third voice.
    UnprovenPossible,
}

/// The application outcome summary (§1.5). `produced = Bottom` only when the absence
/// of every `Produced` outcome is proven (empty selection, all rows fall-through, or
/// all rows proven non-completing) — **grayness never implies Bottom**.
#[derive(Clone, Debug)]
pub struct ApplicationOutcome {
    pub produced: AnalysisContract,
    pub completion: CompletionWithoutValue,
    /// At least one represented execution may not complete (E10's triple) — a
    /// conservative possibility feeding **no** safety verdict, so it needs no
    /// divergence witness.
    pub may_not_complete: bool,
}

impl ApplicationOutcome {
    /// The identity of the union join (§1.7) — the `Known(∅)` cached core: absence
    /// proven vacuously, no completion, complete. Also the summary of a call with no
    /// live callee.
    pub fn empty() -> ApplicationOutcome {
        ApplicationOutcome {
            produced: AnalysisContract::bottom(),
            completion: CompletionWithoutValue::ProvenAbsent,
            may_not_complete: false,
        }
    }
}

/// The union of two produced contracts (§1.7, produced-by-union). `Bottom` is the
/// identity; otherwise the ordinary-contract union with the metadata joined.
pub fn union_ac(a: &AnalysisContract, b: &AnalysisContract) -> AnalysisContract {
    if a.is_bottom() {
        return b.clone();
    }
    if b.is_bottom() {
        return a.clone();
    }
    AnalysisContract::new(
        Contract::Union(Box::new(a.contract.clone()), Box::new(b.contract.clone())),
        InstanceMetadata::join(&a.metadata, &b.metadata),
    )
}

/// The evidence-preserving completion join (§1.7): any `ProvenPresent` dominates with
/// its witness; else any `UnprovenPossible`; else `ProvenAbsent`.
fn join_completion(a: CompletionWithoutValue, b: CompletionWithoutValue) -> CompletionWithoutValue {
    match (a, b) {
        (CompletionWithoutValue::ProvenPresent(w), _) => CompletionWithoutValue::ProvenPresent(w),
        (_, CompletionWithoutValue::ProvenPresent(w)) => CompletionWithoutValue::ProvenPresent(w),
        (CompletionWithoutValue::UnprovenPossible, _) | (_, CompletionWithoutValue::UnprovenPossible) => {
            CompletionWithoutValue::UnprovenPossible
        }
        _ => CompletionWithoutValue::ProvenAbsent,
    }
}

/// The union of callees (§1.7): summaries join componentwise — produced by union,
/// completion by the evidence-preserving join, `may_not_complete` by `or`.
pub fn join(a: ApplicationOutcome, b: ApplicationOutcome) -> ApplicationOutcome {
    ApplicationOutcome {
        produced: union_ac(&a.produced, &b.produced),
        completion: join_completion(a.completion, b.completion),
        may_not_complete: a.may_not_complete || b.may_not_complete,
    }
}

/// Join a set of per-instance/per-alternative outcomes (§1.7). The empty set folds to
/// [`ApplicationOutcome::empty`] — the `Known(∅)` identity.
pub fn join_all(outcomes: impl IntoIterator<Item = ApplicationOutcome>) -> ApplicationOutcome {
    outcomes.into_iter().fold(ApplicationOutcome::empty(), join)
}

/// The **completion demand** at the seat (§1.6) — three-voiced, seat-applied, never
/// cached. An expecting seat (E10 `demand`) rejects only a *witnessed* fall-through;
/// a statement seat accepts all three. `may_not_complete` violates nothing anywhere.
pub fn seat_demand(outcome: &ApplicationOutcome, expecting: bool) -> Verdict {
    if !expecting {
        return Verdict::Proven; // statement seats accept ProvenAbsent / Present / Unproven
    }
    match &outcome.completion {
        CompletionWithoutValue::ProvenAbsent => Verdict::Proven,
        CompletionWithoutValue::ProvenPresent(w) => Verdict::Refuted(w.clone()),
        CompletionWithoutValue::UnprovenPossible => Verdict::Unproven,
    }
}

/// **Act-kind admission** in the seat's world (§1.1) — the one world-dependent step,
/// applied at the seat, outside the cache. Over `Known(S)`: every non-empty member
/// admitted by `world_admits` → proven; `Known(∅)` passes **vacuously** (no
/// represented application exists — the seat's unreachability is emptiness's
/// diagnostic, not admission's refutation). Over `Unknown`: **unproven** — no witness
/// can exist, and coarsening never invents evidence. An inadmissible member refutes
/// only with an inhabitance-backed **represented-closure** witness; the algebra layer
/// carries none, so an inadmissible member lands `unproven` here — the witness-backed
/// refutation arrives with real callees in 8.1c.
pub fn admit_callee(meta: &InstanceMetadata, world_admits: impl Fn(ActKind) -> bool) -> Verdict {
    match meta {
        InstanceMetadata::Unknown => Verdict::Unproven,
        InstanceMetadata::Known(s) => {
            let all_admitted = s
                .iter()
                .filter(|i| !i.is_empty()) // a proven-empty member is dropped from S
                .all(|i| world_admits(i.shape.act_kind));
            if all_admitted {
                Verdict::Proven // includes Known(∅): the `all` is vacuously true
            } else {
                Verdict::Unproven
            }
        }
    }
}

/// The pure-world admission predicate (the analysis world for pure seats): only
/// `Pure` act-kinds are admitted (B4 — a mutator/effect call is inadmissible in the
/// pure world).
pub fn pure_world_admits(kind: ActKind) -> bool {
    matches!(kind, ActKind::Pure)
}
