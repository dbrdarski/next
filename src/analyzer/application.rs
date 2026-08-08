//! The application transfer rule (§1) — the **outcome algebra** and the **joint
//! operand driver**.
//!
//! `analyzeOperation(application, AC_operands)` receives **one joint correlated**
//! [`AnalysisContract`] denoting `[callee, …arguments]` tuples, and processes it
//! **per live correlated alternative** — so a correlated union like `[numFn, 5] |
//! [strFn, "hi"]` is handled as `(numFn, 5)` OR `(strFn, "hi")`, never as the
//! synthesized cross-pairs `(numFn, "hi")` / `(strFn, 5)`. A **projecting** operand
//! (correlation already flattened positionally) is permitted, but any failure that
//! arises only from a synthesized cross-pair degrades to **unproven, never refuted**
//! (AP-29).
//!
//! This module carries the outcome algebra (steps 1/5/6/7 — admission, the summary
//! shape, the three-voiced completion demand, union of callees) and the one
//! per-alternative traversal, [`drive_application`]. [`analyze_application`] is its thin
//! admission/input-obligation facade. Computing a single instance's summary from its
//! body (steps 2–4) remains fact machinery supplied to the driver by the expression
//! adapter; it is not reimplemented here.

use crate::analyzer::domain::{AnalysisContract, InstanceMetadata};
use crate::ast::ActKind;
use crate::contract::{Contract, Kind, Verdict, disjoint};
use crate::interner::Interner;
use crate::value::ValueRef;

/// A **represented application execution** — the structural refutation / fall-through
/// witness (checkpoint review §7). A witness is a concrete callee applied to concrete
/// arguments, never a bare token or two independently plausible values.
#[derive(Clone, Debug)]
pub struct ApplicationWitness {
    pub callee: ValueRef,
    pub arguments: Vec<ValueRef>,
}

/// Whether a **completed-without-value** (fall-through, E10) execution is present
/// (§1.5, tri-state — round 4).
///
/// This is the application layer's face of the expression layer's
/// [`crate::analyzer::Completion`]; the two are deliberately distinct types
/// (Tier-4 reviewed, not merged): §1.5/AP-29 admit **only a jointly-represented
/// application witness** into `ProvenPresent`, so the conversion
/// [`CompletionWithoutValue::of`] narrows every other witness class to the third
/// voice, and the type system keeps that discipline from eroding.
#[derive(Clone, Debug)]
pub enum CompletionWithoutValue {
    /// `(E × A) ∩ Row = ∅` for every fall-through row — the product proves *absence*.
    ProvenAbsent,
    /// A fall-through is present, witnessed by a **jointly-represented** completing
    /// execution (never a synthesized cross-pair, §1.5 / AP-29).
    ProvenPresent(ApplicationWitness),
    /// A live fall-through row whose intersection is not proven empty, but whose joint
    /// inhabitance is not proved — the third voice.
    UnprovenPossible,
}

impl CompletionWithoutValue {
    /// The canonical narrowing from the expression layer (AP-29): an application
    /// witness crosses; a match-remainder or write witness — represented at its own
    /// layer but not a joint application execution — does **not**, and becomes the
    /// third voice here.
    pub fn of(completion: crate::analyzer::Completion) -> CompletionWithoutValue {
        use crate::analyzer::{Completion, CompletionWitness};
        match completion {
            Completion::Produces => CompletionWithoutValue::ProvenAbsent,
            Completion::FallsThrough(CompletionWitness::Application(witness)) => {
                CompletionWithoutValue::ProvenPresent(witness)
            }
            Completion::MayFallThrough | Completion::FallsThrough(_) => {
                CompletionWithoutValue::UnprovenPossible
            }
        }
    }
}

/// The application outcome summary (§1.5). `produced = Bottom` only when the absence
/// of every `Produced` outcome is proven — grayness never implies Bottom.
#[derive(Clone, Debug)]
pub struct ApplicationOutcome {
    pub produced: AnalysisContract,
    pub completion: CompletionWithoutValue,
    /// At least one represented execution may not complete — a conservative
    /// possibility feeding **no** safety verdict, so it needs no divergence witness.
    pub may_not_complete: bool,
}

impl ApplicationOutcome {
    /// The identity of the union join (§1.7) — the `Known(∅)` cached core.
    pub fn empty() -> ApplicationOutcome {
        ApplicationOutcome {
            produced: AnalysisContract::bottom(),
            completion: CompletionWithoutValue::ProvenAbsent,
            may_not_complete: false,
        }
    }
}

/// The three-valued verdict of a **seat** demand or the application driver, carrying a
/// **structural** witness on refutation (never a bare value).
pub type SeatVerdict = crate::contract::Voice<ApplicationWitness>;

/// The union of two produced contracts (§1.7): the correlated union — a structural
/// `Alt` that keeps each branch's internal correlation.
pub fn union_ac(a: &AnalysisContract, b: &AnalysisContract) -> AnalysisContract {
    if a.is_bottom() {
        return b.clone();
    }
    if b.is_bottom() {
        return a.clone();
    }
    AnalysisContract::alt(vec![a.clone(), b.clone()])
}

/// The evidence-preserving completion join (§1.7): any `ProvenPresent` dominates with
/// its witness; else any `UnprovenPossible`; else `ProvenAbsent`.
fn join_completion(a: CompletionWithoutValue, b: CompletionWithoutValue) -> CompletionWithoutValue {
    match (a, b) {
        (CompletionWithoutValue::ProvenPresent(w), _) => CompletionWithoutValue::ProvenPresent(w),
        (_, CompletionWithoutValue::ProvenPresent(w)) => CompletionWithoutValue::ProvenPresent(w),
        (CompletionWithoutValue::UnprovenPossible, _)
        | (_, CompletionWithoutValue::UnprovenPossible) => CompletionWithoutValue::UnprovenPossible,
        _ => CompletionWithoutValue::ProvenAbsent,
    }
}

/// The union of callees (§1.7): summaries join componentwise.
pub fn join(a: ApplicationOutcome, b: ApplicationOutcome) -> ApplicationOutcome {
    ApplicationOutcome {
        produced: union_ac(&a.produced, &b.produced),
        completion: join_completion(a.completion, b.completion),
        may_not_complete: a.may_not_complete || b.may_not_complete,
    }
}

/// Join a set of per-instance/per-alternative outcomes; the empty set folds to
/// [`ApplicationOutcome::empty`] — the `Known(∅)` identity.
pub fn join_all(outcomes: impl IntoIterator<Item = ApplicationOutcome>) -> ApplicationOutcome {
    outcomes.into_iter().fold(ApplicationOutcome::empty(), join)
}

/// The **completion demand** at the seat (§1.6) — three-voiced, seat-applied, never
/// cached. An expecting seat rejects *only* a witnessed fall-through; a statement seat
/// accepts all three. `may_not_complete` violates nothing.
pub fn seat_demand(outcome: &ApplicationOutcome, expecting: bool) -> SeatVerdict {
    if !expecting {
        return SeatVerdict::Proven;
    }
    match &outcome.completion {
        CompletionWithoutValue::ProvenAbsent => SeatVerdict::Proven,
        CompletionWithoutValue::ProvenPresent(w) => SeatVerdict::Refuted(w.clone()),
        CompletionWithoutValue::UnprovenPossible => SeatVerdict::Unproven,
    }
}

/// **Act-kind admission** in the seat's world (§1.1). Over `Known(S)` every non-empty
/// member's act-kind must be admitted (`Known(∅)` vacuous); over `Unknown` → unproven.
/// An inadmissible member is unproven at this layer (the witness-backed refutation
/// needs a represented closure — the tail).
pub fn admit_callee(meta: &InstanceMetadata, world_admits: impl Fn(ActKind) -> bool) -> Verdict {
    match meta {
        InstanceMetadata::Unknown => Verdict::Unproven,
        InstanceMetadata::Known(s) => {
            let all_admitted = s
                .iter()
                .filter(|i| !i.is_empty())
                .all(|i| world_admits(i.act_kind()));
            if all_admitted {
                Verdict::Proven
            } else {
                Verdict::Unproven
            }
        }
    }
}

/// The pure-world admission predicate: only `Pure` act-kinds are admitted (B4).
pub fn pure_world_admits(kind: ActKind) -> bool {
    matches!(kind, ActKind::Pure)
}

// ── The joint operand driver (§1, per live alternative) ───────────────────────

/// One **live correlated alternative** of the joint operand state — a `[callee,
/// …arguments]` tuple whose callee⟷argument correlation is preserved.
#[derive(Clone, Debug)]
pub struct Alternative {
    pub callee: AnalysisContract,
    pub arguments: Vec<AnalysisContract>,
}

/// Total classification of one erased callee leaf. This is shared by the expression
/// bridge and its fact callback so a union member can never disappear between operand
/// construction and transfer.
#[derive(Clone, Debug)]
pub(crate) enum CalleeAlternative {
    Known(ValueRef),
    UnknownFunction,
    NotAFunction { inhabited: bool },
}

/// Classify every live leaf of an erased callee contract exactly once. `Bottom` is the
/// empty list; unions preserve source order; every other leaf is known, unknown-function,
/// or proven non-function.
pub(crate) fn classify_callees(
    contract: &Contract,
    interner: &mut Interner,
) -> Vec<CalleeAlternative> {
    fn go(contract: &Contract, out: &mut Vec<CalleeAlternative>, interner: &mut Interner) {
        match contract {
            Contract::Union(a, b) => {
                go(a, out, interner);
                go(b, out, interner);
            }
            Contract::Bottom => {}
            Contract::Equals(value)
                if value.is_function()
                    || value
                        .as_native()
                        .is_some_and(|native| native.get().act_kind == ActKind::Effect) =>
            {
                out.push(CalleeAlternative::Known(value.clone()));
            }
            _ if disjoint(contract, &Contract::Kind(Kind::Function)) => {
                out.push(CalleeAlternative::NotAFunction {
                    inhabited: contract.has_proven_inhabitant(interner),
                });
            }
            _ => out.push(CalleeAlternative::UnknownFunction),
        }
    }

    let mut out = Vec::new();
    go(contract, &mut out, interner);
    out
}

/// Form the joint application operand from annotated source positions. Callee unions
/// become alternatives, while argument alternatives remain positional unless a caller
/// supplies an already-correlated `Alt(Tuple(...))`. That distinction is AP-29's
/// represented-vs-projected boundary.
pub(crate) fn operand_from_annotated(
    callee: &AnalysisContract,
    arguments: &[AnalysisContract],
) -> AnalysisContract {
    let alternatives = callee_branches(callee)
        .into_iter()
        .map(|callee| {
            let mut positions = Vec::with_capacity(arguments.len() + 1);
            positions.push(callee);
            positions.extend(arguments.iter().cloned());
            AnalysisContract::tuple(positions)
        })
        .collect();
    AnalysisContract::alt(alternatives)
}

fn callee_branches(callee: &AnalysisContract) -> Vec<AnalysisContract> {
    match callee {
        AnalysisContract::Bottom => Vec::new(),
        AnalysisContract::Alt(alternatives) => {
            alternatives.iter().flat_map(callee_branches).collect()
        }
        AnalysisContract::Leaf {
            contract, metadata, ..
        } => match contract {
            Contract::Union(left, right) => [left, right]
                .into_iter()
                .flat_map(|branch| {
                    callee_branches(&AnalysisContract::leaf(
                        (**branch).clone(),
                        metadata.clone(),
                    ))
                })
                .collect(),
            _ => vec![callee.clone()],
        },
        AnalysisContract::Tuple(_) | AnalysisContract::Record(_) => vec![callee.clone()],
    }
}

/// One alternative's contribution to the canonical application driver. The caller
/// supplies the evidence-producing work (input facts, body facts, diagnostics); the
/// driver owns traversal, projection discipline, and joins.
#[derive(Clone, Debug)]
pub struct AlternativeContribution<T> {
    pub verdict: SeatVerdict,
    pub outcome: ApplicationOutcome,
    pub detail: T,
}

/// The aggregate produced by [`drive_application`]. `details` remain in alternative
/// order so the expression adapter can retain precise diagnostics without re-walking
/// the operand.
#[derive(Clone, Debug)]
pub struct ApplicationTransfer<T> {
    pub verdict: SeatVerdict,
    pub outcome: ApplicationOutcome,
    pub details: Vec<T>,
}

/// Extract the live correlated alternatives of a joint operand denoting `[callee,
/// …arguments]`, and whether they are **correlated**:
/// - an `Alt` of tuples → one alternative per branch, **correlated**;
/// - a bare `Tuple([callee, args…])` with no positional `Alt` → one alternative,
///   **correlated**;
/// - a `Tuple` carrying positional `Alt`s (correlation already flattened) → the
///   **cross-product** of the positions, **not correlated** — a projecting read whose
///   failures the driver must degrade;
/// - anything else → no analyzable alternatives (unproven).
pub fn live_alternatives(operand: &AnalysisContract) -> (Vec<Alternative>, bool) {
    match operand {
        AnalysisContract::Alt(branches) => {
            let mut out = Vec::new();
            let mut correlated = true;
            for b in branches {
                let (alts, c) = live_alternatives(b);
                correlated &= c;
                out.extend(alts);
            }
            (out, correlated)
        }
        AnalysisContract::Tuple(elems) if !elems.is_empty() => {
            if elems.iter().any(|e| matches!(e, AnalysisContract::Alt(_))) {
                // Projected form: expand the positional cross-product (uncorrelated).
                let positions: Vec<Vec<AnalysisContract>> = elems
                    .iter()
                    .map(|e| match e {
                        AnalysisContract::Alt(bs) => bs.clone(),
                        other => vec![other.clone()],
                    })
                    .collect();
                let combos = cross_product(&positions);
                let out = combos
                    .into_iter()
                    .map(|combo| Alternative {
                        callee: combo[0].clone(),
                        arguments: combo[1..].to_vec(),
                    })
                    .collect();
                (out, false)
            } else {
                let alt = Alternative {
                    callee: elems[0].clone(),
                    arguments: elems[1..].to_vec(),
                };
                (vec![alt], true)
            }
        }
        _ => (vec![], false),
    }
}

/// The Cartesian product of per-position choice lists.
fn cross_product(positions: &[Vec<AnalysisContract>]) -> Vec<Vec<AnalysisContract>> {
    let mut combos: Vec<Vec<AnalysisContract>> = vec![vec![]];
    for choices in positions {
        let mut next = Vec::new();
        for prefix in &combos {
            for choice in choices {
                let mut row = prefix.clone();
                row.push(choice.clone());
                next.push(row);
            }
        }
        combos = next;
    }
    combos
}

/// The one application-alternative driver. It extracts each live joint alternative,
/// asks the caller for that alternative's fact-backed contribution, applies AP-29/AP-30
/// projection weakening once, and joins both the seat verdict and complete outcome.
///
/// A canonical `Bottom` operand represents no execution and therefore contributes the
/// empty/vacuous identity. A non-bottom value with no analyzable tuple structure remains
/// the honest third voice with a coarse outcome.
pub fn drive_application<T>(
    operand: &AnalysisContract,
    mut contribute: impl FnMut(&Alternative, bool) -> AlternativeContribution<T>,
) -> ApplicationTransfer<T> {
    let (alternatives, correlated) = live_alternatives(operand);
    if alternatives.is_empty() {
        if operand.is_bottom() {
            return ApplicationTransfer {
                verdict: SeatVerdict::Proven,
                outcome: ApplicationOutcome::empty(),
                details: Vec::new(),
            };
        }
        return ApplicationTransfer {
            verdict: SeatVerdict::Unproven,
            outcome: ApplicationOutcome {
                produced: AnalysisContract::of_contract(crate::contract::Contract::Top),
                completion: CompletionWithoutValue::UnprovenPossible,
                may_not_complete: true,
            },
            details: Vec::new(),
        };
    }

    let mut verdict = SeatVerdict::Proven;
    let mut outcome = ApplicationOutcome::empty();
    let mut details = Vec::with_capacity(alternatives.len());
    for alternative in &alternatives {
        let mut contribution = contribute(alternative, correlated);
        if !correlated {
            contribution.verdict = degrade(contribution.verdict);
            contribution.outcome = degrade_outcome(contribution.outcome);
        }
        verdict = conj(verdict, contribution.verdict);
        outcome = join(outcome, contribution.outcome);
        details.push(contribution.detail);
    }
    ApplicationTransfer {
        verdict,
        outcome,
        details,
    }
}

/// A projecting read may discover a fall-through only on a synthesized cross-pair.
/// Presence therefore weakens to possibility; absence, produced values, and the
/// conservative non-completion flag remain sound under projection.
fn degrade_outcome(mut outcome: ApplicationOutcome) -> ApplicationOutcome {
    if matches!(outcome.completion, CompletionWithoutValue::ProvenPresent(_)) {
        outcome.completion = CompletionWithoutValue::UnprovenPossible;
    }
    outcome
}

/// Analyze the application over the joint operand state (§1, steps 1 + 3, per live
/// alternative). For each alternative: act-kind admission over the callee metadata,
/// then the input obligation via `accepts` (the args accepted by the callee). The
/// verdict is **conjunctive** across alternatives (the operand may be any of them at
/// runtime). Correlated alternatives may refute with their witness; an **uncorrelated
/// (projected)** operand degrades every obligation failure to `Unproven` — never a
/// refutation from a synthesized cross-pair (AP-29).
pub fn analyze_application(
    operand: &AnalysisContract,
    world_admits: impl Fn(ActKind) -> bool + Copy,
    accepts: impl Fn(&AnalysisContract, &[AnalysisContract]) -> SeatVerdict,
) -> SeatVerdict {
    drive_application(operand, |alt, _| {
        let admit = match admit_callee(&callee_metadata(&alt.callee), world_admits) {
            Verdict::Proven => SeatVerdict::Proven,
            _ => SeatVerdict::Unproven, // admission never refutes at this layer
        };
        AlternativeContribution {
            verdict: conj(admit, accepts(&alt.callee, &alt.arguments)),
            outcome: ApplicationOutcome::empty(),
            detail: (),
        }
    })
    .verdict
}

/// The callee's metadata (for admission). A `Leaf` carries it directly; any other
/// shape coarsens to `Unknown` (no proven callee set).
fn callee_metadata(callee: &AnalysisContract) -> InstanceMetadata {
    match callee {
        AnalysisContract::Leaf { metadata, .. } => metadata.clone(),
        _ => InstanceMetadata::Unknown,
    }
}

/// Conjunction of seat verdicts: both proven → proven; any refuted → that refutation;
/// else unproven.
fn conj(a: SeatVerdict, b: SeatVerdict) -> SeatVerdict {
    match (a, b) {
        (SeatVerdict::Refuted(w), _) => SeatVerdict::Refuted(w),
        (_, SeatVerdict::Refuted(w)) => SeatVerdict::Refuted(w),
        (x, y) if x.is_proven() && y.is_proven() => SeatVerdict::Proven,
        _ => SeatVerdict::Unproven,
    }
}

/// Degrade a refutation to unproven (the projected-operand rule, AP-29).
fn degrade(v: SeatVerdict) -> SeatVerdict {
    match v {
        SeatVerdict::Refuted(_) => SeatVerdict::Unproven,
        other => other,
    }
}
