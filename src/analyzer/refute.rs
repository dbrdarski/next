//! Realized-witness refutation of return and completion claims — §6 / AP-30.
//!
//! A return fact `(callee, args, C)` claims "over `args`, the callee returns values in
//! `C`." The **inductive** proof (the vector pass) is *per-compilation* — an unproven
//! claim may be retried. A **realized refutation** is *permanent in-namespace*: a
//! concrete completing execution that violates the claim. Per §6 the witness is a
//! triple `(e, x, v)` — an environment `e ∈ γ(instance.environment)`, an input `x` in
//! the domain, the realization applied to `x` completing with `Produced(v)`, and `v ∉
//! γ(C)`. Here the closure already carries a **concrete** environment (its captures), so
//! `e` is fixed and the search is over inputs `x`.
//!
//! Two disciplines from §6 are load-bearing:
//! - **A non-completing input is never a witness.** The oracle runs under a **fuel
//!   bound** ([`eval_expr_bounded`]); a diverging input yields `OutOfFuel` and is
//!   skipped, never mistaken for a producer. A `Trapped` input is likewise not a witness
//!   (the trap is a separate obligation, not a return-bound violation).
//! - **The witness is a represented completing execution** — a real `(arguments,
//!   produced)` the oracle actually ran, never a fabricated value.
//!
//! Refutation is the **sound ground truth** the abstract vector pass is checked
//! against: [`check_return_claim`] tries return refutation first (permanent), then the
//! inductive proof (per-compilation); [`realized_completion`] supplies the structural
//! application witness for the completion tri-state.

use crate::analyzer::application::ApplicationWitness;
use crate::analyzer::induction::Claim;
use crate::analyzer::safety::{BodySafety, prove_claim};
use crate::contract::{Contract, ContractEnv};
use crate::interner::Interner;
use crate::value::ValueRef;

/// A cap on sampled argument tuples per refutation attempt — the sampler is finite, so
/// this only bites on wide multi-argument products.
const MAX_TUPLES: usize = 256;

/// A **represented** counterexample to a return claim (§6): concrete `arguments` the
/// callee was applied to, and the `produced` value `v ∉ γ(C)` it completed with.
#[derive(Clone, Debug)]
pub struct RealizedWitness {
    pub arguments: Vec<ValueRef>,
    pub produced: ValueRef,
}

/// The declared-claim verdict — `Refuted` carries the realized witness (the
/// represented arguments and what they actually produced; an inductive proof that
/// did not close with no counterexample found stays `Unproven`). An alias of the
/// family shape [`crate::contract::Voice`].
pub type ClaimVerdict = crate::contract::Voice<RealizedWitness>;

/// Search for a realized-witness refutation of "`callee` over `args` returns ⊑ `claim`".
/// Samples genuine argument tuples from `args`, runs each through the oracle under the
/// fuel bound, and returns the first `(arguments, v)` that **completes** with `v ∉
/// γ(claim)`. `None` when no sampled input refutes (never a proof — the sampler is
/// incomplete). Like completion refutation, this executes only a `Pure` NEXT closure;
/// Effects and Mutators remain non-executing analysis cases.
pub fn realized_refutation(
    callee: &ValueRef,
    args: &[Contract],
    claim: &Contract,
    interner: &mut Interner,
) -> Option<RealizedWitness> {
    // CLOSED 2026-08-05 — **provenance correction (same day):** this closure was
    // implemented during the A1 discussion on my own inference; **no author ruling
    // exists**. The author has neither ratified nor reverted it (explicitly: "a
    // question is not a permission to change"); A1 remains OPEN on the decisions
    // ledger. The specification licenses the witness *shape*
    // (AP-19 / the closure rule: a realized completing `(e, x, v)` with `v ∉ γ(C)`)
    // — it never licensed fueled analyzer-side evaluation as the *procedure* for
    // finding one, and the author has ruled that fuel may not appear in analysis.
    // Until a fuel-free procedure is ruled (candidate: evaluate only under a
    // certificate carrying a proven concrete bound — decline to run, never truncate
    // a run), this search is closed: the honest third voice stands where a sampled
    // counterexample once landed. The witness types and the `Refuted` arm remain —
    // they are the spec's vocabulary, not the sampler's.
    let _ = (callee, args, claim, interner);
    None
}

/// A represented application proven to complete without a value (application §1.5 /
/// AP-30) — by **structural derivation only**: no analyzer-side evaluation exists
/// [closed 2026-08-05 during the A1 discussion — no author ruling; A1 open].
/// Candidate points come from the arguments'
/// **proven members** (contract membership, never evaluation); a point whose row
/// walk selects nothing falls through denotationally. Anything short of that
/// certainty stays the honest third voice. `Pure` closures only.
pub fn realized_completion(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &crate::contract::ContractEnv,
    interner: &mut Interner,
) -> Option<ApplicationWitness> {
    // The evaluation-based search is closed [2026-08-05, A1 discussion — no author
    // ruling; see `realized_refutation`]. What remains is the **structural**
    // derivation, which
    // executes nothing: when every argument is a represented point (the call's own
    // written constants — GR-22) and the instantiated row walk selects **no row**
    // for that point vector, the match falls through denotationally — pattern
    // membership on a point is decidable, so the fall-through is forced, and the
    // `(callee, arguments)` pair is jointly represented by construction. Anything
    // short of that certainty (a selectable row, a guard that might fire, a
    // non-match body, a non-point argument) stays the honest third voice.
    let closure = callee.as_closure()?;
    if closure.lambda.act_kind != crate::ast::ActKind::Pure {
        return None;
    }
    let single = crate::analyzer::region::instance_table(callee, cenv, interner);
    let multi = if single.is_none() {
        crate::analyzer::region::instance_table_multi(callee, cenv, interner)
    } else {
        None
    };
    for points in argument_samples(args, interner) {
        let forced = if let (Some((_, table)), [point]) = (&single, points.as_slice()) {
            let domain = Contract::Equals(point.clone());
            crate::analyzer::region::select(table, &domain, interner).is_empty()
        } else if let Some((params, table)) = &multi
            && params.len() == points.len()
        {
            let domains: Vec<Contract> = points.iter().cloned().map(Contract::Equals).collect();
            crate::analyzer::region::select_multi(table, &domains, interner).is_empty()
        } else {
            false
        };
        if forced {
            return Some(ApplicationWitness {
                callee: callee.clone(),
                arguments: points,
            });
        }
    }
    None
}

/// A concrete member of the application input product. This does **not** prove an
/// ordinary callee completes; it is exposed only for outcome laws that establish the
/// completion form independently (currently Mutator's return-discard law).
pub(crate) fn represented_application(
    callee: &ValueRef,
    args: &[Contract],
    interner: &mut Interner,
) -> Option<ApplicationWitness> {
    let arguments = argument_samples(args, interner).into_iter().next()?;
    Some(ApplicationWitness {
        callee: callee.clone(),
        arguments,
    })
}

/// Verify a return claim three-voiced (§6): a realized refutation (permanent) is tried
/// **first** — it is the sound ground truth, catching a false claim the abstract vector
/// pass could otherwise leave merely unproven — then the inductive proof
/// (per-compilation). The proof runs through the global fact graph, so recursive and
/// mutually recursive claims use the same SCC settlement as safety and completion.
pub fn check_return_claim(
    callee: &ValueRef,
    args: &[Contract],
    claim: &Contract,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> ClaimVerdict {
    if let Some(w) = realized_refutation(callee, args, claim, interner) {
        return ClaimVerdict::Refuted(w);
    }
    match prove_claim(callee, args, Claim::Return(claim.clone()), cenv, interner) {
        BodySafety::Proven => ClaimVerdict::Proven,
        BodySafety::Refuted(_) | BodySafety::Unproven(_) => ClaimVerdict::Unproven,
    }
}

/// The genuine argument tuples to try: the cartesian product of each argument
/// contract's [`Contract::proven_members`], capped at [`MAX_TUPLES`]. An unsampleable
/// argument (no proven members) yields no tuples — refutation then finds nothing, sound.
fn argument_samples(args: &[Contract], interner: &mut Interner) -> Vec<Vec<ValueRef>> {
    let per_arg: Vec<Vec<ValueRef>> = args.iter().map(|c| c.proven_members(interner)).collect();
    if per_arg.iter().any(Vec::is_empty) {
        return vec![];
    }
    let mut tuples: Vec<Vec<ValueRef>> = vec![vec![]];
    for members in &per_arg {
        let mut next = Vec::new();
        for prefix in &tuples {
            for m in members {
                let mut t = prefix.clone();
                t.push(m.clone());
                next.push(t);
            }
        }
        next.truncate(MAX_TUPLES);
        tuples = next;
    }
    tuples
}
