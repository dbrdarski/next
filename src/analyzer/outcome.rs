//! Per-instance **outcome contribution** (§1 steps 4–5) — the callee body summary.
//!
//! A single instance's [`ApplicationOutcome`] is read off its body: bind the captures
//! and the argument-narrowed parameters, then analyze the body. The existing Match
//! analysis (E9/E10) already performs row selection — arm-by-arm narrowing, the
//! unioned produced contract, and the fall-through flag — so `summarize_instance`
//! maps its result:
//!
//! - **produced** = the body's inferred contract (the union over selected rows);
//! - **completion** = `ProvenAbsent` when the body always produces, else
//!   `UnprovenPossible` — **conservative here**: a *proven* fall-through is not yet
//!   promoted to `ProvenPresent` (the structured AP-30 witness is owed); the call site
//!   reads the finer three-voice `Completion` off [`analyze_instance_body`] directly.
//!
//! **Recursion is coarse and terminating here.** A recursive/mutual call resolves its
//! callee to a captured `Equals(closure)`; with abstract (non-singleton) argument
//! contracts the call does not constant-fold, so `analyze_apply` returns `Top` for the
//! recursive result rather than re-entering the body. The summary is therefore sound
//! but coarse on recursion; the §6 return induction sharpens the recursive result from
//! `Top` to a proven contract under the induction hypothesis.
//!
//! `may_not_complete` (divergence) is left `false` — it feeds no safety verdict (§1.5)
//! and its precise value on a gray SCC is the §6 concern.

use crate::analyzer::application::{ApplicationOutcome, CompletionWithoutValue};
use crate::analyzer::domain::AnalysisContract;
use crate::analyzer::{Analysis, Completion, TypeEnv, analyze, bind_pattern};
use crate::contract::{Contract, ContractEnv};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

/// Analyze one instance's body in its environment — captures bound to their exact
/// values (`Equals`), parameters narrowed by the argument tuple — **coarsely**: the
/// guard keeps recursive/non-hypothesis calls resolving through the active hypotheses
/// or `Top`, never a nested inference, so the driver stays in control of fact-proving
/// (§6). `None` for a non-function. The shared core of the outcome summary and the
/// call-site completion read ([`crate::analyzer`]'s `callee_completion`).
pub(crate) fn analyze_instance_body(
    callee: &ValueRef,
    arg_contracts: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Analysis> {
    let closure = callee.as_closure()?;
    let free: Vec<String> = callee.as_fn()?.free_vars().to_vec();

    let mut tenv = TypeEnv::new();
    // Captures first, so a same-named parameter shadows them.
    for name in &free {
        if let Some(Binding::Value(v)) = closure.env.lookup(name) {
            tenv.insert(name.clone(), Contract::Equals(v));
        }
    }
    // Parameters narrowed by the argument tuple.
    let arg_tuple = Contract::Tuple(arg_contracts.to_vec());
    bind_pattern(&closure.lambda.params, &arg_tuple, &mut tenv);

    Some(crate::analyzer::induction::without_inference(|| analyze(&closure.lambda.body, &tenv, cenv, interner)))
}

/// Summarize applying the callee closure to arguments described by `arg_contracts`
/// (§1 steps 4–5). `None` for a non-function. Completion is **conservative here**: a
/// proven and a merely-possible fall-through both map to `UnprovenPossible` — the
/// structured `ProvenPresent` witness (AP-30) is owed, and the call site reads the
/// finer `Completion` tri-state directly.
pub fn summarize_instance(
    callee: &ValueRef,
    arg_contracts: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<ApplicationOutcome> {
    let a = analyze_instance_body(callee, arg_contracts, cenv, interner)?;
    let completion = match a.completion {
        Completion::Produces => CompletionWithoutValue::ProvenAbsent,
        Completion::MayFallThrough | Completion::FallsThrough => CompletionWithoutValue::UnprovenPossible,
    };
    Some(ApplicationOutcome {
        produced: AnalysisContract::of_contract(a.contract),
        completion,
        may_not_complete: false,
    })
}
