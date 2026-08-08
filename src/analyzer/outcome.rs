//! Per-instance **outcome contribution** (§1 steps 4–5) — the callee body summary.
//!
//! A single instance's [`ApplicationOutcome`] is read off its body: bind the captures
//! and the argument-narrowed parameters, then analyze the body. The existing Match
//! analysis (E9/E10) already performs row selection — arm-by-arm narrowing, the
//! unioned produced contract, and the fall-through flag — so `summarize_instance`
//! maps its result:
//!
//! - **produced** = the body's inferred contract (the union over selected rows);
//! - **completion** = the evidence-preserving AP-30 tri-state: a represented bounded
//!   execution that completes without a value supplies `ProvenPresent(witness)`;
//!   otherwise a non-producing voice remains `UnprovenPossible`.
//!
//! **Recursion is coarse and terminating here.** The active canonical-code sequence
//! implements §4a's discovery cutoff: re-entering code contributes the conservative `Top` /
//! possible-completion outcome instead of re-entering its body. The summary is therefore
//! sound but coarse on recursion; the §6 return and completion facts sharpen that fallback
//! when their hypotheses cover the recursive call.
//!
//! `may_not_complete` (divergence) is left `false` — it feeds no safety verdict (§1.5)
//! and its precise value on a gray SCC is the §6 concern.

use std::cell::RefCell;

use crate::analyzer::application::{ApplicationOutcome, CompletionWithoutValue};
use crate::analyzer::domain::AnalysisContract;
use crate::analyzer::{
    Analysis, Completion, TypeEnv, analyze_in_world, bind_pattern, world_for_act,
};
use crate::contract::{Contract, ContractEnv};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

thread_local! {
    /// §4a's active canonical-code sequence for the coarse outcome projection. This is not a
    /// proof cache: it only prevents a body summary from recursively summarizing a
    /// repeated code node after safety has already been settled by the candidate graph.
    static ACTIVE_SHAPES: RefCell<Vec<crate::intern::Interned<crate::ast::Lambda>>> =
        const { RefCell::new(Vec::new()) };
}

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
    let function = callee.as_fn()?;
    let shape = function.shape_rc();
    let repeated =
        ACTIVE_SHAPES.with(|active| active.borrow().iter().any(|held| held.ptr_eq(&shape)));
    if repeated {
        return Some(Analysis {
            contract: Contract::Top,
            annotated: AnalysisContract::of_contract(Contract::Top),
            image: None,
            findings: Vec::new(),
            safety_demands: Vec::new(),
            completion: Completion::MayFallThrough,
        });
    }
    let free: Vec<String> = function.free_vars().to_vec();

    let mut tenv = TypeEnv::new();
    // Captures first, so a same-named parameter shadows them.
    for name in &free {
        if let Some(Binding::Value(v)) = function.capture_binding(name) {
            tenv.insert(name.clone(), AnalysisContract::of_value(v, interner));
        }
    }
    // Parameters narrowed by the argument tuple.
    let arg_tuple = Contract::tuple(arg_contracts.to_vec(), interner);
    bind_pattern(&closure.lambda.params, &arg_tuple, &mut tenv, interner);

    ACTIVE_SHAPES.with(|active| active.borrow_mut().push(shape));
    let analysis = crate::analyzer::induction::without_inference(|| {
        analyze_in_world(
            &closure.lambda.body,
            &tenv,
            cenv,
            world_for_act(closure.lambda.act_kind),
            interner,
        )
    });
    ACTIVE_SHAPES.with(|active| {
        active.borrow_mut().pop();
    });
    Some(analysis)
}

/// Summarize applying the callee closure to arguments described by `arg_contracts`
/// (§1 steps 4–5). `None` for a non-function. `ProvenPresent` is minted only from a
/// represented bounded execution, never from product inhabitance alone (AP-30).
pub fn summarize_instance(
    callee: &ValueRef,
    arg_contracts: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<ApplicationOutcome> {
    let a = analyze_instance_body(callee, arg_contracts, cenv, interner)?;
    // Deliberately NOT `CompletionWithoutValue::of`: this is the coarse instance
    // path, whose completion evidence lacks per-execution provenance — so any
    // fall-through is re-derived as a **realized** witness (AP-30) or stays the
    // third voice. The structural narrowing would trust a witness this summary
    // cannot vouch for.
    let completion = match &a.completion {
        Completion::Produces => CompletionWithoutValue::ProvenAbsent,
        Completion::MayFallThrough | Completion::FallsThrough(_) => {
            crate::analyzer::refute::realized_completion(callee, arg_contracts, cenv, interner)
                .map_or(
                    CompletionWithoutValue::UnprovenPossible,
                    CompletionWithoutValue::ProvenPresent,
                )
        }
    };
    Some(ApplicationOutcome {
        produced: a.annotated,
        completion,
        may_not_complete: false,
    })
}
