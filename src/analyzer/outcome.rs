//! Per-instance **outcome contribution** (§1 steps 4–5) — the callee body summary.
//!
//! A single instance's [`ApplicationOutcome`] is read off its body: bind the captures
//! and the argument-narrowed parameters, then analyze the body. The existing Match
//! analysis (E9/E10) already performs row selection — arm-by-arm narrowing, the
//! unioned produced contract, and the fall-through flag — so `summarize_instance`
//! maps its result:
//!
//! - **produced** = the body's inferred contract (the union over selected rows);
//! - **completion** = `may_complete ? UnprovenPossible : ProvenAbsent` — a possible
//!   fall-through is the third voice; a body that always produces is `ProvenAbsent`.
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
use crate::analyzer::{TypeEnv, analyze, bind_pattern};
use crate::contract::{Contract, ContractEnv};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

/// Summarize applying the callee closure `callee` to arguments described by
/// `arg_contracts`. `None` for a non-function. The captures are bound to their exact
/// values (`Equals`), the parameters narrowed by the argument tuple, and the body
/// analyzed in that environment.
pub fn summarize_instance(
    callee: &ValueRef,
    arg_contracts: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<ApplicationOutcome> {
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

    let a = analyze(&closure.lambda.body, &tenv, cenv, interner);
    let completion = if a.may_complete {
        CompletionWithoutValue::UnprovenPossible
    } else {
        CompletionWithoutValue::ProvenAbsent
    };
    Some(ApplicationOutcome {
        produced: AnalysisContract::of_contract(a.contract),
        completion,
        may_not_complete: false,
    })
}
