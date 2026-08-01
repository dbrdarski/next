//! The **input obligation** (§1 step 3) — the real accepted-domain check.
//!
//! A callee's **accepted input domain** is the contract its parameter pattern
//! requires of the argument tuple. Contract-pattern names survive shape
//! canonicalization, so the domain is [`pattern_contract`] over the callee's
//! parameter pattern — used here as a **sound** accepted set, not a narrowing.
//!
//! `pattern_contract` is built for narrowing (it *over-approximates* matched values),
//! so it is a sound accepted domain **only when the pattern has no tuple rest** —
//! `(a, …rest)` widens to `Kind(Tuple)`, which would bless `f()` even though the
//! pattern rejects the empty tuple. So [`accepted_domain`] declines a rest-bearing
//! pattern (returns `None` → the obligation is `Unproven`); the length-precise domain
//! for rest parameters is the tuple-family (§4 `restrictLen`) refinement, owed.
//!
//! The obligation `A ⊑ᴬ AcceptedInputs(instance)` is decided as the argument tuple
//! against the domain: `Proven` when it is a subcontract; `Refuted` — with a
//! **represented** `(callee, arguments)` witness — when a rejecting argument tuple is
//! found; else `Unproven`.

use crate::analyzer::application::{ApplicationWitness, SeatVerdict};
use crate::analyzer::pattern_contract;
use crate::ast::{Pat, PatElem, PatField};
use crate::contract::{Contract, ContractEnv, Verdict, subcontract};
use crate::interner::Interner;
use crate::value::ValueRef;

/// The accepted input domain of a callee closure — the contract of its parameter
/// pattern. `None` for a non-function, or for a **rest-bearing** pattern whose sound
/// domain is length-precise (owed, §4). The returned contract is a sound accepted set:
/// an argument tuple inside it is *matched* by the pattern (never merely narrowed to).
pub fn accepted_domain(
    callee: &ValueRef,
    cenv: &ContractEnv,
    i: &mut Interner,
) -> Option<Contract> {
    let closure = callee.as_closure()?;
    if has_rest(&closure.lambda.params) {
        return None; // length-precise domain owed (§4 restrictLen)
    }
    Some(pattern_contract(&closure.lambda.params, cenv, i))
}

/// The input obligation for a known callee closure against argument contracts. The
/// argument tuple is `Tuple(arg_contracts)`; the obligation is its subcontract into
/// the accepted domain. A refutation carries the concrete callee and the rejecting
/// argument tuple (a represented execution — the review's §7 witness discipline).
pub fn input_obligation(
    callee: &ValueRef,
    arg_contracts: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> SeatVerdict {
    let Some(domain) = accepted_domain(callee, cenv, interner) else {
        return SeatVerdict::Unproven; // no soundly-derivable domain
    };
    let arg_tuple = Contract::tuple(arg_contracts.to_vec(), interner);
    match subcontract(&arg_tuple, &domain, interner) {
        Verdict::Proven => SeatVerdict::Proven,
        Verdict::Refuted(w) => {
            // w ∈ ⟦arg_tuple⟧ ∖ ⟦domain⟧ — a represented argument tuple this callee rejects.
            let arguments = w.as_tuple().map(<[ValueRef]>::to_vec).unwrap_or_default();
            SeatVerdict::Refuted(ApplicationWitness {
                callee: callee.clone(),
                arguments,
            })
        }
        Verdict::Unproven => SeatVerdict::Unproven,
    }
}

/// Whether the pattern contains **any** rest binding (`…rest`) — the case where
/// `pattern_contract` over-approximates the accepted set.
fn has_rest(pat: &Pat) -> bool {
    match pat {
        Pat::Const(_) | Pat::Wild | Pat::Bind(_) | Pat::Contract(_) => false,
        Pat::Tuple(elems) => elems.iter().any(|e| match e {
            PatElem::Rest(_) => true,
            PatElem::Pat(p) => has_rest(p),
        }),
        Pat::Record { fields, .. } => fields.iter().any(|f| match f {
            PatField::Rest(_) => true,
            PatField::Field { pat, .. } => has_rest(pat),
        }),
    }
}
