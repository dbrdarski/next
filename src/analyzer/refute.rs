//! Realized-witness refutation of a return claim — §6, the permanent third voice.
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
//! against: [`check_return_claim`] tries refutation first (permanent), then the
//! inductive proof (per-compilation) — three-voiced.

use crate::analyzer::induction::{Candidate, joint_vector_pass};
use crate::ast::{Arg, Expr};
use crate::contract::{Contract, ContractEnv};
use crate::interner::Interner;
use crate::oracle::{BoundedOutcome, eval_expr_bounded};
use crate::value::ValueRef;

/// The step bound for a refutation run. Generous enough for the small concrete inputs
/// the sampler produces to complete; a diverging input hits it and is skipped.
const REFUTE_FUEL: u64 = 200_000;

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

/// A three-voiced verdict on a return claim (§6). `Refuted` is **permanent
/// in-namespace** (a realized witness); `Unproven` is **per-compilation** (the
/// inductive proof did not close, but no counterexample was found).
#[derive(Clone, Debug)]
pub enum ClaimVerdict {
    Proven,
    Refuted(RealizedWitness),
    Unproven,
}

/// Search for a realized-witness refutation of "`callee` over `args` returns ⊑ `claim`".
/// Samples genuine argument tuples from `args`, runs each through the oracle under the
/// fuel bound, and returns the first `(arguments, v)` that **completes** with `v ∉
/// γ(claim)`. `None` when no sampled input refutes (never a proof — the sampler is
/// incomplete).
pub fn realized_refutation(
    callee: &ValueRef,
    args: &[Contract],
    claim: &Contract,
    interner: &mut Interner,
) -> Option<RealizedWitness> {
    callee.as_fn()?; // only a function can be applied
    for tuple in argument_samples(args, interner) {
        let node = Expr::Apply {
            callee: Box::new(Expr::Const(callee.clone())),
            args: tuple.iter().cloned().map(|v| Arg::Expr(Expr::Const(v))).collect(),
        };
        // Only a *completing* run with an out-of-claim value is a witness; OutOfFuel
        // (diverged), CompletedWithoutValue, and Trapped are all skipped (§6).
        if let BoundedOutcome::Produced(v) = eval_expr_bounded(&node, REFUTE_FUEL, interner)
            && !claim.contains(&v)
        {
            return Some(RealizedWitness { arguments: tuple, produced: v });
        }
    }
    None
}

/// Verify a return claim three-voiced (§6): a realized refutation (permanent) is tried
/// **first** — it is the sound ground truth, catching a false claim the abstract vector
/// pass could otherwise leave merely unproven — then the inductive proof
/// (per-compilation). Single-candidate; a mutual claim goes through the driver
/// (`prove_facts`).
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
    let cand = Candidate {
        callee: callee.clone(),
        args: args.to_vec(),
        claim: crate::analyzer::induction::Claim::Return(claim.clone()),
        cutoff: false,
    };
    if joint_vector_pass(&[cand], cenv, interner) {
        ClaimVerdict::Proven
    } else {
        ClaimVerdict::Unproven
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
