//! Return induction — §6, the joint vector pass (the induction step).
//!
//! A **return candidate** claims that a function, applied over an argument domain,
//! returns values in a contract `C`. The induction: **assume** every candidate in a
//! recursive component (SCC) returns its claimed `C`, then verify that each member's
//! body actually produces a subcontract of its `C`. If every member verifies, the
//! component closes — the returns are proven; a **vector failure** (any member
//! unproven) leaves the whole component unproven (per-compilation, §6).
//!
//! The hypotheses are installed as a **dynamic-scope** table that `analyze_apply`
//! consults: a recursive/mutual call whose callee shape is under an active hypothesis
//! returns the assumed contract instead of the coarse `Top` (step 3's fallback). This
//! is what turns `f = (n) => n == 0 ? 1 : n * f(n-1)`'s coarse `Union(Equals(0), Top)`
//! into a proof that `f` returns `Number` under the hypothesis `f: Number`.
//!
//! This lands the **joint vector pass** over one component, over real closures. The
//! multi-SCC driver (call-graph SCC decomposition + reverse-topological ordering,
//! carrying each proven component's contract as a hypothesis for its dependents) and
//! AP-30's `ProvenPresent` half are the wiring that follows.

use std::cell::RefCell;

use crate::analyzer::outcome::summarize_instance;
use crate::ast::Lambda;
use crate::contract::{Contract, ContractEnv, Verdict, subcontract};
use crate::interner::Interner;
use crate::value::ValueRef;

thread_local! {
    /// Dynamic-scope return-induction hypotheses: each shape's assumed return
    /// contract, consulted by `analyze_apply` during a vector pass. A `Vec` (linear
    /// lookup) — components are small.
    static HYPOTHESES: RefCell<Vec<(Lambda, Contract)>> = const { RefCell::new(Vec::new()) };
}

/// The assumed return contract for a callee shape, if one is under an active
/// hypothesis. Consulted by the analyzer's application rule for recursive/mutual calls.
pub(crate) fn hypothesis_for(shape: &Lambda) -> Option<Contract> {
    HYPOTHESES.with(|h| h.borrow().iter().find(|(s, _)| s == shape).map(|(_, c)| c.clone()))
}

/// Run `body` with `hyps` installed as the active hypotheses, restoring the previous
/// table afterward (so nested/stacked passes compose).
fn with_hypotheses<R>(hyps: Vec<(Lambda, Contract)>, body: impl FnOnce() -> R) -> R {
    let saved = HYPOTHESES.with(|h| std::mem::replace(&mut *h.borrow_mut(), hyps));
    let out = body();
    HYPOTHESES.with(|h| *h.borrow_mut() = saved);
    out
}

/// A return candidate: the closure `callee`, applied over arguments described by
/// `args`, claimed to return values in `contract`.
#[derive(Clone)]
pub struct Candidate {
    pub callee: ValueRef,
    pub args: Vec<Contract>,
    pub contract: Contract,
}

/// One **joint vector pass** over a recursive component (§6). Installs every member's
/// claim as a hypothesis, then verifies each member's body produces a subcontract of
/// its claimed contract. Returns `true` iff **all** members verify — a vector failure
/// leaves the whole component unproven.
pub fn joint_vector_pass(members: &[Candidate], cenv: &ContractEnv, interner: &mut Interner) -> bool {
    let hyps: Vec<(Lambda, Contract)> = members
        .iter()
        .filter_map(|c| c.callee.as_fn().map(|f| (f.shape().clone(), c.contract.clone())))
        .collect();

    members.iter().all(|c| {
        let hyps = hyps.clone();
        let summary = with_hypotheses(hyps, || summarize_instance(&c.callee, &c.args, cenv, interner));
        match summary {
            Some(o) => matches!(subcontract(&o.produced.erase(), &c.contract, interner), Verdict::Proven),
            None => false,
        }
    })
}
