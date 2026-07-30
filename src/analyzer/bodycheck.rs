//! The **call-site body check** — `BodySafe(instance, argument)` (E3/E-7; region-table
//! §6 consumer). This is the *dissolved accepted-domain* safety proof: there is no
//! materialized accepted-domain object, so a call is proven safe by **running the
//! ordinary body check under the actual input** (errata E-6/E-7/E-8).
//!
//! For a single-parameter callee: build the region table (`region.rs`), select the
//! rows reachable for the argument, and analyze each selected row's result with the
//! parameter narrowed to that row's region. **RT-14 witness discipline:** only a
//! *definitely reached* row — this row exact **and** every earlier selected row exact —
//! may carry an `Error` (a real input reaches it and traps); a may-region row's trap is
//! downgraded to a `Warning` (an over-approximate candidate invents no witness).
//!
//! Scope: capture-free, zero-/single-parameter. Multi-parameter (argument-tuple
//! projection, §5) and the guards' own path demands are owed; this is not yet wired
//! into `analyze_apply` (the superseded machinery still runs — audit §5).
//!
//! **Swap blocker (finding, 2026-07-30).** Wiring `body_summary` in place of
//! `induction::instance_body_summary` was attempted and reverted: the coarse
//! instance-keyed [`ACTIVE`] re-entry guard is **unsound for domain-changing
//! recursion**. `f = (x) => x==0 ? f("x") : x+1` called as `f(0)` recurses to `f("x")`,
//! where `"x" + 1` traps at runtime; cutting the recursive edge on the *instance* (f is
//! already active) discards that trap and accepts a trapping program. The superseded
//! `instance_body_summary` handles it soundly via **domain-indexed** analysis (`"x"` is
//! a program literal → the new-domain edge is analyzed, not cut). The sound replacement
//! for that domain-indexed edge-following is the **grounding arc** (C§10), which derives
//! the recursion's input domain — and grounding is not built. So the swap is blocked on
//! grounding, not merely on `body_check`'s capture/multi-param coverage; the Archive9
//! domain-indexed machinery (`domain_admitted`, widening) stays until grounding lands.
//! The test that pins this: `body_safety::a_recursive_call_over_a_new_domain_is_analyzed`.

use std::cell::RefCell;

use crate::analyzer::region::{region_table, select};
use crate::analyzer::{Completion, Finding, Severity, TypeEnv, analyze, bind_pattern};
use crate::ast::{Pat, PatElem};
use crate::contract::{Contract, ContractEnv};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

thread_local! {
    /// The callees currently being summarized — the **re-entry guard**. A recursive
    /// edge (a callee already on the stack) returns the cycle assumption instead of
    /// re-entering its own body, so a *wired* `body_summary` terminates. Keyed on the
    /// closure **instance** — coarser than Archive9's domain-indexed cutoff, and (finding
    /// 2026-07-30) **unsound for domain-changing recursion**: cutting on the instance
    /// discards a trap that lives only on a new argument domain (see the module header).
    /// This guard is therefore inert until grounding derives the recursion domain; it
    /// stays for the standalone `body_summary` API but is not yet the wired cutoff.
    static ACTIVE: RefCell<Vec<ValueRef>> = const { RefCell::new(Vec::new()) };
}

/// A per-instance body summary — the region-table replacement for the wrong-layer
/// `induction::InstanceBodySummary`. `findings` is the path-sensitive [`body_check`]
/// safety; `produced` and `completion` come from analyzing the whole body under the
/// argument (E10 exhaustiveness handled by `analyze_match`).
#[derive(Clone, Debug)]
pub struct BodySummary {
    pub produced: Contract,
    pub completion: Completion,
    pub findings: Vec<Finding>,
}

impl BodySummary {
    /// The cycle assumption for a recursive re-entry (and a non-function): produces
    /// `Top`, completes, no direct trap (the cycle adds no new *direct* trap; the
    /// recursive return is sharpened by the induction, `call_return`).
    fn cycle() -> BodySummary {
        BodySummary { produced: Contract::Top, completion: Completion::Produces, findings: vec![] }
    }

    /// The **Error**-severity findings only — the proven traps to surface at a call site
    /// (a `Warning` over a coarsened domain would be spurious; warnings staying local is
    /// the standing diagnostic gap).
    pub fn errors(&self) -> Vec<Finding> {
        self.findings.iter().filter(|f| f.severity == Severity::Error).cloned().collect()
    }
}

/// Summarize applying `callee` to arguments described by `args`. Re-entrant on the same
/// callee → the cycle assumption (terminates when wired into `analyze_apply`).
pub fn body_summary(callee: &ValueRef, args: &[Contract], cenv: &ContractEnv, interner: &mut Interner) -> BodySummary {
    if ACTIVE.with(|s| s.borrow().iter().any(|c| c == callee)) {
        return BodySummary::cycle();
    }
    ACTIVE.with(|s| s.borrow_mut().push(callee.clone()));
    let findings = body_check(callee, args, cenv, interner);
    let (produced, completion) = whole_body(callee, args, cenv, interner);
    ACTIVE.with(|s| {
        s.borrow_mut().pop();
    });
    BodySummary { produced, completion, findings }
}

/// `produced` (the body's inferred contract) and `completion` (E10), by analyzing the
/// whole body once with the captures bound and the parameters narrowed by the argument
/// tuple. Safety findings here are discarded — [`body_check`] supplies the
/// path-sensitive ones.
fn whole_body(callee: &ValueRef, args: &[Contract], cenv: &ContractEnv, interner: &mut Interner) -> (Contract, Completion) {
    let Some(closure) = callee.as_closure() else { return (Contract::Top, Completion::Produces) };
    let mut env = capture_env(callee);
    bind_pattern(&closure.lambda.params, &Contract::Tuple(args.to_vec()), &mut env);
    let a = analyze(&closure.lambda.body, &env, cenv, interner);
    (a.contract, a.completion)
}

/// Findings from checking a call to `callee` with argument contracts `args`. Empty ⇒ no
/// finding proved. `Error` ⇒ a definitely-reached row traps (refutation); `Warning` ⇒
/// unproven (a may-region row traps, or safety could not be proven).
pub fn body_check(callee: &ValueRef, args: &[Contract], cenv: &ContractEnv, interner: &mut Interner) -> Vec<Finding> {
    let Some(closure) = callee.as_closure() else { return vec![] };
    let base = capture_env(callee);

    match param_name(&closure.lambda.params) {
        Param::Zero => analyze(&closure.lambda.body, &base, cenv, interner).findings,
        Param::One(name) => {
            let arg = args.first().cloned().unwrap_or(Contract::Top);
            let table = region_table(&closure.lambda.body, &name, cenv);
            let selected = select(&table, &arg);
            let mut findings = Vec::new();
            let mut all_prior_exact = true;
            for sel in &selected {
                let definite = sel.exact && all_prior_exact;
                let mut env = base.clone();
                env.insert(name.clone(), sel.region.clone());
                for f in analyze(&sel.result, &env, cenv, interner).findings {
                    findings.push(if definite { f } else { downgrade(f) });
                }
                all_prior_exact = all_prior_exact && sel.exact;
            }
            findings
        }
        Param::Other => vec![], // multi/complex params — §5 argument-tuple projection owed
    }
}

/// The single-parameter shape this increment handles.
enum Param {
    /// No parameter (`()`).
    Zero,
    /// A single bound parameter (`(n)`).
    One(String),
    /// Multi-parameter or a complex pattern — not handled here.
    Other,
}

fn param_name(params: &Pat) -> Param {
    let Pat::Tuple(elems) = params else { return Param::Other };
    match elems.as_slice() {
        [] => Param::Zero,
        [PatElem::Pat(Pat::Bind(n))] => Param::One(n.clone()),
        _ => Param::Other,
    }
}

/// The captured environment as contracts — each free variable bound to `Equals(value)`.
fn capture_env(callee: &ValueRef) -> TypeEnv {
    let mut env = TypeEnv::new();
    let (Some(f), Some(closure)) = (callee.as_fn(), callee.as_closure()) else { return env };
    for name in f.free_vars() {
        if let Some(Binding::Value(v)) = closure.env.lookup(name) {
            env.insert(name.clone(), Contract::Equals(v));
        }
    }
    env
}

/// A may-region row's finding cannot refute (RT-14): an `Error` becomes a `Warning`.
fn downgrade(f: Finding) -> Finding {
    match f.severity {
        Severity::Error => Finding { severity: Severity::Warning, ..f },
        Severity::Warning => f,
    }
}
