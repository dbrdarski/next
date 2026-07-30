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
//! **Swap status (finding, 2026-07-30, corrected).** Wiring `body_summary` in place of
//! `induction::instance_body_summary` was attempted, failed one test, and reverted. The
//! failure was **not** a grounding gap — it was a wrong cycle key in [`ACTIVE`]. The
//! first cut of the guard keyed on the *instance* alone, so `f = (x) => x==0 ? f("x") :
//! x+1` called as `f(0)` cut its `f("x")` edge (f already active) and discarded the
//! `"x" + 1` trap. The fix is the **(instance, domain)** key (C§13.2a / GR-07: nodes are
//! *"instance × row/domain"*) — the same key the old `ACTIVE_BODIES` uses: `f(0)` and
//! `f("x")` are distinct nodes, so `f("x")` is analyzed and the trap is caught. That
//! demand chain **terminates on its own** (`f("x")` reaches `x+1`, no further recursion)
//! — no termination bound is needed for this example, and grounding is a *termination*
//! judgment, not what it needs. What grounding **is** needed for: bounding a domain that
//! grows without end (`f(Range(1,3)) → f(Range(2,5)) → …`, all distinct nodes → the
//! analysis would not converge), the job the old machine's widening does. So grounding
//! gates **deleting the widening / the swap+delete**, not fixing domain-changing
//! recursion. The pinning test: `body_safety::a_recursive_call_over_a_new_domain_is_analyzed`.
//!
//! **Verified empirically (2026-07-30).** Wiring `body_summary` *with* this corrected
//! `(instance, domain)` key was run against the full suite: it **hangs** on
//! `a_growing_union_recursive_domain_terminates` and
//! `recursive_domains::a_growing_non_singleton_recursive_domain_terminates` — the
//! growing-domain cases — because the correct key (rightly) refuses to cut distinct nodes
//! and there is no bound yet. So a *wired* machine needs **both** the correct key (this
//! change, sound on the example) **and** the termination bound (grounding, unbuilt).
//! Reverted to unwired; the key change stands as the right key for when it is wired.

use std::cell::RefCell;

use crate::analyzer::region::{region_table, select};
use crate::analyzer::{Completion, Finding, Severity, TypeEnv, analyze, bind_pattern};
use crate::ast::{Pat, PatElem};
use crate::contract::{Contract, ContractEnv};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

thread_local! {
    /// The `(instance, domain)` nodes currently being summarized — the **cycle guard**.
    /// A demand reaching a node **already on the current path** closes a cycle and returns
    /// the cycle assumption instead of re-entering the body (C§13.2a / grounding GR-02a;
    /// GR-07 pins the node grain as *"instance × row/domain under the region partition"*).
    /// The key is `(closure, argument contracts)` — **domain-indexed**, matching the old
    /// machine's `ACTIVE_BODIES` key. `f(0) → f("x")` are *distinct* nodes, so `f("x")` is
    /// analyzed (not cut) and its `"x" + 1` trap is caught — domain-changing recursion is
    /// sound. What this guard does **not** yet do is *bound* a domain that grows without
    /// end (`f(Range(1,3)) → f(Range(2,5)) → …`, all distinct nodes): that needs the
    /// termination bound the old machine got from widening and grounding is the specified
    /// replacement for. See the module header.
    static ACTIVE: RefCell<Vec<(ValueRef, Vec<Contract>)>> = const { RefCell::new(Vec::new()) };
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
/// `(instance, domain)` node → the cycle assumption (so a *wired* `body_summary`
/// terminates on same-domain recursion; unbounded-domain growth still needs grounding).
pub fn body_summary(callee: &ValueRef, args: &[Contract], cenv: &ContractEnv, interner: &mut Interner) -> BodySummary {
    let key = (callee.clone(), args.to_vec());
    if ACTIVE.with(|s| s.borrow().contains(&key)) {
        return BodySummary::cycle();
    }
    ACTIVE.with(|s| s.borrow_mut().push(key));
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
