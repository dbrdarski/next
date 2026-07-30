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
//! **Recursion (finding, 2026-07-30, spec-verified — see `OwedItems.md §0.1`).** The
//! swap attempt hung on growing-domain recursion. Two prior diagnoses were wrong (a cycle
//! key; then grounding). The verified truth: NEXT does **not** unfold recursion (region-
//! table §8: *"analyze the suspension, don't expand it"*; §10.6 return facts are
//! summaries), and widening is a **foreign** mechanism. The termination bound is the
//! **finite region partition** (GR-03 row-set lattice / app-induction §4a shape cutoff):
//! a growing concrete domain folds into a fixed row, so the reachable-row closure is
//! finite. [`reachable_rows`] computes that closure — the substrate for the summary body
//! check that will **replace `body_check`'s unfolding**: check each reachable row once
//! under the row's own domain (so a trap anywhere in a reachable row is caught without
//! unfolding), summarize recursive calls (shape cutoff), consult grounding/refutation for
//! completion. The `(instance, domain)` [`ACTIVE`] key below is the pre-fixpoint stopgap
//! and is superseded by the row-closure approach.

use std::cell::RefCell;

use crate::analyzer::grounding::collect_self_calls;
use crate::analyzer::region::{Row, region_table, select};
use crate::analyzer::{Completion, Finding, Severity, TypeEnv, analyze, bind_pattern};
use crate::ast::{Pat, PatElem};
use crate::contract::{Contract, ContractEnv, disjoint};
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

/// The demand core's **reachable-rows fixpoint** (GR-03 finite row-set lattice). The finite
/// set of `region_table` **row indices** a call over `arg` can reach through recursion: seed
/// with the rows `arg` selects, and for each reachable row whose result recurses, compute
/// the recursive call's argument domain and add the rows *it* selects. Because a growing
/// concrete domain (`Range(1,3) → Range(2,5) → …`) folds into a fixed row, the closure is
/// **finite** — bounded by the row count — with no widening. This is the substrate the
/// summary body check walks: each reachable row is checked once, **under the row's own
/// domain**, so a trap living anywhere in a reachable row is caught without unfolding the
/// recursion (`f(0) → f("x")` reaches the `else` row, whose `Top` domain covers `String`, so
/// `x + 1` traps).
///
/// Substrate only in this increment (proved by its tests); the summary body check that
/// walks these rows — replacing `body_check`'s unfolding — is the next increment.
#[allow(dead_code)]
fn reachable_rows(callee: &ValueRef, param: &str, arg: &Contract, cenv: &ContractEnv, interner: &mut Interner) -> Vec<usize> {
    let Some(closure) = callee.as_closure() else { return vec![] };
    let table = region_table(&closure.lambda.body, param, cenv);
    let mut seen: Vec<usize> = Vec::new();
    let mut work: Vec<usize> = selected_indices(&table, arg);
    while let Some(i) = work.pop() {
        if seen.contains(&i) {
            continue;
        }
        seen.push(i);
        let mut calls = Vec::new();
        collect_self_calls(&table[i].result, &closure, callee, &mut calls);
        for arglist in &calls {
            let Some(arg_expr) = arglist.first() else { continue };
            let mut env = capture_env(callee);
            env.insert(param.to_string(), table[i].region.clone());
            let dom = analyze(arg_expr, &env, cenv, interner).contract;
            for j in selected_indices(&table, &dom) {
                if !seen.contains(&j) && !work.contains(&j) {
                    work.push(j);
                }
            }
        }
    }
    seen.sort_unstable();
    seen
}

/// The row indices a value in `domain` may select — the first-match remainder walk of
/// [`select`], returning indices (exact rows consume, uncertain rows do not).
#[allow(dead_code)]
fn selected_indices(table: &[Row], domain: &Contract) -> Vec<usize> {
    if let Contract::Equals(v) = domain {
        let mut out = Vec::new();
        for (i, row) in table.iter().enumerate() {
            if row.region.contains(v) {
                out.push(i);
                if row.exact {
                    break;
                }
            }
        }
        return out;
    }
    let mut remaining = domain.clone();
    let mut out = Vec::new();
    for (i, row) in table.iter().enumerate() {
        if !disjoint(&remaining, &row.region) {
            out.push(i);
        }
        if row.exact {
            remaining = Contract::Difference(Box::new(remaining), Box::new(row.region.clone()));
        }
    }
    out
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::harness::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    #[test]
    fn domain_changing_recursion_reaches_both_rows() {
        // f(0) → f("x"): the `x==0` row (0) and — via the recursive call's String target —
        // the `else` row (1). Both reachable; the else row's Top domain is where `x + 1`
        // traps, so a summary check over these rows catches it without unfolding.
        let mut i = Interner::new();
        let g = f("f = (x) => x == 0 ? f(\"x\") : x + 1\nf", &mut i);
        let zero = Contract::Equals(i.integer(0));
        assert_eq!(reachable_rows(&g, "x", &zero, &ContractEnv::new(), &mut i), vec![0, 1]);
    }

    #[test]
    fn growing_domain_recursion_has_a_finite_row_closure() {
        // `f(x) => f(x + 1)` grows the domain forever, but every domain folds into the single
        // (baseless) row — so the reachable-rows closure is finite: one row, no widening, no
        // hang. This is GR-03's finite row-set lattice replacing the old machine's widening.
        let mut i = Interner::new();
        let g = f("f = (x) => f(x + 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert_eq!(reachable_rows(&g, "x", &five, &ContractEnv::new(), &mut i).len(), 1);
    }

    #[test]
    fn descending_recursion_reaches_base_and_step_rows() {
        // countDown: from Equals(5) the else (step) row recurses over Number, which selects
        // both the base (n==0) and step rows — a finite two-row closure.
        let mut i = Interner::new();
        let g = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert_eq!(reachable_rows(&g, "n", &five, &ContractEnv::new(), &mut i), vec![0, 1]);
    }
}
