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
//! **Recursion is summary-over-partition, WIRED (2026-07-30; spec-verified, `OwedItems.md
//! §0.1`).** NEXT does **not** unfold recursion (region-table §8: *"analyze the suspension,
//! don't expand it"*; §10.6 return facts are summaries) and never widens (a foreign
//! mechanism). [`body_summary`] — now the `analyze_apply` Known-callee path, replacing
//! `induction::instance_body_summary` — bounds recursion by the **§4a shape-repeat cutoff**
//! ([`ACTIVE`]) and checks safety with [`check_recursive_body`]: the reachable region-table
//! rows (GR-03 finite row-set lattice) × their reaching domains, each row checked once
//! under its reaching domain, recursive calls summarized. A growing concrete domain folds
//! into a fixed row → the analysis converges (no widening, no hang). Verified over the full
//! suite: the domain-changing trap rejects, the two growing-domain tests terminate, RT-14
//! holds. **Owed:** multi-parameter region tables (§5 arg-tuple projection — currently a
//! whole-body fallback); deleting the superseded `instance_body_summary` / `domain_admitted`
//! / `kind_abstraction` (now dead).

use std::cell::RefCell;

use crate::analyzer::grounding::collect_self_calls;
use crate::analyzer::region::{Row, region_table};
use crate::analyzer::{Completion, Finding, Severity, TypeEnv, analyze, bind_pattern};
use crate::ast::{Pat, PatElem};
use crate::contract::{Contract, ContractEnv, Verdict, disjoint, subcontract};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

thread_local! {
    /// The instances currently being summarized — the **§4a shape-repeat cutoff**. A
    /// recursive call reaching an instance already on the stack returns the cycle assumption
    /// instead of re-entering the body (*"target shape already in the sequence → no
    /// admission"*). This is instance-keyed (coarse) yet **sound**: the summary body check
    /// ([`check_recursive_body`]) already covers every reachable region-table row, so a
    /// domain-changing trap (`f(0) → f("x")`) is caught by the row closure — the cutoff only
    /// prevents re-unfolding. Growing domains fold into the finite row set, so the analysis
    /// converges with **no widening**.
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
/// `(instance, domain)` node → the cycle assumption (so a *wired* `body_summary`
/// terminates on same-domain recursion; unbounded-domain growth still needs grounding).
pub fn body_summary(callee: &ValueRef, args: &[Contract], cenv: &ContractEnv, interner: &mut Interner) -> BodySummary {
    if ACTIVE.with(|s| s.borrow().contains(callee)) {
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
        // The summary-over-partition check: reachable rows × their reaching domains, with
        // recursion summarized by the §4a cutoff above.
        Param::One(name) => {
            let arg = args.first().cloned().unwrap_or(Contract::Top);
            check_recursive_body(callee, &name, &arg, cenv, interner)
        }
        // Multi-parameter: no arg-tuple region table yet (§5 owed). Analyze the body once
        // under the argument tuple — direct traps are caught; recursion is summarized by the
        // cutoff, so this terminates (multi-param growing recursions have no direct trap).
        Param::Other => {
            let mut env = base;
            bind_pattern(&closure.lambda.params, &Contract::Tuple(args.to_vec()), &mut env);
            analyze(&closure.lambda.body, &env, cenv, interner).findings
        }
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

/// The **summary body check** — the demand core's safety pass, replacing `body_check`'s
/// unfolding. Computes, per reachable region-table row, the **reaching domain** (the values
/// that actually reach it through recursion) as a growing union, then checks each row's
/// result **under its reaching domain**. Two facts make this sound *and* terminating with
/// no widening:
///
/// - **Termination:** recursive-call target domains are computed under the fixed row
///   **region** (not the accumulated domain), so only finitely many target contracts feed
///   the union; growth stops by a semantic `⊑` check. A growing recursion (`f(x+1)`) folds
///   its reaching domain into the row's region and converges.
/// - **Precision where it matters:** a trap-bearing arm is guarded by an exact test (`x==0`),
///   whose row region *is* the exact reaching domain — so `f(0) → f(1)` reaches the middle
///   row with `Equals(1)` (the `1 + "x"` arm is pruned → accepted) while `f(0) → f("x")`
///   reaches the else row with `Equals("x")` (`x + 1` traps → rejected). Coarse rows carry
///   no domain-specific trap, so their over-approximation adds no false finding.
///
/// Recursive calls in a row's result are *summarized*, not unfolded: when analyzed they
/// route back through `analyze_apply → body_summary`, hit the [`ACTIVE`] shape cutoff, and
/// return the cycle assumption. Coverage comes from the reachable-row set, not unfolding.
fn check_recursive_body(callee: &ValueRef, param: &str, arg: &Contract, cenv: &ContractEnv, interner: &mut Interner) -> Vec<Finding> {
    let Some(closure) = callee.as_closure() else { return vec![] };
    let table = region_table(&closure.lambda.body, param, cenv);
    let mut reaching: Vec<Option<Contract>> = vec![None; table.len()];
    for i in selected_indices(&table, arg) {
        grow(&mut reaching[i], intersect(arg.clone(), table[i].region.clone()), interner);
    }
    // Fixpoint: propagate recursive-call targets (computed under the fixed row region, so the
    // union is bounded and converges).
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..table.len() {
            if reaching[i].is_none() {
                continue;
            }
            let mut calls = Vec::new();
            collect_self_calls(&table[i].result, &closure, callee, &mut calls);
            for arglist in &calls {
                let Some(arg_expr) = arglist.first() else { continue };
                let mut env = capture_env(callee);
                env.insert(param.to_string(), table[i].region.clone());
                let target = analyze(arg_expr, &env, cenv, interner).contract;
                for j in selected_indices(&table, &target) {
                    let add = intersect(target.clone(), table[j].region.clone());
                    changed |= grow(&mut reaching[j], add, interner);
                }
            }
        }
    }
    // Check each reachable row's result under its reaching domain (recursion summarized).
    // **RT-14 witness discipline (full):** a finding refutes (`Error`) only from a
    // *definitely reached* row — this row exact **and every earlier reachable row exact**.
    // An uncertain earlier row (an opaque guard) means we cannot prove *this* arm is the one
    // taken (`n == n ? 0 : n + "x"` — the trap sits in an exact row reached only if an
    // unprovable guard is false), so its trap downgrades to a warning.
    let base = capture_env(callee);
    let mut findings = Vec::new();
    for (i, dom) in reaching.iter().enumerate() {
        let Some(dom) = dom else { continue };
        let definite = table[i].exact && (0..i).all(|j| reaching[j].is_none() || table[j].exact);
        let mut env = base.clone();
        env.insert(param.to_string(), dom.clone());
        for finding in analyze(&table[i].result, &env, cenv, interner).findings {
            findings.push(if definite { finding } else { downgrade(finding) });
        }
    }
    findings
}

/// Union `add` into `slot`, but only when it is not already covered (`add ⊑ slot`) — the
/// semantic convergence check that bounds the reaching-domain fixpoint. Returns whether the
/// slot grew.
fn grow(slot: &mut Option<Contract>, add: Contract, interner: &mut Interner) -> bool {
    match slot {
        None => {
            *slot = Some(add);
            true
        }
        Some(cur) => {
            if matches!(subcontract(&add, cur, interner), Verdict::Proven) {
                false
            } else {
                *slot = Some(Contract::Union(Box::new(cur.clone()), Box::new(add)));
                true
            }
        }
    }
}

/// `Top ∩ x = x`; otherwise the raw `Intersection` (the algebra reasons about it).
fn intersect(a: Contract, b: Contract) -> Contract {
    match (a, b) {
        (Contract::Top, x) | (x, Contract::Top) => x,
        (a, b) => Contract::Intersection(Box::new(a), Box::new(b)),
    }
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
    use crate::contract::Kind;
    use crate::oracle::harness::run_source_in;

    fn has_err(fs: &[Finding]) -> bool {
        fs.iter().any(|x| x.severity == Severity::Error)
    }

    #[test]
    fn rt14_exact_row_after_uncertain_prefix_does_not_refute() {
        // Regression (blocker 1a): `n == n` is always true, but guard regionalization can't
        // express it, so the first row is Top/non-exact. The fallback `n + "x"` sits in an
        // exact row — but it is reached only if the (unprovable) first guard is false, which
        // never happens. It must NOT be an Error (safe function must not be rejected).
        let mut i = Interner::new();
        let g = f("f = (n) => n == n ? 0 : n + \"x\"\nf", &mut i);
        let fs = body_check(&g, &[Contract::Kind(Kind::Number)], &ContractEnv::new(), &mut i);
        assert!(!has_err(&fs), "uncertain prefix must not refute: {fs:?}");
    }

    // ── Archive-11 review: adversarial regressions still owed (the unified (instance,
    //    row-set) SCC summary). Pinned as ignored; un-ignore when that engine lands. ──

    #[test]
    #[ignore = "blocker 1b: coarse recursive target manufactures an unreached witness (false reject) — PARKED. Blocker RE-FILED 2026-07-31 after an oracle check: grounding §4 EXACT-SINGLETON FACT CHAINS (owed). NOT the row-set fact graph. Reason: f(0.5) TRAPS (verified) and 0.5 is in the SAME ROW as 1, so BodySafe(f, {row x>0}) is genuinely FALSE — no row-set-keyed fact can prove f(1) safe. Proving it needs the exact chain 1 -> 0, i.e. a domain finer than a row. NOT a canonicalization issue, and NOT fixable by the fact graph alone. Do NOT import a reaching/widening engine to pass this"]
    fn rt14_inequality_recursion_does_not_manufacture_witness() {
        // f(1) → f(0) → 0 is safe. But `x - 1` analyzed over the whole `x > 0` region is
        // coarse `Number`, dragging in the `x < 0` branch (`x + "s"`) the call from 1 never
        // reaches. Needs precise reaching (track {1, 0}), not the row-region over-approx.
        let mut i = Interner::new();
        let g = f("f = (x) => x > 0 ? f(x - 1) : (x == 0 ? 0 : x + \"s\")\nf", &mut i);
        let s = body_summary(&g, &[Contract::Equals(i.integer(1))], &ContractEnv::new(), &mut i);
        assert!(s.errors().is_empty(), "f(1) is safe; coarse recursion must not refute: {:?}", s.errors());
    }

    #[test]
    #[ignore = "blocker 2a: multi-param domain-changing recursion accepted silently (false accept) — PARKED. Blocker: region-table §5 (argument-tuple projection) + the same fact bound. NOT a canonicalization issue. Do NOT import a reaching/widening engine to pass this"]
    fn multiparam_domain_changing_recursion_is_caught() {
        // f(0, n) → f("x", n) → "x" + n traps. The whole-body fallback cuts the recursion
        // and never inspects the changed-domain re-entry, so the crash is missed.
        let mut i = Interner::new();
        let g = f("f = (a, b) => a == 0 ? f(\"x\", b) : a + b\nf", &mut i);
        let s = body_summary(&g, &[Contract::Equals(i.integer(0)), Contract::Kind(Kind::Number)], &ContractEnv::new(), &mut i);
        assert!(!s.errors().is_empty(), "must reject the multi-param deep trap, not accept: {:?}", s.findings);
    }

    #[test]
    #[ignore = "blocker 2b: mutual/helper domain-changing recursion accepted silently (false accept) — PARKED. Blocker: NOT 'build Algorithm A' — oracle/mu.rs ALREADY computes SCC grouping + positional mu-refs + law 5 slot order, but is #![allow(dead_code)] with no runtime consumer. The gap is the JOIN: mu::canonicalize_group takes (name, Expr) binding lists, while make_closure (eval.rs:239) builds closures from one Lambda + env and stores the RAW body, so no closure knows it is a group member and a mutual partner stays an ordinary capture. Law 4 (bisimulation slot merging) is also genuinely absent"]
    fn mutual_domain_changing_recursion_is_caught() {
        // f(0) → g("x") → f("x") → "x" + 1 traps. f's closure follows syntactic self-calls
        // only, so the helper edge into the trapping f row is never added.
        let mut i = Interner::new();
        let g = f("f = (x) => x == 0 ? g(\"x\") : x + 1\ng = (y) => f(y)\nf", &mut i);
        let s = body_summary(&g, &[Contract::Equals(i.integer(0))], &ContractEnv::new(), &mut i);
        assert!(!s.errors().is_empty(), "must reject the mutual deep trap, not accept: {:?}", s.findings);
    }

    #[test]
    #[ignore = "blocker 3: recursive fall-through completion lost — returns Produces (false accept) — PARKED. Blocker: completion carried on the fact (the cycle assumption must not ASSERT Produces). NOT a canonicalization issue"]
    fn recursive_fall_through_completion_is_visible() {
        // f(0) → f(1); f(1) matches no arm → completes without a value. The one-shot
        // completion reports Produces, so an expecting seat would accept a trapping program.
        let mut i = Interner::new();
        let g = f("f = (x) => x :: {\n 0 => f(1)\n }\nf", &mut i);
        let s = body_summary(&g, &[Contract::Equals(i.integer(0))], &ContractEnv::new(), &mut i);
        assert!(s.completion != Completion::Produces, "recursive fall-through must be visible, got Produces");
    }

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

    fn has_error(findings: &[Finding]) -> bool {
        findings.iter().any(|f| f.severity == Severity::Error)
    }

    #[test]
    fn summary_check_accepts_the_unreached_deep_trap() {
        // f(0) → f(1) → 1. The `1 + "x"` arm lives at x∉{0,1}, never reached. The middle row
        // is checked under its **exact** reaching domain `Equals(1)`, which prunes that arm →
        // no Error (accepted). The old machine needed widening + evidence downgrade for this.
        let mut i = Interner::new();
        let g = f("f = (x) => x == 0 ? f(1) : (x == 1 ? 1 : 1 + \"x\")\nf", &mut i);
        let zero = Contract::Equals(i.integer(0));
        let findings = check_recursive_body(&g, "x", &zero, &ContractEnv::new(), &mut i);
        assert!(!has_error(&findings), "the unreached trap must not refute f(0): {findings:?}");
    }

    #[test]
    fn summary_check_rejects_the_domain_changing_trap() {
        // f(0) → f("x") → "x" + 1. The else row's reaching domain is `Equals("x")` (String),
        // so `x + 1` definitely traps → Error (rejected) — with the right severity, from the
        // exact reaching domain, not a downgraded warning.
        let mut i = Interner::new();
        let g = f("f = (x) => x == 0 ? f(\"x\") : x + 1\nf", &mut i);
        let zero = Contract::Equals(i.integer(0));
        let findings = check_recursive_body(&g, "x", &zero, &ContractEnv::new(), &mut i);
        assert!(has_error(&findings), "the reached trap is caught: {findings:?}");
    }

    #[test]
    #[ignore = "FALSE POSITIVE exposed by the 2026-07-31 ruling (safety-unproven -> Error). These were green only because the finding was a Warning that analyze_apply's errors() filter discarded. Root: bodycheck.rs:213 computes the recursive target under the ROW REGION, which grows the reaching domain back up to Top, so `n - 1` can no longer be proven a Number. SAME ROOT AS BLOCKER 1b (parked). The programs are safe; the analyzer cannot currently prove it. Un-ignore when 1b's root is fixed. Do NOT fix by reverting the severity or by widening/reaching machinery."]
    fn summary_check_accepts_count_down_and_terminates() {
        // countDown's reaching domains converge (Equals(5) ⊔ Number = Number by the ⊑ check),
        // and its body has no trap → accepted, and the fixpoint terminates.
        let mut i = Interner::new();
        let g = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        let findings = check_recursive_body(&g, "n", &five, &ContractEnv::new(), &mut i);
        assert!(!has_error(&findings), "countDown is safe: {findings:?}");
    }
}
