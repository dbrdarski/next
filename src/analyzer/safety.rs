//! `BodySafe(instance, I)` — the domain-indexed **safety fact** (C§13.2a), the safety
//! analogue of the return fact.
//!
//! **Where `I` comes from.** The call site: `I` is the argument-tuple contract actually
//! presented at the call (E-7 — analyze the body under the actual input), or the declared
//! input of a `where` assertion (E-8 — `BodySafe(instance, DeclaredInput) = proven`). It is
//! never synthesized here: inventing a covering domain is candidate synthesis, which is
//! forbidden. `I` is the fact's **input domain**; the contract an operation *demands* of an
//! operand is `C`, a separate thing — the two never merge.
//!
//! **How recursion closes — assume-and-check, never unfolding.** To establish
//! `BodySafe(instance, I)` the fact is *assumed*, the body analyzed **once** under `I`, and
//! a recursive reference whose argument domain is contained in `I` **resolves through the
//! assumption** (C§13.2: *"recursive references never unfold; they resolve through proven
//! facts"*). Nothing accumulates across depths, so there is nothing to widen.
//!
//! ```text
//! countDown where (GE(0) ∧ Mod(1,0)) => …        I = the declared domain D
//!   assume BodySafe(countDown, D)
//!     row n == 0 → 0                              safe
//!     row n != 0 → countDown(n - 1)
//!         n ∈ D ∧ n != 0  ⇒  n ≥ 1  ⇒  n-1 ≥ 0, still an integer  ⇒  n-1 ∈ D
//!         discharged by the assumption — the body is not re-entered
//!   ⇒ BodySafe(countDown, D) proven
//! ```
//!
//! (That `n-1 ∈ D` step is decided by the operation rulebook's interval **and congruence**
//! transfer — integrality surviving `−` is what keeps the recursive argument inside `D`.)
//!
//! **What is deliberately left unproven.** A recursive call whose argument domain is *not*
//! contained in `I` is covered by no fact here, so the verdict is `Unproven`. Widening `I`
//! until it closes, or accumulating the domains that reach each row, are the two forbidden
//! shapes; the honest third voice is the correct outcome. Proving such a call needs a
//! *legitimate* wider domain — a `where`, or grounding's derived input domain / §4
//! exact-singleton chain — none of which this module invents.

use std::cell::RefCell;

use crate::analyzer::region::{region_table, select};
use crate::analyzer::{Finding, Severity, TypeEnv, analyze, bind_pattern};
use crate::contract::{Contract, ContractEnv, Verdict, subcontract};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

/// An **assumed** safety fact: the body of `callee` is safe for every argument tuple
/// contained in `input`. Keyed by `(instance, I)` — instance identity (a closure value,
/// which carries its captures) plus the input domain. Shape alone never suffices, and a
/// fact proved over one domain is never reused on a wider one.
#[derive(Clone)]
pub struct SafetyFact {
    pub callee: ValueRef,
    pub input: Vec<Contract>,
}

thread_local! {
    /// The facts assumed by an in-progress proof — the induction hypotheses.
    static ASSUMED: RefCell<Vec<SafetyFact>> = const { RefCell::new(Vec::new()) };
}

/// The three-voiced verdict for `BodySafe(instance, I)`.
#[derive(Debug)]
pub enum BodySafety {
    /// Every operation the body reaches over `I` discharges.
    Proven,
    /// A definitely-reached operation traps — carries the refuting findings.
    Refuted(Vec<Finding>),
    /// Neither proved nor refuted (an unproven operation, or a recursive call whose
    /// domain no assumed fact covers). **Safety-unproven blocks at a seat**
    /// (late-resolution §5) — it is not a licence to proceed.
    Unproven(Vec<Finding>),
}

impl BodySafety {
    /// Whether the fact is proven (the only voice that discharges a seat).
    pub fn is_proven(&self) -> bool {
        matches!(self, BodySafety::Proven)
    }

    pub fn findings(&self) -> &[Finding] {
        match self {
            BodySafety::Proven => &[],
            BodySafety::Refuted(f) | BodySafety::Unproven(f) => f,
        }
    }
}

/// Whether an assumed fact **discharges** a call to `callee` over `args`: the same
/// instance, and the call's domain contained in the fact's (`args ⊑ I`). This is what
/// lets a recursive reference resolve through a fact instead of re-entering the body.
pub fn discharged(callee: &ValueRef, args: &[Contract], interner: &mut Interner) -> bool {
    let domains: Vec<Vec<Contract>> = ASSUMED.with(|a| {
        a.borrow().iter().filter(|f| f.callee == *callee).map(|f| f.input.clone()).collect()
    });
    domains.into_iter().any(|input| {
        let call = Contract::Tuple(args.to_vec());
        let dom = Contract::Tuple(input);
        matches!(subcontract(&call, &dom, interner), Verdict::Proven)
    })
}

/// Prove `BodySafe(callee, args)` (§6): discover the candidate graph, then settle it by
/// SCC in reverse topological order with one joint vector pass per cyclic component.
/// Recursion resolves through facts and the body is never unfolded.
pub fn prove(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> BodySafety {
    if callee.as_closure().is_none() {
        return BodySafety::Unproven(Vec::new()); // not a known function — nothing to prove over
    }
    let (nodes, edges) = discover(callee, args, cenv, interner);
    settle(&nodes, &edges, cenv, interner)
}

/// Verify the fact **per region-table row** (§5's partition rule). `region::select`
/// already narrows each selected row to `remaining ∩ row.region`, so each row is checked
/// under exactly the part of `I` that reaches it.
///
/// **RT-14 witness discipline** is preserved: a finding from a non-exact (may-region) row
/// is downgraded, because an over-approximate candidate authorizes no refutation. *(With
/// only two severities that also makes it non-blocking; carrying "blocks but claims no
/// witness" needs the third voice as a severity — recorded, not invented here.)*
fn verify_by_partition(
    callee: &ValueRef,
    closure: &crate::value::Closure,
    param: &str,
    domain: &Contract,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Vec<Finding> {
    let table = region_table(&closure.lambda.body, param, cenv);
    let base = capture_env(callee);
    let mut out = Vec::new();
    for sel in select(&table, domain) {
        let mut env = base.clone();
        env.insert(param.to_string(), sel.region.clone());
        for f in analyze(&sel.result, &env, cenv, interner).findings {
            out.push(if sel.exact { f } else { downgrade(f) });
        }
    }
    out
}

/// A may-region row cannot refute (RT-14): an `Error` becomes advisory.
fn downgrade(f: Finding) -> Finding {
    match f.severity {
        Severity::Error => Finding { severity: Severity::Warning, ..f },
        Severity::Warning => f,
    }
}

/// The single bound parameter name, when the pattern is one plain binding.
fn single_param(params: &crate::ast::Pat) -> Option<String> {
    use crate::ast::{Pat, PatElem};
    match params {
        Pat::Tuple(elems) => match elems.as_slice() {
            [PatElem::Pat(Pat::Bind(n))] => Some(n.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Three-voiced from the body's findings: any refutation refutes; else any unproven
/// operation leaves the fact unproven; else proven.
fn classify(findings: Vec<Finding>) -> BodySafety {
    if findings.iter().any(|f| f.severity == Severity::Error) {
        return BodySafety::Refuted(findings);
    }
    if findings.is_empty() {
        return BodySafety::Proven;
    }
    BodySafety::Unproven(findings)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::harness::run_source_in;
    use crate::rational::Rational;
    use num_bigint::BigInt;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    /// `GE(0) ∧ Mod(1,0)` — the non-negative integers.
    fn nonneg_ints() -> Contract {
        Contract::Intersection(
            Box::new(Contract::GreaterEq(Rational::from(0))),
            Box::new(Contract::Mod { n: BigInt::from(1), r: BigInt::from(0) }),
        )
    }

    #[test]
    fn declared_domain_recursion_proves_by_induction() {
        // The clean inductive case, and the point of the whole mechanism: with `I` the
        // declared domain, the recursive argument `n - 1` stays inside it, so the call is
        // discharged by the ASSUMPTION and the body is analyzed exactly once.
        // `n-1 ∈ D` is decided by the operation rulebook's interval + congruence transfer
        // (integrality surviving `−`), which is why F0 had to exist first.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let v = prove(&cd, &[nonneg_ints()], &ContractEnv::new(), &mut i);
        assert!(v.is_proven(), "countDown over its declared domain proves by induction: {v:?}");
    }

    #[test]
    fn safety_is_not_termination_and_the_proof_still_closes() {
        // Isolation: a body that never terminates is still *safe* (divergence is not a
        // trap), and the recursive call `f(n)` is inside `I`, so it discharges. If the
        // proof were unfolding rather than closing on the fact, this would not return.
        let mut i = Interner::new();
        let loopy = f("f = (n) => f(n)\nf", &mut i);
        let v = prove(&loopy, &[Contract::Kind(crate::contract::Kind::Number)], &ContractEnv::new(), &mut i);
        assert!(v.is_proven(), "safety != termination; the fact discharges the self-call: {v:?}");
    }

    #[test]
    fn a_call_outside_the_fact_is_not_discharged() {
        // The honest limit. `Equals(4) ⊄ Equals(5)`, so an assumed fact over `Equals(5)`
        // does not cover the recursive call — this module does **not** widen `I` until it
        // closes, nor accumulate the domains that reach each row. Proving such a call
        // needs a legitimate wider domain (a `where`, or grounding's derived domain).
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        let four = Contract::Equals(i.integer(4));
        let fact = SafetyFact { callee: cd.clone(), input: vec![five] };
        let covered = with_assumed_all(vec![fact], || discharged(&cd, std::slice::from_ref(&four), &mut i));
        assert!(!covered, "a narrower-but-different domain must not be discharged");
    }

    #[test]
    fn a_declared_domain_fact_discharges_any_call_inside_it() {
        // The reuse that makes facts worth having: `BodySafe(f, D)` discharges every call
        // whose argument is contained in `D` — so `f(5)` needs no re-analysis of the body.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        let fact = SafetyFact { callee: cd.clone(), input: vec![nonneg_ints()] };
        let covered = with_assumed_all(vec![fact], || discharged(&cd, std::slice::from_ref(&five), &mut i));
        assert!(covered, "Equals(5) is inside the non-negative integers");
    }
}

// ── The candidate graph (app-induction §6 / C§13.2a) ─────────────────────────
//
// §6 gives the procedure outright, and it is followed here rather than reinvented:
//
//   seed with the candidates the program's safety obligations demand
//     → discovery closure: for each new candidate, find its referenced candidates and
//       **intern every candidate and edge** — *no verification occurs during discovery*
//       (a premature unproven result is non-conforming)
//     → collapse SCCs, process in **reverse topological order** (dependencies first)
//     → per cyclic component, **one joint vector pass**: assume every member's fact
//       jointly, verify each member; all must hold, and a vector failure leaves the
//       whole component unproven.
//
// The joint pass is what mutual recursion needs: proving `f` alone cannot discharge its
// call to `g`, because only `f`'s own fact would be assumed.
//
// **Finiteness** is C§13.3(2)'s instance-chain cutoff, not a budget: a target whose
// *shape* already appears on the discovery path is not instantiated further; it is
// admitted as a `cutoff` node whose verdict is `Unproven` (the ladder's (c) rung). An
// existing candidate whose domain **covers** the target is reused instead of creating a
// node — that reuse is what closes `countDown`'s self-loop into one component.

/// A node of the safety-fact graph: `BodySafe(callee, input)`.
struct Node {
    callee: ValueRef,
    input: Vec<Contract>,
    /// Shape already on the discovery path — not expanded; resolves as `Unproven`.
    cutoff: bool,
}

/// Discovery closure (§6). Interns candidates and edges; **verifies nothing**.
fn discover(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> (Vec<Node>, Vec<Vec<usize>>) {
    let mut nodes = vec![Node { callee: callee.clone(), input: args.to_vec(), cutoff: false }];
    let mut edges: Vec<Vec<usize>> = vec![Vec::new()];
    let mut work = vec![(0usize, vec![shape_of(callee)])];

    while let Some((i, path)) = work.pop() {
        for (target, targs) in calls_of(&nodes[i], cenv, interner) {
            // Reuse: an existing candidate whose domain covers the target. This is the
            // fact-reuse rung, and it is what turns self-recursion into a self-loop
            // rather than an unbounded chain of nodes.
            if let Some(j) = covering_node(&nodes, &target, &targs, interner) {
                edges[i].push(j);
                continue;
            }
            let shape = shape_of(&target);
            let cutoff = path.contains(&shape);
            nodes.push(Node { callee: target, input: targs, cutoff });
            edges.push(Vec::new());
            let j = nodes.len() - 1;
            edges[i].push(j);
            if !cutoff {
                let mut next = path.clone();
                next.push(shape);
                work.push((j, next));
            }
        }
    }
    (nodes, edges)
}

/// Settlement (§6): SCC collapse, **reverse topological** order, one **joint vector
/// pass** per component. Returns the seed's verdict (node 0).
fn settle(
    nodes: &[Node],
    edges: &[Vec<usize>],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> BodySafety {
    let mut proven: Vec<SafetyFact> = Vec::new(); // facts settled by earlier components
    let mut seed = BodySafety::Unproven(Vec::new());

    for component in crate::analyzer::induction::scc_reverse_topo(edges) {
        // A cutoff member is the ladder's (c) rung — unproven, and it poisons its
        // component (the vector pass needs every member to hold).
        let has_cutoff = component.iter().any(|&i| nodes[i].cutoff);
        let assumed: Vec<SafetyFact> = component
            .iter()
            .map(|&i| SafetyFact { callee: nodes[i].callee.clone(), input: nodes[i].input.clone() })
            .collect();

        let mut findings = Vec::new();
        let mut ok = !has_cutoff;
        if ok {
            // One joint pass: every member's fact assumed, every member verified.
            let mut table = proven.clone();
            table.extend(assumed.iter().cloned());
            for &i in &component {
                let fs = with_assumed_all(table.clone(), || {
                    verify(&nodes[i].callee, &nodes[i].input, cenv, interner)
                });
                if !fs.is_empty() {
                    ok = false;
                }
                findings.extend(fs);
            }
        }
        if ok {
            proven.extend(assumed); // carry to dependants (reverse topological order)
        }
        if component.contains(&0) {
            seed = if ok { BodySafety::Proven } else { classify(findings) };
        }
    }
    seed
}

/// Every call a candidate's body makes, with the callee resolved to a concrete instance
/// and the argument domains evaluated **per region-table row** (so each call is
/// discovered under the domain that actually reaches it).
fn calls_of(node: &Node, cenv: &ContractEnv, interner: &mut Interner) -> Vec<(ValueRef, Vec<Contract>)> {
    let Some(closure) = node.callee.as_closure() else { return Vec::new() };
    let base = capture_env(&node.callee);
    let mut out = Vec::new();
    // Per-row walk (single parameter), else one whole-body walk.
    match (single_param(&closure.lambda.params), node.input.as_slice()) {
        (Some(param), [domain]) => {
            let table = region_table(&closure.lambda.body, &param, cenv);
            for sel in select(&table, domain) {
                let mut env = base.clone();
                env.insert(param.clone(), sel.region.clone());
                collect_calls(&sel.result, &closure, &env, cenv, interner, &mut out);
            }
        }
        _ => {
            let mut env = base.clone();
            bind_pattern(&closure.lambda.params, &Contract::Tuple(node.input.clone()), &mut env);
            collect_calls(&closure.lambda.body, &closure, &env, cenv, interner, &mut out);
        }
    }
    out
}

/// An existing candidate for the same instance whose domain **covers** the target.
fn covering_node(
    nodes: &[Node],
    target: &ValueRef,
    targs: &[Contract],
    interner: &mut Interner,
) -> Option<usize> {
    let cands: Vec<(usize, Vec<Contract>)> = nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| n.callee == *target)
        .map(|(i, n)| (i, n.input.clone()))
        .collect();
    cands.into_iter().find(|(_, input)| {
        let call = Contract::Tuple(targs.to_vec());
        let dom = Contract::Tuple(input.clone());
        matches!(subcontract(&call, &dom, interner), Verdict::Proven)
    })
    .map(|(i, _)| i)
}

fn shape_of(v: &ValueRef) -> crate::ast::Lambda {
    v.as_fn().map(|f| f.shape().clone()).unwrap_or_else(|| {
        crate::ast::Lambda {
            params: crate::ast::Pat::Wild,
            body: Box::new(crate::ast::Expr::Const(v.clone())),
            act_kind: crate::ast::ActKind::Pure,
        }
    })
}

/// Install a whole fact table for the duration of `body` (the joint pass's assumption).
fn with_assumed_all<R>(facts: Vec<SafetyFact>, body: impl FnOnce() -> R) -> R {
    let saved = ASSUMED.with(|a| std::mem::replace(&mut *a.borrow_mut(), facts));
    let out = body();
    ASSUMED.with(|a| *a.borrow_mut() = saved);
    out
}

/// Verify one member under the currently-assumed facts (the partition rule).
fn verify(callee: &ValueRef, args: &[Contract], cenv: &ContractEnv, interner: &mut Interner) -> Vec<Finding> {
    let Some(closure) = callee.as_closure() else { return Vec::new() };
    match (single_param(&closure.lambda.params), args) {
        (Some(param), [domain]) => verify_by_partition(callee, &closure, &param, domain, cenv, interner),
        _ => {
            let mut env = capture_env(callee);
            bind_pattern(&closure.lambda.params, &Contract::Tuple(args.to_vec()), &mut env);
            analyze(&closure.lambda.body, &env, cenv, interner).findings
        }
    }
}

/// Collect every application in `e` whose callee resolves through the closure's captured
/// environment to a concrete function, paired with its argument domains under `env`.
/// Nested lambdas are not descended (a distinct instance); a spread argument declines
/// (no positional mapping).
fn collect_calls(
    e: &crate::ast::Expr,
    closure: &crate::value::Closure,
    env: &TypeEnv,
    cenv: &ContractEnv,
    interner: &mut Interner,
    out: &mut Vec<(ValueRef, Vec<Contract>)>,
) {
    use crate::ast::{AccessForm, Arg, Bind, Element, Expr, Field, MatchItem, TemplatePart};
    match e {
        Expr::Const(_) | Expr::Ref(_) | Expr::Lambda(_) => {}
        Expr::Apply { callee, args } => {
            if let Some(target) = resolve_callee(callee, closure) {
                let mut domains = Vec::new();
                let mut clean = true;
                for a in args {
                    match a {
                        Arg::Expr(x) => domains.push(analyze(x, env, cenv, interner).contract),
                        Arg::Spread(_) => clean = false,
                    }
                }
                if clean {
                    out.push((target, domains));
                }
            }
            collect_calls(callee, closure, env, cenv, interner, out);
            for a in args {
                let (Arg::Expr(x) | Arg::Spread(x)) = a;
                collect_calls(x, closure, env, cenv, interner, out);
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                collect_calls(a, closure, env, cenv, interner, out);
            }
        }
        Expr::Match(m) => {
            if let Some(s) = &m.scrutinee {
                collect_calls(s, closure, env, cenv, interner, out);
            }
            for item in &m.items {
                match item {
                    MatchItem::Bind(Bind { value, .. }) => collect_calls(value, closure, env, cenv, interner, out),
                    MatchItem::Stmt(x) => collect_calls(x, closure, env, cenv, interner, out),
                    MatchItem::Arm(arm) => {
                        if let Some(g) = &arm.guard {
                            collect_calls(g, closure, env, cenv, interner, out);
                        }
                        collect_calls(&arm.result, closure, env, cenv, interner, out);
                    }
                }
            }
        }
        Expr::TupleCons(els) => {
            for el in els {
                let (Element::Expr(x) | Element::Spread(x)) = el;
                collect_calls(x, closure, env, cenv, interner, out);
            }
        }
        Expr::RecordCons(fs) => {
            for f in fs {
                match f {
                    Field::Field { value, .. } | Field::Spread(value) => {
                        collect_calls(value, closure, env, cenv, interner, out)
                    }
                    Field::Computed { key, value } => {
                        collect_calls(key, closure, env, cenv, interner, out);
                        collect_calls(value, closure, env, cenv, interner, out);
                    }
                }
            }
        }
        Expr::Access { target, form, .. } => {
            collect_calls(target, closure, env, cenv, interner, out);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(x) => collect_calls(x, closure, env, cenv, interner, out),
                AccessForm::Slice { lo, hi } => {
                    for x in [lo, hi].into_iter().flatten() {
                        collect_calls(x, closure, env, cenv, interner, out);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    collect_calls(x, closure, env, cenv, interner, out);
                }
            }
        }
        Expr::Write { value, .. } => collect_calls(value, closure, env, cenv, interner, out),
    }
}

/// The concrete function a callee expression names, via the closure's captures.
fn resolve_callee(callee: &crate::ast::Expr, closure: &crate::value::Closure) -> Option<ValueRef> {
    let crate::ast::Expr::Ref(crate::ast::Ref::Immutable(crate::ast::BindingRef::Name(n))) = callee else {
        return None;
    };
    match closure.env.lookup(n) {
        Some(Binding::Value(v)) if v.is_function() => Some(v),
        _ => None,
    }
}

#[cfg(test)]
mod graph_tests {
    use super::*;
    use crate::oracle::harness::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    #[test]
    fn mutual_recursion_closes_via_the_joint_vector_pass() {
        // f -> g -> f, and the String reaches f's `x + 1`. Proving `f` ALONE cannot
        // discharge its call to `g` — only `f`'s own fact would be assumed. The joint
        // pass assumes every member of the component, which is what makes the mutual
        // edge resolvable and the deep trap visible.
        let mut i = Interner::new();
        let m = f("f = (x) => x == 0 ? g(\"x\") : x + 1\ng = (y) => f(y)\nf", &mut i);
        let zero = Contract::Equals(i.integer(0));
        let v = prove(&m, std::slice::from_ref(&zero), &ContractEnv::new(), &mut i);
        assert!(matches!(v, BodySafety::Refuted(_)), "the mutual deep trap must refute: {v:?}");
    }

    #[test]
    fn a_self_loop_settles_as_one_component() {
        // countDown's recursive call is *covered* by the seed's domain, so discovery
        // reuses that candidate rather than minting a new one — the component is a
        // self-loop and the joint pass proves it.
        let mut i = Interner::new();
        let d = Contract::Intersection(
            Box::new(Contract::GreaterEq(crate::rational::Rational::from(0))),
            Box::new(Contract::Mod { n: num_bigint::BigInt::from(1), r: num_bigint::BigInt::from(0) }),
        );
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        assert!(prove(&cd, &[d], &ContractEnv::new(), &mut i).is_proven());
    }

    #[test]
    fn discovery_terminates_on_a_divergent_body() {
        // Safety is not termination: `f(n) = f(n)` is safe, and the graph must close
        // rather than expand forever — the target is covered by the seed.
        let mut i = Interner::new();
        let lp = f("f = (n) => f(n)\nf", &mut i);
        let num = Contract::Kind(crate::contract::Kind::Number);
        assert!(prove(&lp, std::slice::from_ref(&num), &ContractEnv::new(), &mut i).is_proven());
    }

    #[test]
    fn an_uncovered_recursive_chain_is_cut_off_not_expanded() {
        // A concrete chain (5 -> 4 -> ...) is never covered by its predecessor, so the
        // shape-repeat cutoff (C§13.3(2)) stops discovery and the verdict is the ladder's
        // (c) rung — unproven, never an invented covering domain.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        let v = prove(&cd, std::slice::from_ref(&five), &ContractEnv::new(), &mut i);
        assert!(!v.is_proven(), "an uncovered chain must not be proven by expansion: {v:?}");
    }
}
