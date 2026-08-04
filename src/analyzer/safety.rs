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
//! **What is deliberately left unproven.** A **seed's** `I` is never synthesized — it is
//! the call's or the `where`'s own domain. For a **dependency** target that repeats an
//! active shape, **the drift is what closes** ([author, 2026-08-03]): the descent
//! certificate derives the orbit envelope the recursion actually visits from its exact
//! start (`countDown(5)` → `Range(0,5) ∧ Mod(1,0)`), composed from the program's own
//! drift arithmetic — C§13.3(1)'s "derived grounding contracts". The derivation
//! **proposes** the fact domain; the same vector induction as every fact must prove it,
//! and where no certificate applies the honest cutoff stays `Unproven`. Kind-menu
//! widening and accumulated reaching domains remain the forbidden, imported shapes.

use std::cell::Cell;

use crate::analyzer::factcache;
use crate::analyzer::induction::{self, Candidate, Claim};
use crate::analyzer::region::{region_table, select};
use crate::analyzer::{
    Analysis, Finding, SafetyDemand, Severity, TypeEnv, analyze_in_world, bind_pattern,
    world_for_act,
};
use crate::contract::OpSafety;
use crate::contract::{Contract, ContractEnv, Verdict, subcontract};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

/// The three-voiced verdict for `BodySafe(instance, I)`.
#[derive(Debug, Clone)]
pub enum BodySafety {
    /// Every operation the body reaches over `I` discharges.
    Proven,
    /// A definitely-reached operation traps — carries diagnostics and the nested
    /// typed demands, including any primitive operation witness.
    Refuted(BodySafetyEvidence),
    /// Neither proved nor refuted (an unproven operation, or a recursive call whose
    /// domain no assumed fact covers). **Safety-unproven blocks at a seat**
    /// (late-resolution §5) — it is not a licence to proceed.
    Unproven(BodySafetyEvidence),
}

/// Evidence retained by a failed body-safety judgment. The demand list is recursive
/// through a `Vec`, so a body fact can preserve the exact operation witness or nested
/// body voice that caused it without changing the finite value layout.
#[derive(Debug, Clone, Default)]
pub struct BodySafetyEvidence {
    pub findings: Vec<Finding>,
    pub demands: Vec<SafetyDemand>,
}

impl BodySafety {
    /// Whether the fact is proven (the only voice that discharges a seat).
    pub fn is_proven(&self) -> bool {
        matches!(self, BodySafety::Proven)
    }

    pub fn findings(&self) -> &[Finding] {
        match self {
            BodySafety::Proven => &[],
            BodySafety::Refuted(evidence) | BodySafety::Unproven(evidence) => &evidence.findings,
        }
    }
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
    prove_claim(callee, args, Claim::Safety, cenv, interner)
}

/// Settle any [`Claim`] over `(callee, args)` through the one global fact graph
/// (C§13.2a): discover the candidates, collapse to SCCs, settle in reverse topological
/// order with a joint vector pass per cyclic component.
///
/// Claim-general because discovery is claim-independent — the dependency structure of a
/// body is a property of the body, not of what is being asked about it. Safety,
/// completion and return claims are three questions over the **same** graph, which is why
/// they must not grow three graphs.
pub(crate) fn prove_claim(
    callee: &ValueRef,
    args: &[Contract],
    claim: Claim,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> BodySafety {
    if callee.as_closure().is_none() {
        return BodySafety::Unproven(BodySafetyEvidence::default()); // not a known function
    }

    // Keyed by the **fact node**, not by a global "am I settling?" flag. That distinction
    // is the whole point (C§13.4): a re-entrant query on *this* node is a recursive
    // reference and resolves through its hypothesis; a query on any *other* node is
    // genuinely settled. A global flag answers both from hypotheses and so drops the traps
    // of callees that hold none — measured as a false accept on 2026-08-01.
    let Some(key) = factcache::key(callee, args, &claim, cenv, interner) else {
        let (nodes, edges) = discover(callee, args, &claim, cenv, interner);
        return settle(nodes, &edges, claim, cenv, interner).verdict;
    };
    match factcache::lookup(&key) {
        Some(factcache::Cached::Settled(v)) => return v,
        Some(factcache::Cached::InProgress) => return assumed(callee, args, &claim, interner),
        None => {}
    }
    // Resolution by coverage [author, 2026-08-03]: a proven fact whose domain contains
    // the asked one answers in this same resolution step — `instanceof` on semantics,
    // without a chain walk: the subcontract test *is* the resolution, never a recovery
    // after a failure. The exact-pointer hit above is its trivial case.
    if let Some(v) = factcache::covering(&key, interner) {
        return v;
    }

    factcache::begin(&key);
    let (nodes, edges) = discover(callee, args, &claim, cenv, interner);
    let settlement = settle(nodes, &edges, claim, cenv, interner);
    let outer = factcache::finish(&key, &settlement.verdict);
    if outer {
        // The graph settled dependencies before their dependants. They are ordinary
        // proven facts of their complete semantic keys, not seed-local evidence; keep
        // them so later outcome dimensions consult rather than re-settle them.
        for candidate in &settlement.proven {
            if let Some(key) = factcache::key(
                &candidate.callee,
                &candidate.args,
                &candidate.claim,
                cenv,
                interner,
            ) {
                factcache::record_settled(key, BodySafety::Proven);
            }
        }
    }
    settlement.verdict
}

/// The verdict for a **recursive reference** — a query for a node already being settled.
/// C§13.2: recursive references never unfold; they resolve through the assumed fact. No
/// hypothesis covering this call's domain means the third voice, never a pass.
fn assumed(
    callee: &ValueRef,
    args: &[Contract],
    claim: &Claim,
    interner: &mut Interner,
) -> BodySafety {
    let held = match claim {
        Claim::Safety => induction::safety_assumed(callee, args, interner),
        Claim::Completes => induction::completes_assumed(callee, args, interner),
        Claim::Return(want) => {
            induction::hypothesis_for(callee, args, interner).is_some_and(|got| {
                matches!(
                    crate::contract::subcontract(&got, want, interner),
                    crate::contract::Verdict::Proven
                )
            })
        }
    };
    if held {
        BodySafety::Proven
    } else {
        BodySafety::Unproven(BodySafetyEvidence::default())
    }
}

thread_local! {
    /// Set while a completion settlement is running — the **re-entrancy guard**. A
    /// settlement analyzes bodies, whose calls reach `analyze_apply` again; without this
    /// each such call would launch a *nested* settlement. Inside one, a call resolves
    /// through the assumed facts instead (the same discipline as
    /// `induction::without_inference` for return facts).
    static SETTLING: Cell<bool> = const { Cell::new(false) };

    /// Set during every body-safety verification, including the diagnostic pass after
    /// a vector failure. Calls not covered by the current graph must remain Unproven;
    /// launching another settlement here would recurse past the graph cutoff.
    static VERIFYING_SAFETY: Cell<bool> = const { Cell::new(false) };
}

/// Whether a body-safety verification is active. The hypothesis table covers normal
/// vector passes; `VERIFYING_SAFETY` also covers post-settlement diagnostic recovery.
pub(crate) fn safety_context_active() -> bool {
    VERIFYING_SAFETY.with(Cell::get) || induction::safety_hypotheses_active()
}

/// Whether **every path** through `callee`'s body over `args` produces a value — settled
/// through the same graph, with [`Claim::Completes`]. `false` is the honest third voice
/// (unproven), never a claim that it falls through.
pub fn completes(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> bool {
    if callee.as_closure().is_none() {
        return false;
    }
    // Already settling: resolve through the assumed facts, never nest.
    if SETTLING.with(Cell::get) {
        return induction::completes_assumed(callee, args, interner);
    }
    SETTLING.with(|f| f.set(true));
    let out = matches!(
        prove_claim(callee, args, Claim::Completes, cenv, interner),
        BodySafety::Proven
    );
    SETTLING.with(|f| f.set(false));
    out
}

/// Verify the fact **per region-table row** (§5's partition rule). `region::select`
/// already narrows each selected row to `remaining ∩ row.region`, so each row is checked
/// under exactly the part of `I` that reaches it.
///
/// **RT-14 witness discipline** is preserved: a finding from a non-exact (may-region) row
/// is downgraded, because an over-approximate candidate authorizes no refutation. Its
/// typed demand is weakened to `Unproven`, which still blocks at policy without falsely
/// claiming a witness; diagnostic severity no longer has to encode that third voice.
fn verify_by_partition(
    callee: &ValueRef,
    closure: &crate::value::Closure,
    param: &str,
    domain: &Contract,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> SafetyReport {
    let table = region_table(&closure.lambda.body, param, cenv, interner);
    let base = capture_env(callee);
    let mut out = SafetyReport::default();
    for sel in select(&table, domain, interner) {
        let mut env = base.clone();
        env.insert(param.to_string(), sel.region.clone());
        let analysis = analyze_in_world(
            &sel.result,
            &env,
            cenv,
            world_for_act(closure.lambda.act_kind),
            interner,
        );
        out.extend_analysis(analysis, sel.exact);
    }
    out
}

/// A may-region row cannot refute (RT-14): an `Error` becomes advisory.
fn downgrade(f: Finding) -> Finding {
    match f.severity {
        Severity::Error => Finding {
            severity: Severity::Warning,
            ..f
        },
        Severity::Warning => f,
    }
}

/// The evidence returned by one body verification. Diagnostics remain available for
/// policy and reporting, while typed demands decide whether a failed safety judgment is
/// `Refuted` or merely `Unproven`.
#[derive(Default)]
struct SafetyReport {
    findings: Vec<Finding>,
    demands: Vec<SafetyDemand>,
}

impl SafetyReport {
    fn extend_analysis(&mut self, analysis: Analysis, exact: bool) {
        if exact {
            self.findings.extend(analysis.findings);
            self.demands.extend(analysis.safety_demands);
            return;
        }
        self.findings
            .extend(analysis.findings.into_iter().map(downgrade));
        self.demands.extend(
            analysis
                .safety_demands
                .into_iter()
                .map(weaken_may_region_demand),
        );
    }
}

/// RT-14: a demand observed only in an over-approximate row cannot retain refutation
/// evidence. It becomes the honest third voice, matching the diagnostic downgrade.
fn weaken_may_region_demand(demand: SafetyDemand) -> SafetyDemand {
    match demand {
        SafetyDemand::Operation(mut operation) => {
            if matches!(operation.verdict, OpSafety::Refuted(_)) {
                operation.verdict = OpSafety::Unproven;
            }
            SafetyDemand::Operation(operation)
        }
        SafetyDemand::Body(mut body) => {
            body.verdict = match body.verdict {
                BodySafety::Refuted(evidence) => {
                    BodySafety::Unproven(weaken_refutation_evidence(evidence))
                }
                other => other,
            };
            SafetyDemand::Body(body)
        }
    }
}

pub(crate) fn weaken_refutation_evidence(evidence: BodySafetyEvidence) -> BodySafetyEvidence {
    BodySafetyEvidence {
        findings: evidence.findings.into_iter().map(downgrade).collect(),
        demands: evidence
            .demands
            .into_iter()
            .map(weaken_may_region_demand)
            .collect(),
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

/// Three-voiced from the body's typed judgments first, with findings as the fallback
/// for safety checks that do not yet expose a dedicated verdict type. Rejecting policy
/// severity must never relabel `Unproven` as `Refuted`.
fn classify(report: SafetyReport) -> BodySafety {
    let refuted = report.demands.iter().any(|demand| match demand {
        SafetyDemand::Operation(operation) => {
            matches!(operation.verdict, OpSafety::Refuted(_))
        }
        SafetyDemand::Body(body) => matches!(body.verdict, BodySafety::Refuted(_)),
    });
    if refuted {
        return BodySafety::Refuted(BodySafetyEvidence {
            findings: report.findings,
            demands: report.demands,
        });
    }

    // Any still-untyped definite trap remains a refutation, even when a different
    // typed demand in the same body is merely Unproven. Typed Unproven diagnostics are
    // advisory until policy, so they cannot be mistaken for this fallback.
    if report
        .findings
        .iter()
        .any(|finding| finding.severity == Severity::Error)
    {
        return BodySafety::Refuted(BodySafetyEvidence {
            findings: report.findings,
            demands: report.demands,
        });
    }

    let unproven = report.demands.iter().any(|demand| match demand {
        SafetyDemand::Operation(operation) => matches!(operation.verdict, OpSafety::Unproven),
        SafetyDemand::Body(body) => matches!(body.verdict, BodySafety::Unproven(_)),
    });
    if unproven {
        return BodySafety::Unproven(BodySafetyEvidence {
            findings: report.findings,
            demands: report.demands,
        });
    }
    if report.findings.is_empty() {
        return BodySafety::Proven;
    }
    BodySafety::Unproven(BodySafetyEvidence {
        findings: report.findings,
        demands: report.demands,
    })
}

/// The captured environment as contracts — each free variable bound to `Equals(value)`.
fn capture_env(callee: &ValueRef) -> TypeEnv {
    let mut env = TypeEnv::new();
    let (Some(f), Some(closure)) = (callee.as_fn(), callee.as_closure()) else {
        return env;
    };
    for name in f.free_vars() {
        if let Some(Binding::Value(v)) = closure.env.lookup(name) {
            env.insert(
                name.clone(),
                crate::analyzer::domain::AnalysisContract::of_value(v),
            );
        }
    }
    env
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer::induction::Hypothesis;
    use crate::oracle::harness::run_source_in;
    use crate::rational::Rational;
    use num_bigint::BigInt;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    /// `GE(0) ∧ Mod(1,0)` — the non-negative integers.
    fn nonneg_ints(i: &mut Interner) -> Contract {
        Contract::intersection(
            Contract::GreaterEq(Rational::from(0)),
            Contract::Mod {
                n: BigInt::from(1),
                r: BigInt::from(0),
            },
            i,
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
        let v = prove(&cd, &[nonneg_ints(&mut i)], &ContractEnv::new(), &mut i);
        assert!(
            v.is_proven(),
            "countDown over its declared domain proves by induction: {v:?}"
        );
    }

    #[test]
    fn safety_is_not_termination_and_the_proof_still_closes() {
        // Isolation: a body that never terminates is still *safe* (divergence is not a
        // trap), and the recursive call `f(n)` is inside `I`, so it discharges. If the
        // proof were unfolding rather than closing on the fact, this would not return.
        let mut i = Interner::new();
        let loopy = f("f = (n) => f(n)\nf", &mut i);
        let v = prove(
            &loopy,
            &[Contract::Kind(crate::contract::Kind::Number)],
            &ContractEnv::new(),
            &mut i,
        );
        assert!(
            v.is_proven(),
            "safety != termination; the fact discharges the self-call: {v:?}"
        );
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
        let fact = Hypothesis {
            callee: cd.clone(),
            input: vec![five],
            claim: Claim::Safety,
        };
        let covered = induction::with_hypotheses(vec![fact], || {
            induction::safety_assumed(&cd, std::slice::from_ref(&four), &mut i)
        });
        assert!(
            !covered,
            "a narrower-but-different domain must not be discharged"
        );
    }

    #[test]
    fn a_declared_domain_fact_discharges_any_call_inside_it() {
        // The reuse that makes facts worth having: `BodySafe(f, D)` discharges every call
        // whose argument is contained in `D` — so `f(5)` needs no re-analysis of the body.
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        let fact = Hypothesis {
            callee: cd.clone(),
            input: vec![nonneg_ints(&mut i)],
            claim: Claim::Safety,
        };
        let covered = induction::with_hypotheses(vec![fact], || {
            induction::safety_assumed(&cd, std::slice::from_ref(&five), &mut i)
        });
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
#[derive(Clone)]
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
    claim: &Claim,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> (Vec<Node>, Vec<Vec<usize>>) {
    let mut nodes = vec![Node {
        callee: callee.clone(),
        input: args.to_vec(),
        cutoff: false,
    }];
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
            // A settled proven fact whose domain contains the target discharges the
            // dependency in the same resolution step — coverage as resolution, for
            // the claim this graph will be settled under.
            if let Some(key) = factcache::key(&target, &targs, claim, cenv, interner)
                && matches!(factcache::covering(&key, interner), Some(v) if v.is_proven())
            {
                continue;
            }
            let shape = shape_of(&target);
            let mut cutoff = path.contains(&shape);
            let mut input = targs;
            if cutoff {
                // [author correction, 2026-08-03] **The drift is what closes.** From an
                // exact start, the descent certificate derives the orbit envelope the
                // recursion actually visits — `Range(0,5) ∧ Mod(1,0)` for
                // `countDown(5)` — composed from the program's own drift arithmetic
                // (C§13.3(1) "derived grounding contracts"). A Kind-menu widening
                // briefly stood here; it was the imported abstract-interpretation
                // shape and is gone. The derivation **proposes** a fact domain — the
                // ordinary vector induction must still prove the fact over it — and
                // where no certificate applies, the honest cutoff remains.
                if let [single] = &input[..]
                    && let Some(envelope) = crate::analyzer::grounding::derived_orbit_domain(
                        &target, single, cenv, interner,
                    )
                {
                    // Propose the envelope node even when it equals the asked domain —
                    // the node itself is what closes (its recursive targets fall inside
                    // it and covering-reuse makes it a self-loop); duplicates are
                    // prevented by the covering check, never by skipping.
                    let derived = vec![envelope];
                    if let Some(j) = covering_node(&nodes, &target, &derived, interner) {
                        edges[i].push(j);
                        continue;
                    }
                    input = derived;
                    cutoff = false;
                }
            }
            nodes.push(Node {
                callee: target,
                input,
                cutoff,
            });
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

/// Settlement (§6) — delegated to the **one** driver in `induction`, over this graph's
/// own domain-aware edges. There is a single place components are settled; the safety
/// fact is simply the [`Claim::Safety`] node kind travelling through it.
struct Settlement {
    verdict: BodySafety,
    proven: Vec<Candidate>,
}

fn settle(
    nodes: Vec<Node>,
    edges: &[Vec<usize>],
    claim: Claim,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Settlement {
    let seed = nodes[0].clone();
    let candidates: Vec<Candidate> = nodes
        .into_iter()
        .map(|n| Candidate {
            callee: n.callee,
            args: n.input,
            claim: claim.clone(),
            cutoff: n.cutoff,
        })
        .collect();
    let result = induction::settle_components(candidates, edges, cenv, interner);
    let settled = result
        .proven
        .iter()
        .any(|c| c.callee == seed.callee && c.args == seed.input);
    if settled {
        return Settlement {
            verdict: BodySafety::Proven,
            proven: result.proven,
        };
    }
    // Not settled. A **safety** claim re-verifies only to recover refuting/unproven
    // diagnostics; that diagnostic pass may never upgrade the graph's `Unproven` to
    // `Proven` (notably when a shape-cutoff dependency remains unresolved).
    // Completion/return likewise retain the graph verdict.
    let verdict = match claim {
        Claim::Safety => match verify(&seed.callee, &seed.input, cenv, interner) {
            BodySafety::Refuted(evidence) => BodySafety::Refuted(evidence),
            BodySafety::Unproven(evidence) => BodySafety::Unproven(evidence),
            BodySafety::Proven => BodySafety::Unproven(BodySafetyEvidence::default()),
        },
        Claim::Completes | Claim::Return(_) => BodySafety::Unproven(BodySafetyEvidence::default()),
    };
    Settlement {
        verdict,
        proven: result.proven,
    }
}

/// Every call a candidate's body makes, with the callee resolved to a concrete instance
/// and the argument domains evaluated **per region-table row** (so each call is
/// discovered under the domain that actually reaches it).
fn calls_of(
    node: &Node,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Vec<(ValueRef, Vec<Contract>)> {
    let Some(closure) = node.callee.as_closure() else {
        return Vec::new();
    };
    let base = capture_env(&node.callee);
    let mut out = Vec::new();
    // Discovery may contract-evaluate local bindings, projections, callees, and
    // arguments, but it may not settle a nested safety fact. Keep the existing
    // verification guard active so any nested application contributes a coarse
    // Unproven result and is then discovered structurally by `collect_calls` itself.
    let saved = VERIFYING_SAFETY.with(|active| active.replace(true));
    // Per-row walk (single parameter), else one whole-body walk.
    match (single_param(&closure.lambda.params), node.input.as_slice()) {
        (Some(param), [domain]) => {
            let table = region_table(&closure.lambda.body, &param, cenv, interner);
            for sel in select(&table, domain, interner) {
                let mut env = base.clone();
                env.insert(param.clone(), sel.region.clone());
                collect_calls(&sel.result, &closure, &env, cenv, interner, &mut out);
            }
        }
        _ => {
            let mut env = base.clone();
            let arg_tuple = Contract::tuple(node.input.clone(), interner);
            bind_pattern(&closure.lambda.params, &arg_tuple, &mut env);
            collect_calls(
                &closure.lambda.body,
                &closure,
                &env,
                cenv,
                interner,
                &mut out,
            );
        }
    }
    VERIFYING_SAFETY.with(|active| active.set(saved));
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
    cands
        .into_iter()
        .find(|(_, input)| {
            let call = Contract::tuple(targs.to_vec(), interner);
            let dom = Contract::tuple(input.clone(), interner);
            matches!(subcontract(&call, &dom, interner), Verdict::Proven)
        })
        .map(|(i, _)| i)
}

fn shape_of(v: &ValueRef) -> crate::ast::Lambda {
    v.as_fn()
        .map(|f| f.shape().clone())
        .unwrap_or_else(|| crate::ast::Lambda {
            params: crate::ast::Pat::Wild,
            body: Box::new(crate::ast::Expr::Const(v.clone())),
            act_kind: crate::ast::ActKind::Pure,
        })
}

/// Verify a **completion** claim: every completing path through the body over `I`
/// produces a value. The single-parameter case uses the same §5 partition as safety,
/// discovery, and return facts: selected results are analyzed under their effective row
/// regions, and exact rows must cover the input. Whole-body analysis would lose the
/// guard narrowing (`n != 0` in `countDown`) and miss the active completion fact.
pub(crate) fn verify_completes(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> bool {
    // A realized completing-without-value execution permanently refutes the universal
    // completion claim. This is AP-30's positive witness path and is tried before the
    // abstract proof, just as realized return refutations are.
    if crate::analyzer::refute::realized_completion(callee, args, interner).is_some() {
        return false;
    }
    let Some(closure) = callee.as_closure() else {
        return false;
    };
    if let (Some(param), [domain]) = (single_param(&closure.lambda.params), args) {
        let table = region_table(&closure.lambda.body, &param, cenv, interner);
        let base = capture_env(callee);
        for sel in select(&table, domain, interner) {
            let mut env = base.clone();
            env.insert(param.clone(), sel.region);
            let selected = analyze_in_world(
                &sel.result,
                &env,
                cenv,
                world_for_act(closure.lambda.act_kind),
                interner,
            );
            if !matches!(selected.completion, crate::analyzer::Completion::Produces) {
                return false;
            }
        }

        let mut remainder = domain.clone();
        for row in &table {
            if row.exact {
                remainder = if matches!(
                    subcontract(&remainder, &row.region, interner),
                    Verdict::Proven
                ) {
                    Contract::Bottom
                } else {
                    Contract::difference(remainder, row.region.clone(), interner)
                };
            }
        }
        return matches!(
            subcontract(&remainder, &Contract::Bottom, interner),
            Verdict::Proven
        );
    }

    let mut env = capture_env(callee);
    let arg_tuple = Contract::tuple(args.to_vec(), interner);
    bind_pattern(&closure.lambda.params, &arg_tuple, &mut env);
    matches!(
        analyze_in_world(
            &closure.lambda.body,
            &env,
            cenv,
            world_for_act(closure.lambda.act_kind),
            interner,
        )
        .completion,
        crate::analyzer::Completion::Produces
    )
}

/// Verify one member under the currently-assumed facts (the partition rule).
pub(crate) fn verify(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> BodySafety {
    let saved = VERIFYING_SAFETY.with(|active| active.replace(true));
    let verdict = classify(verify_inner(callee, args, cenv, interner));
    VERIFYING_SAFETY.with(|active| active.set(saved));
    verdict
}

fn verify_inner(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> SafetyReport {
    let Some(closure) = callee.as_closure() else {
        return SafetyReport::default();
    };
    match (single_param(&closure.lambda.params), args) {
        (Some(param), [domain]) => {
            verify_by_partition(callee, &closure, &param, domain, cenv, interner)
        }
        _ => {
            let mut env = capture_env(callee);
            let arg_tuple = Contract::tuple(args.to_vec(), interner);
            bind_pattern(&closure.lambda.params, &arg_tuple, &mut env);
            let analysis = analyze_in_world(
                &closure.lambda.body,
                &env,
                cenv,
                world_for_act(closure.lambda.act_kind),
                interner,
            );
            let mut report = SafetyReport::default();
            report.extend_analysis(analysis, true);
            report
        }
    }
}

/// The contract a member **produces** over `args`, evaluated by the same §5 partition the
/// safety check uses (C§13.2: the region-table walk contract-evaluates the result
/// expressions of the selected rows).
///
/// The partition is not an optimization here — it is what makes a recursive return claim
/// provable at all. `countDown = (n) => n == 0 ? 0 : countDown(n - 1)` over the
/// non-negative integers only keeps `n - 1` inside that domain **because the else row
/// carries `n ≠ 0`**; analyzed whole, `n` still admits `0`, `n - 1` reaches `-1`, no
/// assumed fact covers the call, and the claim fails on a body that plainly satisfies it.
/// Safety saw this correctly and the return did not, purely because only one of them
/// walked the rows.
///
/// `None` when the partition does not apply (not a single plain parameter — the §5
/// multi-parameter case is owed); the caller falls back to the whole-body summary.
pub(crate) fn produced_by_partition(
    callee: &ValueRef,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Contract> {
    let closure = callee.as_closure()?;
    let (param, domain) = match (single_param(&closure.lambda.params), args) {
        (Some(param), [domain]) => (param, domain),
        _ => return None,
    };
    let table = region_table(&closure.lambda.body, &param, cenv, interner);
    let base = capture_env(callee);
    let mut parts = Vec::new();
    for sel in select(&table, domain, interner) {
        let mut env = base.clone();
        env.insert(param.to_string(), sel.region.clone());
        parts.push(
            analyze_in_world(
                &sel.result,
                &env,
                cenv,
                world_for_act(closure.lambda.act_kind),
                interner,
            )
            .contract,
        );
    }
    // No row selected means no path through the body over this domain produces anything.
    if parts.is_empty() {
        None
    } else {
        Some(crate::analyzer::union_of(parts, interner))
    }
}

/// Collect every application in `e` whose joint annotated operand resolves to concrete
/// functions, paired with the correlated argument domains under `env`. This is the
/// discovery face of the same AP-29 representation used by live application analysis:
/// a local `choice = [f, x] | [g, y]` followed by `choice[0](choice[1])` contributes
/// `(f, x)` and `(g, y)`, never an unresolved access and never synthesized cross-pairs.
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
    use crate::ast::{AccessForm, Arg, Element, Expr, Field, MatchItem, TemplatePart};
    match e {
        Expr::Const(_) | Expr::Ref(_) | Expr::Lambda(_) => {}
        Expr::Apply { callee, args } => {
            let callee_analysis = analyze_in_world(
                callee,
                env,
                cenv,
                world_for_act(closure.lambda.act_kind),
                interner,
            );
            let mut arguments = Vec::new();
            let clean = args.iter().all(|argument| match argument {
                Arg::Expr(expression) => {
                    arguments.push(
                        analyze_in_world(
                            expression,
                            env,
                            cenv,
                            world_for_act(closure.lambda.act_kind),
                            interner,
                        )
                        .annotated,
                    );
                    true
                }
                Arg::Spread(_) => false,
            });
            if clean {
                let operand =
                    super::correlated_access_operand(callee, args, env).unwrap_or_else(|| {
                        super::application::operand_from_annotated(
                            &callee_analysis.annotated,
                            &arguments,
                        )
                    });
                let (alternatives, _) = super::application::live_alternatives(&operand);
                for alternative in alternatives {
                    let callee_contract = alternative.callee.erase(interner);
                    let domains: Vec<Contract> = alternative
                        .arguments
                        .iter()
                        .map(|argument| argument.erase(interner))
                        .collect();
                    for target in super::application::classify_callees(&callee_contract, interner) {
                        if let super::application::CalleeAlternative::Known(target) = target {
                            out.push((target, domains.clone()));
                        }
                    }
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
            let mut body_env = env.clone();
            for item in &m.items {
                match item {
                    MatchItem::Bind(binding) => {
                        collect_calls(&binding.value, closure, &body_env, cenv, interner, out);
                        let analysis = analyze_in_world(
                            &binding.value,
                            &body_env,
                            cenv,
                            world_for_act(closure.lambda.act_kind),
                            interner,
                        );
                        let mut ignored = Vec::new();
                        super::analyze_bind(
                            &binding.target,
                            &analysis.annotated,
                            &mut body_env,
                            &mut ignored,
                            cenv,
                            interner,
                        );
                    }
                    MatchItem::Stmt(x) => collect_calls(x, closure, &body_env, cenv, interner, out),
                    MatchItem::Arm(arm) => {
                        if let Some(g) = &arm.guard {
                            collect_calls(g, closure, &body_env, cenv, interner, out);
                        }
                        collect_calls(&arm.result, closure, &body_env, cenv, interner, out);
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

#[cfg(test)]
mod graph_tests {
    use super::*;
    use crate::oracle::harness::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    #[test]
    fn a_shape_repeat_without_an_admitted_fact_is_unproven() {
        // f(0) -> g("x") -> f("x"). The second f is a distinct domain-indexed fact,
        // but its shape already occurs on this inventory path, so §4a admits no node
        // through that path. Without ladder (b)'s generalized fact or an exact-chain
        // witness, the graph must stop at the honest third voice. The program seat still
        // rejects safety-unproven; this test locks the graph's witness discipline.
        let mut i = Interner::new();
        let m = f(
            "f = (x) => x == 0 ? g(\"x\") : x + 1\ng = (y) => f(y)\nf",
            &mut i,
        );
        let zero = Contract::Equals(i.integer(0));
        let v = prove(&m, std::slice::from_ref(&zero), &ContractEnv::new(), &mut i);
        assert!(
            matches!(v, BodySafety::Unproven(_)),
            "shape-cutoff evidence cannot refute: {v:?}"
        );
    }

    #[test]
    fn an_outer_graph_publishes_proven_dependency_facts() {
        // f(Number) depends on g(Number). The reverse-topological pass proves g first;
        // that result is an ordinary fact of g's complete key, not private evidence for
        // f. Later outcome dimensions must be able to consult it without re-settling.
        factcache::clear();
        let mut i = Interner::new();
        let root = f("f = (x) => g(x)\ng = (y) => y + 1\nf", &mut i);
        let g = match root.as_closure().unwrap().env.lookup("g") {
            Some(Binding::Value(v)) => v,
            other => panic!("f must capture g, got {other:?}"),
        };
        let args = vec![Contract::Kind(crate::contract::Kind::Number)];
        assert!(prove(&root, &args, &ContractEnv::new(), &mut i).is_proven());

        let key = factcache::key(&g, &args, &Claim::Safety, &ContractEnv::new(), &mut i)
            .expect("captured closure has a fact key");
        assert!(
            matches!(
                factcache::lookup(&key),
                Some(factcache::Cached::Settled(BodySafety::Proven))
            ),
            "the dependency component must remain memoized"
        );
    }

    #[test]
    fn a_self_loop_settles_as_one_component() {
        // countDown's recursive call is *covered* by the seed's domain, so discovery
        // reuses that candidate rather than minting a new one — the component is a
        // self-loop and the joint pass proves it.
        let mut i = Interner::new();
        let d = Contract::intersection(
            Contract::GreaterEq(crate::rational::Rational::from(0)),
            Contract::Mod {
                n: num_bigint::BigInt::from(1),
                r: num_bigint::BigInt::from(0),
            },
            &mut i,
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
    fn a_concrete_chain_closes_through_its_derived_orbit_not_expansion() {
        // [author, 2026-08-03] A concrete chain (5 → 4 → …) is never expanded node by
        // node — **the drift is what closes**. At the shape repeat the descent
        // certificate derives the orbit envelope (`Range(0,5) ∧ Mod(1,0)`) from the
        // program's own arithmetic, and the ordinary induction proves the fact over
        // it, so the safe chain proves with no contracts…
        let mut i = Interner::new();
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let five = Contract::Equals(i.integer(5));
        assert!(
            prove(
                &cd,
                std::slice::from_ref(&five),
                &ContractEnv::new(),
                &mut i,
            )
            .is_proven(),
            "the derived orbit closes the safe concrete chain"
        );

        // …while an edge with no descent certificate (0 → 1 drifts **up**) derives no
        // envelope: the honest cutoff stays unproven — never proven by expansion, and
        // never refuted without a witness represented at the asked domain.
        let tr = f(
            "f = (x) => x == 0 ? f(1) : (x == 1 ? 1 : 1 + \"x\")\nf",
            &mut i,
        );
        let zero = Contract::Equals(i.integer(0));
        let v = prove(
            &tr,
            std::slice::from_ref(&zero),
            &ContractEnv::new(),
            &mut i,
        );
        assert!(
            !v.is_proven(),
            "no certificate, no envelope, no proof: {v:?}"
        );
        assert!(
            !matches!(v, BodySafety::Refuted(_)),
            "no refutation without a represented witness: {v:?}"
        );
    }
}

#[cfg(test)]
mod completion_tests {
    use super::*;
    use crate::oracle::harness::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    #[test]
    fn recursive_fall_through_is_not_claimed_to_produce() {
        // Blocker 3's shape. `f(0)` matches the only arm and calls `f(1)`; under
        // `Equals(1)` NO arm matches, so the body completes without a value. The old
        // cycle assumption *asserted* `Produces`; settling completion on the fact makes
        // `f(1)` a distinct node whose own claim fails, so `f(0)`'s cannot hold either.
        let mut i = Interner::new();
        let g = f("f = (x) => x :: {\n 0 => f(1)\n }\nf", &mut i);
        let zero = Contract::Equals(i.integer(0));
        assert!(
            !completes(&g, std::slice::from_ref(&zero), &ContractEnv::new(), &mut i),
            "a recursive fall-through must not be claimed to produce"
        );
    }

    #[test]
    fn an_exhaustive_recursion_does_complete() {
        // The converse, so the rule is not blanket: countDown covers its domain on every
        // path, and the recursive call is covered by the seed's own fact.
        let mut i = Interner::new();
        let d = Contract::intersection(
            Contract::GreaterEq(crate::rational::Rational::from(0)),
            Contract::Mod {
                n: num_bigint::BigInt::from(1),
                r: num_bigint::BigInt::from(0),
            },
            &mut i,
        );
        let cd = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        assert!(
            completes(&cd, &[d], &ContractEnv::new(), &mut i),
            "countDown produces on every path"
        );
    }
}
