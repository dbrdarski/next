//! Program-level analysis entry — the missing top of the analyzer (plan T1.1).
//!
//! Every analyzer path below this point answers a question somebody asked. Until now
//! nobody asked: `main.rs` only ran the oracle, and the analyzer was reachable solely from
//! unit tests, which is how ~3000 lines got built without a consumer. This module is the
//! consumer.
//!
//! **Demand origins.** An author-written `where` supplies a declared domain, so the pass
//! verifies `BodySafe(instance, DeclaredInput)` through
//! [`crate::analyzer::safety::prove`]. Every executable binding RHS, slot initializer, and
//! statement is also a compulsory fixed-rule demand: operation safety fires even when a
//! result is discarded, while completion is demanded only at expecting seats.
//!
//! **Analysis never runs the program.** The oracle's module runner evaluates items
//! eagerly in effect world; calling it here would execute the program at compile time.
//! Instead the pass builds closures ([`make_closure_in`]) without touching their bodies,
//! then analyzes executable expressions symbolically in item order. The narrow AP-30
//! exception is a fuel-bounded Pure call used only to certify a represented completion
//! witness; Effect/Mutator bodies are never run by this pass. Named contract expressions
//! are statically evaluated by the contract layer rather than mistaken for runtime
//! constructor calls.

use std::collections::{HashMap, HashSet};

use super::{
    Analysis, Completion, Finding, SafetyDemand, Severity, TypeEnv, analyze_bind, analyze_in_world,
    demand, grounding, induction, safety,
};
use crate::analyzer::TrapClass;
use crate::analyzer::domain::AnalysisContract;
use crate::analyzer::refute::ClaimVerdict;
use crate::ast::{Bind, BindTarget, Expr, Item, Lambda, Module, Pat};
use crate::contract::{Contract, ContractEnv, Verdict, disjoint, eval_contract, subcontract};
use crate::env::{Binding, Env, Scope};
use crate::interner::Interner;
use crate::oracle::{World, make_closure_in};
use crate::value::ValueRef;

/// The executable source seat that originated a compulsory analysis demand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecutableOrigin {
    Binding { item: usize, name: Option<String> },
    SlotInitializer { item: usize, name: String },
    Statement { item: usize },
}

/// Whether completion must produce a value at the source seat.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutableSeat {
    Expecting,
    Statement,
}

/// The typed record retained for an executable demand before program policy is
/// reduced to accept/reject. World and seat stay explicit dependencies; the expression's
/// inferred output and completion voice remain available to later consumers.
#[derive(Debug, Clone)]
pub struct ExecutableDemand {
    pub origin: ExecutableOrigin,
    pub seat: ExecutableSeat,
    pub world: World,
    pub contract: Contract,
    pub annotated_contract: AnalysisContract,
    pub completion: Completion,
    pub findings: Vec<Finding>,
    pub safety_demands: Vec<SafetyDemand>,
}

/// A source `where` demand for `BodySafe(instance, DeclaredInput)`. The declaration's
/// acceptance policy is intentionally separate from this retained three-voice fact.
#[derive(Debug, Clone)]
pub struct DeclaredBodySafetyDemand {
    pub name: String,
    pub callee: ValueRef,
    pub domain: Vec<Contract>,
    pub verdict: safety::BodySafety,
}

/// A declared return demand retained through the program-policy boundary. `verdict`
/// preserves all three voices; a `Refuted` record owns the represented arguments and
/// produced value that made the declaration false.
#[derive(Debug, Clone)]
pub struct ReturnDemand {
    pub name: String,
    pub domain: Vec<Contract>,
    pub required: Contract,
    pub verdict: ClaimVerdict,
}

/// A termination (grounding) demand adjudicated at a program seat, all three voices
/// retained. Principle 9 as stamped [user, 2026-08-03]: the gray warn-and-compile tier
/// is gone — `Unproven` and `Refuted` are both compile errors, like every other
/// unproven obligation.
#[derive(Debug, Clone)]
pub struct GroundingDemand {
    pub callee: ValueRef,
    pub domain: Vec<Contract>,
    pub verdict: grounding::Verdict,
    /// GR-24's SCC certificate, consumed at the seat per GR-26's row: the recursion's
    /// every cycle observes the world afresh, so completion is the world's decision
    /// and the iteration bound is excused (D-α/D-β). Only ever `true` alongside
    /// `Unproven` — an all-`Grounded` call keeps ordinary proven completion, and a
    /// witnessed refutation is never swallowed.
    pub world_decided: bool,
}

/// The result of analyzing a whole module.
#[derive(Debug, Clone)]
pub struct ProgramVerdict {
    /// Every finding raised, in item order.
    pub findings: Vec<Finding>,
    /// Every declared return contract checked, including concrete refutation evidence and
    /// honest unproven outcomes. Policy may reject both latter voices, but does not erase
    /// their semantic distinction.
    pub return_demands: Vec<ReturnDemand>,
    /// Every declared body-safety fact checked at a `where`, with all three voices
    /// retained after policy emits any rejecting diagnostic.
    pub body_safety_demands: Vec<DeclaredBodySafetyDemand>,
    /// Every checked executable seat, in item order. Keeping this record makes a
    /// regression to “only `where` was checked” directly observable.
    pub executable_demands: Vec<ExecutableDemand>,
    /// Every termination demand adjudicated on a recursive callee, deduplicated per
    /// (callee, domain), with the verdict retained through policy.
    pub grounding_demands: Vec<GroundingDemand>,
}

impl ProgramVerdict {
    /// A module is accepted when program policy emitted no `Error`. `Warning`s do not
    /// reject; both a concrete refutation and a blocking `Unproven` verdict surface as
    /// errors, while their typed records remain distinct.
    pub fn accepted(&self) -> bool {
        !self.findings.iter().any(|f| f.severity == Severity::Error)
    }

    /// The rejecting findings only.
    pub fn errors(&self) -> impl Iterator<Item = &Finding> {
        self.findings
            .iter()
            .filter(|f| f.severity == Severity::Error)
    }
}

/// Analyze a module without running it: collect closure identities and named contracts,
/// then walk every item in source order, checking executable seats and `where` demands.
pub fn analyze_program(module: &Module, interner: &mut Interner) -> ProgramVerdict {
    let scope = Scope::root();
    analyze_program_in(module, &scope, interner)
}

/// Analyze in a caller-supplied initial environment. This is the check-mode seam
/// for prelude, host, and eventually imported bindings: their values are available
/// symbolically, but no native or NEXT function is invoked while installing them.
pub(crate) fn analyze_program_in(
    module: &Module,
    scope: &Env,
    interner: &mut Interner,
) -> ProgramVerdict {
    analyze_program_project(module, scope, &ContractEnv::new(), interner).0
}

/// The project-check seam (E12/C§14 — static whole-program resolution): analyze one
/// module with `seed_cenv` pre-installed (imported named contracts), returning the
/// module's own contract environment so the project driver can harvest its exported
/// contract names for downstream importers.
pub(crate) fn analyze_program_project(
    module: &Module,
    scope: &Env,
    seed_cenv: &ContractEnv,
    interner: &mut Interner,
) -> (ProgramVerdict, ContractEnv) {
    // Snapshot before `collect`: that pass installs every lambda into the shared
    // late-binding scope, but eager item analysis must still see module bindings
    // only after their source-order declaration.
    let mut tenv = TypeEnv::new();
    for (name, binding) in scope.visible_bindings() {
        if let Binding::Value(value) = binding {
            tenv.insert(name, AnalysisContract::of_value(value));
        }
    }
    let (values, cenv, contract_names, collect_findings) =
        collect(module, scope, seed_cenv, interner);
    // C§9's group-aware consumers: when the environment defines recursive named
    // contracts, install the ambient group for this analysis's whole extent, so
    // narrowing, dead arms, exhaustiveness, and the where demands resolve
    // `Contract::Ref` through the group walk. Ref-free environments skip it.
    let _rec_group = if cenv.values().any(crate::contract::mentions_ref) {
        Some(crate::contract::rec_group_guard(
            crate::contract::RecGroup::new(cenv.clone()),
        ))
    } else {
        None
    };
    let top_world = if module.name.is_some() {
        World::Pure
    } else {
        World::Effect
    };

    let mut findings = collect_findings;
    let mut return_demands = Vec::new();
    let mut body_safety_demands = Vec::new();
    let mut executable_demands = Vec::new();
    let mut grounding_demands = Vec::new();

    // E12's self-prefix lint: naming a sibling under this module's own first dotted
    // segment is legal — inside the project the bare name suffices. (No manifest
    // exists yet; the shared first segment is the v1 project proxy.)
    if let Some(name) = &module.name
        && let Some(prefix) = name.split('.').next()
    {
        for item in &module.items {
            if let Item::Import(imp) = item
                && imp.module.split('.').next() == Some(prefix)
            {
                findings.push(Finding {
                    class: TrapClass::ArgumentObligation,
                    severity: Severity::Warning,
                    message: format!(
                        "self-prefix module reference `{}` — inside this project the bare \
                         name suffices",
                        imp.module
                    ),
                });
            }
        }
    }

    // Declarations first [author, 2026-08-03]: a `where` is a fact, not a statement, so
    // its position among the executable items is immaterial — every seat resolves
    // against the same settled declarations regardless of source order.
    for item in &module.items {
        if let Item::Where(w) = item {
            analyze_where(
                w,
                &values,
                &cenv,
                &mut findings,
                &mut return_demands,
                &mut body_safety_demands,
                &mut grounding_demands,
                interner,
            );
        }
    }

    for (item_index, item) in module.items.iter().enumerate() {
        match item {
            Item::Bind(b) => {
                let name = match &b.target {
                    BindTarget::Name(name) => Some(name.clone()),
                    BindTarget::Pattern(_) => None,
                };

                // Contract definitions are static analyzer bindings (E11), not calls to
                // runtime values named `Range`, `Union`, etc.
                if name
                    .as_ref()
                    .is_some_and(|name| contract_names.contains(name))
                {
                    continue;
                }

                let analysis = match (&b.target, &b.value) {
                    (BindTarget::Name(name), Expr::Lambda(_)) => values
                        .get(name)
                        .cloned()
                        .map(|value| {
                            let annotated = AnalysisContract::of_value(value);
                            Analysis {
                                contract: annotated.erase(interner),
                                annotated,
                                findings: Vec::new(),
                                safety_demands: Vec::new(),
                                completion: Completion::Produces,
                            }
                        })
                        .unwrap_or_else(|| {
                            analyze_in_world(&b.value, &tenv, &cenv, top_world, interner)
                        }),
                    _ => analyze_in_world(&b.value, &tenv, &cenv, top_world, interner),
                };
                ground_executable(
                    &analysis,
                    &cenv,
                    &mut findings,
                    &mut grounding_demands,
                    interner,
                );
                let annotated = record_executable(
                    ExecutableOrigin::Binding {
                        item: item_index,
                        name: name.clone(),
                    },
                    ExecutableSeat::Expecting,
                    top_world,
                    analysis,
                    &mut findings,
                    &mut executable_demands,
                );
                analyze_bind(
                    &b.target,
                    &annotated,
                    &mut tenv,
                    &mut findings,
                    &cenv,
                    interner,
                );
                if let (Some(name), Contract::Equals(value)) = (name, annotated.erase(interner)) {
                    scope.define(&name, Binding::Value(value));
                }
            }
            Item::SlotDecl(slot) => {
                let analysis = analyze_in_world(&slot.init, &tenv, &cenv, World::Pure, interner);
                ground_executable(
                    &analysis,
                    &cenv,
                    &mut findings,
                    &mut grounding_demands,
                    interner,
                );
                let annotated = record_executable(
                    ExecutableOrigin::SlotInitializer {
                        item: item_index,
                        name: slot.name.clone(),
                    },
                    ExecutableSeat::Expecting,
                    World::Pure,
                    analysis,
                    &mut findings,
                    &mut executable_demands,
                );
                tenv.insert(slot.name.clone(), annotated);
            }
            Item::ActBind(ab) => {
                if let Some(value) = values.get(&ab.name) {
                    tenv.insert(ab.name.clone(), AnalysisContract::of_value(value.clone()));
                }
            }
            Item::Stmt(expr) => {
                let analysis = analyze_in_world(expr, &tenv, &cenv, top_world, interner);
                statement_lints(expr, &analysis, &values, scope, &mut findings, interner);
                ground_executable(
                    &analysis,
                    &cenv,
                    &mut findings,
                    &mut grounding_demands,
                    interner,
                );
                record_executable(
                    ExecutableOrigin::Statement { item: item_index },
                    ExecutableSeat::Statement,
                    top_world,
                    analysis,
                    &mut findings,
                    &mut executable_demands,
                );
            }
            // Handled in the declaration pre-pass above.
            Item::Where(_) => {}
            Item::Import(_) => {}
        }
    }

    (
        ProgramVerdict {
            findings,
            return_demands,
            body_safety_demands,
            executable_demands,
            grounding_demands,
        },
        cenv,
    )
}

#[allow(clippy::too_many_arguments)]
fn analyze_where(
    w: &crate::ast::Where,
    values: &HashMap<String, ValueRef>,
    cenv: &ContractEnv,
    findings: &mut Vec<Finding>,
    return_demands: &mut Vec<ReturnDemand>,
    body_safety_demands: &mut Vec<DeclaredBodySafetyDemand>,
    grounding_demands: &mut Vec<GroundingDemand>,
    interner: &mut Interner,
) {
    let Some(callee) = values.get(&w.name) else {
        findings.push(malformed(
            &w.name,
            "names no function binding in this module",
        ));
        return;
    };
    let Some(declared) = eval_contract(&w.input_contract, cenv, interner) else {
        findings.push(malformed(
            &w.name,
            "declares an input contract this pass cannot evaluate statically \
             (C§12.2 computed contract arguments are owed)",
        ));
        return;
    };

    let Some(args) = spread_input(callee, declared) else {
        findings.push(malformed(
            &w.name,
            "declares an input contract whose arity does not match the function's parameters",
        ));
        return;
    };

    let body_safety = safety::prove(callee, &args, cenv, interner);
    findings.extend(verdict_findings(&w.name, &body_safety));
    body_safety_demands.push(DeclaredBodySafetyDemand {
        name: w.name.clone(),
        callee: callee.clone(),
        domain: args.clone(),
        verdict: body_safety,
    });

    // The declared domain also demands termination (Principle 9 as stamped): a `where`
    // asserts the function over this whole domain, divergence included.
    ground_demand(callee, &args, cenv, findings, grounding_demands, interner);

    // The declared **return** contract is a demand (C§13.1): the `where` asks whether
    // the body produces a value satisfying it, adjudicated here, at the ask site.
    if let Some(ret) = eval_contract(&w.return_contract, cenv, interner) {
        failure_overlap_demand(&w.name, &ret, findings, interner);
        let asker = format!("where {}", w.name);
        let verdict = super::demand::returns(callee, &args, &ret, &asker, cenv, interner);
        match &verdict {
            ClaimVerdict::Proven => {}
            ClaimVerdict::Refuted(witness) => findings.push(malformed(
                &w.name,
                &format!(
                    "declares a return contract refuted by represented arguments {:?}, \
                     which produce {:?}",
                    witness.arguments, witness.produced
                ),
            )),
            // Unproven rejects. A declared return the compiler cannot discharge is not
            // a declaration it may assume — the same discipline as safety-unproven
            // (late-resolution §5), and the reason the third voice is un-suppressible.
            ClaimVerdict::Unproven => findings.push(malformed(
                &w.name,
                "declares a return contract that cannot be proven of its body",
            )),
        }
        return_demands.push(ReturnDemand {
            name: w.name.clone(),
            domain: args,
            required: ret,
            verdict,
        });
    }
}

fn record_executable(
    origin: ExecutableOrigin,
    seat: ExecutableSeat,
    world: World,
    analysis: Analysis,
    findings: &mut Vec<Finding>,
    demands: &mut Vec<ExecutableDemand>,
) -> AnalysisContract {
    let mut local = Vec::new();
    if seat == ExecutableSeat::Expecting {
        demand(&analysis, &mut local);
    }
    local.extend(analysis.findings.iter().cloned());
    local.extend(safety_policy_findings(&analysis.safety_demands));
    findings.extend(local.iter().cloned());
    let annotated = analysis.annotated.clone();
    let safety_demands = analysis.safety_demands.clone();
    demands.push(ExecutableDemand {
        origin,
        seat,
        world,
        contract: analysis.contract,
        annotated_contract: analysis.annotated,
        completion: analysis.completion,
        findings: local,
        safety_demands,
    });
    annotated
}

/// Apply late-resolution §5 at an executable consuming seat. Refutations already own
/// error diagnostics from the trapping rule that established them; an `Unproven`
/// judgment gains its unsuppressible Error here, after the typed voice has been retained.
fn safety_policy_findings(demands: &[SafetyDemand]) -> Vec<Finding> {
    demands
        .iter()
        .filter_map(|demand| match demand {
            SafetyDemand::Operation(operation)
                if matches!(operation.verdict, crate::contract::OpSafety::Unproven) =>
            {
                Some(Finding {
                    class: TrapClass::OperationSafety,
                    severity: Severity::Error,
                    message: format!(
                        "cannot prove `{:?}` safe at this executable seat",
                        operation.operation
                    ),
                })
            }
            SafetyDemand::Body(body) if matches!(body.verdict, safety::BodySafety::Unproven(_)) => {
                Some(Finding {
                    class: TrapClass::OperationSafety,
                    severity: Severity::Error,
                    message: "callee body safety cannot be proven at this executable seat".into(),
                })
            }
            SafetyDemand::Operation(_) | SafetyDemand::Body(_) => None,
        })
        .collect()
}

/// Walk the items once, building the module environment (function values, so that late
/// binding resolves a call to a sibling) and the named-contract environment.
///
/// Two passes over the items would let a `where` precede its function, and a named
/// contract precede its use — but `eval_contract` resolves a reference to an *already
/// evaluated* definition, so contracts stay single-pass and in order (recursive source
/// contracts are a separate increment, plan T2.4). Values get the two passes, since a
/// closure captures `scope` by reference and is order-independent.
fn collect(
    module: &Module,
    scope: &Env,
    seed_cenv: &ContractEnv,
    interner: &mut Interner,
) -> (
    HashMap<String, ValueRef>,
    ContractEnv,
    HashSet<String>,
    Vec<Finding>,
) {
    let mut values = HashMap::new();
    let mut cenv = seed_cenv.clone();
    let mut contract_names = HashSet::new();
    let mut findings = Vec::new();
    let mut deferred: Vec<(String, Expr)> = Vec::new();

    for item in &module.items {
        match item {
            Item::Bind(Bind {
                target: BindTarget::Name(name),
                value: Expr::Lambda(l),
                ..
            }) => {
                define(name, l, scope, &mut values, interner);
            }
            Item::ActBind(ab) => define(&ab.name, &ab.lambda, scope, &mut values, interner),
            // A non-lambda binding of a contract expression is a **named contract**
            // (`Percent = Range(0, 100)` — C§12.2). Other bindings are handled by the
            // later executable walk, where their contracts can depend on prior items.
            Item::Bind(Bind {
                target: BindTarget::Name(name),
                value,
                ..
            }) => {
                if let Some(c) = eval_contract(value, &cenv, interner) {
                    cenv.insert(name.clone(), c);
                    contract_names.insert(name.clone());
                } else {
                    // A literal constant binding is a module value the sibling
                    // closures capture (`limit = 5`; `f = (n) => n <= limit ? …`).
                    // Defining it into the shared late-binding scope here is what
                    // lets `capture_env` — and through it the *instantiated* region
                    // table (C§12.3) — see the capture during the `where` pre-pass,
                    // whose source position is immaterial. Computed bindings stay
                    // runtime-only and their captures honestly opaque.
                    if let Expr::Const(v) = value {
                        scope.define(name, Binding::Value(v.clone()));
                    }
                    // Deferred to the C§9 second pass: a recursive named contract
                    // fails in-order evaluation only because it mentions itself or
                    // its group.
                    deferred.push((name.clone(), value.clone()));
                }
            }
            _ => {}
        }
    }

    // The C§9 second pass (T2.4): recursive named contracts are ordinary bindings
    // mentioning themselves or their group. An inadmissible group is a **definition
    // error** — the whole group is rejected (members define each other), the names
    // still count as contract definitions (suppressing executable-walk noise on the
    // same items), and nothing enters the environment.
    match crate::contract::eval_recursive_contract_bindings(&deferred, &cenv, interner) {
        Ok(defs) => {
            for (name, c) in defs {
                contract_names.insert(name.clone());
                cenv.insert(name, c);
            }
        }
        Err(err) => {
            for (name, _) in &deferred {
                contract_names.insert(name.clone());
            }
            let message = match err {
                crate::contract::recursive::DefError::NegativeOccurrence { name } => format!(
                    "recursive contract definition error: `{name}` occurs at negative \
                     polarity (under a Difference exclusion) — no least fixpoint exists"
                ),
                crate::contract::recursive::DefError::Unguarded { name, hint } => format!(
                    "recursive contract definition error: the reference cycle through \
                     `{name}` crosses no Tuple/Record constructor — {hint}"
                ),
            };
            findings.push(Finding {
                class: TrapClass::OperationSafety,
                severity: Severity::Error,
                message,
            });
        }
    }

    // Every sibling is now present in the shared late-binding scope. Close the
    // captured graphs in a stable order so analyzer-created function values obey
    // the same universal interning invariant as oracle-created values.
    let mut names: Vec<String> = values.keys().cloned().collect();
    names.sort();
    for name in names {
        let raw = values[&name].clone();
        if interner.value_is_closed(&raw) {
            let canonical = interner.close_value_graph(raw);
            scope.define(&name, Binding::Value(canonical.clone()));
            values.insert(name, canonical);
        }
    }
    (values, cenv, contract_names, findings)
}

fn define(
    name: &str,
    lambda: &Lambda,
    scope: &Env,
    values: &mut HashMap<String, ValueRef>,
    interner: &mut Interner,
) {
    let v = make_closure_in(lambda, scope, interner);
    scope.define(name, Binding::Value(v.clone()));
    values.insert(name.to_string(), v);
}

/// Map a declared input contract onto the function's parameters.
///
/// A single-parameter `where` declares that parameter's contract directly; a multi-element
/// one desugars to a tuple over the argument list (desugar `where_clause`), so its parts
/// map positionally. `None` on an arity mismatch — a real authoring error, not a shrug.
///
/// **One mismatch is undetectable here, by construction.** `where_clause` desugars a
/// multi-element list to `TupleCons`, which is the same shape a single tuple-valued
/// parameter produces — so on a one-parameter function, `where (Number, Number)` and
/// `where ((Number, Number))` are indistinguishable by the time this sees a `Contract`.
/// The reading taken is the legal one (the parameter is a 2-tuple). Distinguishing them
/// would need the element count preserved on `Where`, which is an AST change and not this
/// slice's business.
fn spread_input(callee: &ValueRef, declared: Contract) -> Option<Vec<Contract>> {
    let arity = match &callee.as_closure()?.lambda.params {
        Pat::Tuple(elems) => elems.len(),
        _ => 1,
    };
    match declared {
        _ if arity == 1 => Some(vec![declared]),
        Contract::Tuple(parts) if parts.len() == arity => {
            Some(parts.iter().map(|c| (**c).clone()).collect())
        }
        _ => None,
    }
}

/// Turn a settled safety fact into findings.
///
/// `Refuted` and `Unproven` both reject: late-resolution §5 makes safety-unproven a
/// compile error, un-suppressible — a `where` the compiler cannot discharge is not a
/// `where` it may assume. A voice that carries no finding of its own still rejects, with
/// the fact named, so the verdict is never silently empty.
fn verdict_findings(name: &str, v: &safety::BodySafety) -> Vec<Finding> {
    let (voice, mut fs, unproven) = match v {
        safety::BodySafety::Proven => return Vec::new(),
        safety::BodySafety::Refuted(evidence) => {
            ("is refuted over", evidence.findings.clone(), false)
        }
        safety::BodySafety::Unproven(evidence) => {
            ("cannot be proven over", evidence.findings.clone(), true)
        }
    };
    if unproven || !fs.iter().any(|finding| finding.severity == Severity::Error) {
        fs.push(malformed(
            name,
            &format!("{voice} its declared input domain"),
        ));
    }
    fs
}

/// A `where` this pass cannot act on. `ArgumentObligation` is the closest existing class —
/// the declared input *is* the argument obligation — but no trap class names a malformed
/// signature, because a `where` is analyzer-facing metadata with no evaluation behavior
/// (AST `Where`), so it can never trap at runtime and the §6 concordance has no row for it.
// [ask-author] Should a malformed/undischargeable `where` (unknown name, arity mismatch,
// statically un-evaluable contract expression) carry its own diagnostic class rather than
// borrowing `ArgumentObligation`? These are authoring errors in the signature itself, not
// trap-class rejections, and the concordance has no row for them.
fn malformed(name: &str, why: &str) -> Finding {
    Finding {
        class: TrapClass::ArgumentObligation,
        severity: Severity::Error,
        message: format!("`where {name}` {why}"),
    }
}

/// B6's Failure-overlap rule [1.0.2], at the one adapter boundary that exists today —
/// a declared fallible return. Where a union alternative is provably on the `Failure`
/// rail, every success alternative must be **proven** disjoint from `Failure`: a success
/// value inhabiting the failure shape would be swallowed by the discharge match, so the
/// explicit success wrapper is demanded where the union is formed. Ordinary emptiness
/// checking, nothing new; `conform` inherits this same boundary rule when it lands.
fn failure_overlap_demand(
    name: &str,
    declared: &Contract,
    findings: &mut Vec<Finding>,
    interner: &mut Interner,
) {
    let failure = Contract::failure(interner);
    let alternatives = union_alternatives(declared);
    let on_failure_rail: Vec<bool> = alternatives
        .iter()
        .map(|alt| matches!(subcontract(alt, &failure, interner), Verdict::Proven))
        .collect();
    if !on_failure_rail.iter().any(|&rail| rail) {
        return;
    }
    for (alt, rail) in alternatives.iter().zip(on_failure_rail) {
        if !rail && !disjoint(alt, &failure) {
            findings.push(malformed(
                name,
                &format!(
                    "declares a fallible return whose success alternative {alt:?} is not \
                     proven disjoint from Failure — wrap successes explicitly (B6)"
                ),
            ));
        }
    }
}

/// The statement-seat lints (E10/B6). A bare **pure** expression's result goes
/// nowhere; a discarded **fallible-effect** result silently drops its Failure rail
/// (fires only when an alternative of the produced contract is provably on the
/// Failure rail — absence of a lint is always sound).
fn statement_lints(
    expr: &Expr,
    analysis: &Analysis,
    values: &HashMap<String, ValueRef>,
    scope: &Env,
    findings: &mut Vec<Finding>,
    interner: &mut Interner,
) {
    match act_statement(expr, values, scope) {
        None => findings.push(Finding {
            class: TrapClass::ArgumentObligation,
            severity: Severity::Warning,
            message: "this pure expression's result goes nowhere (bare-statement lint)".into(),
        }),
        Some(crate::ast::ActKind::Effect) => {
            let failure = Contract::failure(interner);
            let fallible = union_alternatives(&analysis.contract)
                .iter()
                .any(|alt| matches!(subcontract(alt, &failure, interner), Verdict::Proven));
            if fallible {
                findings.push(Finding {
                    class: TrapClass::ArgumentObligation,
                    severity: Severity::Warning,
                    message: "a fallible effect result is discarded — its Failure rail is \
                              silently dropped (discarded-effect lint)"
                        .into(),
                });
            }
        }
        Some(_) => {}
    }
}

/// The act kind of a statement-position application's callee, or `None` for a pure
/// statement (including calls to pure functions — their results are discarded too).
fn act_statement(
    expr: &Expr,
    values: &HashMap<String, ValueRef>,
    scope: &Env,
) -> Option<crate::ast::ActKind> {
    let Expr::Apply { callee, .. } = expr else {
        return None;
    };
    let Expr::Ref(crate::ast::Ref::Immutable(crate::ast::BindingRef::Name(n))) = &**callee else {
        return None;
    };
    let v = values.get(n).cloned().or_else(|| match scope.lookup(n) {
        Some(Binding::Value(v)) => Some(v),
        _ => None,
    })?;
    if v.as_native().is_some() {
        return Some(crate::ast::ActKind::Effect);
    }
    v.as_closure()
        .map(|c| c.lambda.act_kind)
        .filter(|k| *k != crate::ast::ActKind::Pure)
}

/// Adjudicate every recursive callee the analyzed expression applied: each distinct
/// `(callee, argument domain)` pair from the typed body-safety demands also demands
/// termination.
fn ground_executable(
    analysis: &Analysis,
    cenv: &ContractEnv,
    findings: &mut Vec<Finding>,
    grounding_demands: &mut Vec<GroundingDemand>,
    interner: &mut Interner,
) {
    for demand in &analysis.safety_demands {
        if let SafetyDemand::Body(body) = demand {
            ground_demand(
                &body.callee,
                &body.arguments,
                cenv,
                findings,
                grounding_demands,
                interner,
            );
        }
    }
}

/// Principle 9 as stamped [user, 2026-08-03]: recursion must be proven to terminate.
/// `Grounded` passes silently; `Refuted` errors with its witness (the program provably
/// never finishes from that written start); `Unproven` errors honestly (termination is
/// not shown — the gray warn-and-compile tier is gone). Non-recursive callees carry no
/// demand, and each `(callee, domain)` is adjudicated once.
fn ground_demand(
    callee: &ValueRef,
    arguments: &[Contract],
    cenv: &ContractEnv,
    findings: &mut Vec<Finding>,
    grounding_demands: &mut Vec<GroundingDemand>,
    interner: &mut Interner,
) {
    if !induction::is_recursive(callee) {
        return;
    }
    if grounding_demands
        .iter()
        .any(|g| g.callee == *callee && g.domain == arguments)
    {
        return;
    }
    let verdict = grounding::ground_args(callee, arguments, cenv, interner);
    // GR-26's aggregation order: a witnessed refutation is never swallowed; an
    // all-Grounded call keeps ordinary proven completion; only the honest Unproven
    // may be excused by GR-24's world-decided certificate — and only for an Effect
    // callee (at pure/mutation seats such a callee is already a world-admission
    // error, so the callee's act kind is the seat condition).
    let world_decided =
        matches!(verdict, grounding::Verdict::Unproven) && grounding::world_decided(callee);
    match &verdict {
        grounding::Verdict::Grounded => {}
        grounding::Verdict::Refuted(refutation) => findings.push(Finding {
            class: TrapClass::ArgumentObligation,
            severity: Severity::Error,
            message: format!(
                "this recursion never finishes: starting from {}, every step stays away \
                 from a finishing case (Principle 9: divergence is an error)",
                refutation.witness
            ),
        }),
        grounding::Verdict::Unproven if world_decided => {}
        grounding::Verdict::Unproven => findings.push(Finding {
            class: TrapClass::ArgumentObligation,
            severity: Severity::Error,
            message: "this recursive call is not proven to finish (Principle 9: \
                      unproven termination is an error, never a warning)"
                .into(),
        }),
    }
    grounding_demands.push(GroundingDemand {
        callee: callee.clone(),
        domain: arguments.to_vec(),
        verdict,
        world_decided,
    });
}

/// The flattened alternatives of a (possibly nested) `Union`; a non-union contract is
/// its own single alternative.
fn union_alternatives(contract: &Contract) -> Vec<Contract> {
    match contract {
        Contract::Union(a, b) => {
            let mut out = union_alternatives(a);
            out.extend(union_alternatives(b));
            out
        }
        _ => vec![contract.clone()],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer::{CompletionWitness, SafetyDemand};
    use crate::contract::OpSafety;

    /// Through the shared front end (`check_source`), so these tests exercise the same
    /// lex/parse/desugar path the CLI does.
    fn check(src: &str) -> (ProgramVerdict, Interner) {
        crate::oracle::harness::check_source(src).expect("lexes, parses, desugars")
    }

    /// Adversarial-review counterexample (2026-08-04): `g(3)` descends 3 → 1.5 →
    /// 0.75 → … — it never completes and never traps (`/` is total via
    /// Indeterminate; the `+` never receives a recursive value because no recursive
    /// call returns). Before the produced-path sharpening, the recursive call's
    /// produced coarsened to `Top`, and refutation sampling then minted
    /// `Add: Refuted([0, "s"])` — a manufactured refutation of a trap-free body,
    /// from a value `g(1.5)` cannot produce. The law: imprecision yields Unproven,
    /// never a manufactured verdict; refutations need represented witnesses.
    #[test]
    fn a_divergent_recursion_is_not_falsely_refuted_from_a_sampled_top() {
        let (v, _) = check("g = (n) => n == 0 ? \"a\" : g(n / 2) + \"s\"\nx = g(3)\n");
        assert!(!v.accepted(), "safety stays unproven and blocks the seat");
        let refuted = v
            .executable_demands
            .iter()
            .flat_map(|d| &d.safety_demands)
            .any(|d| match d {
                SafetyDemand::Operation(o) => matches!(o.verdict, OpSafety::Refuted(_)),
                SafetyDemand::Body(b) => matches!(b.verdict, safety::BodySafety::Refuted(_)),
            });
        assert!(
            !refuted,
            "no refutation may be minted without a represented witness: {:?}",
            v.findings
        );
    }

    /// McCarthy 91's end state (2026-08-04): safety, the return claim over `Number`,
    /// completion, **and termination** all prove — the nested `m(m(n + 11))` resolves
    /// the inner return through the (90, 101] zone induction, the outer expecting
    /// seat's completion through the completion fact, and grounding through the
    /// nested landing-zone certificate (grid §6's closed form; GR specimen 7:
    /// "proven — the negative battery's baseline"). The declared program accepts.
    #[test]
    fn mccarthy_91_accepts_with_every_voice_proven() {
        let (v, _) = check(
            "m where (Number) => Number\n\
             m = (n) => n > 100 ? n - 10 : m(m(n + 11))\n\
             x = m(1)\n",
        );
        assert!(
            v.body_safety_demands.iter().all(|d| d.verdict.is_proven()),
            "declared body safety proves: {:?}",
            v.body_safety_demands
        );
        assert!(
            v.return_demands
                .iter()
                .all(|d| matches!(d.verdict, ClaimVerdict::Proven)),
            "the declared return claim proves: {:?}",
            v.return_demands
        );
        assert!(
            v.grounding_demands
                .iter()
                .all(|d| matches!(d.verdict, grounding::Verdict::Grounded)),
            "the landing-zone certificate grounds every demand: {:?}",
            v.grounding_demands
        );
        assert!(v.accepted(), "McCarthy 91 accepts: {:?}", v.findings);
    }

    /// The certificate's negative twins, pinned so its conditions cannot silently
    /// widen. Lap net `d + s = 0` (`n - 11` against `+11`) is the exact self-loop
    /// family — `m(100)` recurs on itself forever; triple nesting is Knuth's k-fold
    /// generalization, divergent for McCarthy's own constants (2·10 > 11). Both must
    /// stay honestly rejected.
    #[test]
    fn the_zone_certificate_declines_its_divergent_twins() {
        let (lap_zero, _) = check("m = (n) => n > 100 ? n - 11 : m(m(n + 11))\nx = m(1)\n");
        assert!(
            !lap_zero.accepted(),
            "a lap net of zero laps forever and must not ground"
        );
        let (k3, _) = check("m = (n) => n > 100 ? n - 10 : m(m(m(n + 11)))\nx = m(1)\n");
        assert!(
            !k3.accepted(),
            "one nesting level only — the k-fold generalization diverges"
        );
    }

    /// The point of the whole pass: an author declares a domain, the body traps somewhere
    /// inside it, and the module is rejected — with no call site anywhere in the program.
    /// Before this entry existed, nothing asked the question.
    #[test]
    fn a_where_whose_body_traps_over_its_declared_domain_is_rejected() {
        let (v, _) = check(
            "f where (Number) => Number\nf = (n) => n + 1\ng where (String) => Number\ng = (s) => s + 1\n",
        );
        assert!(
            !v.accepted(),
            "a String input to `+` must reject: {:?}",
            v.findings
        );
    }

    /// The complement — and the harder half. A declared domain that *does* discharge must
    /// be accepted, or the pass is just a rejector.
    #[test]
    fn a_where_whose_body_is_safe_over_its_declared_domain_is_accepted() {
        let (v, _) = check("f where (Number) => Number\nf = (n) => n + 1\n");
        assert!(
            v.accepted(),
            "a Number input to `+` discharges: {:?}",
            v.findings
        );
    }

    /// E-8's whole reason for existing: the declared domain is what makes recursion
    /// provable. `countDown` over `GE(0)` keeps `n - 1` inside the domain, so the fact
    /// closes by induction — no unfolding, no growth.
    #[test]
    fn a_declared_domain_lets_recursion_close_by_induction() {
        // Non-negative **integers**: `n - 1` stays inside the declared domain, so the
        // recursive call discharges against the assumed fact and the body is analyzed once.
        // Integrality surviving `−` is an operation-rulebook (F0) transfer — which is why
        // F0 had to be built before this could work.
        let (v, _) = check(
            "countDown where (Intersection(GreaterEq(0), Mod(1, 0))) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n",
        );
        assert!(
            v.accepted(),
            "declared-domain recursion proves by induction: {:?}",
            v.findings
        );
    }

    /// The same program over a domain **without** integrality must NOT prove — and this is
    /// the analyzer being right, not a gap to paper over. `GreaterEq(0)` admits `0.5`, which
    /// never satisfies `n == 0` and recurses to `-0.5`, outside the declared domain; no
    /// assumed fact covers that call. The honest verdict is unproven, which rejects.
    ///
    /// Pinned deliberately: making this accept would require growing the domain until it
    /// stabilized, which is the reverted reaching engine. If this test ever flips to
    /// accepted, check `tests/machinery_gate.rs` before believing it.
    #[test]
    fn a_declared_domain_that_omits_integrality_does_not_prove() {
        let (v, _) = check(
            "countDown where (GreaterEq(0)) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n",
        );
        assert!(
            !v.accepted(),
            "0.5 leaves the declared domain — unproven, not accepted"
        );
    }

    /// Program policy may reject both failed voices, but it must retain which one the
    /// declared BodySafe judgment actually produced. Otherwise an unproven proof is
    /// indistinguishable from a represented refutation at the public boundary.
    #[test]
    fn declared_body_safety_retains_all_three_voices() {
        let (proven, _) = check("f where (Number) => Number\nf = (n) => n + 1\n");
        assert!(matches!(
            proven.body_safety_demands[0].verdict,
            safety::BodySafety::Proven
        ));

        let (refuted, mut interner) = check("g where (String) => Number\ng = (s) => s + 1\n");
        let safety::BodySafety::Refuted(evidence) = &refuted.body_safety_demands[0].verdict else {
            panic!("the String-domain body must be refuted");
        };
        let operation = evidence
            .demands
            .iter()
            .find_map(|demand| match demand {
                SafetyDemand::Operation(operation) => Some(operation),
                SafetyDemand::Body(_) => None,
            })
            .expect("the body refutation retains its primitive operation evidence");
        let OpSafety::Refuted(witness) = &operation.verdict else {
            panic!("the nested operation demand must own a refuting witness");
        };
        assert!(
            crate::oracle::eval_prim(operation.operation, witness, &mut interner).is_err(),
            "the retained operand tuple must actually trap in the oracle"
        );
        assert!(
            operation
                .inputs
                .iter()
                .zip(witness)
                .all(|(contract, value)| contract.contains(value)),
            "the retained witness must inhabit the declared operation inputs"
        );

        // The changed-domain mutual case is the honest third voice: the String-domain
        // dependency fails, but no witness is represented at the declared `Number`
        // domain, so the graph reports Unproven — never a manufactured refutation.
        // (The former specimen — countDown over `GreaterEq(0)` — is now genuinely
        // Proven: the basis rung closes its recursion, and safety is a separate
        // question from termination.)
        let (unproven, _) = check(
            "g = (y) => f(y)\n\
             f where (Number) => Number\n\
             f = (x) => x == 0 ? g(\"x\") : x + 1\n",
        );
        assert!(matches!(
            unproven.body_safety_demands[0].verdict,
            safety::BodySafety::Unproven(_)
        ));

        let (operation_unproven, _) = check(
            "useFn where (Function) => Top\n\
             useFn = (candidate) => candidate + 1\n",
        );
        assert!(
            matches!(
                operation_unproven.body_safety_demands[0].verdict,
                safety::BodySafety::Unproven(_)
            ),
            "an unsampleable operation domain must not become a false body refutation"
        );

        let (mixed, _) = check(
            "mixed where (Function) => Top\n\
             mixed = (candidate) => {\n\
              missing\n\
              => candidate + 1\n\
             }\n",
        );
        assert!(
            matches!(
                mixed.body_safety_demands[0].verdict,
                safety::BodySafety::Refuted(_)
            ),
            "a separate definite trap must dominate an unrelated Unproven operation"
        );
    }

    /// A `where` naming nothing, and one whose arity disagrees with the function, are
    /// authoring errors — they must not pass silently just because there is no body to check.
    #[test]
    fn a_where_that_cannot_be_acted_on_rejects_rather_than_passing_silently() {
        let (v, _) = check("ghost where (Number) => Number\nf = (n) => n\n");
        assert!(
            !v.accepted(),
            "a `where` naming no binding rejects: {:?}",
            v.findings
        );

        // Detectable only in this direction — see `spread_input`: a *declared* tuple on a
        // one-parameter function is legal (that parameter may be a tuple), so the mismatch
        // that can be caught is a declaration too narrow for the parameter list.
        let (v, _) = check("f where (Number) => Number\nf = (a, b) => a + b\n");
        assert!(!v.accepted(), "an arity mismatch rejects: {:?}", v.findings);
    }

    /// Named contracts are ordinary bindings of contract expressions (C§12.2), so a `where`
    /// may name one — and the declared domain is then the *named* contract, not `Number`.
    #[test]
    fn a_where_may_declare_a_named_contract() {
        let (v, _) =
            check("Percent = Range(0, 100)\nf where (Percent) => Number\nf = (p) => p + 1\n");
        assert!(
            v.accepted(),
            "a named contract resolves as the declared domain: {:?}",
            v.findings
        );
    }

    /// A-VER's union-at-boundary pair. Direct access is unsafe because `Failure` does not
    /// guarantee `body`; after an exhaustive contract-pattern match, the `Response` arm has the
    /// narrowed receiver and both arms produce String. The return demand must consume that
    /// same arm-local analysis rather than re-summarizing an erased whole body.
    #[test]
    fn a_union_receiver_rejects_until_an_exhaustive_match_narrows_it() {
        const CONTRACTS: &str = "Response = {body: String}\n\
            Result = Union(Response, Failure)\n";

        let (direct, _) = check(&format!(
            "{CONTRACTS}get where (Result) => String\n\
             get = (data) => data.body\n"
        ));
        assert!(
            !direct.accepted(),
            "the Failure alternative makes direct `.body` unsafe"
        );
        assert!(
            direct
                .findings
                .iter()
                .any(|finding| finding.class == TrapClass::AbsentField),
            "the rejection must retain the field-access demand: {direct:?}"
        );

        let (narrowed, _) = check(&format!(
            "{CONTRACTS}get where (Result) => String\n\
             get = (data) => data :: {{\n\
              Response => data.body\n\
              Failure => \"failed\"\n\
             }}\n"
        ));
        assert!(
            narrowed.accepted(),
            "the exhaustive match discharges `.body` in the Response arm: {narrowed:#?}"
        );
        assert!(matches!(
            narrowed.return_demands[0].verdict,
            ClaimVerdict::Proven
        ));
    }

    /// [author, 2026-08-03] Resolution is subcontract-aware from the start — like
    /// `instanceof` on semantics, without the chain walk: a demanded fact is answered
    /// by any proven fact whose domain **contains** the asked one, in the same
    /// resolution step. No fail-then-retry, no re-analysis. Two parameters here, so no
    /// orbit derivation applies — coverage is the only route.
    #[test]
    fn a_declared_fact_answers_concrete_calls_by_coverage() {
        let (covered, _) = check(
            "f where (Number, Number) => Number\n\
             f = (a, b) => 2 * a + b <= 0 ? 0 : f(a - 1, b + 1)\n\
             x = f(5, 0)\n",
        );
        assert!(
            covered.accepted(),
            "(5, 0) is inside the proven (Number, Number) fact: {:#?}",
            covered.findings
        );

        // A `where` is a fact, not a statement — declaring it after the call serves
        // the call identically.
        let (declared_last, _) = check(
            "f = (a, b) => 2 * a + b <= 0 ? 0 : f(a - 1, b + 1)\n\
             x = f(5, 0)\n\
             f where (Number, Number) => Number\n",
        );
        assert!(
            declared_last.accepted(),
            "declaration order is immaterial to fact resolution: {:#?}",
            declared_last.findings
        );

        // Outside the declared domain coverage does not apply, and the honest
        // judgment remains.
        let (outside, _) = check(
            "f where (Number, Number) => Number\n\
             f = (a, b) => 2 * a + b <= 0 ? 0 : f(a - 1, b + 1)\n\
             y = f(\"x\", 0)\n",
        );
        assert!(
            !outside.accepted(),
            "a String argument is not covered by the Number fact: {:#?}",
            outside.findings
        );
    }

    /// The **group orbit**: a bare mutual pair needs no contracts either. Every
    /// cross-call drifts by a constant negative step on the shared parameter, every
    /// recursive member stops on a descending half-line, so the group's visited
    /// values from a bounded start live in one derived envelope — the joint
    /// induction proves both facts over it, and the shared-measure certificate
    /// already grounds termination.
    #[test]
    fn a_bare_mutual_pair_closes_through_the_group_orbit() {
        let (mutual, _) = check(
            "isEven = (n) => n <= 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n <= 0 ? false : isEven(n - 1)\n\
             x = isEven(4)\n",
        );
        assert!(
            mutual.accepted(),
            "the group orbit closes the bare pair: {:#?}",
            mutual.findings
        );
    }

    /// GR-24's WorldDecided classifier, v1 (the D-α/D-β rulings): effect-world
    /// recursion whose every cycle observes the world afresh, with a completing arm
    /// for the observation to select, is the **world's** decision — not a
    /// termination bug — and compiles. The stale-carried and decorative
    /// counter-specimens stay rejected.
    #[test]
    fn a_world_driven_polling_loop_is_world_decided() {
        // Specimen 14's polling idiom: fresh observation, completing arm.
        let (poll, _) = check(
            "@effect poll = () => {\n\
              readFile(\"q\") :: {\n\
               Failure => poll()\n\
               data => data\n\
              }\n\
             }\n\
             poll()\n",
        );
        assert!(
            poll.accepted(),
            "the world decides this loop: {:#?}",
            poll.findings
        );

        // Specimen 13: a carried parameter is stale — no cycle sees the world.
        let (stale, _) = check(
            "@effect loop = (msg) => {\n\
              msg == \"quit\" ? 0 : loop(msg)\n\
             }\n\
             loop(\"go\")\n",
        );
        assert!(
            !stale.accepted(),
            "stale-carried is not world-decided: {:#?}",
            stale.findings
        );

        // Specimen 16: every arm recurses — no completing transition to seed.
        let (decorative, _) = check(
            "@effect flip = () => {\n\
              readFile(\"b\") :: {\n\
               Failure => flip()\n\
               _ => flip()\n\
              }\n\
             }\n\
             flip()\n",
        );
        assert!(
            !decorative.accepted(),
            "the decorative branch seeds nothing: {:#?}",
            decorative.findings
        );
    }

    /// A half-line guard's remainder tightens like a point guard's: `n ∈ Nat` minus
    /// `n <= 0` is `n ≥ 1`, so `n − 1` lands back inside the declared domain. This was
    /// F0's recorded "non-singleton exclusion dropped" gap, and it blocked every
    /// `<=`-guarded recursion — including all mutual pairs, whose bases idiomatically
    /// read `n <= 0`.
    #[test]
    fn a_half_line_guard_remainder_tightens() {
        let (le, _) = check(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\n\
             f where (Nat) => Number\n\
             f = (n) => n <= 0 ? 0 : f(n - 1)\n",
        );
        assert!(
            le.accepted(),
            "the `<=` remainder lands the step back inside the domain: {:#?}",
            le.findings
        );

        let (mutual, _) = check(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\n\
             isEven where (Nat) => Boolean\n\
             isOdd where (Nat) => Boolean\n\
             isEven = (n) => n <= 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n <= 0 ? false : isEven(n - 1)\n\
             x = isEven(4)\n",
        );
        assert!(
            mutual.accepted(),
            "the declared mutual pair closes jointly and covers the call: {:#?}",
            mutual.findings
        );
    }

    /// GR-18's grid: a constant step of −2 lands exactly when the start sits on the
    /// base's lattice — `6 → 4 → 2 → 0` lands and accepts; `5 → 3 → 1 → −1 …` misses
    /// forever and keeps its refutation; a declared broad domain grounds through the
    /// same divisibility question.
    #[test]
    fn a_non_unit_step_lands_on_its_grid() {
        let (aligned, _) = check("f = (n) => n == 0 ? 0 : f(n - 2)\nx = f(6)\n");
        assert!(
            aligned.accepted(),
            "6 is on the base's step-2 lattice: {:#?}",
            aligned.findings
        );

        let (misaligned, _) = check("f = (n) => n == 0 ? 0 : f(n - 2)\nx = f(5)\n");
        assert!(
            !misaligned.accepted(),
            "5 misses the base forever and must stay rejected: {:#?}",
            misaligned.findings
        );

        let (declared, _) = check(
            "Ev = Intersection(GreaterEq(0), Mod(2, 0))\n\
             f where (Ev) => Number\n\
             f = (n) => n == 0 ? 0 : f(n - 2)\n",
        );
        assert!(
            declared.accepted(),
            "the declared lattice grounds through the same grid: {:#?}",
            declared.findings
        );
    }

    /// [author, 2026-08-03] **The drift is what closes** — a concrete call to a
    /// terminating recursion needs no contracts. At the shape-repeat stop the checker
    /// reads the drift (5 → 4 = −1), the certificate derives the orbit envelope
    /// (`Range(0,5) ∧ Mod(1,0)`), and the fact is proven by ordinary induction over
    /// that envelope; the same drift logic proves termination at the seat.
    #[test]
    fn a_concrete_call_to_a_terminating_recursion_needs_no_contracts() {
        let (bare, _) =
            check("countDown = (n) => n == 0 ? 0 : countDown(n - 1)\nx = countDown(5)\n");
        assert!(
            bare.accepted(),
            "inference alone carries the call: {:#?}",
            bare.findings
        );

        // The declared form accepts identically.
        let (declared, _) = check(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\n\
             countDown where (Nat) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n\
             x = countDown(5)\n",
        );
        assert!(
            declared.accepted(),
            "the declared form accepts too: {:#?}",
            declared.findings
        );

        // The ascending twin still rejects: drift +1 from 5 never lands on 0.
        let (ascending, _) = check("up = (n) => n == 0 ? 0 : up(n + 1)\nx = up(5)\n");
        assert!(
            !ascending.accepted(),
            "drift away from the finish is still an error: {:#?}",
            ascending.findings
        );
    }

    /// Principle 9 stamped [user, 2026-08-03]: the gray tier is gone. Recursion the
    /// compiler cannot prove terminates is a compile **error** at every seat — never a
    /// warning, never silent — joining every other unproven obligation.
    #[test]
    fn a_recursion_not_proven_to_terminate_is_an_error() {
        // `loop(1)` never finishes. Before the stamp this compiled silently.
        let (diverging, _) = check("loop = (n) => loop(n)\nx = loop(1)\n");
        assert!(
            !diverging.accepted(),
            "a diverging call is an error now: {:#?}",
            diverging.findings
        );

        // A statement seat softens nothing: discarding the result is still divergence.
        let (statement, _) = check("loop = (n) => loop(n)\nloop(1)\n");
        assert!(
            !statement.accepted(),
            "a diverging statement is an error too: {:#?}",
            statement.findings
        );

        // Control: recursion the compiler proves terminating still accepts —
        // `countDown` descends by 1 and lands on 0 over the naturals.
        let (grounded, _) = check(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\n\
             countDown where (Nat) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n",
        );
        assert!(
            grounded.accepted(),
            "proven-terminating recursion accepts: {:#?}",
            grounded.findings
        );
    }

    /// A-VER's Failure-overlap wrapper demand (B6 [1.0.2]): where a declared fallible
    /// boundary's success alternative is not proven disjoint from `Failure`, a success
    /// value could inhabit the failure rail and its discharge match would swallow it —
    /// so the explicit success wrapper is demanded at the boundary that forms the union.
    #[test]
    fn a_fallible_boundary_demands_failure_disjoint_successes() {
        // `Data` is open (`HasField`): a record carrying `value` *and* `path`/`reason`
        // inhabits both rails, so the boundary must reject until successes are wrapped.
        let (overlapping, _) = check(
            "Data = HasField(\"value\")\n\
             parse where (Record) => Union(Data, Failure)\n\
             parse = (raw) => raw :: {\n\
              Data => raw\n\
              _ => {path: \"adapter\", reason: \"malformed\"}\n\
             }\n",
        );
        assert!(
            !overlapping.accepted(),
            "an open success shape is not proven disjoint from Failure: {:#?}",
            overlapping.findings
        );

        // The demanded fix: an exact success wrapper without `path`/`reason` is proven
        // disjoint from Failure, and the same adapter body then passes the boundary.
        let (wrapped, _) = check(
            "Ok = {value: Record}\n\
             parse where (Record) => Union(Ok, Failure)\n\
             parse = (raw) => raw :: {\n\
              Ok => raw\n\
              _ => {path: \"adapter\", reason: \"malformed\"}\n\
             }\n",
        );
        assert!(
            wrapped.accepted(),
            "the wrapped boundary is proven disjoint and accepts: {:#?}",
            wrapped.findings
        );
    }

    /// A fact depends on every named contract its function body reads. Reusing one pure
    /// memo table is sound only when that dependency is part of the semantic key: changing
    /// `N` changes which arm is reachable even though the canonical function body, value
    /// captures, call input, and claim are otherwise identical.
    #[test]
    fn fact_memo_records_named_contract_dependencies() {
        const SAFE: &str = "N = String\n\
            f where (Number) => Number\n\
            f = (x) => x :: {\n\
             N => 1 + \"s\"\n\
             _ => 1\n\
            }\n";
        const UNSAFE: &str = "N = Number\n\
            f where (Number) => Number\n\
            f = (x) => x :: {\n\
             N => 1 + \"s\"\n\
             _ => 1\n\
            }\n";

        super::super::factcache::clear();
        let mut interner = Interner::new();
        let safe = crate::oracle::harness::check_source_in(SAFE, &mut interner)
            .expect("safe variant parses and checks");
        assert!(
            safe.accepted(),
            "String does not select the trapping arm: {safe:?}"
        );
        let unsafe_variant = crate::oracle::harness::check_source_in(UNSAFE, &mut interner)
            .expect("unsafe variant parses and checks");
        assert!(
            !unsafe_variant.accepted(),
            "Number selects the trapping arm; a fact for N=String must not be reused: \
             {unsafe_variant:?}"
        );

        // The reverse order catches the symmetric stale-refutation failure mode too.
        super::super::factcache::clear();
        let mut interner = Interner::new();
        let unsafe_variant = crate::oracle::harness::check_source_in(UNSAFE, &mut interner)
            .expect("unsafe variant parses and checks");
        assert!(
            !unsafe_variant.accepted(),
            "the unsafe variant rejects from a cold memo"
        );
        let safe = crate::oracle::harness::check_source_in(SAFE, &mut interner)
            .expect("safe variant parses and checks");
        assert!(
            safe.accepted(),
            "a refutation for N=Number must not be reused when N=String: {safe:?}"
        );
        super::super::factcache::clear();
    }

    /// The declared **return** contract is now checked (demand core, C§13.1). This test
    /// previously asserted the opposite — that the contract was recorded but unverified —
    /// and it is the flip that slice was written to produce.
    #[test]
    fn a_declared_return_contract_that_the_body_does_not_meet_rejects() {
        let (v, _) = check("f where (Number) => String\nf = (n) => n + 1\n");
        assert!(
            !v.accepted(),
            "`f` returns a Number where String is declared: {:?}",
            v.findings
        );
        assert!(
            v.findings
                .iter()
                .any(|f| f.message.contains("refuted by represented arguments")),
            "a concrete counterexample must remain Refuted at the program boundary: {v:?}"
        );
        assert_eq!(v.return_demands.len(), 1);
        match &v.return_demands[0].verdict {
            ClaimVerdict::Refuted(witness) => {
                assert_eq!(witness.arguments.len(), 1);
                assert!(!Contract::Kind(crate::contract::Kind::String).contains(&witness.produced));
            }
            other => panic!("the typed program record lost its refutation: {other:?}"),
        }
    }

    /// A failed abstract proof with no represented counterexample remains Unproven; the
    /// rejection policy is the same, but the semantic evidence is deliberately distinct.
    #[test]
    fn an_unproven_declared_return_is_not_reported_as_refuted() {
        let (v, _) = check(
            "factorial where (Number) => Greater(0)\n\
             factorial = (n) => n == 0 ? 1 : n * factorial(n - 1)\n",
        );
        assert!(!v.accepted(), "an unproven declaration remains rejecting");
        assert!(matches!(
            v.return_demands[0].verdict,
            ClaimVerdict::Unproven
        ));
        assert!(
            v.findings
                .iter()
                .any(|f| f.message.contains("cannot be proven of its body")),
            "Unproven keeps the non-witness diagnostic: {v:?}"
        );
        assert!(
            v.findings
                .iter()
                .all(|f| !f.message.contains("refuted by represented arguments")),
            "Unproven must not claim a represented counterexample: {v:?}"
        );
    }

    /// And the complement: a return contract the body does meet is proven and recorded.
    #[test]
    fn a_declared_return_contract_the_body_meets_is_proven() {
        let (v, _) = check("f where (Number) => Number\nf = (n) => n + 1\n");
        assert!(v.accepted(), "{:?}", v.findings);
        assert_eq!(
            v.return_demands.len(),
            1,
            "the discharge is recorded: {v:?}"
        );
        assert!(matches!(v.return_demands[0].verdict, ClaimVerdict::Proven));
    }

    /// AP-29 at the source boundary: both accesses project one immutable correlated
    /// choice. The represented calls are `(numFn, 5)` and `(strFn, "hello")`; the
    /// analyzer must not synthesize `(numFn, "hello")` while rebuilding the joint
    /// application operand.
    #[test]
    fn correlated_choice_accesses_reach_the_joint_application_driver() {
        let (v, _) = check(
            "numFn = (n) => n + 1\n\
             strFn = (s) => `${s}`\n\
             apply where (Boolean) => Top\n\
             apply = (cond) => {\n\
              choice = cond ? [numFn, 5] : [strFn, \"hello\"]\n\
              => choice[0](choice[1])\n\
             }\n",
        );
        assert!(
            v.accepted(),
            "the two represented alternatives are safe; false cross-pairs are not executions: \
             {:#?}",
            v.findings
        );
    }

    /// Analysis checks a binding's executable RHS without running it. This used to pass
    /// because the program entry only originated `where` demands.
    #[test]
    fn an_unsafe_binding_rhs_is_checked_without_being_evaluated() {
        let (v, mut interner) = check("boom = 1 + \"x\"\n");
        assert!(
            !v.accepted(),
            "the binding operation-safety demand must reject: {:?}",
            v.findings
        );
        assert!(
            v.findings
                .iter()
                .any(|f| f.class == TrapClass::OperationSafety)
        );
        let operation = v.executable_demands[0]
            .safety_demands
            .iter()
            .find_map(|demand| match demand {
                SafetyDemand::Operation(operation) => Some(operation),
                SafetyDemand::Body(_) => None,
            })
            .expect("the executable record retains the primitive operation judgment");
        assert_eq!(operation.operation, crate::ast::PrimOp::Add);
        match &operation.verdict {
            OpSafety::Refuted(witness) => {
                assert_eq!(
                    witness,
                    &vec![interner.integer(1), interner.string("x")],
                    "the typed refutation owns the exact operand witness"
                );
            }
            other => panic!("the operation refutation was collapsed to {other:?}"),
        }
    }

    /// Operation safety fires on arrival even when the result is discarded (C§7).
    #[test]
    fn an_unsafe_executable_statement_is_checked() {
        let (v, _) = check("(1 / 0) + 5\n");
        assert!(
            !v.accepted(),
            "the statement must discharge its own operation demand: {:?}",
            v.findings
        );
        assert!(
            v.findings
                .iter()
                .any(|f| f.class == TrapClass::UndischargedIndeterminate)
        );
    }

    /// A statement seat discards completion, while a binding RHS is an expecting seat.
    /// The same partial expression is therefore legal in the first and rejecting in the
    /// second; this is the program-level E10 distinction, not a special-case warning.
    #[test]
    fn executable_seats_preserve_statement_vs_expecting_completion() {
        let (statement, _) = check("1 :: { 2 => 3 }\n");
        assert!(
            statement.accepted(),
            "fall-through is legal when the result is discarded: {:?}",
            statement.findings
        );

        let (binding, _) = check("x = 1 :: { 2 => 3 }\n");
        assert!(
            !binding.accepted(),
            "a binding demands a produced value: {:?}",
            binding.findings
        );
        assert!(
            binding
                .findings
                .iter()
                .any(|f| f.class == TrapClass::ExpectingSeat)
        );
    }

    /// A selected arm returns its result's whole outcome. The Match itself does not
    /// demand that result: only the Match's consumer does. This is the recursive form
    /// of the same E10 seat distinction exercised above.
    #[test]
    fn selected_arm_completion_is_demanded_only_by_the_match_consumer() {
        let source = "partial = (n) => n :: { 0 => 1 }\n\
                      1 :: { 1 => partial(1) }\n";
        let (statement, mut interner) = check(source);
        assert!(
            statement.accepted(),
            "the selected arm's completion is legal when the enclosing Match is a statement: {:?}",
            statement.findings
        );
        match &statement
            .executable_demands
            .last()
            .expect("the statement demand is retained")
            .completion
        {
            Completion::FallsThrough(CompletionWitness::Application(witness)) => {
                assert_eq!(witness.arguments, vec![interner.integer(1)]);
            }
            other => panic!("the Match must retain the arm's application witness, got {other:?}"),
        }

        let source = "partial = (n) => n :: { 0 => 1 }\n\
                      result = 1 :: { 1 => partial(1) }\n";
        let (binding, _) = check(source);
        assert!(
            !binding.accepted(),
            "the same selected-arm completion must reject when the enclosing Match is expected: {:?}",
            binding.findings
        );
        assert!(
            binding
                .findings
                .iter()
                .any(|f| f.class == TrapClass::ExpectingSeat)
        );
    }

    /// Static binding still applies at the entry: earlier values feed later statements,
    /// while an eager reference cannot see a later declaration.
    #[test]
    fn executable_demands_follow_item_order() {
        let (ordered, _) = check("x = 1\nx + 2\n");
        assert!(
            ordered.accepted(),
            "the earlier binding is available: {:?}",
            ordered.findings
        );
        assert_eq!(ordered.executable_demands.len(), 2);
        assert!(matches!(
            ordered.executable_demands[0],
            ExecutableDemand {
                origin: ExecutableOrigin::Binding { item: 0, .. },
                seat: ExecutableSeat::Expecting,
                world: World::Effect,
                ..
            }
        ));
        assert!(matches!(
            ordered.executable_demands[1],
            ExecutableDemand {
                origin: ExecutableOrigin::Statement { item: 1 },
                seat: ExecutableSeat::Statement,
                world: World::Effect,
                ..
            }
        ));

        let (forward, _) = check("x + 2\nx = 1\n");
        assert!(
            !forward.accepted(),
            "an eager forward reference must reject: {:?}",
            forward.findings
        );
        assert!(
            forward
                .findings
                .iter()
                .any(|f| f.class == TrapClass::UnboundEvaluation)
        );
    }

    /// Constructing a lambda does not inspect or run its body; applying it creates the
    /// body-safety demand that exposes the trap.
    #[test]
    fn a_function_body_is_checked_when_the_executable_program_calls_it() {
        let (constructed, _) = check("f = () => 1 + \"x\"\n");
        assert!(
            constructed.accepted(),
            "construction alone is inert: {:?}",
            constructed.findings
        );

        let (called, _) = check("f = () => 1 + \"x\"\nf()\n");
        assert!(
            !called.accepted(),
            "the call must check its body: {:?}",
            called.findings
        );
        assert!(
            called
                .findings
                .iter()
                .any(|f| f.class == TrapClass::OperationSafety)
        );
    }

    /// The program path must consume the global fact graph. The helper edge changes
    /// the domain before returning to `f`; §4a cuts off that repeated shape, leaving
    /// safety unproven, and late-resolution §5 therefore blocks the executable seat.
    #[test]
    fn an_executable_mutual_domain_change_is_not_silently_accepted() {
        let (v, _) = check(
            "f = (x) => x == 0 ? g(\"x\") : x + 1\n\
             g = (y) => f(y)\n\
             f(0)\n",
        );
        assert!(
            !v.accepted(),
            "f(0) -> g(\"x\") -> f(\"x\") must not pass an unsettled fact graph: {:?}",
            v.findings
        );
        assert!(
            v.findings
                .iter()
                .any(|f| f.class == TrapClass::OperationSafety)
        );
        assert!(
            v.executable_demands
                .last()
                .expect("the call statement is recorded")
                .safety_demands
                .iter()
                .any(|demand| matches!(
                    demand,
                    SafetyDemand::Body(body)
                        if matches!(body.verdict, safety::BodySafety::Unproven(_))
                )),
            "the blocking policy must not relabel an unsettled BodySafe fact as Refuted"
        );
    }

    /// Multi-parameter row projection remains a precision gap, but it cannot remain a
    /// soundness hole: the changed-domain re-entry is a repeated-shape fact with no
    /// admitted proof, so safety-unproven rejects until §5 tuple projection can prove or
    /// refute it more precisely.
    #[test]
    fn an_executable_multiparameter_domain_change_is_not_silently_accepted() {
        let (v, _) = check(
            "f = (a, b) => a == 0 ? f(\"x\", b) : a + b\n\
             f(0, 1)\n",
        );
        assert!(
            !v.accepted(),
            "f(0, 1) -> f(\"x\", 1) must not pass an unsettled fact graph: {:?}",
            v.findings
        );
        assert!(
            v.findings
                .iter()
                .any(|f| f.class == TrapClass::OperationSafety)
        );
    }

    /// Entry statements run in effect world, but a named module's executable bindings
    /// remain pure. World is part of the demand key; it cannot be guessed from the callee.
    #[test]
    fn executable_demands_carry_their_top_level_world() {
        let (entry, _) = check("@effect ping = () => { }\nping()\n");
        assert!(
            entry.accepted(),
            "entry top level admits Effects: {:?}",
            entry.findings
        );

        let (nested_effect, _) = check(
            "@effect inner = () => { }\n\
             @effect outer = () => { inner() }\n\
             outer()\n",
        );
        assert!(
            nested_effect.accepted(),
            "an Effect body owns effect world independently of its caller: {:?}",
            nested_effect.findings
        );

        let (mutator, _) = check(
            "@state x = 0\n\
             @mutate setX = () => { x := 1 }\n\
             setX()\n",
        );
        assert!(
            mutator.accepted(),
            "a Mutator body owns mutation world and may write: {:?}",
            mutator.findings
        );

        let (module, _) = check(
            "module M\n\
             @effect ping = () => { }\n\
             export result = ping()\n",
        );
        assert!(
            !module.accepted(),
            "module top level is pure: {:?}",
            module.findings
        );
        assert!(
            module
                .findings
                .iter()
                .any(|f| f.class == TrapClass::WorldAdmission)
        );
    }

    /// Slot allocation is declarative, but its initializer is still a pure expecting seat.
    #[test]
    fn a_slot_initializer_originates_an_executable_demand() {
        let (v, _) = check("@state x = 1 + \"x\"\n");
        assert!(
            !v.accepted(),
            "the initializer must be checked: {:?}",
            v.findings
        );
    }

    /// A write is legal only in mutator world. Entry top level is effect world, which does
    /// not grant direct write permission.
    #[test]
    fn a_top_level_write_is_rejected() {
        let (v, _) = check("@state x = 0\nx := 1\n");
        assert!(!v.accepted(), "only a Mutator may write: {:?}", v.findings);
        assert!(
            v.findings
                .iter()
                .any(|f| f.class == TrapClass::WorldAdmission)
        );
    }

    /// Check mode starts from the same harness values as run mode. Installing a
    /// native value is inert; only a legal Effect-world call creates a demand.
    #[test]
    fn executable_demands_can_resolve_the_host_prelude() {
        let (v, _) = check("println(\"hello\")\n");
        assert!(
            v.accepted(),
            "the entry harness provides println to the checker: {:?}",
            v.findings
        );
        assert_eq!(v.executable_demands.len(), 1);
        assert_eq!(v.executable_demands[0].world, World::Effect);
    }
}
