//! The analyzer — contract inference over the kernel AST, and the compile-time
//! face of the oracle's traps (§6 trap↔compile-error concordance).
//!
//! Per Part I this layer is legitimate only now that the oracle, the
//! normalization harness, and the contract algebra (C.1–C.3, C§9) are green. The
//! analyzer walks an [`Expr`], infers a [`Contract`] over-approximating the value
//! it produces, and at each operation site discharges the operation's safety
//! demand ([`analyze_operation`]) — emitting a [`Finding`] for anything that
//! **will** trap or that it **cannot prove** safe. Both reject after typed safety
//! verdicts reach their consuming seat: safety-Unproven carries an advisory diagnostic
//! during fact calculation, then gains its Error at policy. Non-safety third voices such
//! as completion that may fall through remain warning-only.
//! The soundness contract (§6): an expression the analyzer accepts with no error
//! never traps in the oracle.
//!
//! **Scope so far:** `Const`, `Ref`, `PrimOp`, `TupleCons`, `RecordCons`,
//! `Template` (E11), `Access` (E6), `Match` (E9/E10), and `Apply` (C§7/B5/E10).
//! Closed **primitive** operations and **accesses** fold through the finite oracle
//! kernel (`eval_prim` / `eval_expr` on a `Const` target) for an exact verdict; a
//! **closed function calls are not executed as the transfer rule** — a callee's traps
//! come from the domain-indexed candidate graph (`safety` + `induction`), completion
//! from its settled completion fact plus AP-30's bounded pure-call witness refutation,
//! and return from the coarse shape-bounded outcome projection sharpened by return
//! facts. The source seat supplies its actual world; a function body instead owns the
//! world declared by its `ActKind` (B5/E14). Index/slice bounds await C§17 (see
//! `OwedItems.md`). `Write` checks
//! world admission and its right-hand expression; resolving and validating the target
//! slot remains owed.
//!
//! Analysis carries a **named-contract environment** ([`ContractEnv`]) alongside the
//! value-contract [`TypeEnv`]: user contracts (`Percent = Range(0, 100)`, C§12.2)
//! resolve in contract-as-pattern position (E9), so they narrow arms and police
//! destructuring irrefutability exactly as the prelude Kind names do.

use std::collections::HashMap;

use num_traits::ToPrimitive;

use crate::ast::{
    AccessForm, ActKind, Arg, BindingRef, Element, Expr, Field, PrimOp, Ref, SlotRef, TemplatePart,
};
use crate::contract::{
    Contract, ContractEnv, Kind, OpSafety, Verdict, analyze_operation, disjoint, eval_contract,
    subcontract,
};
use crate::interner::Interner;
use crate::oracle::{Outcome, TrapClass, World, eval_expr, eval_prim};
use crate::value::ValueRef;

use self::application::{
    AlternativeContribution, ApplicationOutcome, ApplicationWitness, CalleeAlternative,
    CompletionWithoutValue, SeatVerdict,
};
use self::domain::AnalysisContract;

pub mod application;
pub mod bodywalk;
pub mod demand;
pub mod domain;
pub(crate) mod factcache;
pub mod grounding;
pub mod induction;
pub mod inventory;
pub mod obligation;
pub mod outcome;
pub mod program;
pub mod refute;
pub mod region;
pub mod safety;

#[cfg(test)]
mod tests;

/// How serious a finding is for acceptance.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    /// The operation is proven to trap on some reachable input — a rejection.
    Error,
    /// Advisory evidence. It does not reject by itself; a typed safety-unproven verdict
    /// gains an Error when policy is applied at its consuming seat.
    Warning,
}

/// A compile-time diagnostic, tagged with the oracle trap class it mirrors (§6).
#[derive(Clone, Debug)]
pub struct Finding {
    pub class: TrapClass,
    pub severity: Severity,
    pub message: String,
}

/// Whether an expression completes **without** producing a value (E10 — a `Match`
/// that may fall through), three-voiced (the application spec's `CompletionWithoutValue`
/// at the expression layer): the seat demand's compile-time face. The application
/// layer's [`crate::analyzer::application::CompletionWithoutValue`] is its deliberate
/// counterpart across the AP-29 witness boundary — convert with
/// `CompletionWithoutValue::of` (narrowing) / `completion_from_application` (faithful).
#[derive(Clone, Debug)]
pub enum Completion {
    /// Every path produces a value (`ProvenAbsent`) — an expecting seat is satisfied.
    Produces,
    /// A fall-through is possible but **not proven reachable** (`UnprovenPossible`) —
    /// an expecting seat is the third voice: a *warning*, never a rejection.
    MayFallThrough,
    /// A fall-through is **proven reachable** (`ProvenPresent`) — a represented input
    /// completes without a value, so an expecting seat is *refuted* (an error).
    FallsThrough(CompletionWitness),
}

/// Evidence retained by a proven completed-without-value outcome. Applications carry
/// the normative joint `(callee, arguments)` witness (AP-30); other kernel operations
/// retain the structural reason their own execution completes without a value.
#[derive(Clone, Debug)]
pub enum CompletionWitness {
    Application(ApplicationWitness),
    MatchRemainder { scrutinee: Option<ValueRef> },
    Write { slot: SlotRef },
}

/// One primitive-operation safety judgment, retained independently of the diagnostic
/// policy applied at the operation's consuming seat. A refutation owns the exact
/// operand witness supplied by the operation rulebook.
#[derive(Clone, Debug)]
pub struct OperationSafetyDemand {
    pub operation: PrimOp,
    pub inputs: Vec<Contract>,
    pub verdict: OpSafety,
}

/// One domain-indexed body-safety judgment made while analyzing an application.
/// Program policy blocks both failed voices, but this record keeps `Refuted` and
/// `Unproven` semantically distinct after that policy is applied.
#[derive(Clone, Debug)]
pub struct BodySafetyDemand {
    pub callee: ValueRef,
    pub arguments: Vec<Contract>,
    pub verdict: safety::BodySafety,
}

/// Typed safety evidence raised by an expression and all of its reachable children.
#[derive(Clone, Debug)]
pub enum SafetyDemand {
    Operation(OperationSafetyDemand),
    Body(BodySafetyDemand),
}

/// The result of analyzing an expression: the inferred contract, any findings
/// gathered from it and its subexpressions, and its completion (E10).
#[derive(Clone, Debug)]
pub struct Analysis {
    pub contract: Contract,
    /// The same produced values in the structural annotated domain. `contract` is
    /// `erase(annotated)` and remains the ordinary language-facing denotation.
    pub annotated: AnalysisContract,
    /// Local analyzer-only branch provenance. It never crosses a call, return,
    /// structure, or fact boundary; operations carry it lazily and routing forces it.
    pub(crate) image: Option<domain::ImageOperand>,
    pub findings: Vec<Finding>,
    /// Semantic safety judgments before their accepting/rejecting diagnostics are
    /// interpreted. Findings are the policy surface; they are not the evidence store.
    pub safety_demands: Vec<SafetyDemand>,
    pub completion: Completion,
}

impl Analysis {
    /// An expression that always produces a value.
    fn produced(contract: Contract, findings: Vec<Finding>) -> Analysis {
        Analysis {
            annotated: AnalysisContract::of_contract(contract.clone()),
            contract,
            image: None,
            findings,
            safety_demands: Vec::new(),
            completion: Completion::Produces,
        }
    }

    fn produced_annotated(
        annotated: AnalysisContract,
        findings: Vec<Finding>,
        interner: &mut Interner,
    ) -> Analysis {
        Analysis {
            contract: annotated.erase(interner),
            annotated,
            image: None,
            findings,
            safety_demands: Vec::new(),
            completion: Completion::Produces,
        }
    }

    fn produced_with_safety(
        contract: Contract,
        findings: Vec<Finding>,
        safety_demands: Vec<SafetyDemand>,
    ) -> Analysis {
        Analysis {
            annotated: AnalysisContract::of_contract(contract.clone()),
            contract,
            image: None,
            findings,
            safety_demands,
            completion: Completion::Produces,
        }
    }

    fn produced_annotated_with_safety(
        annotated: AnalysisContract,
        findings: Vec<Finding>,
        safety_demands: Vec<SafetyDemand>,
        interner: &mut Interner,
    ) -> Analysis {
        Analysis {
            contract: annotated.erase(interner),
            annotated,
            image: None,
            findings,
            safety_demands,
            completion: Completion::Produces,
        }
    }

    /// Whether the expression is accepted. Typed safety-unproven blocks even while its
    /// diagnostic remains advisory inside analysis; the consuming program seat later
    /// materializes the unsuppressible Error without erasing the verdict.
    pub fn accepted(&self) -> bool {
        self.findings.iter().all(|f| f.severity != Severity::Error)
            && self.safety_demands.iter().all(|demand| match demand {
                SafetyDemand::Operation(operation) => {
                    matches!(operation.verdict, OpSafety::Proven)
                }
                SafetyDemand::Body(body) => matches!(body.verdict, safety::BodySafety::Proven),
            })
    }

    /// Whether evaluation may complete without a value (either voice of fall-through).
    pub fn may_complete(&self) -> bool {
        !matches!(&self.completion, Completion::Produces)
    }
}

/// An expecting seat (E10) demands `Produced`. The compile-time mirror of the
/// expecting-seat trap is **three-voiced** (E10 / application §1.6): a **proven**
/// fall-through refutes (error); a merely **possible** one is unproven (warning); a
/// guaranteed producer is fine.
fn demand(a: &Analysis, findings: &mut Vec<Finding>) {
    let (severity, message) = match &a.completion {
        Completion::Produces => return,
        Completion::FallsThrough(_) => (
            Severity::Error,
            "a value is demanded here, but this expression completes without one on some input",
        ),
        Completion::MayFallThrough => (
            Severity::Warning,
            "a value is demanded here, but this expression cannot be proven to produce one",
        ),
    };
    findings.push(Finding {
        class: TrapClass::ExpectingSeat,
        severity,
        message: message.into(),
    });
}

/// The annotated expression environment. Ordinary contracts inserted by older
/// operation/fact code are lifted with `Unknown` metadata; source expressions insert
/// their complete [`AnalysisContract`] so structure and correlation survive references.
#[derive(Clone, Debug)]
struct TypeBinding {
    annotated: AnalysisContract,
    image: Option<domain::ImageOperand>,
    /// A local pure function whose runtime closure is deliberately not formed by
    /// analysis. The closed callee is an analyzer-only lambda-lifted identity; the
    /// prefix is the arrived outer environment, represented as ordinary arguments.
    deferred_call: Option<DeferredCall>,
}

#[derive(Clone, Debug)]
struct DeferredCall {
    callee: ValueRef,
    prefix: Vec<AnalysisContract>,
}

#[derive(Clone, Debug, Default)]
pub struct TypeEnv(HashMap<String, TypeBinding>);

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv(HashMap::new())
    }

    pub fn insert(
        &mut self,
        name: String,
        value: impl Into<AnalysisContract>,
    ) -> Option<AnalysisContract> {
        let annotated = value.into();
        let image = domain::ImageOperand::source_annotated(&annotated);
        self.insert_with_image(name, annotated, image)
    }

    pub fn get(&self, name: &str) -> Option<&AnalysisContract> {
        self.0.get(name).map(|binding| &binding.annotated)
    }

    fn image(&self, name: &str) -> Option<&domain::ImageOperand> {
        self.0.get(name).and_then(|binding| binding.image.as_ref())
    }

    fn deferred_call(&self, name: &str) -> Option<&DeferredCall> {
        self.0
            .get(name)
            .and_then(|binding| binding.deferred_call.as_ref())
    }

    fn insert_deferred_call(&mut self, name: String, call: DeferredCall) {
        self.0.insert(
            name,
            TypeBinding {
                annotated: AnalysisContract::of_contract(Contract::Kind(Kind::Function)),
                image: None,
                deferred_call: Some(call),
            },
        );
    }

    fn insert_with_image(
        &mut self,
        name: String,
        annotated: AnalysisContract,
        image: Option<domain::ImageOperand>,
    ) -> Option<AnalysisContract> {
        self.0
            .insert(
                name,
                TypeBinding {
                    annotated,
                    image,
                    deferred_call: None,
                },
            )
            .map(|prior| prior.annotated)
    }

    /// BR-09: every local source and derived node sharing a source with the routed
    /// arrivals narrows simultaneously. Unrelated bindings remain independent.
    fn narrow_to(&mut self, arrivals: &domain::BranchSet, interner: &mut Interner) {
        for binding in self.0.values_mut() {
            let Some(image) = &binding.image else {
                continue;
            };
            let Some(relation) = image.force(interner) else {
                continue;
            };
            let narrowed = relation.narrowed_by(arrivals);
            let Some(contract) = narrowed.contract(interner) else {
                binding.annotated = AnalysisContract::bottom();
                binding.image = None;
                continue;
            };
            binding.annotated = domain::intersect_a(
                &binding.annotated,
                &AnalysisContract::of_contract(contract),
                interner,
            );
            binding.image = Some(domain::ImageOperand::Branches(std::rc::Rc::new(narrowed)));
        }
    }
}

/// Analyze a kernel expression against a contract environment.
pub fn analyze(
    expr: &Expr,
    env: &TypeEnv,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Analysis {
    analyze_in_world(expr, env, cenv, World::Pure, interner)
}

/// Analyze a kernel expression in its actual evaluation world. World is a seat
/// dependency: the expression/core contract can be reused, but call admission and
/// writes must be judged where the expression occurs (B5 / application §1.7).
pub(crate) fn analyze_in_world(
    expr: &Expr,
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    match expr {
        // A literal denotes exactly itself.
        Expr::Const(v) => Analysis::produced_annotated(
            AnalysisContract::of_value(v.clone(), interner),
            vec![],
            interner,
        ),

        // An immutable reference takes its bound contract; an unbound name is the
        // unbound-evaluation trap's compile-time mirror.
        Expr::Ref(Ref::Immutable(BindingRef::Name(name))) => match env.get(name) {
            Some(c) => {
                let mut analysis = Analysis::produced_annotated(c.clone(), vec![], interner);
                analysis.image = env.image(name).cloned();
                analysis
            }
            None => Analysis::produced(
                Contract::Top,
                vec![Finding {
                    class: TrapClass::UnboundEvaluation,
                    severity: Severity::Error,
                    message: format!("reference to unbound name `{name}`"),
                }],
            ),
        },
        // Positional / Location / Mu references are out of scope for this increment.
        Expr::Ref(_) => exact(Contract::Top),

        Expr::PrimOp { op, args } => analyze_primop(*op, args, env, cenv, world, interner),

        Expr::TupleCons(elems) => analyze_tuple(elems, env, cenv, world, interner),
        Expr::RecordCons(fields) => analyze_record(fields, env, cenv, world, interner),
        Expr::Template(parts) => analyze_template(parts, env, cenv, world, interner),
        Expr::Access {
            target,
            form,
            total,
        } => analyze_access(target, form, *total, env, cenv, world, interner),
        Expr::Match(m) => analyze_match(m, env, cenv, world, interner),
        Expr::Apply { callee, args } => analyze_apply(callee, args, env, cenv, world, interner),
        Expr::Write { slot, value } => analyze_write(slot, value, env, cenv, world, interner),

        // A body-nested lambda (C§13.2's instance flow, the exact-singleton cut):
        // when every free variable resolves to a singleton value in the current
        // environment, the closure is **constructible** — building it evaluates
        // nothing (the body is untouched; universal interning makes the value
        // canonical) — and the produced contract is the exact function value. A
        // non-singleton function that actually flows through a value seat instead
        // carries an analysis descriptor beside `Kind(Function)`; this is not a formed
        // closure value. Direct recursive locals use the separate late-call path below.
        Expr::Lambda(l) => analyze_lambda(l, env, interner),
    }
}

/// The single bound parameter name, when the pattern is one plain binding — the
/// shape the single-parameter region table serves.
pub(crate) fn single_plain_param(params: &crate::ast::Pat) -> Option<String> {
    use crate::ast::{Pat, PatElem};
    match params {
        Pat::Tuple(elems) => match elems.as_slice() {
            [PatElem::Pat(Pat::Bind(n))] => Some(n.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn exact(contract: Contract) -> Analysis {
    Analysis::produced(contract, vec![])
}

/// Analyze a bare lambda expression (see the `Expr::Lambda` arm's note).
fn analyze_lambda(l: &crate::ast::Lambda, env: &TypeEnv, interner: &mut Interner) -> Analysis {
    let free = crate::oracle::lambda_free_vars(l, interner);
    let mut captures: Vec<(String, ValueRef)> = Vec::with_capacity(free.len());
    for name in &free {
        let singleton = env
            .get(name)
            .and_then(|annotated| match annotated.erase(interner) {
                Contract::Equals(v) => Some(v),
                _ => None,
            });
        match singleton {
            Some(v) => captures.push((name.clone(), v)),
            // **C§13.2's flowing-value descriptor.** A capture that is not a single
            // value cannot make a closure *value* — but the analysis descriptor is
            // "shape + environment **contracts**", and the spec's own example is this
            // case (`makeAdder(someInput)`). Carry it as metadata beside the coarse
            // `Kind(Function)` so the callable "arrives at call sites with instances
            // recoverable"; returning a bare `Kind(Function)` here is what made a
            // factory product unusable under a `where`.
            None => {
                let captured: Vec<AnalysisContract> = free
                    .iter()
                    .map(|n| {
                        env.get(n)
                            .cloned()
                            .unwrap_or_else(|| AnalysisContract::of_contract(Contract::Top))
                    })
                    .collect();
                let instance = domain::Instance::from_lambda(l, captured, interner);
                return Analysis::produced_annotated(
                    AnalysisContract::leaf(
                        Contract::Kind(Kind::Function),
                        domain::InstanceMetadata::Known(vec![instance]),
                    ),
                    vec![],
                    interner,
                );
            }
        }
    }
    let scope = crate::env::Scope::root();
    for (name, v) in captures {
        scope.define(&name, crate::env::Binding::Value(v));
    }
    let value = crate::oracle::make_closure_in(l, &scope, interner);
    Analysis::produced_annotated(
        AnalysisContract::of_value(value, interner),
        vec![],
        interner,
    )
}

/// Prebind the block's named lambda identities before any initializer is analyzed, so a
/// self- or mutually-recursive local function can see itself and its siblings — exactly
/// as `program::define` does for module functions. Resolved captures produce concrete
/// closure values; open outer arguments produce only a delayed direct-call adapter.
///
/// The provisional closures share one construction scope, so a member created before
/// its sibling is defined resolves it at joint close. The closed functions retain
/// positional graph edges, not that scope. This makes `a = () => b(); b = () => a()`
/// inside a block work as well as at module level.
///
/// A lambda whose other captures are not single values cannot become a runtime closure
/// value during analysis. A direct self-recursive Pure member is instead installed as a
/// [`DeferredCall`]: closure conversion makes the outer environment explicit arguments
/// to an analyzer-only closed function. Runtime closure formation remains late.
fn prebind_sibling_lambdas(m: &crate::ast::Match, body_env: &mut TypeEnv, interner: &mut Interner) {
    let siblings: Vec<(&String, &crate::ast::Lambda)> = m
        .items
        .iter()
        .filter_map(|item| match item {
            crate::ast::MatchItem::Bind(crate::ast::Bind {
                target: crate::ast::BindTarget::Name(name),
                value: Expr::Lambda(l),
                ..
            }) => Some((name, l)),
            _ => None,
        })
        .collect();
    if siblings.is_empty() {
        return;
    }

    let scope = crate::env::Scope::root();
    let names: Vec<&str> = siblings.iter().map(|(n, _)| n.as_str()).collect();
    // Seed the shared scope with every singleton already visible, so a local lambda
    // may capture enclosing values as well as its siblings.
    let mut seeded: Vec<String> = Vec::new();
    for (_, l) in &siblings {
        for name in crate::oracle::lambda_free_vars(l, interner) {
            if names.contains(&name.as_str()) || seeded.contains(&name) {
                continue;
            }
            if let Some(Contract::Equals(v)) = body_env.get(&name).map(|a| a.erase(interner)) {
                scope.define(&name, crate::env::Binding::Value(v));
                seeded.push(name);
            }
        }
    }

    // **Build the group once.** A block is analyzed several times in one pass — region
    // rows, safety verification, return inference — and rebuilding gives a *different*
    // closure each time: a member's captures are self-referential, so a fresh scope makes
    // a fresh cycle rather than the same interned value. Measured: four distinct addresses
    // for one source function, which contradicts the identity law outright (same value =
    // same pointer) and means facts keyed on a callee say nothing about the next pass's
    // copy of it. Verified by probe: one construction, then hits at one address.
    //
    // The interned query is the whole immutable input to the construction — which lambdas,
    // under which names, over which captured values — so it determines what it returns.
    let key = interner.memo_query(GroupKey {
        siblings: siblings
            .iter()
            .map(|(n, l)| ((*n).clone(), (*l).clone()))
            .collect(),
        seeds: seeded
            .iter()
            .filter_map(|n| {
                scope.lookup(n).and_then(|b| match b {
                    crate::env::Binding::Value(v) => Some((n.clone(), v)),
                    _ => None,
                })
            })
            .collect(),
    });
    let built = if let Some(hit) = interner.memo_get::<GroupKey, LocalGroup>(&key) {
        hit.0.clone()
    } else {
        // A sibling whose captures are still unresolved cannot become a runtime value.
        // Build only the genuinely closed subset here; the delayed-call pass below owns
        // the non-singleton direct-recursion case.
        let mut built: Vec<(String, ValueRef)> = Vec::new();
        for (name, l) in &siblings {
            let resolvable = crate::oracle::lambda_free_vars(l, interner)
                .iter()
                .all(|f| names.contains(&f.as_str()) || seeded.contains(f));
            if !resolvable {
                continue;
            }
            let v = crate::oracle::make_closure_in(l, &scope, interner);
            scope.define(name, crate::env::Binding::Value(v.clone()));
            built.push(((*name).clone(), v));
        }
        if !built.is_empty()
            && built
                .iter()
                .all(|(_, value)| interner.value_is_closed(value))
        {
            let canonical = interner.close_recursive_group(&built, &scope);
            for ((name, value), canonical) in built.iter_mut().zip(canonical) {
                *value = canonical.clone();
                scope.define(name, crate::env::Binding::Value(canonical));
            }
        }
        interner.memo_publish(key, LocalGroup(built.clone()));
        built
    };

    for (name, value) in &built {
        body_env.insert(
            name.clone(),
            AnalysisContract::of_value(value.clone(), interner),
        );
    }

    // Do not invent a symbolic closure value for unresolved captures. For a direct
    // self-recursive Pure function, expose the enclosing values as leading arguments
    // of an analyzer-only closed function. Thus
    //
    //     outer(limit) { f(n) = ... f(n - 1) ... }
    //
    // is judged as `f(limit, n)`, and its back-edge as `f(limit, n - 1)`. The ordinary
    // recursion and drift machinery can then stop at that back-edge. The source runtime
    // still constructs `f` only when `outer` executes and captures the concrete limit.
    for (name, lambda) in siblings {
        if built.iter().any(|(built_name, _)| built_name == name) {
            continue;
        }
        if let Some(call) = lift_deferred_self_call(name, lambda, &names, body_env, interner) {
            body_env.insert_deferred_call(name.clone(), call);
        }
    }
}

/// The complete input to a local group's construction.
#[derive(Clone, PartialEq, Eq, Hash)]
struct GroupKey {
    siblings: Vec<(String, crate::ast::Lambda)>,
    seeds: Vec<(String, ValueRef)>,
}

/// The immutable answer to one local-group construction query. It lives under the
/// interner that owns every closure in it; no process/thread-local map may return values
/// from a different identity universe.
struct LocalGroup(Vec<(String, ValueRef)>);

/// The immutable input/output memo for one analyzer-only lambda-lifted recursive
/// target. Its source environment is *not* part of the function value: those arrived
/// contracts are supplied as call arguments by [`DeferredCall::prefix`].
#[derive(Clone, PartialEq, Eq, Hash)]
struct DeferredCallKey(crate::ast::Lambda);

struct DeferredCallTarget(ValueRef);

/// Convert one direct self-recursive Pure local lambda into a closed analyzer target.
/// This is closure conversion for a judgment, not construction of the source value.
fn lift_deferred_self_call(
    name: &str,
    lambda: &crate::ast::Lambda,
    sibling_names: &[&str],
    env: &TypeEnv,
    interner: &mut Interner,
) -> Option<DeferredCall> {
    use crate::ast::{Pat, PatElem};

    if lambda.act_kind != ActKind::Pure {
        return None;
    }
    let (canonical, free_names) = crate::oracle::canonical_function(lambda, interner);
    let self_slot = free_names.iter().position(|free| free == name)?;

    // Mutual recursion is already handled when concrete captures can be formed. The
    // abstract multi-member case needs simultaneous lifting; do not pretend a sibling
    // is an outer value in this narrow, sound first landing.
    if free_names
        .iter()
        .enumerate()
        .any(|(slot, free)| slot != self_slot && sibling_names.contains(&free.as_str()))
    {
        return None;
    }

    let external: Vec<(usize, String, AnalysisContract)> = free_names
        .iter()
        .enumerate()
        .filter(|(slot, _)| *slot != self_slot)
        .map(|(slot, source)| {
            env.get(source)
                .cloned()
                .map(|contract| (slot, format!("__next_env_{slot}"), contract))
        })
        .collect::<Option<_>>()?;
    if external.is_empty() {
        return None;
    }

    let self_name = "__next_recursive_self";
    let body = lift_deferred_expr(&canonical.body, self_slot, &external, self_name)?;
    let Pat::Tuple(original_params) = &canonical.params else {
        return None;
    };
    let mut params = Vec::with_capacity(external.len() + original_params.len());
    params.extend(
        external
            .iter()
            .map(|(_, parameter, _)| PatElem::Pat(Pat::Bind(parameter.clone()))),
    );
    params.extend(original_params.iter().cloned());
    let lifted = crate::ast::Lambda {
        params: Pat::Tuple(params),
        body: Box::new(body),
        act_kind: ActKind::Pure,
    };

    let key = interner.memo_query(DeferredCallKey(lifted.clone()));
    let callee = if let Some(hit) = interner.memo_get::<DeferredCallKey, DeferredCallTarget>(&key) {
        hit.0.clone()
    } else {
        let scope = crate::env::Scope::root();
        let provisional = crate::oracle::make_closure_in(&lifted, &scope, interner);
        scope.define(self_name, crate::env::Binding::Value(provisional.clone()));
        let roots = vec![(self_name.to_string(), provisional)];
        let callee = interner
            .close_recursive_group(&roots, &scope)
            .into_iter()
            .next()?;
        interner.memo_publish(key, DeferredCallTarget(callee.clone()));
        callee
    };

    Some(DeferredCall {
        callee,
        prefix: external
            .into_iter()
            .map(|(_, _, contract)| contract)
            .collect(),
    })
}

fn capture_name(slot: usize) -> String {
    format!("@cap{slot}")
}

fn immutable_name(name: impl Into<String>) -> Expr {
    Expr::Ref(Ref::Immutable(BindingRef::Name(name.into())))
}

fn lift_deferred_expr(
    expr: &Expr,
    self_slot: usize,
    external: &[(usize, String, AnalysisContract)],
    self_name: &str,
) -> Option<Expr> {
    use crate::ast::{Arm, Bind, Match, MatchItem};

    let self_capture = capture_name(self_slot);
    let replace_name = |name: &str| {
        external
            .iter()
            .find(|(slot, _, _)| capture_name(*slot) == name)
            .map(|(_, parameter, _)| parameter.clone())
    };
    Some(match expr {
        Expr::Const(value) => Expr::Const(value.clone()),
        Expr::Ref(Ref::Immutable(BindingRef::Name(name))) if name == &self_capture => {
            // A first-class escape of the recursive binding would require a closure
            // result, not merely delayed direct-call resolution. Leave it unproven.
            return None;
        }
        Expr::Ref(Ref::Immutable(BindingRef::Name(name))) => {
            immutable_name(replace_name(name).unwrap_or_else(|| name.clone()))
        }
        Expr::Ref(reference) => Expr::Ref(reference.clone()),
        Expr::Lambda(lambda) => Expr::Lambda(crate::ast::Lambda {
            params: lambda.params.clone(),
            body: Box::new(lift_deferred_expr(
                &lambda.body,
                self_slot,
                external,
                self_name,
            )?),
            act_kind: lambda.act_kind,
        }),
        Expr::Apply { callee, args }
            if matches!(
                &**callee,
                Expr::Ref(Ref::Immutable(BindingRef::Name(name))) if name == &self_capture
            ) =>
        {
            let mut lifted_args = Vec::with_capacity(external.len() + args.len());
            lifted_args.extend(
                external
                    .iter()
                    .map(|(_, parameter, _)| Arg::Expr(immutable_name(parameter.clone()))),
            );
            lifted_args.extend(
                args.iter()
                    .map(|arg| lift_deferred_arg(arg, self_slot, external, self_name))
                    .collect::<Option<Vec<_>>>()?,
            );
            Expr::Apply {
                callee: Box::new(immutable_name(self_name)),
                args: lifted_args,
            }
        }
        Expr::Apply { callee, args } => Expr::Apply {
            callee: Box::new(lift_deferred_expr(callee, self_slot, external, self_name)?),
            args: args
                .iter()
                .map(|arg| lift_deferred_arg(arg, self_slot, external, self_name))
                .collect::<Option<_>>()?,
        },
        Expr::PrimOp { op, args } => Expr::PrimOp {
            op: *op,
            args: args
                .iter()
                .map(|arg| lift_deferred_expr(arg, self_slot, external, self_name))
                .collect::<Option<_>>()?,
        },
        Expr::Match(match_expr) => Expr::Match(Match {
            scrutinee: match &match_expr.scrutinee {
                Some(scrutinee) => Some(Box::new(lift_deferred_expr(
                    scrutinee, self_slot, external, self_name,
                )?)),
                None => None,
            },
            items: match_expr
                .items
                .iter()
                .map(|item| {
                    Some(match item {
                        MatchItem::Bind(bind) => MatchItem::Bind(Bind {
                            target: bind.target.clone(),
                            value: lift_deferred_expr(&bind.value, self_slot, external, self_name)?,
                            exported: bind.exported,
                        }),
                        MatchItem::Stmt(statement) => MatchItem::Stmt(lift_deferred_expr(
                            statement, self_slot, external, self_name,
                        )?),
                        MatchItem::Arm(arm) => MatchItem::Arm(Arm {
                            pattern: arm.pattern.clone(),
                            guard: match &arm.guard {
                                Some(guard) => {
                                    Some(lift_deferred_expr(guard, self_slot, external, self_name)?)
                                }
                                None => None,
                            },
                            result: lift_deferred_expr(
                                &arm.result,
                                self_slot,
                                external,
                                self_name,
                            )?,
                        }),
                    })
                })
                .collect::<Option<_>>()?,
        }),
        Expr::TupleCons(elements) => Expr::TupleCons(
            elements
                .iter()
                .map(|element| lift_deferred_element(element, self_slot, external, self_name))
                .collect::<Option<_>>()?,
        ),
        Expr::RecordCons(fields) => Expr::RecordCons(
            fields
                .iter()
                .map(|field| lift_deferred_field(field, self_slot, external, self_name))
                .collect::<Option<_>>()?,
        ),
        Expr::Access {
            target,
            form,
            total,
        } => Expr::Access {
            target: Box::new(lift_deferred_expr(target, self_slot, external, self_name)?),
            form: lift_deferred_access(form, self_slot, external, self_name)?,
            total: *total,
        },
        Expr::Template(parts) => Expr::Template(
            parts
                .iter()
                .map(|part| match part {
                    TemplatePart::Segment(segment) => Some(TemplatePart::Segment(segment.clone())),
                    TemplatePart::Interp(interpolation) => Some(TemplatePart::Interp(
                        lift_deferred_expr(interpolation, self_slot, external, self_name)?,
                    )),
                })
                .collect::<Option<_>>()?,
        ),
        Expr::Write { slot, value } => {
            let slot = match slot {
                SlotRef::Name(name) if name == &self_capture => {
                    SlotRef::Name(self_name.to_string())
                }
                SlotRef::Name(name) => {
                    SlotRef::Name(replace_name(name).unwrap_or_else(|| name.clone()))
                }
                SlotRef::Location(location) => SlotRef::Location(*location),
            };
            Expr::Write {
                slot,
                value: Box::new(lift_deferred_expr(value, self_slot, external, self_name)?),
            }
        }
    })
}

fn lift_deferred_arg(
    arg: &Arg,
    self_slot: usize,
    external: &[(usize, String, AnalysisContract)],
    self_name: &str,
) -> Option<Arg> {
    match arg {
        Arg::Expr(expr) => Some(Arg::Expr(lift_deferred_expr(
            expr, self_slot, external, self_name,
        )?)),
        Arg::Spread(expr) => Some(Arg::Spread(lift_deferred_expr(
            expr, self_slot, external, self_name,
        )?)),
    }
}

fn lift_deferred_element(
    element: &Element,
    self_slot: usize,
    external: &[(usize, String, AnalysisContract)],
    self_name: &str,
) -> Option<Element> {
    match element {
        Element::Expr(expr) => Some(Element::Expr(lift_deferred_expr(
            expr, self_slot, external, self_name,
        )?)),
        Element::Spread(expr) => Some(Element::Spread(lift_deferred_expr(
            expr, self_slot, external, self_name,
        )?)),
    }
}

fn lift_deferred_field(
    field: &Field,
    self_slot: usize,
    external: &[(usize, String, AnalysisContract)],
    self_name: &str,
) -> Option<Field> {
    Some(match field {
        Field::Field { key, value } => Field::Field {
            key: key.clone(),
            value: lift_deferred_expr(value, self_slot, external, self_name)?,
        },
        Field::Computed { key, value } => Field::Computed {
            key: lift_deferred_expr(key, self_slot, external, self_name)?,
            value: lift_deferred_expr(value, self_slot, external, self_name)?,
        },
        Field::Spread(expr) => {
            Field::Spread(lift_deferred_expr(expr, self_slot, external, self_name)?)
        }
    })
}

fn lift_deferred_access(
    form: &AccessForm,
    self_slot: usize,
    external: &[(usize, String, AnalysisContract)],
    self_name: &str,
) -> Option<AccessForm> {
    Some(match form {
        AccessForm::Field(name) => AccessForm::Field(name.clone()),
        AccessForm::Index(index) => AccessForm::Index(Box::new(lift_deferred_expr(
            index, self_slot, external, self_name,
        )?)),
        AccessForm::Slice { lo, hi } => AccessForm::Slice {
            lo: match lo {
                Some(bound) => Some(Box::new(lift_deferred_expr(
                    bound, self_slot, external, self_name,
                )?)),
                None => None,
            },
            hi: match hi {
                Some(bound) => Some(Box::new(lift_deferred_expr(
                    bound, self_slot, external, self_name,
                )?)),
                None => None,
            },
        },
    })
}

/// The world a function body owns, independent of the world where its closure was
/// constructed or called (B5/E14).
pub(crate) fn world_for_act(kind: ActKind) -> World {
    match kind {
        ActKind::Pure => World::Pure,
        ActKind::Mutator => World::Mutator,
        ActKind::Effect => World::Effect,
    }
}

fn analyze_primop(
    op: PrimOp,
    args: &[Expr],
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();
    let mut inputs = Vec::with_capacity(args.len());
    let mut image_operands: Vec<domain::ImageOperand> = Vec::with_capacity(args.len());
    let mut singleton_operands: Vec<Option<ValueRef>> = Vec::with_capacity(args.len());
    for a in args {
        let mut r = analyze_in_world(a, env, cenv, world, interner);
        demand(&r, &mut findings); // operands are expecting seats
        findings.append(&mut r.findings);
        safety_demands.append(&mut r.safety_demands);
        // An operand that holds its own image is carried **as that image**, so a chain
        // stays exact instead of collapsing at the first coarse step.
        image_operands.push(
            r.image
                .clone()
                .unwrap_or_else(|| domain::ImageOperand::Points(r.contract.clone())),
        );
        // Exact aggregates are represented structurally in `annotated` (for
        // correlation and projection), not necessarily as `Contract::Equals`.
        // Recover their one canonical value for the existing oracle fold; otherwise
        // `[...][0] == 7` and `[] == []` lose exactness precisely where GR-09 needs
        // nested exact path selection.
        singleton_operands.push(r.annotated.singleton_value(interner));
        inputs.push(r.contract);
    }

    // **A consequence never speaks.** If analyzing the operands already produced an
    // Error, this operation cannot run at all — the operand halts first — so it has
    // no obligation to record and nothing to add. `f = d + e` fails *because* `d`
    // did, and `(1 + "x") + (2 * "y")` fails because its operand did: the same
    // descendant relation, once across a binding and once inside an expression. The
    // statement level already suppressed the first; this suppresses the second.
    // Returning `Bottom` carries the poison up, so the grandparent stays quiet too
    // and a chain reports one finding per real site.
    //
    // **Only an Error suppresses.** A merely *Unproven* operand leaves this seat's
    // Error as the thing that actually rejects the program (§5 late resolution) —
    // suppressing there would let an unproven program compile.
    if findings.iter().any(|f| f.severity == Severity::Error) {
        return Analysis::produced_with_safety(Contract::Bottom, findings, safety_demands);
    }

    // The rulebook judgment is made for every operation, including a closed one. The
    // oracle still supplies the exact folded value/trap below; the typed judgment is
    // retained separately so its witness/third voice survives program policy.
    let operation_result = analyze_operation(op, &inputs, interner);
    let operation_verdict = operation_result.safety.clone();
    safety_demands.push(SafetyDemand::Operation(OperationSafetyDemand {
        operation: op,
        inputs: inputs.clone(),
        verdict: operation_verdict.clone(),
    }));

    // Constant-fold when every operand is a singleton: run the oracle's own primop
    // semantics, so the trap class is predicted exactly (§6 concordance).
    let singletons: Option<Vec<ValueRef>> = singleton_operands.into_iter().collect();

    let contract = match singletons {
        Some(vals) => match eval_prim(op, &vals, interner) {
            Ok(v) => Contract::Equals(v),
            Err(trap) => {
                findings.push(Finding {
                    class: trap.class,
                    severity: Severity::Error,
                    message: trap.message,
                });
                Contract::Bottom // the operation halts; nothing flows downstream
            }
        },
        None => {
            match operation_verdict {
                OpSafety::Proven => {}
                OpSafety::Refuted(witness) => {
                    // The exact class comes from the oracle trapping on the witness.
                    let class = eval_prim(op, &witness, interner)
                        .err()
                        .map(|t| t.class)
                        .unwrap_or(TrapClass::OperationSafety);
                    findings.push(Finding {
                        class,
                        severity: Severity::Error,
                        message: format!("`{op:?}` traps on some input admitted by the operands"),
                    });
                }
                OpSafety::Unproven => findings.push(Finding {
                    class: TrapClass::OperationSafety,
                    severity: Severity::Warning,
                    message: format!("cannot prove `{op:?}` safe for these operands"),
                }),
            }
            operation_result.output
        }
    };

    // **Hold the exact image** (DR-16/17). When every operand is a finite point set the
    // operation has an exact result — but no *result* demand needs it (`⊑ Numeric` is
    // discharged at the producer's mapping, DR-02/DR-09), so it is not computed. The
    // ingredients ride beside the coarse contract, and a **routing** judgment that
    // cannot proceed without them forces this one node — never the whole judgment.
    let held = domain::HeldImage::hold(op, image_operands);
    let mut analysis = Analysis::produced_with_safety(contract, findings, safety_demands);
    if let Some(image) = held {
        analysis.image = Some(domain::ImageOperand::Nested(std::rc::Rc::new(image)));
    }
    analysis
}

fn analyze_tuple(
    elems: &[Element],
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();
    let mut segments: Vec<Contract> = Vec::new();
    let mut run: Vec<Contract> = Vec::new(); // the current spread-free element run
    let mut annotated_elements = Vec::new();
    let mut has_spread = false;
    for el in elems {
        match el {
            Element::Expr(e) => {
                let mut r = analyze_in_world(e, env, cenv, world, interner);
                demand(&r, &mut findings); // elements are expecting seats
                findings.append(&mut r.findings);
                safety_demands.append(&mut r.safety_demands);
                run.push(r.contract);
                annotated_elements.push(r.annotated);
            }
            // A spread must be a Tuple (E5 — else the spread-kind trap); the
            // result shape is a Concat with the spread's contract as a segment
            // (the tuple family's constructor, §1).
            Element::Spread(e) => {
                has_spread = true;
                let mut r = analyze_in_world(e, env, cenv, world, interner);
                demand(&r, &mut findings); // the spread operand is an expecting seat
                check_spread_kind(
                    &r.contract,
                    Kind::Tuple,
                    "tuple spread of a non-Tuple",
                    &mut findings,
                    interner,
                );
                findings.append(&mut r.findings);
                safety_demands.append(&mut r.safety_demands);
                if !run.is_empty() {
                    segments.push(Contract::tuple(std::mem::take(&mut run), interner));
                }
                segments.push(tuple_shaped(&r.contract));
            }
        }
    }
    if !run.is_empty() {
        segments.push(Contract::tuple(run, interner));
    }
    // With no spreads this normalizes straight back to the exact Tuple.
    if has_spread {
        Analysis::produced_with_safety(
            Contract::concat(segments, interner),
            findings,
            safety_demands,
        )
    } else {
        Analysis::produced_annotated_with_safety(
            AnalysisContract::tuple(annotated_elements),
            findings,
            safety_demands,
            interner,
        )
    }
}

/// The spread operand's contract as a Concat segment. On the non-trapping path
/// the value *is* a Tuple, so widening anything non-tuple-shaped to `Kind(Tuple)`
/// is sound.
fn tuple_shaped(c: &Contract) -> Contract {
    match c {
        Contract::Tuple(_) | Contract::Concat(_) | Contract::Kind(Kind::Tuple) => c.clone(),
        Contract::Equals(v) if v.as_tuple().is_some() => c.clone(),
        _ => Contract::Kind(Kind::Tuple),
    }
}

fn analyze_record(
    fields: &[Field],
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();
    let mut pairs = Vec::new();
    let mut annotated_pairs = Vec::new();
    let mut exact_shape = true;
    for field in fields {
        match field {
            Field::Field { key, value } => {
                let mut r = analyze_in_world(value, env, cenv, world, interner);
                demand(&r, &mut findings); // field values are expecting seats
                findings.append(&mut r.findings);
                safety_demands.append(&mut r.safety_demands);
                pairs.push((key.clone(), r.contract));
                annotated_pairs.push((key.clone(), r.annotated));
            }
            // A computed key must be a String at runtime (the computed-key trap)
            // and a **proven-finite string set** for the analyzer (E5, fork 12 = R;
            // A-VER: `Kind(String)` REJECTs). Both key and value are expecting seats.
            Field::Computed { key, value } => {
                let mut ka = analyze_in_world(key, env, cenv, world, interner);
                demand(&ka, &mut findings);
                findings.append(&mut ka.findings);
                safety_demands.append(&mut ka.safety_demands);
                check_computed_key(&ka.contract, &mut findings);
                let mut va = analyze_in_world(value, env, cenv, world, interner);
                demand(&va, &mut findings);
                findings.append(&mut va.findings);
                safety_demands.append(&mut va.safety_demands);
                exact_shape = false;
            }
            // A record spread must be a Record (else the spread-kind trap).
            Field::Spread(e) => {
                let mut r = analyze_in_world(e, env, cenv, world, interner);
                demand(&r, &mut findings);
                check_spread_kind(
                    &r.contract,
                    Kind::Record,
                    "record spread of a non-Record",
                    &mut findings,
                    interner,
                );
                findings.append(&mut r.findings);
                safety_demands.append(&mut r.safety_demands);
                exact_shape = false;
            }
        }
    }
    let contract = if exact_shape {
        Contract::record(pairs, interner)
    } else {
        Contract::Top
    };
    if exact_shape {
        Analysis::produced_annotated_with_safety(
            AnalysisContract::record(annotated_pairs),
            findings,
            safety_demands,
            interner,
        )
    } else {
        Analysis::produced_with_safety(contract, findings, safety_demands)
    }
}

/// A template always produces a String. **Structure interpolation is total**
/// [user, 2026-07-18]: every value renders (canonical literal forms for data,
/// `<Function>`, `<Indeterminate …>`), so an interpolation carries **no
/// printability demand** — there is nothing here to reject. Interpolations remain
/// ordinary expecting seats, and their subexpressions are analyzed as usual.
fn analyze_template(
    parts: &[TemplatePart],
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();
    for part in parts {
        let TemplatePart::Interp(e) = part else {
            continue;
        };
        let mut r = analyze_in_world(e, env, cenv, world, interner);
        demand(&r, &mut findings); // interpolations are expecting seats
        findings.append(&mut r.findings);
        safety_demands.append(&mut r.safety_demands);
    }
    Analysis::produced_with_safety(Contract::Kind(Kind::String), findings, safety_demands)
}

/// Access demands (E6). The *demand form* (`total = false`) must prove the
/// receiver non-null and the field present / index in bounds; the *total form*
/// (`?.`) totalizes to `null` and does not trap on those. Slices are clamped-total
/// on the window but still demand a sliceable receiver and integer bounds.
///
/// Closed accesses are constant-folded through the oracle (`eval_expr`) for an
/// exact verdict. Field access is fully reasoned on open receivers. Open slices
/// prove the receiver's String/Tuple carrier and integer bounds (the clamped window
/// is total); GR-08 separately reads direct tail-slice progress. General index
/// bounds and wider slice-length transfer remain tuple-family breadth.
fn analyze_access(
    target: &Expr,
    form: &AccessForm,
    total: bool,
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();
    let ta = analyze_in_world(target, env, cenv, world, interner);
    demand(&ta, &mut findings); // the receiver is an expecting seat
    let target_annotated = ta.annotated.clone();
    let tc = ta.contract.clone();
    findings.extend(ta.findings);
    safety_demands.extend(ta.safety_demands);

    // Analyze the index/bound subexpressions for their findings and fold values.
    let mut child = |e: &Expr, findings: &mut Vec<Finding>| -> Contract {
        let mut a = analyze_in_world(e, env, cenv, world, interner);
        demand(&a, findings); // index / slice bounds are expecting seats
        findings.append(&mut a.findings);
        safety_demands.append(&mut a.safety_demands);
        a.contract
    };
    let idx_c = match form {
        AccessForm::Index(e) => Some(child(e, &mut findings)),
        _ => None,
    };
    let (lo_c, hi_c) = match form {
        AccessForm::Slice { lo, hi } => (
            lo.as_ref().map(|e| child(e, &mut findings)),
            hi.as_ref().map(|e| child(e, &mut findings)),
        ),
        _ => (None, None),
    };

    // Try an exact fold: target and every relevant bound must be singletons.
    let folded_target = target_annotated.singleton_value(interner);
    let folded = folded_target.as_ref().and_then(|target| {
        fold_node(
            target,
            form,
            total,
            idx_c.as_ref(),
            lo_c.as_ref(),
            hi_c.as_ref(),
        )
    });
    if let Some(node) = folded {
        return match eval_expr(&node, interner) {
            Ok(Outcome::Produced(v)) => Analysis::produced_annotated_with_safety(
                AnalysisContract::of_value(v, interner),
                findings,
                safety_demands,
                interner,
            ),
            Ok(Outcome::CompletedWithoutValue) => {
                Analysis::produced_with_safety(Contract::Top, findings, safety_demands)
            }
            Err(trap) => {
                findings.push(Finding {
                    class: trap.class,
                    severity: Severity::Error,
                    message: trap.message,
                });
                Analysis::produced_with_safety(Contract::Bottom, findings, safety_demands)
            }
        };
    }

    // Structural source contracts can prove an access safe without flattening their
    // alternatives. This is the access half of AP-29: project each represented source
    // alternative, retaining branch correlation for a later joint application.
    let projected = match form {
        AccessForm::Field(name) => target_annotated.project_field(name, interner),
        AccessForm::Index(_) => idx_c
            .as_ref()
            .and_then(singleton_index)
            .and_then(|index| target_annotated.project_index(index, interner)),
        AccessForm::Slice { .. } => None,
    };
    if let Some(projected) = projected {
        return Analysis::produced_annotated_with_safety(
            projected,
            findings,
            safety_demands,
            interner,
        );
    }

    // Open path.
    let contract = match form {
        AccessForm::Field(name) => analyze_field(&tc, name, total, &mut findings, interner),
        AccessForm::Index(_) => analyze_index(&tc, total, &mut findings, interner),
        AccessForm::Slice { .. } => {
            analyze_slice(&tc, lo_c.as_ref(), hi_c.as_ref(), &mut findings, interner)
        }
    };
    Analysis::produced_with_safety(contract, findings, safety_demands)
}

fn singleton_index(contract: &Contract) -> Option<usize> {
    let Contract::Equals(value) = contract else {
        return None;
    };
    let number = value.as_number()?;
    if !number.is_integer() {
        return None;
    }
    number.as_ratio().numer().to_usize()
}

/// Reconstruct a closed `Access` node from singleton operand values, or `None` if
/// any relevant operand is not a singleton.
fn fold_node(
    tv: &ValueRef,
    form: &AccessForm,
    total: bool,
    idx_c: Option<&Contract>,
    lo_c: Option<&Contract>,
    hi_c: Option<&Contract>,
) -> Option<Expr> {
    let as_const = |c: &Contract| match c {
        Contract::Equals(v) => Some(Expr::Const(v.clone())),
        _ => None,
    };
    let form2 = match form {
        AccessForm::Field(name) => AccessForm::Field(name.clone()),
        AccessForm::Index(_) => AccessForm::Index(Box::new(as_const(idx_c?)?)),
        AccessForm::Slice { lo, hi } => AccessForm::Slice {
            lo: match (lo, lo_c) {
                (None, _) => None,
                (Some(_), Some(c)) => Some(Box::new(as_const(c)?)),
                (Some(_), None) => return None,
            },
            hi: match (hi, hi_c) {
                (None, _) => None,
                (Some(_), Some(c)) => Some(Box::new(as_const(c)?)),
                (Some(_), None) => return None,
            },
        },
    };
    Some(Expr::Access {
        target: Box::new(Expr::Const(tv.clone())),
        form: form2,
        total,
    })
}

/// Field access (E6): prove receiver non-null and field present (demand form).
fn analyze_field(
    tc: &Contract,
    name: &str,
    total: bool,
    findings: &mut Vec<Finding>,
    interner: &mut Interner,
) -> Contract {
    let has_field = Contract::HasField(name.to_string());
    let output = field_output(tc, name, interner);
    let null = Contract::Kind(Kind::Null);

    if matches!(subcontract(tc, &has_field, interner), Verdict::Proven) {
        // Record with the field, non-null — safe.
        return if total {
            or_null(output, interner)
        } else {
            output
        };
    }
    if total {
        // `?.` totalizes null and absent to null — never traps.
        return or_null(output, interner);
    }
    if disjoint(tc, &has_field) {
        // Every inhabitant either is null (null-receiver) or lacks the field
        // (absent-field) — always traps.
        let could_null = !disjoint(tc, &null);
        let class = if could_null {
            TrapClass::NullReceiver
        } else {
            TrapClass::AbsentField
        };
        findings.push(Finding {
            class,
            severity: Severity::Error,
            message: format!("field `{name}` access always traps on this receiver"),
        });
        return Contract::Bottom;
    }
    findings.push(Finding {
        class: TrapClass::AbsentField,
        severity: Severity::Error,
        message: format!("cannot prove field `{name}` present and receiver non-null"),
    });
    output
}

/// The values a successful field access can produce.
///
/// A selected Match row carries the effective input as an intersection such as
/// `(Response ∪ Failure) ∩ Response`. Looking only for a top-level `Record` loses the
/// contract of `body` at exactly the boundary where the pattern proved it. Projection
/// therefore follows the ordinary set constructors: union joins branch images,
/// intersection combines simultaneous field constraints, and difference can safely use
/// its base image. A branch on which the access cannot succeed contributes `Bottom`;
/// an open record constraint contributes `Top`.
fn field_output(tc: &Contract, name: &str, interner: &mut Interner) -> Contract {
    match tc {
        Contract::Bottom => Contract::Bottom,
        Contract::Equals(value) => value
            .as_record()
            .and_then(|entries| {
                let key: Vec<u16> = name.encode_utf16().collect();
                entries
                    .iter()
                    .find(|entry| entry.key == key)
                    .map(|entry| Contract::Equals(entry.value.clone()))
            })
            .unwrap_or(Contract::Bottom),
        Contract::Record(fields) => fields
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, c)| (**c).clone())
            .unwrap_or(Contract::Bottom),
        Contract::Union(left, right) => union_of(
            vec![
                field_output(left, name, interner),
                field_output(right, name, interner),
            ],
            interner,
        ),
        Contract::Intersection(left, right) => intersect(
            &field_output(left, name, interner),
            &field_output(right, name, interner),
            interner,
        ),
        Contract::Difference(base, _) => field_output(base, name, interner),
        Contract::Kind(
            Kind::Boolean | Kind::Function | Kind::Null | Kind::Number | Kind::String | Kind::Tuple,
        )
        | Contract::Indeterminate(_)
        | Contract::Range(..)
        | Contract::Greater(_)
        | Contract::GreaterEq(_)
        | Contract::Less(_)
        | Contract::LessEq(_)
        | Contract::Mod { .. }
        | Contract::Geo { .. }
        | Contract::Tuple(_)
        | Contract::Concat(_)
        | Contract::LengthRestricted(..) => Contract::Bottom,
        Contract::Top | Contract::Kind(Kind::Record) | Contract::HasField(_) | Contract::Ref(_) => {
            Contract::Top
        }
    }
}

fn or_null(c: Contract, i: &mut Interner) -> Contract {
    Contract::union(c, Contract::Kind(Kind::Null), i)
}

fn analyze_index(
    tc: &Contract,
    total: bool,
    findings: &mut Vec<Finding>,
    interner: &mut Interner,
) -> Contract {
    if total {
        return Contract::Top; // `?.[i]` totalizes null / out-of-bounds / non-integer to null
    }
    if matches!(
        subcontract(tc, &Contract::Kind(Kind::Null), interner),
        Verdict::Proven
    ) {
        findings.push(Finding {
            class: TrapClass::NullReceiver,
            severity: Severity::Error,
            message: "index of a null receiver".into(),
        });
        return Contract::Bottom;
    }
    // Bounds require tuple-length reasoning (C§17 owed).
    findings.push(Finding {
        class: TrapClass::IndexBounds,
        severity: Severity::Error,
        message: "cannot prove index in bounds (tuple-length rules owed, C§17)".into(),
    });
    Contract::Top
}

fn analyze_slice(
    tc: &Contract,
    lo: Option<&Contract>,
    hi: Option<&Contract>,
    findings: &mut Vec<Finding>,
    interner: &mut Interner,
) -> Contract {
    if matches!(tc, Contract::Bottom) {
        return Contract::Bottom;
    }
    // Slices trap on a non-sliceable receiver (operation-safety); null is not
    // totalized. Provably-null ⇒ always traps.
    if matches!(
        subcontract(tc, &Contract::Kind(Kind::Null), interner),
        Verdict::Proven
    ) {
        findings.push(Finding {
            class: TrapClass::OperationSafety,
            severity: Severity::Error,
            message: "slice of a null receiver".into(),
        });
        return Contract::Bottom;
    }

    let string = Contract::Kind(Kind::String);
    let tuple = Contract::Kind(Kind::Tuple);
    let output = if matches!(subcontract(tc, &string, interner), Verdict::Proven) {
        Some(string.clone())
    } else if matches!(subcontract(tc, &tuple, interner), Verdict::Proven) {
        Some(tuple.clone())
    } else {
        let sliceable = Contract::union(string, tuple, interner);
        matches!(subcontract(tc, &sliceable, interner), Verdict::Proven).then_some(sliceable)
    };
    let integers = Contract::Mod {
        n: num_bigint::BigInt::from(1),
        r: num_bigint::BigInt::from(0),
    };
    let bounds_are_integers = [lo, hi]
        .into_iter()
        .flatten()
        .all(|bound| matches!(subcontract(bound, &integers, interner), Verdict::Proven));
    if let Some(output) = output
        && bounds_are_integers
    {
        // The window itself is clamped-total. Kind is preserved; the grounding
        // segment candidate separately reads the relational length drop from the
        // recursive arm's effective input region.
        return output;
    }
    findings.push(Finding {
        class: TrapClass::OperationSafety,
        severity: Severity::Error,
        message: "cannot prove receiver sliceable / bounds integer (C§17 owed)".into(),
    });
    Contract::Top
}

/// Analyze mutation without executing it. The oracle checks world admission before
/// evaluating the RHS, so an illegal write reports that trap alone. A legal write
/// evaluates its RHS at an expecting seat and completes without producing a value.
fn analyze_write(
    slot: &SlotRef,
    value: &Expr,
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    if world != World::Mutator {
        return Analysis::produced(
            Contract::Bottom,
            vec![Finding {
                class: TrapClass::WorldAdmission,
                severity: Severity::Error,
                message: "`:=` is legal only inside a mutator".into(),
            }],
        );
    }

    let mut findings = Vec::new();
    let mut rhs = analyze_in_world(value, env, cenv, world, interner);
    demand(&rhs, &mut findings);
    findings.append(&mut rhs.findings);
    Analysis {
        contract: Contract::Bottom,
        annotated: AnalysisContract::bottom(),
        image: None,
        findings,
        safety_demands: rhs.safety_demands,
        completion: Completion::FallsThrough(CompletionWitness::Write { slot: slot.clone() }),
    }
}

// ── Apply (C§7 / B5 / E10) — application ──────────────────────────────────────

/// Analyze an application without using execution as its transfer rule (Archive6
/// §8/§9). AP-30's realized-witness refutation is the narrow exception: a bounded
/// concrete Pure call may certify `CompletedWithoutValue`, but never infer safety or a
/// return contract. Each
/// argument spread must be a Tuple (`spread-kind`); the callee must be a function (else
/// operation-safety); and when the callee value is known, its act-kind is checked
/// against the analysis world (`world-admission`), the argument tuple against its
/// parameter pattern (`argument-obligation`), its body's proven traps surfaced by
/// **interprocedural body safety** (`induction::body_safety`), its return inferred
/// (`call_return`), and its completion demanded (`callee_completion`). A closed call is
/// no longer folded through the oracle — a diverging closed call is analyzed, never run.
///
/// World admission is applied at this seat from the caller-supplied world; it is
/// deliberately absent from the reusable callee/body facts.
fn analyze_apply(
    callee: &Expr,
    args: &[Arg],
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    // A local recursive closure over an open outer argument does not exist yet. Its
    // direct call is nevertheless a judgment we can make now by supplying that outer
    // environment as ordinary leading arguments to the analyzer-only lifted target.
    // Spreads stay on the general application path because their positional expansion
    // is not available here.
    if args.iter().all(|arg| matches!(arg, Arg::Expr(_)))
        && let Expr::Ref(Ref::Immutable(BindingRef::Name(name))) = callee
        && let Some(call) = env.deferred_call(name).cloned()
    {
        return analyze_deferred_call(&call, args, env, cenv, world, interner);
    }

    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();

    let ca = analyze_in_world(callee, env, cenv, world, interner);
    demand(&ca, &mut findings); // the callee is an expecting seat
    let callee_annotated = ca.annotated.clone();
    findings.extend(ca.findings);
    safety_demands.extend(ca.safety_demands);

    let mut argument_annotated: Vec<AnalysisContract> = Vec::new();
    let mut has_spread = false;
    for a in args {
        match a {
            Arg::Expr(e) => {
                let aa = analyze_in_world(e, env, cenv, world, interner);
                demand(&aa, &mut findings);
                argument_annotated.push(aa.annotated.clone());
                findings.extend(aa.findings);
                safety_demands.extend(aa.safety_demands);
            }
            Arg::Spread(e) => {
                has_spread = true;
                let aa = analyze_in_world(e, env, cenv, world, interner);
                demand(&aa, &mut findings);
                check_spread_kind(
                    &aa.contract,
                    Kind::Tuple,
                    "argument spread of a non-Tuple",
                    &mut findings,
                    interner,
                );
                findings.extend(aa.findings);
                safety_demands.extend(aa.safety_demands);
            }
        }
    }

    // Preserve a joint source relation when every position is an immutable projection
    // of the same correlated binding (AP-29). Otherwise form the legal projected
    // operand from the independently analyzed positions.
    let operand = correlated_access_operand(callee, args, env, interner).unwrap_or_else(|| {
        application::operand_from_annotated(&callee_annotated, &argument_annotated)
    });
    let transfer = application::drive_application(&operand, |alternative, correlated| {
        analyze_application_alternative(alternative, correlated, has_spread, world, cenv, interner)
    });
    for mut detail in transfer.details {
        findings.append(&mut detail.findings);
        safety_demands.append(&mut detail.safety_demands);
    }
    Analysis {
        contract: transfer.outcome.produced.erase(interner),
        annotated: transfer.outcome.produced,
        image: None,
        findings,
        safety_demands,
        completion: completion_from_application(transfer.outcome.completion),
    }
}

fn analyze_deferred_call(
    call: &DeferredCall,
    args: &[Arg],
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();
    let mut arguments = call.prefix.clone();
    for arg in args {
        let Arg::Expr(expr) = arg else {
            unreachable!("the deferred-call adapter accepts only positional arguments")
        };
        let mut analyzed = analyze_in_world(expr, env, cenv, world, interner);
        demand(&analyzed, &mut findings);
        arguments.push(analyzed.annotated.clone());
        findings.append(&mut analyzed.findings);
        safety_demands.append(&mut analyzed.safety_demands);
    }
    let argument_contracts: Vec<Contract> = arguments
        .iter()
        .map(|argument| argument.erase(interner))
        .collect();
    let mut contribution = analyze_known_application_alternative(
        &call.callee,
        &argument_contracts,
        true,
        false,
        world,
        cenv,
        interner,
    );
    findings.append(&mut contribution.detail.findings);
    safety_demands.append(&mut contribution.detail.safety_demands);
    Analysis {
        contract: contribution.outcome.produced.erase(interner),
        annotated: contribution.outcome.produced,
        image: None,
        findings,
        safety_demands,
        completion: completion_from_application(contribution.outcome.completion),
    }
}

/// Analyze an application whose callee is a **contract-level instance** (C§13.2):
/// bind canonical capture positions and parameters, then run the ordinary body
/// walk under an interner-owned domain-indexed symbolic fact. A recursive edge
/// closes only when its full instance and arrived input are covered by the active
/// hypothesis; a mere code-shape repeat is honestly unproven.
fn analyze_contract_level_instance(
    instance: &domain::Instance,
    arg_contracts: &[Contract],
    seat_world: World,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> AlternativeContribution<ApplicationDetail> {
    let mut seat_findings = Vec::new();
    if !seat_world.admits(instance.act_kind()) {
        seat_findings.push(Finding {
            class: TrapClass::WorldAdmission,
            severity: Severity::Error,
            message: format!(
                "a {:?} call is not admitted in {seat_world:?} world",
                instance.act_kind()
            ),
        });
    }

    let arg_tuple = Contract::tuple(arg_contracts.to_vec(), interner);
    let params = pattern_contract(&instance.code().params, cenv, interner);
    if !matches!(subcontract(&arg_tuple, &params, interner), Verdict::Proven) {
        let message = if disjoint(&arg_tuple, &params) {
            "arguments cannot match the parameter pattern"
        } else {
            "cannot prove the arguments match the parameter pattern"
        };
        seat_findings.push(Finding {
            class: TrapClass::ArgumentObligation,
            severity: Severity::Error,
            message: message.into(),
        });
    }

    let key = factcache::symbolic_key(instance, arg_contracts, cenv, interner);
    let analysis = match factcache::symbolic_lookup(&key, interner) {
        factcache::SymbolicCached::Hypothesis => Analysis {
            contract: Contract::Top,
            annotated: AnalysisContract::of_contract(Contract::Top),
            image: None,
            findings: Vec::new(),
            safety_demands: Vec::new(),
            completion: Completion::MayFallThrough,
        },
        factcache::SymbolicCached::Settled(answer) => (*answer).clone(),
        factcache::SymbolicCached::UncoveredRepeat => Analysis {
            contract: Contract::Top,
            annotated: AnalysisContract::of_contract(Contract::Top),
            image: None,
            findings: vec![Finding {
                class: TrapClass::OperationSafety,
                severity: Severity::Error,
                message: "symbolic recursive call is not covered by the active domain-indexed fact"
                    .into(),
            }],
            safety_demands: Vec::new(),
            completion: Completion::MayFallThrough,
        },
        factcache::SymbolicCached::Missing => {
            let mut env = TypeEnv::new();
            for (index, captured) in instance.captures().iter().enumerate() {
                env.insert(format!("@cap{index}"), captured.clone());
            }
            bind_pattern(&instance.code().params, &arg_tuple, &mut env, interner);
            let tainted = induction::any_hypotheses_active();
            factcache::symbolic_begin(&key);
            let answer = analyze_in_world(
                &instance.code().body,
                &env,
                cenv,
                world_for_act(instance.act_kind()),
                interner,
            );
            factcache::symbolic_finish(&key, &answer, tainted, interner);
            answer
        }
    };

    seat_findings.extend(analysis.findings);
    application_contribution(
        seat_findings,
        analysis.safety_demands,
        analysis.annotated,
        analysis.completion,
    )
}

fn analyze_contract_level_instances(
    instances: &[domain::Instance],
    arg_contracts: &[Contract],
    seat_world: World,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> AlternativeContribution<ApplicationDetail> {
    let mut contributions: Vec<AlternativeContribution<ApplicationDetail>> = instances
        .iter()
        .filter(|instance| !instance.is_empty())
        .map(|instance| {
            analyze_contract_level_instance(instance, arg_contracts, seat_world, cenv, interner)
        })
        .collect();
    if contributions.is_empty() {
        return application_contribution(
            Vec::new(),
            Vec::new(),
            Contract::Bottom,
            Completion::Produces,
        );
    }

    let verdict = if contributions
        .iter()
        .all(|contribution| matches!(contribution.verdict, SeatVerdict::Proven))
    {
        SeatVerdict::Proven
    } else {
        SeatVerdict::Unproven
    };
    let outcome = application::join_all(
        contributions
            .iter()
            .map(|contribution| contribution.outcome.clone()),
    );
    let mut detail = ApplicationDetail::default();
    for contribution in &mut contributions {
        detail.findings.append(&mut contribution.detail.findings);
        detail
            .safety_demands
            .append(&mut contribution.detail.safety_demands);
    }
    AlternativeContribution {
        verdict,
        outcome,
        detail,
    }
}

#[derive(Clone, Debug, Default)]
struct ApplicationDetail {
    findings: Vec<Finding>,
    safety_demands: Vec<SafetyDemand>,
}

/// Supply one fact-backed contribution to the canonical application driver. This is
/// the only expression-layer adapter: it erases the driver's annotated positions for
/// the currently-live fact machinery, classifies the one callee leaf, and returns the
/// complete outcome plus diagnostics without performing an alternative join.
fn analyze_application_alternative(
    alternative: &application::Alternative,
    correlated: bool,
    has_spread: bool,
    world: World,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> AlternativeContribution<ApplicationDetail> {
    let arg_contracts: Vec<Contract> = alternative
        .arguments
        .iter()
        .map(|argument| argument.erase(interner))
        .collect();
    // **C§13.2's contract-level instance at the seat.** A callable with no value but a
    // recoverable instance — shape + capture contracts — resolves *through* that
    // instance instead of being declared unknown ("callables … arrive at call sites
    // with instances recoverable"). Every represented instance contributes through
    // the same alternative; admission, safety, produced values, and completion join
    // conjunctively/componentwise as required by the canonical driver.
    if !has_spread
        && let AnalysisContract::Leaf {
            contract: Contract::Kind(Kind::Function),
            metadata: domain::InstanceMetadata::Known(instances),
            ..
        } = &alternative.callee
    {
        return analyze_contract_level_instances(instances, &arg_contracts, world, cenv, interner);
    }

    let erased_callee = alternative.callee.erase(interner);
    let classified = application::classify_callees(&erased_callee, interner);
    let callee = match classified.as_slice() {
        [callee] => callee.clone(),
        _ => CalleeAlternative::UnknownFunction,
    };

    match callee {
        CalleeAlternative::NotAFunction { inhabited } => {
            let message = if inhabited {
                "callee is not a function"
            } else {
                "callee may not be a function (no represented inhabitant to confirm)"
            };
            application_contribution(
                vec![Finding {
                    class: TrapClass::OperationSafety,
                    severity: Severity::Error,
                    message: message.into(),
                }],
                Vec::new(),
                Contract::Bottom,
                Completion::Produces,
            )
        }
        CalleeAlternative::UnknownFunction => application_contribution(
            vec![Finding {
                class: TrapClass::OperationSafety,
                severity: Severity::Error,
                message:
                    "cannot prove this callee's body safe (callee not resolved to a known function)"
                        .into(),
            }],
            Vec::new(),
            Contract::Top,
            Completion::MayFallThrough,
        ),
        CalleeAlternative::Known(callee) => analyze_known_application_alternative(
            &callee,
            &arg_contracts,
            correlated,
            has_spread,
            world,
            cenv,
            interner,
        ),
    }
}

#[derive(Clone)]
enum AccessProjection {
    Index(usize),
    Field(String),
}

/// Rebuild the exact joint relation for immutable projections of one correlated
/// source binding. This is deliberately narrow: if any position has a different
/// source, a spread, a total access, or a projection the structural domain cannot
/// certify, the ordinary projected operand is used instead.
fn correlated_access_operand(
    callee: &Expr,
    args: &[Arg],
    env: &TypeEnv,
    interner: &mut Interner,
) -> Option<AnalysisContract> {
    let (source, callee_projection) = source_projection(callee)?;
    let mut projections = vec![callee_projection];
    for argument in args {
        let Arg::Expr(expr) = argument else {
            return None;
        };
        let (argument_source, projection) = source_projection(expr)?;
        if argument_source != source {
            return None;
        }
        projections.push(projection);
    }

    let source_contract = env.get(&source)?;
    let alternatives: Vec<AnalysisContract> = match source_contract {
        AnalysisContract::Alt(alternatives) => alternatives.clone(),
        other => vec![other.clone()],
    };
    let mut operand_alternatives = Vec::with_capacity(alternatives.len());
    for alternative in alternatives {
        let positions = projections
            .iter()
            .map(|projection| match projection {
                AccessProjection::Index(index) => alternative.project_index(*index, interner),
                AccessProjection::Field(name) => alternative.project_field(name, interner),
            })
            .collect::<Option<Vec<_>>>()?;
        operand_alternatives.push(AnalysisContract::tuple(positions));
    }
    Some(AnalysisContract::alt(operand_alternatives))
}

fn source_projection(expr: &Expr) -> Option<(String, AccessProjection)> {
    let Expr::Access {
        target,
        form,
        total: false,
    } = expr
    else {
        return None;
    };
    let Expr::Ref(Ref::Immutable(BindingRef::Name(source))) = &**target else {
        return None;
    };
    let projection = match form {
        AccessForm::Field(name) => AccessProjection::Field(name.clone()),
        AccessForm::Index(index) => {
            let Expr::Const(value) = &**index else {
                return None;
            };
            let number = value.as_number()?;
            if !number.is_integer() {
                return None;
            }
            AccessProjection::Index(number.as_ratio().numer().to_usize()?)
        }
        AccessForm::Slice { .. } => return None,
    };
    Some((source.clone(), projection))
}

fn analyze_known_application_alternative(
    callee: &ValueRef,
    arg_contracts: &[Contract],
    correlated: bool,
    has_spread: bool,
    world: World,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> AlternativeContribution<ApplicationDetail> {
    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();
    analyze_known_callee(
        callee,
        arg_contracts,
        has_spread,
        world,
        &mut findings,
        cenv,
        interner,
    );

    // Effect primitives are total-return by the B6 user ruling: host failure is
    // ordinary `Failure` data, never a trap. Their Rust body is not analyzer input.
    if callee.as_native().is_some() {
        return application_contribution(
            findings,
            safety_demands,
            Contract::Top,
            Completion::Produces,
        );
    }

    // A dependency already established resolves through that fact; acyclic
    // dependencies retain their exact body outcome. `safety::established` is the
    // *same* predicate graph discovery uses, so a dependency discovery discharged is
    // one this seat can consume (2026-08-06 — they used to disagree, and a `where`
    // could thereby change a call site's verdict).
    if !has_spread
        && safety::established(
            callee,
            arg_contracts,
            &induction::Claim::Safety,
            cenv,
            interner,
        )
    {
        safety_demands.push(SafetyDemand::Body(BodySafetyDemand {
            callee: callee.clone(),
            arguments: arg_contracts.to_vec(),
            verdict: safety::BodySafety::Proven,
        }));
        if induction::is_recursive(callee) {
            let produced = call_return(callee, arg_contracts, has_spread, cenv, interner);
            let completes = induction::completes_assumed(callee, arg_contracts, interner)
                || safety::completes(callee, arg_contracts, cenv, interner);
            let completion = callee_completion(callee, arg_contracts, completes, cenv, interner);
            return application_contribution(findings, safety_demands, produced, completion);
        }
        let observed = outcome::analyze_instance_body(callee, arg_contracts, cenv, interner)
            .expect("a known closure has a body outcome");
        let completes = matches!(&observed.completion, Completion::Produces);
        let completion = callee_completion(callee, arg_contracts, completes, cenv, interner);
        return application_contribution(findings, safety_demands, observed.annotated, completion);
    }

    // Candidate-graph verification may consume only the active/settled graph. Starting
    // another settlement here would bypass a cutoff dependency.
    if !has_spread && safety::safety_context_active() {
        let advisory = Finding {
            class: TrapClass::OperationSafety,
            severity: Severity::Warning,
            message: "callee safety is not established by the active fact graph".into(),
        };
        findings.push(advisory.clone());
        safety_demands.push(SafetyDemand::Body(BodySafetyDemand {
            callee: callee.clone(),
            arguments: arg_contracts.to_vec(),
            verdict: safety::BodySafety::Unproven(safety::BodySafetyEvidence {
                findings: vec![advisory],
                demands: Vec::new(),
            }),
        }));
        // The safety voice stays Unproven; the OTHER judgments still answer from their
        // own facts (§1.6 — separate judgment classes). A recursive callee's produced
        // comes from `call_return` (the return fact is its own induction and settles
        // no safety facts), so a nested `m(m(n + 11))` keeps a real outer-argument
        // contract instead of minting an uncoverable `(m, [Top])` node. Completion
        // consults the assumed completion facts and settled coverage — read-only,
        // never a settlement past the cutoff.
        //
        // A **non-recursive** callee answers its produced voice the same way: the
        // ordinary instance-body walk, which settles no fact and is bounded by the
        // shape-repeat cutoff. Collapsing it to `Top` was not free — a function
        // *produced by a nested call* became unresolvable, so
        // `build = () => makeCounter(7)(3)` was rejected with "callee not resolved to
        // a known function" while the identical two-step form at module level passed.
        // The annotated form, not the erased one: a produced **callable** carries its
        // analysis instance as metadata (C§13.2), and erasing here would strip it —
        // leaving a later seat with an unresolvable `Kind(Function)`.
        let produced = if induction::is_recursive(callee) {
            AnalysisContract::of_contract(call_return(
                callee,
                arg_contracts,
                has_spread,
                cenv,
                interner,
            ))
        } else {
            outcome::analyze_instance_body(callee, arg_contracts, cenv, interner).map_or_else(
                || AnalysisContract::of_contract(Contract::Top),
                |a| a.annotated,
            )
        };
        let completion = if induction::completes_assumed(callee, arg_contracts, interner)
            || safety::completes_settled(callee, arg_contracts, cenv, interner)
        {
            Completion::Produces
        } else {
            Completion::MayFallThrough
        };
        return application_contribution(findings, safety_demands, produced, completion);
    }
    if has_spread {
        return application_contribution(
            findings,
            safety_demands,
            Contract::Top,
            Completion::Produces,
        );
    }

    let body_safe = weaken_projected_body_safety(
        safety::prove(callee, arg_contracts, cenv, interner),
        correlated,
    );
    safety_demands.push(SafetyDemand::Body(BodySafetyDemand {
        callee: callee.clone(),
        arguments: arg_contracts.to_vec(),
        verdict: body_safe.clone(),
    }));
    if !discharge_body_safety(&body_safe, &mut findings) {
        // Safety's failure blocks this seat, but the produced and completion voices
        // remain their own judgments (§1.6). Under a return pass's hypotheses the
        // recursive callee must contribute its assumed contract — under the
        // proposal's bottoms that is `Bottom`, not a proposal-poisoning `Top`.
        // Completion likewise reads the assumed/settled completion facts only.
        //
        // A **non-recursive** callee keeps its own produced judgment too: analyze the
        // instance body (which settles no fact — it is the ordinary body walk) rather
        // than collapsing to `Top`. Sound either way — if the body is genuinely unsafe
        // the seat already carries the error and no value is produced — but the
        // collapse was **not** free: during a safety settlement, nested applications
        // are deliberately answered coarsely (the `VERIFYING_SAFETY` guard), so a
        // function *produced by a nested call* became `Top` and could then never be
        // applied. That rejected correct code — `build = () => makeCounter(7)(3)` —
        // with "callee not resolved to a known function".
        // The annotated form, not the erased one: a produced **callable** carries its
        // analysis instance as metadata (C§13.2), and erasing here would strip it —
        // leaving a later seat with an unresolvable `Kind(Function)`.
        let produced = if induction::is_recursive(callee) {
            AnalysisContract::of_contract(call_return(
                callee,
                arg_contracts,
                has_spread,
                cenv,
                interner,
            ))
        } else {
            outcome::analyze_instance_body(callee, arg_contracts, cenv, interner).map_or_else(
                || AnalysisContract::of_contract(Contract::Top),
                |a| a.annotated,
            )
        };
        let completion = if induction::completes_assumed(callee, arg_contracts, interner)
            || safety::completes_settled(callee, arg_contracts, cenv, interner)
        {
            Completion::Produces
        } else {
            Completion::MayFallThrough
        };
        return application_contribution(findings, safety_demands, produced, completion);
    }

    // Safety has settled the complete dependency graph. Completion and recursive
    // returns come from their own domain-indexed facts; an acyclic result stays exact.
    let observed = outcome::analyze_instance_body(callee, arg_contracts, cenv, interner)
        .unwrap_or_else(|| Analysis {
            contract: Contract::Top,
            annotated: AnalysisContract::of_contract(Contract::Top),
            image: None,
            findings: Vec::new(),
            safety_demands: Vec::new(),
            completion: Completion::MayFallThrough,
        });
    let completes = safety::completes(callee, arg_contracts, cenv, interner);
    let completion = callee_completion(callee, arg_contracts, completes, cenv, interner);
    let produced = if induction::is_recursive(callee) {
        AnalysisContract::of_contract(call_return(
            callee,
            arg_contracts,
            has_spread,
            cenv,
            interner,
        ))
    } else {
        observed.annotated
    };
    application_contribution(findings, safety_demands, produced, completion)
}

fn application_contribution(
    findings: Vec<Finding>,
    safety_demands: Vec<SafetyDemand>,
    produced: impl Into<AnalysisContract>,
    completion: Completion,
) -> AlternativeContribution<ApplicationDetail> {
    let produced = produced.into();
    let verdict = if findings
        .iter()
        .any(|finding| finding.severity == Severity::Error)
        || safety_demands.iter().any(|demand| match demand {
            SafetyDemand::Operation(operation) => !matches!(operation.verdict, OpSafety::Proven),
            SafetyDemand::Body(body) => !matches!(body.verdict, safety::BodySafety::Proven),
        }) {
        SeatVerdict::Unproven
    } else {
        SeatVerdict::Proven
    };
    let completion = CompletionWithoutValue::of(completion);
    AlternativeContribution {
        verdict,
        outcome: ApplicationOutcome {
            produced,
            completion,
            may_not_complete: false,
        },
        detail: ApplicationDetail {
            findings,
            safety_demands,
        },
    }
}

/// AP-29: an independently projected callee/argument pair is not a represented
/// execution. A body refutation obtained only from that pair therefore becomes the
/// third voice before the blocking policy is applied; its diagnostics become advisory
/// evidence and the policy adds the unsuppressible Unproven error separately.
fn weaken_projected_body_safety(
    verdict: safety::BodySafety,
    correlated: bool,
) -> safety::BodySafety {
    if correlated {
        return verdict;
    }
    match verdict {
        safety::BodySafety::Refuted(evidence) => {
            safety::BodySafety::Unproven(safety::weaken_refutation_evidence(evidence))
        }
        other => other,
    }
}

fn completion_from_application(completion: CompletionWithoutValue) -> Completion {
    match completion {
        CompletionWithoutValue::ProvenAbsent => Completion::Produces,
        CompletionWithoutValue::ProvenPresent(witness) => {
            Completion::FallsThrough(CompletionWitness::Application(witness))
        }
        CompletionWithoutValue::UnprovenPossible => Completion::MayFallThrough,
    }
}

/// Evidence-preserving completion join for non-application expression composition
/// (currently Match). Application alternatives join in the canonical driver.
fn join_completions(completions: &[Completion]) -> Completion {
    if let Some(witness) = completions.iter().find_map(|completion| match completion {
        Completion::FallsThrough(witness) => Some(witness.clone()),
        Completion::Produces | Completion::MayFallThrough => None,
    }) {
        Completion::FallsThrough(witness)
    } else if completions
        .iter()
        .any(|completion| matches!(completion, Completion::MayFallThrough))
    {
        Completion::MayFallThrough
    } else {
        Completion::Produces
    }
}

/// Attach expression-local diagnostics to a settled body-safety fact. Refutation keeps
/// its Error evidence. Unproven remains advisory here and blocks through the typed
/// demand; the executable or declared consuming boundary materializes its policy Error.
fn discharge_body_safety(verdict: &safety::BodySafety, findings: &mut Vec<Finding>) -> bool {
    match verdict {
        safety::BodySafety::Proven => true,
        safety::BodySafety::Refuted(evidence) => {
            let mut body_findings = evidence.findings.clone();
            if !body_findings.iter().any(|f| f.severity == Severity::Error) {
                body_findings.push(Finding {
                    class: TrapClass::OperationSafety,
                    severity: Severity::Error,
                    message: "callee body safety is refuted".into(),
                });
            }
            findings.append(&mut body_findings);
            false
        }
        safety::BodySafety::Unproven(evidence) => {
            let mut body_findings = evidence.findings.clone();
            body_findings.push(Finding {
                class: TrapClass::OperationSafety,
                severity: Severity::Warning,
                message: "callee body safety cannot be proven".into(),
            });
            findings.append(&mut body_findings);
            false
        }
    }
}

/// The callee's completion (E10) at a call site. A **mutator's completing outcome** is
/// always without a value by the return-discard law (B5), so a represented input tuple
/// supplies its structural witness. Otherwise the settled fact supplies `Produces`; a
/// failed proof stays the third voice unless AP-30 realizes a completing-without-value
/// Pure execution.
fn callee_completion(
    cv: &ValueRef,
    args: &[Contract],
    completes: bool,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Completion {
    if cv
        .as_closure()
        .is_some_and(|c| matches!(c.lambda.act_kind, ActKind::Mutator))
    {
        return refute::represented_application(cv, args, interner)
            .map_or(Completion::MayFallThrough, |witness| {
                Completion::FallsThrough(CompletionWitness::Application(witness))
            });
    }
    if completes {
        return Completion::Produces;
    }
    // Failure to prove universal production is not itself a fall-through witness.
    // AP-30 promotes the third voice only on a **structurally proven** represented
    // `(callee, arguments)` execution that completes without a value (no
    // evaluation — the sampler is revoked).
    refute::realized_completion(cv, args, cenv, interner)
        .map_or(Completion::MayFallThrough, |witness| {
            Completion::FallsThrough(CompletionWitness::Application(witness))
        })
}

/// The inferred return contract for a call to the known closure `cv` over
/// `arg_contracts` (§6 / C§13.2). An active return-induction hypothesis (inside a
/// driver pass) wins directly; otherwise — outside a spread call and outside an
/// in-progress inference — run [`induction::infer_return_fact`] over the **call-site
/// argument contracts**, so `factorial(k)` with `k : Number` returns `Number` rather
/// rather than the untyped-domain coarse result (let alone `Top`). Falls back to
/// `Top` when nothing informative is inferred (sound).
fn call_return(
    cv: &ValueRef,
    arg_contracts: &[Contract],
    has_spread: bool,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Contract {
    // An active hypothesis applies only to the **same instance over a containing input
    // domain** (§6 / C§13.2 domain-indexed facts) — never by shape alone.
    if let Some(c) = induction::hypothesis_for(cv, arg_contracts, interner) {
        return c;
    }
    if cv.as_fn().is_none() || has_spread || induction::currently_inferring() {
        return Contract::Top;
    }
    if let Some(c) = induction::infer_return_fact(cv, Some(arg_contracts), cenv, interner) {
        return c;
    }
    // Coverage through the derived domain (C§13.3(1) "derived grounding contracts",
    // the resolution-by-coverage rule applied to the return question): a concrete
    // start's own proposal often dies on the shape cutoff, but the recursion's derived
    // orbit envelope contains the start, and the return over a containing domain
    // contains the return over the covered one — so the envelope's fact answers,
    // soundly over-approximate. `countDown(5)` and the grid-§6 zone calls resolve here.
    if let [single] = arg_contracts
        && let Some(envelope) = grounding::derived_orbit_domain(cv, single, cenv, interner)
        && matches!(
            crate::contract::subcontract(single, &envelope, interner),
            crate::contract::Verdict::Proven
        )
        && let Some(c) = induction::infer_return_fact(cv, Some(&[envelope]), cenv, interner)
    {
        return c;
    }
    // A closure-converted local keeps its outer environment positions unchanged and
    // derives an orbit only for the recursive argument. The resulting vector is the
    // ordinary containing fact domain; no symbolic captured value is involved.
    if arg_contracts.len() >= 2
        && let Some(envelope) =
            grounding::carried_numeric_orbit_domain(cv, arg_contracts, cenv, interner)
        && let Some(c) = induction::infer_return_fact(cv, Some(&envelope), cenv, interner)
    {
        return c;
    }
    // The multi-parameter form, through the lex envelope (Ackermann's shape).
    if arg_contracts.len() >= 2
        && let Some(envelope) = grounding::lex_envelope(cv, interner)
        && arg_contracts.len() == envelope.len()
        && arg_contracts.iter().zip(&envelope).all(|(a, e)| {
            matches!(
                crate::contract::subcontract(a, e, interner),
                crate::contract::Verdict::Proven
            )
        })
        && let Some(c) = induction::infer_return_fact(cv, Some(&envelope), cenv, interner)
    {
        return c;
    }
    Contract::Top
}

/// Check a known callee's act-kind (world admission) and argument obligation, pushing
/// any findings. Completion is handled separately ([`callee_completion`]).
fn analyze_known_callee(
    cv: &ValueRef,
    arg_contracts: &[Contract],
    has_spread: bool,
    world: World,
    findings: &mut Vec<Finding>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) {
    let admit = |kind: ActKind, findings: &mut Vec<Finding>| {
        if !world.admits(kind) {
            findings.push(Finding {
                class: TrapClass::WorldAdmission,
                severity: Severity::Error,
                message: format!("a {kind:?} call is not admitted in {world:?} world"),
            });
        }
    };

    if let Some(closure) = cv.as_closure() {
        admit(closure.lambda.act_kind, findings);
        // Argument obligation: the argument tuple must match the parameter pattern.
        if !has_spread {
            let arg_tuple = Contract::tuple(arg_contracts.to_vec(), interner);
            let params = pattern_contract(&closure.lambda.params, cenv, interner);
            if matches!(subcontract(&arg_tuple, &params, interner), Verdict::Proven) {
                // obligation met
            } else if disjoint(&arg_tuple, &params) {
                findings.push(Finding {
                    class: TrapClass::ArgumentObligation,
                    severity: Severity::Error,
                    message: "arguments cannot match the parameter pattern".into(),
                });
            } else {
                findings.push(Finding {
                    class: TrapClass::ArgumentObligation,
                    severity: Severity::Error,
                    message: "cannot prove the arguments match the parameter pattern".into(),
                });
            }
        }
        return;
    }
    if let Some(native) = cv.as_native() {
        admit(native.get().act_kind, findings);
    }
}

/// A spread must evaluate to the expected kind — Tuple for argument/tuple spreads
/// (E3/E5), Record for record spreads — else the spread-kind trap.
fn check_spread_kind(
    c: &Contract,
    expected: Kind,
    what: &str,
    findings: &mut Vec<Finding>,
    interner: &mut Interner,
) {
    let want = Contract::Kind(expected);
    if matches!(subcontract(c, &want, interner), Verdict::Proven) {
        return;
    }
    if disjoint(c, &want) {
        findings.push(Finding {
            class: TrapClass::SpreadKind,
            severity: Severity::Error,
            message: what.into(),
        });
    } else {
        findings.push(Finding {
            class: TrapClass::SpreadKind,
            severity: Severity::Error,
            message: format!("cannot prove this spread is a {expected:?}"),
        });
    }
}

/// The computed-key obligation (E5). Runtime face: a non-String key traps
/// `computed-key`. Analyzer face (fork 12 = R; A-VER): the key must be a
/// **proven-finite string set** — `Kind(String)` alone REJECTs. The finiteness
/// rejection is a *domain demand*, not a trap prediction: a `Kind(String)` key
/// never traps, but the record's shape would be unanalyzable.
fn check_computed_key(c: &Contract, findings: &mut Vec<Finding>) {
    if disjoint(c, &Contract::Kind(Kind::String)) {
        findings.push(Finding {
            class: TrapClass::ComputedKey,
            severity: Severity::Error,
            message: "computed record key is not a String".into(),
        });
        return;
    }
    if finite_string_set(c) {
        return;
    }
    findings.push(Finding {
        class: TrapClass::ComputedKey,
        severity: Severity::Error,
        message: "computed keys demand a proven-finite string set (E5)".into(),
    });
}

/// A contract denoting a provably **finite set of Strings**.
fn finite_string_set(c: &Contract) -> bool {
    match c {
        Contract::Bottom => true,
        Contract::Equals(v) => v.as_str_units().is_some(),
        Contract::Union(a, b) => finite_string_set(a) && finite_string_set(b),
        _ => false,
    }
}

// ── Match (E9/E10) — the sole control node ────────────────────────────────────

/// Analyze a `Match`. Each `Arm` narrows the scrutinee by its pattern (the arm
/// body sees `scrutinee ∩ pattern`), and the remainder for later items is the
/// accumulated Difference (E9). Guards are strict tested seats (`tested-seat`),
/// destructuring `Bind`s must be irrefutable (`refuted-binding`), and every
/// value-demanding sub-position is an expecting seat. The result contract is the
/// union of the arm results; a `Match` whose remainder is not provably empty
/// `may_complete` without a value.
fn analyze_match(
    m: &crate::ast::Match,
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    use crate::ast::MatchItem;

    let mut findings = Vec::new();
    let mut safety_demands = Vec::new();

    // The scrutinee is evaluated once, in an expecting seat.
    let (mut scrut, scrut_annotated, scrut_image) = match &m.scrutinee {
        Some(e) => {
            let mut a = analyze_in_world(e, env, cenv, world, interner);
            demand(&a, &mut findings);
            let triple = (a.contract.clone(), a.annotated.clone(), a.image.clone());
            findings.append(&mut a.findings);
            safety_demands.append(&mut a.safety_demands);
            triple
        }
        None => (
            Contract::Top,
            AnalysisContract::of_contract(Contract::Top),
            None,
        ),
    };

    // **Force the held image, here and nowhere else** (DR-17). Routing is the judgment
    // that needs exact branch values; a *result* demand never does (DR-09), so the
    // image stayed unevaluated until this point. Forcing yields a subset of the coarse
    // contract, so every arm this match would have selected coarsely it still selects
    // — the walk can only get sharper, never differently-shaped.
    //
    // Forced unconditionally rather than only on failure: the exact contract is what
    // the arms are walked against, so deciding "did the coarse walk fail?" first would
    // mean walking twice. One node, one walk.
    let routing_operand = scrut_image
        // A finite multi-point scrutinee with no earlier provenance becomes a fresh
        // source at this routing match (BR-02).
        .or_else(|| domain::ImageOperand::source(&scrut));
    let mut branch_remainder = routing_operand
        .as_ref()
        .and_then(|operand| operand.force(interner));
    if let Some(exact) = branch_remainder
        .as_ref()
        .and_then(|branches| branches.contract(interner))
    {
        scrut = exact;
    }

    // `body_env` accumulates Bind / Stmt bindings; each item runs against it.
    let mut body_env = env.clone();
    // **Named block bindings are late-bound siblings** — the same law the module
    // pre-pass and the canonicalizer already apply, now applied here. Without it a
    // locally-bound recursive function has *itself* free while its own initializer is
    // analyzed, no closure value can be built, and every call to it resolves as
    // "not a known function" — so `fib = (n) => { go = (k) => … go(k - 1) …; go(n) }`
    // is rejected outright and its termination is never adjudicated at all.
    prebind_sibling_lambdas(m, &mut body_env, interner);
    let mut remainder = scrut.clone();
    let mut results: Vec<Contract> = Vec::new();
    let mut annotated_results: Vec<AnalysisContract> = Vec::new();
    let mut routed_results = branch_remainder
        .as_ref()
        .map(|_| domain::BranchSet::empty());
    let mut completions: Vec<Completion> = Vec::new();
    // Any guarded arm makes the remainder an *over*-approximation (a guard, not the
    // pattern, decides, and guards consume nothing) — so an inhabited remainder no
    // longer *proves* a fall-through: at most `MayFallThrough`.
    let mut any_guarded = false;

    for item in &m.items {
        match item {
            MatchItem::Bind(b) => {
                // `prebind_sibling_lambdas` already installed the analyzer-only call
                // adapter. Evaluating the source lambda would eagerly manufacture a
                // contract-level closure from captures that are not values — exactly
                // the phase error this path avoids. Runtime formation remains a no-body
                // operation when this Bind is actually executed.
                if let crate::ast::BindTarget::Name(name) = &b.target
                    && matches!(&b.value, Expr::Lambda(_))
                    && body_env.deferred_call(name).is_some()
                {
                    continue;
                }
                let mut a = analyze_in_world(&b.value, &body_env, cenv, world, interner);
                demand(&a, &mut findings); // a bind RHS is an expecting seat
                findings.append(&mut a.findings);
                safety_demands.append(&mut a.safety_demands);
                analyze_bind(
                    &b.target,
                    &a.annotated,
                    a.image.clone(),
                    &mut body_env,
                    &mut findings,
                    cenv,
                    interner,
                );
            }
            MatchItem::Stmt(e) => {
                // A statement's value is discarded — *not* an expecting seat.
                let mut a = analyze_in_world(e, &body_env, cenv, world, interner);
                findings.append(&mut a.findings);
                safety_demands.append(&mut a.safety_demands);
            }
            MatchItem::Arm(arm) => {
                let pc = arm
                    .pattern
                    .as_ref()
                    .map(|p| pattern_contract(p, cenv, interner))
                    .unwrap_or(Contract::Top);
                let narrowed = intersect(&remainder, &pc, interner);
                let narrowed_annotated = domain::intersect_a(
                    &scrut_annotated,
                    &AnalysisContract::of_contract(narrowed.clone()),
                    interner,
                );

                // **Dead arm** (Archive7 §11.3): its scrutinee region is already empty —
                // a prior total arm consumed the remainder, or the pattern is disjoint
                // from what remains — so it can never be selected. Skip it entirely: an
                // unreachable branch contributes no findings, no result, no consumption.
                if matches!(
                    subcontract(&narrowed, &Contract::Bottom, interner),
                    Verdict::Proven
                ) {
                    continue;
                }

                let arrivals = branch_remainder
                    .as_ref()
                    .map(|branches| branches.restricted(&pc));

                // Arm-local environment: the outer bindings plus the pattern's.
                let mut arm_env = body_env.clone();
                if let Some(arrivals) = &arrivals {
                    arm_env.narrow_to(arrivals, interner);
                }
                if let Some(p) = &arm.pattern {
                    bind_pattern_annotated(p, &narrowed_annotated, &mut arm_env, interner);
                    if let crate::ast::Pat::Bind(name) = p
                        && let Some(arrivals) = &arrivals
                        && let Some(annotated) = arm_env.get(name).cloned()
                    {
                        arm_env.insert_with_image(
                            name.clone(),
                            annotated,
                            Some(domain::ImageOperand::Branches(std::rc::Rc::new(
                                arrivals.clone(),
                            ))),
                        );
                    }
                }

                // Guard: a strict Boolean tested seat. A guard **proven false** makes the
                // arm dead (skip its result); a guard **proven true** fires on the whole
                // region like an unguarded arm (so it consumes, emptying the remainder,
                // and does not muddy the fall-through classification); only a genuinely
                // *opaque* guard consumes nothing (uncertainty selects, E9).
                let mut opaque_guard = false;
                let mut guard_consumption: Option<(String, Contract)> = None;
                if let Some(g) = &arm.guard {
                    let mut ga = analyze_in_world(g, &arm_env, cenv, world, interner);
                    demand(&ga, &mut findings);
                    findings.append(&mut ga.findings);
                    safety_demands.append(&mut ga.safety_demands);
                    check_tested_seat(&ga.contract, &mut findings, interner);
                    let t = Contract::Equals(interner.boolean(true));
                    let f = Contract::Equals(interner.boolean(false));
                    if matches!(subcontract(&ga.contract, &f, interner), Verdict::Proven) {
                        continue; // guard can never hold — dead arm
                    }
                    opaque_guard =
                        !matches!(subcontract(&ga.contract, &t, interner), Verdict::Proven);
                    any_guarded |= opaque_guard;

                    // E-4/E9's remainder law, applied to the live environments: a guard
                    // that regionalizes on exactly one in-scope variable narrows that
                    // variable **inside the arm** (the guard held on this path), and an
                    // **exact** guard region is consumed from the variable for the items
                    // after the arm — the same reading the region table performs per row
                    // (`regionalize_guard`), which is what keeps a *nested* tested match
                    // narrowing (`n == 0 ? … : … n - 1 …` inside another arm).
                    if let Some((var, region, exact)) =
                        single_var_guard_region(g, &arm_env, interner)
                    {
                        if let Some(prior) = arm_env.get(&var) {
                            let tightened = domain::intersect_a(
                                prior,
                                &AnalysisContract::of_contract(region.clone()),
                                interner,
                            );
                            arm_env.insert(var.clone(), tightened);
                        }
                        // Consumption is sound only when the arm cannot decline for a
                        // reason other than the guard: a pattern may reject a value the
                        // guard admits, leaving it for later arms.
                        if exact && arm.pattern.is_none() {
                            guard_consumption = Some((var, region));
                        }
                    }
                }

                // The arm exits the Match with its result's whole outcome. The result
                // is demanded only if the enclosing Match's consumer is expecting;
                // demanding here would falsely reject the same Match in a statement
                // seat (E10 / compendium 1.0.8).
                let mut ra = analyze_in_world(&arm.result, &arm_env, cenv, world, interner);
                findings.append(&mut ra.findings);
                safety_demands.append(&mut ra.safety_demands);
                if opaque_guard {
                    // An opaque guard does not determine which source cells actually
                    // leave through this arm. Keep the ordinary over-approximation and
                    // decline to mint an exact branch relation.
                    routed_results = None;
                } else if let (Some(arrivals), Some(accumulated)) =
                    (&arrivals, routed_results.as_mut())
                {
                    let produced = ra
                        .image
                        .as_ref()
                        .and_then(|image| image.force(interner))
                        .or_else(|| domain::BranchSet::singleton(&ra.contract));
                    match produced {
                        Some(produced) => {
                            accumulated.append(arrivals.join_arrivals(&produced));
                        }
                        None => routed_results = None,
                    }
                }
                results.push(ra.contract);
                annotated_results.push(ra.annotated);
                let arm_is_represented = !opaque_guard && narrowed.has_proven_inhabitant(interner);
                completions.push(if arm_is_represented {
                    ra.completion
                } else {
                    weaken_completion(ra.completion)
                });

                // A non-opaque arm (unguarded or proven-true guard) consumes its whole
                // pattern region — emptying the remainder when the pattern covers all of
                // it (e.g. `_` / a bare binding).
                if !opaque_guard {
                    remainder = if matches!(subcontract(&remainder, &pc, interner), Verdict::Proven)
                    {
                        Contract::Bottom
                    } else {
                        difference(&remainder, &pc, interner)
                    };
                    if let Some(branches) = &branch_remainder {
                        branch_remainder = Some(branches.without(&pc));
                    }
                }
                // An exact guard region is consumed from its variable for later items
                // (E9: an exact row consumes; the accumulated Difference is what the
                // next arm's environment sees).
                if let Some((var, region)) = guard_consumption
                    && let Some(prior) = body_env.get(&var)
                {
                    let rest = difference(&prior.erase(interner), &region, interner);
                    body_env.insert(var, AnalysisContract::of_contract(rest));
                }
            }
        }
    }

    let contract = union_of(results, interner);
    let annotated = if annotated_results.is_empty() {
        AnalysisContract::of_contract(contract.clone())
    } else {
        AnalysisContract::alt(annotated_results)
    };
    completions.push(classify_remainder(
        &remainder,
        any_guarded,
        m.scrutinee.is_some(),
        interner,
    ));
    Analysis {
        contract,
        annotated,
        image: routed_results.and_then(|branches| {
            (!branches.cells().is_empty())
                .then(|| domain::ImageOperand::Branches(std::rc::Rc::new(branches)))
        }),
        findings,
        safety_demands,
        completion: join_completions(&completions),
    }
}

/// A guard's region on the **one** in-scope variable it constrains — the region
/// table's own reading (`region::regionalize_guard`) lifted to the expression layer.
/// `None` when the guard constrains no bound variable, or more than one (a
/// two-variable guard is relational — [permanent] — and concludes nothing here).
pub(crate) fn single_var_guard_region(
    g: &Expr,
    env: &TypeEnv,
    interner: &mut Interner,
) -> Option<(String, Contract, bool)> {
    let mut names = Vec::new();
    collect_ref_names(g, &mut names);
    names.sort();
    names.dedup();
    let mut hit: Option<(String, Contract, bool)> = None;
    for name in names {
        if env.get(&name).is_none() {
            continue;
        }
        let (region, exact) = region::regionalize_guard(g, &name, interner);
        if matches!(region, Contract::Top) {
            continue;
        }
        if hit.is_some() {
            return None; // constrains two variables — relational, no conclusion
        }
        hit = Some((name, region, exact));
    }
    hit
}

/// The reference names a guard expression mentions (best-effort walk over the guard
/// shapes `regionalize_guard` reads; unvisited forms only cost narrowing, never
/// soundness).
fn collect_ref_names(e: &Expr, out: &mut Vec<String>) {
    use crate::ast::{Arg, MatchItem, TemplatePart};
    match e {
        Expr::Ref(crate::ast::Ref::Immutable(crate::ast::BindingRef::Name(n))) => {
            out.push(n.clone())
        }
        Expr::Ref(_) => {}
        Expr::Const(_) | Expr::Lambda(_) => {}
        Expr::PrimOp { args, .. } => {
            for a in args {
                collect_ref_names(a, out);
            }
        }
        Expr::Apply { callee, args } => {
            collect_ref_names(callee, out);
            for a in args {
                let (Arg::Expr(x) | Arg::Spread(x)) = a;
                collect_ref_names(x, out);
            }
        }
        Expr::Match(m) => {
            if let Some(s) = &m.scrutinee {
                collect_ref_names(s, out);
            }
            for item in &m.items {
                match item {
                    MatchItem::Bind(b) => collect_ref_names(&b.value, out),
                    MatchItem::Stmt(x) => collect_ref_names(x, out),
                    MatchItem::Arm(arm) => {
                        if let Some(g) = &arm.guard {
                            collect_ref_names(g, out);
                        }
                        collect_ref_names(&arm.result, out);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    collect_ref_names(x, out);
                }
            }
        }
        Expr::Access { target, .. } => collect_ref_names(target, out),
        Expr::TupleCons(_) | Expr::RecordCons(_) | Expr::Write { .. } => {}
    }
}

/// Classify a `Match`'s completion (E10) from its uncovered `remainder` (three-voiced):
/// - **proven empty** → `Produces` (exhaustive — no scrutinee value escapes every arm);
/// - **proven inhabited** by a sampled witness, and **no guarded arm** muddied the
///   remainder → `FallsThrough` (that witness is a represented input that falls
///   through — a real expecting-seat trap);
/// - otherwise (not proven empty, no witness, or guards present) → `MayFallThrough`.
fn classify_remainder(
    remainder: &Contract,
    any_guarded: bool,
    has_scrutinee: bool,
    interner: &mut Interner,
) -> Completion {
    if matches!(
        subcontract(remainder, &Contract::Bottom, interner),
        Verdict::Proven
    ) {
        return Completion::Produces;
    }
    if !any_guarded && let Some(witness) = remainder.proven_members(interner).into_iter().next() {
        return Completion::FallsThrough(CompletionWitness::MatchRemainder {
            scrutinee: has_scrutinee.then_some(witness),
        });
    }
    Completion::MayFallThrough
}

/// A branch whose selection is not itself represented may contribute possibility,
/// but never export another operation's refutation witness as though the branch were
/// known reachable (AP-30's joint-membership discipline).
fn weaken_completion(completion: Completion) -> Completion {
    match completion {
        Completion::Produces => Completion::Produces,
        Completion::MayFallThrough | Completion::FallsThrough(_) => Completion::MayFallThrough,
    }
}

/// The contract of values a pattern matches — a **superset** of the true match set
/// (sound for narrowing by intersection).
pub(crate) fn pattern_contract(
    pat: &crate::ast::Pat,
    cenv: &ContractEnv,
    i: &mut Interner,
) -> Contract {
    use crate::ast::{Pat, PatElem, PatField};
    match pat {
        Pat::Const(v) => Contract::Equals(v.clone()),
        Pat::Wild | Pat::Bind(_) => Contract::Top,
        Pat::Tuple(elems) => {
            // An exact positional tuple (no rest) is a precise Tuple contract;
            // a rest widens to any Tuple (length reasoning is C§17 owed).
            if elems.iter().any(|e| matches!(e, PatElem::Rest(_))) {
                Contract::Kind(Kind::Tuple)
            } else {
                let parts: Vec<Contract> = elems
                    .iter()
                    .map(|e| match e {
                        PatElem::Pat(p) => pattern_contract(p, cenv, i),
                        PatElem::Rest(_) => unreachable!(),
                    })
                    .collect();
                Contract::tuple(parts, i)
            }
        }
        Pat::Record { fields, exact } => {
            let named: Vec<&PatField> = fields
                .iter()
                .filter(|f| matches!(f, PatField::Field { .. }))
                .collect();
            let has_rest = fields.iter().any(|f| matches!(f, PatField::Rest(_)));
            if *exact && !has_rest {
                let pairs: Vec<(String, Contract)> = named
                    .iter()
                    .map(|f| match f {
                        PatField::Field { key, pat } => {
                            (key.clone(), pattern_contract(pat, cenv, i))
                        }
                        PatField::Rest(_) => unreachable!(),
                    })
                    .collect();
                Contract::record(pairs, i)
            } else {
                // Open record: "has at least these fields."
                named
                    .iter()
                    .filter_map(|f| match f {
                        PatField::Field { key, .. } => Some(Contract::HasField(key.clone())),
                        PatField::Rest(_) => None,
                    })
                    .reduce(|a, b| intersect(&a, &b, i))
                    .unwrap_or(Contract::Kind(Kind::Record))
            }
        }
        Pat::Contract(r) => contract_ref(r, cenv, i).unwrap_or(Contract::Top),
    }
}

/// Resolve a contract-as-pattern reference (E9). Prelude Kind names, `Top`,
/// `Bottom` and `Failure` resolve structurally; any other name resolves against the
/// **named-contract environment** (C§12.2 — `Percent = Range(0, 100)`). An
/// unresolvable name yields `None`, which the caller widens to `Top` (no
/// narrowing). Resolution is shared with the contract-expression evaluator so
/// patterns and contract expressions agree by construction.
fn contract_ref(r: &Ref, cenv: &ContractEnv, i: &mut Interner) -> Option<Contract> {
    eval_contract(&Expr::Ref(r.clone()), cenv, i)
}

/// Bind a pattern's names to their narrowed contracts in `env` (best-effort; a
/// name whose position is not tracked binds to `Top`).
pub(crate) fn bind_pattern(
    pat: &crate::ast::Pat,
    narrowed: &Contract,
    env: &mut TypeEnv,
    interner: &mut Interner,
) {
    use crate::ast::{Pat, PatElem, PatField};
    match (pat, narrowed) {
        (Pat::Bind(name), contract) => {
            let annotated = AnalysisContract::of_contract(contract.clone());
            let image = domain::ImageOperand::source(contract);
            env.insert_with_image(name.clone(), annotated, image);
        }
        (Pat::Tuple(patterns), Contract::Tuple(contracts)) => {
            for (position, element) in patterns.iter().enumerate() {
                if let PatElem::Pat(pattern) = element {
                    let contract = contracts
                        .get(position)
                        .map(|contract| &**contract)
                        .unwrap_or(&Contract::Top);
                    bind_pattern(pattern, contract, env, interner);
                }
            }
        }
        (Pat::Record { fields, .. }, Contract::Record(contracts)) => {
            for field in fields {
                if let PatField::Field { key, pat } = field {
                    let contract = contracts
                        .iter()
                        .find(|(candidate, _)| candidate == key)
                        .map(|(_, contract)| &**contract)
                        .unwrap_or(&Contract::Top);
                    bind_pattern(pat, contract, env, interner);
                }
            }
        }
        _ => bind_pattern_annotated(
            pat,
            &AnalysisContract::of_contract(narrowed.clone()),
            env,
            interner,
        ),
    }
}

/// Annotated pattern binding. Structural tuple/record positions and correlated
/// alternatives survive into the bound names; an untracked position widens to Top.
pub(crate) fn bind_pattern_annotated(
    pat: &crate::ast::Pat,
    narrowed: &AnalysisContract,
    env: &mut TypeEnv,
    interner: &mut Interner,
) {
    use crate::ast::{Pat, PatElem, PatField};
    match pat {
        Pat::Bind(name) => {
            env.insert(name.clone(), narrowed.clone());
        }
        Pat::Tuple(elems) => {
            for (pos, e) in elems.iter().enumerate() {
                if let PatElem::Pat(p) = e {
                    let sub = narrowed
                        .project_index(pos, interner)
                        .unwrap_or_else(|| AnalysisContract::of_contract(Contract::Top));
                    bind_pattern_annotated(p, &sub, env, interner);
                }
            }
        }
        Pat::Record { fields, .. } => {
            for f in fields {
                if let PatField::Field { key, pat } = f {
                    let sub = narrowed
                        .project_field(key, interner)
                        .unwrap_or_else(|| AnalysisContract::of_contract(Contract::Top));
                    bind_pattern_annotated(pat, &sub, env, interner);
                }
            }
        }
        // Const / Wild / Contract bind no names.
        _ => {}
    }
}

/// A destructuring `Bind` must be irrefutable (E9): its pattern always matches the
/// value. A `Name` target always binds.
fn analyze_bind(
    target: &crate::ast::BindTarget,
    value: &AnalysisContract,
    image: Option<domain::ImageOperand>,
    env: &mut TypeEnv,
    findings: &mut Vec<Finding>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) {
    use crate::ast::BindTarget;
    let erased = value.erase(interner);
    match target {
        BindTarget::Name(name) => {
            let image = image.or_else(|| domain::ImageOperand::source_annotated(value));
            env.insert_with_image(name.clone(), value.clone(), image);
        }
        BindTarget::Pattern(p) => {
            let pc = pattern_contract(p, cenv, interner);
            if matches!(subcontract(&erased, &pc, interner), Verdict::Proven) {
                // Irrefutable — always matches.
            } else if disjoint(&erased, &pc) {
                findings.push(Finding {
                    class: TrapClass::RefutedBinding,
                    severity: Severity::Error,
                    message: "destructuring binding never matches its value".into(),
                });
            } else {
                findings.push(Finding {
                    class: TrapClass::RefutedBinding,
                    severity: Severity::Error,
                    message: "cannot prove this destructuring binding irrefutable".into(),
                });
            }
            let narrowed = domain::intersect_a(value, &AnalysisContract::of_contract(pc), interner);
            bind_pattern_annotated(p, &narrowed, env, interner);
        }
    }
}

/// A guard occupies a strict tested seat (E10): it must be a Boolean.
pub(crate) fn check_tested_seat(
    guard: &Contract,
    findings: &mut Vec<Finding>,
    interner: &mut Interner,
) {
    let boolean = Contract::Kind(Kind::Boolean);
    if matches!(subcontract(guard, &boolean, interner), Verdict::Proven) {
        return;
    }
    if disjoint(guard, &boolean) {
        findings.push(Finding {
            class: TrapClass::TestedSeat,
            severity: Severity::Error,
            message: "a guard must be a strict Boolean".into(),
        });
    } else {
        findings.push(Finding {
            class: TrapClass::TestedSeat,
            severity: Severity::Error,
            message: "cannot prove this guard is a Boolean".into(),
        });
    }
}

/// Adapter for the canonical simplifying conjunction (Tier-4: one implementation;
/// the elementwise tuple rule lives there now).
fn intersect(a: &Contract, b: &Contract, i: &mut Interner) -> Contract {
    Contract::intersect(a.clone(), b.clone(), i)
}

fn difference(a: &Contract, b: &Contract, i: &mut Interner) -> Contract {
    Contract::difference(a.clone(), b.clone(), i)
}

pub(crate) fn union_of(mut contracts: Vec<Contract>, i: &mut Interner) -> Contract {
    match contracts.len() {
        0 => Contract::Top, // a Match with no arms only ever completes-without-value
        1 => contracts.pop().unwrap(),
        _ => contracts
            .into_iter()
            .reduce(|a, b| Contract::union(a, b, i))
            .unwrap(),
    }
}
