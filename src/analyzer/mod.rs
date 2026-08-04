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
/// at the expression layer): the seat demand's compile-time face.
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
#[derive(Clone, Debug, Default)]
pub struct TypeEnv(HashMap<String, AnalysisContract>);

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv(HashMap::new())
    }

    pub fn insert(
        &mut self,
        name: String,
        value: impl Into<AnalysisContract>,
    ) -> Option<AnalysisContract> {
        self.0.insert(name, value.into())
    }

    pub fn get(&self, name: &str) -> Option<&AnalysisContract> {
        self.0.get(name)
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
        Expr::Const(v) => {
            Analysis::produced_annotated(AnalysisContract::of_value(v.clone()), vec![], interner)
        }

        // An immutable reference takes its bound contract; an unbound name is the
        // unbound-evaluation trap's compile-time mirror.
        Expr::Ref(Ref::Immutable(BindingRef::Name(name))) => match env.get(name) {
            Some(c) => Analysis::produced_annotated(c.clone(), vec![], interner),
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
        // canonical) — and the produced contract is the exact function value, so a
        // factory's product arrives at its call sites as a known instance. Any
        // non-singleton capture keeps the coarse `Kind(Function)` (the annotated
        // instance-metadata union is the owed general form).
        Expr::Lambda(l) => analyze_lambda(l, env, interner),
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
            None => return exact(Contract::Kind(Kind::Function)),
        }
    }
    let scope = crate::env::Scope::root();
    for (name, v) in captures {
        scope.define(&name, crate::env::Binding::Value(v));
    }
    let value = crate::oracle::make_closure_in(l, &scope, interner);
    Analysis::produced_annotated(AnalysisContract::of_value(value), vec![], interner)
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
    for a in args {
        let mut r = analyze_in_world(a, env, cenv, world, interner);
        demand(&r, &mut findings); // operands are expecting seats
        findings.append(&mut r.findings);
        safety_demands.append(&mut r.safety_demands);
        inputs.push(r.contract);
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
    let singletons: Option<Vec<ValueRef>> = inputs
        .iter()
        .map(|c| match c {
            Contract::Equals(v) => Some(v.clone()),
            _ => None,
        })
        .collect();

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

    Analysis::produced_with_safety(contract, findings, safety_demands)
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
/// exact verdict. Field access is fully reasoned on open receivers; index/slice
/// *bounds* reasoning needs the tuple-length family (**C§17 owed**, see
/// `OwedItems.md`), so open index/slice out-of-fold cases are warnings.
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
                AnalysisContract::of_value(v),
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
        AccessForm::Field(name) => target_annotated.project_field(name),
        AccessForm::Index(_) => idx_c
            .as_ref()
            .and_then(singleton_index)
            .and_then(|index| target_annotated.project_index(index)),
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
        AccessForm::Slice { .. } => analyze_slice(&tc, &mut findings, interner),
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

fn analyze_slice(tc: &Contract, findings: &mut Vec<Finding>, interner: &mut Interner) -> Contract {
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
    let operand = correlated_access_operand(callee, args, env).unwrap_or_else(|| {
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
        findings,
        safety_demands,
        completion: completion_from_application(transfer.outcome.completion),
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
                AccessProjection::Index(index) => alternative.project_index(*index),
                AccessProjection::Field(name) => alternative.project_field(name),
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

    // A recursive reference covered by an active safety fact resolves through that
    // fact; acyclic dependencies retain their exact body outcome.
    if !has_spread && induction::safety_assumed(callee, arg_contracts, interner) {
        safety_demands.push(SafetyDemand::Body(BodySafetyDemand {
            callee: callee.clone(),
            arguments: arg_contracts.to_vec(),
            verdict: safety::BodySafety::Proven,
        }));
        if induction::is_recursive(callee) {
            let produced = call_return(callee, arg_contracts, has_spread, cenv, interner);
            let completes = induction::completes_assumed(callee, arg_contracts, interner)
                || safety::completes(callee, arg_contracts, cenv, interner);
            let completion = callee_completion(callee, arg_contracts, completes, interner);
            return application_contribution(findings, safety_demands, produced, completion);
        }
        let observed = outcome::analyze_instance_body(callee, arg_contracts, cenv, interner)
            .expect("a known closure has a body outcome");
        let completes = matches!(&observed.completion, Completion::Produces);
        let completion = callee_completion(callee, arg_contracts, completes, interner);
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
        let produced = if induction::is_recursive(callee) {
            call_return(callee, arg_contracts, has_spread, cenv, interner)
        } else {
            Contract::Top
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
        let produced = if induction::is_recursive(callee) {
            call_return(callee, arg_contracts, has_spread, cenv, interner)
        } else {
            Contract::Top
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
            findings: Vec::new(),
            safety_demands: Vec::new(),
            completion: Completion::MayFallThrough,
        });
    let completes = safety::completes(callee, arg_contracts, cenv, interner);
    let completion = callee_completion(callee, arg_contracts, completes, interner);
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
    let completion = match completion {
        Completion::Produces => CompletionWithoutValue::ProvenAbsent,
        Completion::FallsThrough(CompletionWitness::Application(witness)) => {
            CompletionWithoutValue::ProvenPresent(witness)
        }
        Completion::MayFallThrough | Completion::FallsThrough(_) => {
            CompletionWithoutValue::UnprovenPossible
        }
    };
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
    // AP-30 promotes the third voice only when the bounded oracle realizes one
    // represented `(callee, arguments)` execution that completes without a value.
    refute::realized_completion(cv, args, interner).map_or(Completion::MayFallThrough, |witness| {
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
    let (scrut, scrut_annotated) = match &m.scrutinee {
        Some(e) => {
            let mut a = analyze_in_world(e, env, cenv, world, interner);
            demand(&a, &mut findings);
            let pair = (a.contract.clone(), a.annotated.clone());
            findings.append(&mut a.findings);
            safety_demands.append(&mut a.safety_demands);
            pair
        }
        None => (Contract::Top, AnalysisContract::of_contract(Contract::Top)),
    };

    // `body_env` accumulates Bind / Stmt bindings; each item runs against it.
    let mut body_env = env.clone();
    let mut remainder = scrut.clone();
    let mut results: Vec<Contract> = Vec::new();
    let mut annotated_results: Vec<AnalysisContract> = Vec::new();
    let mut completions: Vec<Completion> = Vec::new();
    // Any guarded arm makes the remainder an *over*-approximation (a guard, not the
    // pattern, decides, and guards consume nothing) — so an inhabited remainder no
    // longer *proves* a fall-through: at most `MayFallThrough`.
    let mut any_guarded = false;

    for item in &m.items {
        match item {
            MatchItem::Bind(b) => {
                let mut a = analyze_in_world(&b.value, &body_env, cenv, world, interner);
                demand(&a, &mut findings); // a bind RHS is an expecting seat
                findings.append(&mut a.findings);
                safety_demands.append(&mut a.safety_demands);
                analyze_bind(
                    &b.target,
                    &a.annotated,
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

                // Arm-local environment: the outer bindings plus the pattern's.
                let mut arm_env = body_env.clone();
                if let Some(p) = &arm.pattern {
                    bind_pattern_annotated(p, &narrowed_annotated, &mut arm_env);
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
pub(crate) fn bind_pattern(pat: &crate::ast::Pat, narrowed: &Contract, env: &mut TypeEnv) {
    bind_pattern_annotated(pat, &AnalysisContract::of_contract(narrowed.clone()), env);
}

/// Annotated pattern binding. Structural tuple/record positions and correlated
/// alternatives survive into the bound names; an untracked position widens to Top.
fn bind_pattern_annotated(pat: &crate::ast::Pat, narrowed: &AnalysisContract, env: &mut TypeEnv) {
    use crate::ast::{Pat, PatElem, PatField};
    match pat {
        Pat::Bind(name) => {
            env.insert(name.clone(), narrowed.clone());
        }
        Pat::Tuple(elems) => {
            for (pos, e) in elems.iter().enumerate() {
                if let PatElem::Pat(p) = e {
                    let sub = narrowed
                        .project_index(pos)
                        .unwrap_or_else(|| AnalysisContract::of_contract(Contract::Top));
                    bind_pattern_annotated(p, &sub, env);
                }
            }
        }
        Pat::Record { fields, .. } => {
            for f in fields {
                if let PatField::Field { key, pat } = f {
                    let sub = narrowed
                        .project_field(key)
                        .unwrap_or_else(|| AnalysisContract::of_contract(Contract::Top));
                    bind_pattern_annotated(pat, &sub, env);
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
    env: &mut TypeEnv,
    findings: &mut Vec<Finding>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) {
    use crate::ast::BindTarget;
    let erased = value.erase(interner);
    match target {
        BindTarget::Name(name) => {
            env.insert(name.clone(), value.clone());
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
            bind_pattern_annotated(p, &narrowed, env);
        }
    }
}

/// A guard occupies a strict tested seat (E10): it must be a Boolean.
fn check_tested_seat(guard: &Contract, findings: &mut Vec<Finding>, interner: &mut Interner) {
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

fn intersect(a: &Contract, b: &Contract, i: &mut Interner) -> Contract {
    match (a, b) {
        (Contract::Top, x) | (x, Contract::Top) => x.clone(),
        // Elementwise on matching tuples, so narrowing reaches sub-patterns.
        (Contract::Tuple(pa), Contract::Tuple(pb)) if pa.len() == pb.len() => {
            let elems: Vec<Contract> = pa.iter().zip(pb).map(|(x, y)| intersect(x, y, i)).collect();
            Contract::tuple(elems, i)
        }
        _ => Contract::intersection(a.clone(), b.clone(), i),
    }
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
