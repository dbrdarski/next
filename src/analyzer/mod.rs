//! The analyzer — contract inference over the kernel AST, and the compile-time
//! face of the oracle's traps (§6 trap↔compile-error concordance).
//!
//! Per Part I this layer is legitimate only now that the oracle, the
//! normalization harness, and the contract algebra (C.1–C.3, C§9) are green. The
//! analyzer walks an [`Expr`], infers a [`Contract`] over-approximating the value
//! it produces, and at each operation site discharges the operation's safety
//! demand ([`analyze_operation`]) — emitting a [`Finding`] for anything that
//! **will** trap or that it **cannot prove** safe. Both reject after typed safety
//! verdicts reach their consuming seat; warnings remain advisory evidence and carry
//! non-safety third voices such as completion that may fall through.
//! The soundness contract (§6): an expression the analyzer accepts with no error
//! never traps in the oracle.
//!
//! **Scope so far:** `Const`, `Ref`, `PrimOp`, `TupleCons`, `RecordCons`,
//! `Template` (E11), `Access` (E6), `Match` (E9/E10), and `Apply` (C§7/B5/E10).
//! Closed **primitive** operations and **accesses** fold through the finite oracle
//! kernel (`eval_prim` / `eval_expr` on a `Const` target) for an exact verdict; a
//! **closed function call is never executed** — a callee's traps come from the
//! domain-indexed candidate graph (`safety` + `induction`), completion from its settled
//! completion fact, and return from the coarse shape-bounded outcome projection sharpened
//! by return facts. The source seat supplies its actual world; a function body instead owns
//! the world declared by its `ActKind` (B5/E14). Index/slice bounds await C§17 (see
//! `OwedItems.md`). `Write` checks world admission and its right-hand expression; resolving
//! and validating the target slot remains owed.
//!
//! Analysis carries a **named-contract environment** ([`ContractEnv`]) alongside the
//! value-contract [`TypeEnv`]: user contracts (`Percent = Range(0, 100)`, C§12.2)
//! resolve in contract-as-pattern position (E9), so they narrow arms and police
//! destructuring irrefutability exactly as the prelude Kind names do.

use std::collections::HashMap;

use crate::ast::{
    AccessForm, ActKind, Arg, BindingRef, Element, Expr, Field, PrimOp, Ref, SlotRef,
    TemplatePart,
};
use crate::contract::{
    Contract, ContractEnv, Kind, OpSafety, Verdict, analyze_operation, disjoint, eval_contract,
    subcontract,
};
use crate::interner::Interner;
use crate::oracle::{Outcome, TrapClass, World, eval_expr, eval_prim};
use crate::value::ValueRef;

pub mod demand;
pub(crate) mod factcache;
pub mod program;
pub mod application;
pub mod bodywalk;
pub mod domain;
pub mod grounding;
pub mod induction;
pub mod inventory;
pub mod obligation;
pub mod outcome;
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
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Completion {
    /// Every path produces a value (`ProvenAbsent`) — an expecting seat is satisfied.
    Produces,
    /// A fall-through is possible but **not proven reachable** (`UnprovenPossible`) —
    /// an expecting seat is the third voice: a *warning*, never a rejection.
    MayFallThrough,
    /// A fall-through is **proven reachable** (`ProvenPresent`) — a represented input
    /// completes without a value, so an expecting seat is *refuted* (an error).
    FallsThrough,
}

/// The result of analyzing an expression: the inferred contract, any findings
/// gathered from it and its subexpressions, and its completion (E10).
#[derive(Clone, Debug)]
pub struct Analysis {
    pub contract: Contract,
    pub findings: Vec<Finding>,
    pub completion: Completion,
}

impl Analysis {
    /// An expression that always produces a value.
    fn produced(contract: Contract, findings: Vec<Finding>) -> Analysis {
        Analysis { contract, findings, completion: Completion::Produces }
    }

    /// Whether the expression is accepted — no error-level findings.
    pub fn accepted(&self) -> bool {
        self.findings.iter().all(|f| f.severity != Severity::Error)
    }

    /// Whether evaluation may complete without a value (either voice of fall-through).
    pub fn may_complete(&self) -> bool {
        !matches!(self.completion, Completion::Produces)
    }
}

/// An expecting seat (E10) demands `Produced`. The compile-time mirror of the
/// expecting-seat trap is **three-voiced** (E10 / application §1.6): a **proven**
/// fall-through refutes (error); a merely **possible** one is unproven (warning); a
/// guaranteed producer is fine.
fn demand(a: &Analysis, findings: &mut Vec<Finding>) {
    let (severity, message) = match a.completion {
        Completion::Produces => return,
        Completion::FallsThrough => (
            Severity::Error,
            "a value is demanded here, but this expression completes without one on some input",
        ),
        Completion::MayFallThrough => (
            Severity::Warning,
            "a value is demanded here, but this expression cannot be proven to produce one",
        ),
    };
    findings.push(Finding { class: TrapClass::ExpectingSeat, severity, message: message.into() });
}

/// A contract environment: immutable-binding name → its contract.
pub type TypeEnv = HashMap<String, Contract>;

/// Analyze a kernel expression against a contract environment.
pub fn analyze(expr: &Expr, env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
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
        Expr::Const(v) => exact(Contract::Equals(v.clone())),

        // An immutable reference takes its bound contract; an unbound name is the
        // unbound-evaluation trap's compile-time mirror.
        Expr::Ref(Ref::Immutable(BindingRef::Name(name))) => match env.get(name) {
            Some(c) => exact(c.clone()),
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
        Expr::Access { target, form, total } => {
            analyze_access(target, form, *total, env, cenv, world, interner)
        }
        Expr::Match(m) => analyze_match(m, env, cenv, world, interner),
        Expr::Apply { callee, args } => {
            analyze_apply(callee, args, env, cenv, world, interner)
        }
        Expr::Write { slot, value } => analyze_write(slot, value, env, cenv, world, interner),

        // Function construction still lacks its universal interning/contract path.
        Expr::Lambda(_) => exact(Contract::Top),
    }
}

fn exact(contract: Contract) -> Analysis {
    Analysis::produced(contract, vec![])
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
    let mut inputs = Vec::with_capacity(args.len());
    for a in args {
        let mut r = analyze_in_world(a, env, cenv, world, interner);
        demand(&r, &mut findings); // operands are expecting seats
        findings.append(&mut r.findings);
        inputs.push(r.contract);
    }

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
            let result = analyze_operation(op, &inputs, interner);
            match result.safety {
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
                    severity: Severity::Error,
                    message: format!("cannot prove `{op:?}` safe for these operands"),
                }),
            }
            result.output
        }
    };

    Analysis::produced(contract, findings)
}

fn analyze_tuple(
    elems: &[Element],
    env: &TypeEnv,
    cenv: &ContractEnv,
    world: World,
    interner: &mut Interner,
) -> Analysis {
    let mut findings = Vec::new();
    let mut segments: Vec<Contract> = Vec::new();
    let mut run: Vec<Contract> = Vec::new(); // the current spread-free element run
    for el in elems {
        match el {
            Element::Expr(e) => {
                let mut r = analyze_in_world(e, env, cenv, world, interner);
                demand(&r, &mut findings); // elements are expecting seats
                findings.append(&mut r.findings);
                run.push(r.contract);
            }
            // A spread must be a Tuple (E5 — else the spread-kind trap); the
            // result shape is a Concat with the spread's contract as a segment
            // (the tuple family's constructor, §1).
            Element::Spread(e) => {
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
    Analysis::produced(Contract::concat(segments, interner), findings)
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
    let mut pairs = Vec::new();
    let mut exact_shape = true;
    for field in fields {
        match field {
            Field::Field { key, value } => {
                let mut r = analyze_in_world(value, env, cenv, world, interner);
                demand(&r, &mut findings); // field values are expecting seats
                findings.append(&mut r.findings);
                pairs.push((key.clone(), r.contract));
            }
            // A computed key must be a String at runtime (the computed-key trap)
            // and a **proven-finite string set** for the analyzer (E5, fork 12 = R;
            // A-VER: `Kind(String)` REJECTs). Both key and value are expecting seats.
            Field::Computed { key, value } => {
                let mut ka = analyze_in_world(key, env, cenv, world, interner);
                demand(&ka, &mut findings);
                findings.append(&mut ka.findings);
                check_computed_key(&ka.contract, &mut findings);
                let mut va = analyze_in_world(value, env, cenv, world, interner);
                demand(&va, &mut findings);
                findings.append(&mut va.findings);
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
                exact_shape = false;
            }
        }
    }
    let contract = if exact_shape {
        Contract::record(pairs, interner)
    } else {
        Contract::Top
    };
    Analysis::produced(contract, findings)
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
    for part in parts {
        let TemplatePart::Interp(e) = part else {
            continue;
        };
        let mut r = analyze_in_world(e, env, cenv, world, interner);
        demand(&r, &mut findings); // interpolations are expecting seats
        findings.append(&mut r.findings);
    }
    Analysis::produced(Contract::Kind(Kind::String), findings)
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
    let ta = analyze_in_world(target, env, cenv, world, interner);
    demand(&ta, &mut findings); // the receiver is an expecting seat
    findings.extend(ta.findings);
    let tc = ta.contract;

    // Analyze the index/bound subexpressions for their findings and fold values.
    let mut child = |e: &Expr, findings: &mut Vec<Finding>| -> Contract {
        let mut a = analyze_in_world(e, env, cenv, world, interner);
        demand(&a, findings); // index / slice bounds are expecting seats
        findings.append(&mut a.findings);
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
    let folded = match &tc {
        Contract::Equals(tv) => fold_node(tv, form, total, idx_c.as_ref(), lo_c.as_ref(), hi_c.as_ref()),
        _ => None,
    };
    if let Some(node) = folded {
        return match eval_expr(&node, interner) {
            Ok(Outcome::Produced(v)) => Analysis::produced(Contract::Equals(v), findings),
            Ok(Outcome::CompletedWithoutValue) => Analysis::produced(Contract::Top, findings),
            Err(trap) => {
                findings.push(Finding { class: trap.class, severity: Severity::Error, message: trap.message });
                Analysis::produced(Contract::Bottom, findings)
            }
        };
    }

    // Open path.
    let contract = match form {
        AccessForm::Field(name) => analyze_field(&tc, name, total, &mut findings, interner),
        AccessForm::Index(_) => analyze_index(&tc, total, &mut findings, interner),
        AccessForm::Slice { .. } => analyze_slice(&tc, &mut findings, interner),
    };
    Analysis::produced(contract, findings)
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
    let output = field_output(tc, name);
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

/// The contract of field `name` if the receiver is an exact record naming it.
fn field_output(tc: &Contract, name: &str) -> Contract {
    match tc {
        Contract::Record(fields) => fields
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, c)| (**c).clone())
            .unwrap_or(Contract::Top),
        _ => Contract::Top,
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
    if matches!(subcontract(tc, &Contract::Kind(Kind::Null), interner), Verdict::Proven) {
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
    _slot: &SlotRef,
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
        findings,
        completion: Completion::FallsThrough,
    }
}

// ── Apply (C§7 / B5 / E10) — application ──────────────────────────────────────

/// Analyze an application — **without executing the callee** (Archive6 §8/§9). Each
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

    let ca = analyze_in_world(callee, env, cenv, world, interner);
    demand(&ca, &mut findings); // the callee is an expecting seat
    let cc = ca.contract.clone();
    findings.extend(ca.findings);

    let mut arg_contracts: Vec<Contract> = Vec::new();
    let mut has_spread = false;
    for a in args {
        match a {
            Arg::Expr(e) => {
                let aa = analyze_in_world(e, env, cenv, world, interner);
                demand(&aa, &mut findings);
                arg_contracts.push(aa.contract.clone());
                findings.extend(aa.findings);
            }
            Arg::Spread(e) => {
                has_spread = true;
                let aa = analyze_in_world(e, env, cenv, world, interner);
                demand(&aa, &mut findings);
                check_spread_kind(&aa.contract, Kind::Tuple, "argument spread of a non-Tuple", &mut findings, interner);
                findings.extend(aa.findings);
            }
        }
    }

    // Enumerate the **live callee alternatives** (Archive8 §6, totalized Archive9
    // §9–§11) and combine them **conjunctively**: every alternative contributes, so a
    // union callee can neither bypass safety nor be sharpened from its known branch
    // alone. Each known alternative is analyzed over the actual argument domain through
    // its `(instance, input-domain)` body summary.
    let callees = callee_alternatives(&cc, interner);
    let (contract, completion) = if callees.is_empty() {
        (Contract::Top, Completion::Produces) // no live alternative (proven empty)
    } else {
        let mut produced: Vec<Contract> = Vec::new();
        let mut completions: Vec<Completion> = Vec::new();
        for alt in &callees {
            match alt {
                // Not callable. A **represented** inhabitant refutes; an alternative whose
                // inhabitance is unproven stays the third voice (Archive10 §14–§16).
                // Either way it produces no value, so it contributes `Bottom`.
                CalleeAlt::NotAFunction { inhabited } => {
                    let (severity, message) = if *inhabited {
                        (Severity::Error, "callee is not a function")
                    } else {
                        (Severity::Error, "callee may not be a function (no represented inhabitant to confirm)")
                    };
                    findings.push(Finding { class: TrapClass::OperationSafety, severity, message: message.into() });
                    produced.push(Contract::Bottom);
                    completions.push(Completion::Produces);
                }
                // Possibly a function, origin unknown: it may return anything, may fall
                // through, and its body cannot be inspected — conservative throughout,
                // never a sharpening (Archive9 §11).
                CalleeAlt::UnknownFunction => {
                    findings.push(Finding {
                        class: TrapClass::OperationSafety,
                        severity: Severity::Error,
                        message: "cannot prove this callee's body safe (callee not resolved to a known function)".into(),
                    });
                    produced.push(Contract::Top);
                    completions.push(Completion::MayFallThrough);
                }
                CalleeAlt::Known(cv) => {
                    analyze_known_callee(
                        cv,
                        &arg_contracts,
                        has_spread,
                        world,
                        &mut findings,
                        cenv,
                        interner,
                    );
                    // Effect primitives are total-return by the B6 user ruling: host
                    // failure is ordinary `Failure` data, never a trap. Their Rust body
                    // is not analyzer input and must not enter the NEXT body graph.
                    if cv.as_native().is_some() {
                        produced.push(Contract::Top);
                        completions.push(Completion::Produces);
                        continue;
                    }
                    // A recursive reference covered by an **assumed safety fact** resolves
                    // through that fact (C§13.2) — the body is not re-entered, so nothing
                    // accumulates across depths. Acyclic dependencies retain their exact
                    // body outcome (`always() -> Equals(true)`); only recursive returns
                    // need the induction/coarse fallback.
                    if !has_spread && induction::safety_assumed(cv, &arg_contracts, interner) {
                        if induction::is_recursive(cv) {
                            produced.push(call_return(cv, &arg_contracts, has_spread, cenv, interner));
                            // Safety of an expecting use also depends on completion. Read
                            // an active completion hypothesis when one covers the call;
                            // otherwise settle that cross-claim through the same fact graph.
                            let completes = induction::completes_assumed(
                                cv,
                                &arg_contracts,
                                interner,
                            ) || safety::completes(cv, &arg_contracts, cenv, interner);
                            completions.push(if completes {
                                Completion::Produces
                            } else {
                                Completion::MayFallThrough
                            });
                        } else {
                            let observed = outcome::analyze_instance_body(
                                cv,
                                &arg_contracts,
                                cenv,
                                interner,
                            )
                            .expect("a known closure has a body outcome");
                            produced.push(observed.contract);
                            completions.push(observed.completion);
                        }
                        continue;
                    }
                    // Inside candidate-graph verification, every admissible dependency
                    // must resolve through a settled/current safety fact. Launching a
                    // nested settlement here would pass a cutoff dependency behind the
                    // graph's back and could turn its required `Unproven` into `Proven`.
                    if !has_spread && safety::safety_context_active() {
                        findings.push(Finding {
                            class: TrapClass::OperationSafety,
                            severity: Severity::Warning,
                            message: "callee safety is not established by the active fact graph".into(),
                        });
                        produced.push(Contract::Top);
                        completions.push(Completion::MayFallThrough);
                        continue;
                    }
                    if has_spread {
                        produced.push(Contract::Top);
                        completions.push(Completion::Produces);
                        continue;
                    }
                    let body_safe = safety::prove(cv, &arg_contracts, cenv, interner);
                    if !discharge_body_safety(body_safe, &mut findings) {
                        produced.push(Contract::Top);
                        completions.push(Completion::MayFallThrough);
                        continue;
                    }

                    // Safety has settled the complete dependency graph. Read the
                    // seat/world-independent body outcome; recursive results are
                    // sharpened separately by the return fact below.
                    let observed = outcome::analyze_instance_body(
                        cv,
                        &arg_contracts,
                        cenv,
                        interner,
                    )
                    .unwrap_or_else(|| Analysis {
                        contract: Contract::Top,
                        findings: Vec::new(),
                        completion: Completion::MayFallThrough,
                    });
                    // Completion comes from the **fact** (settled over the candidate
                    // graph), not from a coarse whole-body pass.
                    let completes = safety::completes(cv, &arg_contracts, cenv, interner);
                    completions.push(callee_completion(cv, completes, observed.completion));
                    // A recursive/mutual return needs the induction (`call_return`
                    // sharpens the coarse cycle assumption); a non-recursive return is its
                    // body's **exact** contract, so `always() → Equals(true)` and the
                    // dependent guard's dead branch is pruned (Archive8 §8/§11.4).
                    produced.push(if induction::is_recursive(cv) {
                        call_return(cv, &arg_contracts, has_spread, cenv, interner)
                    } else {
                        observed.contract
                    });
                }
            }
        }
        (union_of(produced, interner), join_completions(&completions))
    };
    Analysis {
        contract,
        findings,
        completion,
    }
}

/// Apply the program policy to a settled body-safety fact. Both refutation and
/// unproven safety block; an unproven fact may carry only advisory row findings, so
/// it always gains an explicit Error rather than being silently accepted.
fn discharge_body_safety(verdict: safety::BodySafety, findings: &mut Vec<Finding>) -> bool {
    match verdict {
        safety::BodySafety::Proven => true,
        safety::BodySafety::Refuted(mut body_findings) => {
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
        safety::BodySafety::Unproven(mut body_findings) => {
            body_findings.push(Finding {
                class: TrapClass::OperationSafety,
                severity: Severity::Error,
                message: "callee body safety cannot be proven".into(),
            });
            findings.append(&mut body_findings);
            false
        }
    }
}

/// The callee's completion (E10) at a call site. A **mutator** discards its return, so it
/// always completes without a value (proven by law, B5). Otherwise the verdict is the
/// settled completion fact: `Produces` when proven, else the honest third voice —
/// `MayFallThrough`, never an assertion that it does fall through (that needs AP-30's
/// witness).
fn callee_completion(cv: &ValueRef, completes: bool, observed: Completion) -> Completion {
    if cv.as_closure().is_some_and(|c| matches!(c.lambda.act_kind, ActKind::Mutator)) {
        return Completion::FallsThrough; // the return is discarded — always without a value
    }
    if completes {
        return Completion::Produces;
    }
    // The fact did not prove completion. A **proven** fall-through still refutes (it
    // carries a sampled witness); anything else is the third voice. `Produces` is
    // deliberately unreachable here — it may only come from the settled fact, never from
    // a coarse body pass.
    match observed {
        Completion::FallsThrough => Completion::FallsThrough,
        Completion::Produces | Completion::MayFallThrough => Completion::MayFallThrough,
    }
}

/// One live alternative of a callee contract (Archive9 §9–§11). The enumeration is
/// **total**: every live leaf classifies into exactly one of these, so no alternative
/// can silently disappear from the combined outcome.
enum CalleeAlt {
    /// A known concrete function — analyze its body precisely.
    Known(ValueRef),
    /// Possibly a function, origin coarsened away (`Kind(Function)`, `Top`, an open
    /// `Ref`) — contributes a conservative outcome, never a sharpening.
    UnknownFunction,
    /// Provably **not** a function — an inhabitant of it would trap operation-safety.
    /// `inhabited` records whether such an inhabitant is *represented*: disjointness
    /// proves what happens **if** a value exists, never that one **does** (Archive10
    /// §14–§16). Only a represented inhabitant may refute.
    NotAFunction { inhabited: bool },
}

/// The live callee alternatives of a callee contract, **totally** classified: a
/// singleton `Equals(fn)`, a leaf proven non-function, or an unknown (possibly-function)
/// leaf; `Union`s recurse. `Bottom` alternatives are dropped (proven empty — no
/// represented execution). Every other live leaf contributes, so a union mixing a known
/// function with a non-function (`b ? good : 1`) or with an unknown function cannot lose
/// the non-`Known` alternative (Archive9 §10/§11).
fn callee_alternatives(cc: &Contract, interner: &mut Interner) -> Vec<CalleeAlt> {
    fn go(c: &Contract, out: &mut Vec<CalleeAlt>, interner: &mut Interner) {
        match c {
            Contract::Union(a, b) => {
                go(a, out, interner);
                go(b, out, interner);
            }
            Contract::Bottom => {} // proven empty — no represented execution
            Contract::Equals(v)
                if v.is_function()
                    || v
                        .as_native()
                        .is_some_and(|native| native.get().act_kind == ActKind::Effect) =>
            {
                out.push(CalleeAlt::Known(v.clone()))
            }
            // Not callable. Refuting demands a *represented* inhabitant: an empty leaf
            // that is not syntactically `Bottom` (`Intersection(Number, String)`, which
            // narrowing can build) denotes no execution at all, so it must not refute.
            _ if disjoint(c, &Contract::Kind(Kind::Function)) => {
                out.push(CalleeAlt::NotAFunction { inhabited: c.has_proven_inhabitant(interner) });
            }
            _ => out.push(CalleeAlt::UnknownFunction),
        }
    }
    let mut out = Vec::new();
    go(cc, &mut out, interner);
    out
}

/// Join the completions of a union of callees (E10 / §1.7): a **proven** fall-through in
/// any alternative dominates (the represented execution may complete without a value);
/// else a **possible** one; else every alternative produces.
fn join_completions(cs: &[Completion]) -> Completion {
    if cs.iter().any(|c| matches!(c, Completion::FallsThrough)) {
        Completion::FallsThrough
    } else if cs.iter().any(|c| matches!(c, Completion::MayFallThrough)) {
        Completion::MayFallThrough
    } else {
        Completion::Produces
    }
}

/// The inferred return contract for a call to the known closure `cv` over
/// `arg_contracts` (§6 / C§13.2). An active return-induction hypothesis (inside a
/// driver pass) wins directly; otherwise — outside a spread call and outside an
/// in-progress inference — run [`induction::infer_return_fact`] over the **call-site
/// argument contracts**, so `factorial(k)` with `k : Number` returns `Number` rather
/// rather than the untyped-domain coarse result (let alone `Top`). Falls back to
/// `Top` when nothing informative is inferred (sound).
fn call_return(cv: &ValueRef, arg_contracts: &[Contract], has_spread: bool, cenv: &ContractEnv, interner: &mut Interner) -> Contract {
    // An active hypothesis applies only to the **same instance over a containing input
    // domain** (§6 / C§13.2 domain-indexed facts) — never by shape alone.
    if let Some(c) = induction::hypothesis_for(cv, arg_contracts, interner) {
        return c;
    }
    if cv.as_fn().is_none() || has_spread || induction::currently_inferring() {
        return Contract::Top;
    }
    induction::infer_return_fact(cv, Some(arg_contracts), cenv, interner).unwrap_or(Contract::Top)
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

    // The scrutinee is evaluated once, in an expecting seat.
    let scrut = match &m.scrutinee {
        Some(e) => {
            let a = analyze_in_world(e, env, cenv, world, interner);
            demand(&a, &mut findings);
            findings.extend(a.findings);
            a.contract
        }
        None => Contract::Top,
    };

    // `body_env` accumulates Bind / Stmt bindings; each item runs against it.
    let mut body_env = env.clone();
    let mut remainder = scrut.clone();
    let mut results: Vec<Contract> = Vec::new();
    // Any guarded arm makes the remainder an *over*-approximation (a guard, not the
    // pattern, decides, and guards consume nothing) — so an inhabited remainder no
    // longer *proves* a fall-through: at most `MayFallThrough`.
    let mut any_guarded = false;

    for item in &m.items {
        match item {
            MatchItem::Bind(b) => {
                let a = analyze_in_world(&b.value, &body_env, cenv, world, interner);
                demand(&a, &mut findings); // a bind RHS is an expecting seat
                findings.extend(a.findings);
                analyze_bind(&b.target, &a.contract, &mut body_env, &mut findings, cenv, interner);
            }
            MatchItem::Stmt(e) => {
                // A statement's value is discarded — *not* an expecting seat.
                let a = analyze_in_world(e, &body_env, cenv, world, interner);
                findings.extend(a.findings);
            }
            MatchItem::Arm(arm) => {
                let pc = arm
                    .pattern
                    .as_ref()
                    .map(|p| pattern_contract(p, cenv, interner))
                    .unwrap_or(Contract::Top);
                let narrowed = intersect(&remainder, &pc, interner);

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
                    bind_pattern(p, &narrowed, &mut arm_env);
                }

                // Guard: a strict Boolean tested seat. A guard **proven false** makes the
                // arm dead (skip its result); a guard **proven true** fires on the whole
                // region like an unguarded arm (so it consumes, emptying the remainder,
                // and does not muddy the fall-through classification); only a genuinely
                // *opaque* guard consumes nothing (uncertainty selects, E9).
                let mut opaque_guard = false;
                if let Some(g) = &arm.guard {
                    let ga = analyze_in_world(g, &arm_env, cenv, world, interner);
                    demand(&ga, &mut findings);
                    findings.extend(ga.findings);
                    check_tested_seat(&ga.contract, &mut findings, interner);
                    let t = Contract::Equals(interner.boolean(true));
                    let f = Contract::Equals(interner.boolean(false));
                    if matches!(subcontract(&ga.contract, &f, interner), Verdict::Proven) {
                        continue; // guard can never hold — dead arm
                    }
                    opaque_guard = !matches!(subcontract(&ga.contract, &t, interner), Verdict::Proven);
                    any_guarded |= opaque_guard;
                }

                // Arm result — an expecting seat.
                let ra = analyze_in_world(&arm.result, &arm_env, cenv, world, interner);
                demand(&ra, &mut findings);
                findings.extend(ra.findings);
                results.push(ra.contract);

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
            }
        }
    }

    let contract = union_of(results, interner);
    Analysis {
        contract,
        findings,
        completion: classify_remainder(&remainder, any_guarded, interner),
    }
}

/// Classify a `Match`'s completion (E10) from its uncovered `remainder` (three-voiced):
/// - **proven empty** → `Produces` (exhaustive — no scrutinee value escapes every arm);
/// - **proven inhabited** by a sampled witness, and **no guarded arm** muddied the
///   remainder → `FallsThrough` (that witness is a represented input that falls
///   through — a real expecting-seat trap);
/// - otherwise (not proven empty, no witness, or guards present) → `MayFallThrough`.
fn classify_remainder(remainder: &Contract, any_guarded: bool, interner: &mut Interner) -> Completion {
    if matches!(subcontract(remainder, &Contract::Bottom, interner), Verdict::Proven) {
        return Completion::Produces;
    }
    if !any_guarded && remainder.has_proven_inhabitant(interner) {
        return Completion::FallsThrough;
    }
    Completion::MayFallThrough
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
    use crate::ast::{Pat, PatElem, PatField};
    match pat {
        Pat::Bind(name) => {
            env.insert(name.clone(), narrowed.clone());
        }
        Pat::Tuple(elems) => {
            for (pos, e) in elems.iter().enumerate() {
                if let PatElem::Pat(p) = e {
                    let sub = tuple_element(narrowed, pos);
                    bind_pattern(p, &sub, env);
                }
            }
        }
        Pat::Record { fields, .. } => {
            for f in fields {
                if let PatField::Field { key, pat } = f {
                    bind_pattern(pat, &field_output(narrowed, key), env);
                }
            }
        }
        // Const / Wild / Contract bind no names.
        _ => {}
    }
}

fn tuple_element(c: &Contract, i: usize) -> Contract {
    match c {
        Contract::Tuple(parts) => parts.get(i).map(|c| (**c).clone()).unwrap_or(Contract::Top),
        _ => Contract::Top,
    }
}

/// A destructuring `Bind` must be irrefutable (E9): its pattern always matches the
/// value. A `Name` target always binds.
fn analyze_bind(
    target: &crate::ast::BindTarget,
    value: &Contract,
    env: &mut TypeEnv,
    findings: &mut Vec<Finding>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) {
    use crate::ast::BindTarget;
    match target {
        BindTarget::Name(name) => {
            env.insert(name.clone(), value.clone());
        }
        BindTarget::Pattern(p) => {
            let pc = pattern_contract(p, cenv, interner);
            if matches!(subcontract(value, &pc, interner), Verdict::Proven) {
                // Irrefutable — always matches.
            } else if disjoint(value, &pc) {
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
            let narrowed = intersect(value, &pc, interner);
            bind_pattern(p, &narrowed, env);
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
