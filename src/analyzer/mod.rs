//! The analyzer — contract inference over the kernel AST, and the compile-time
//! face of the oracle's traps (§6 trap↔compile-error concordance).
//!
//! Per Part I this layer is legitimate only now that the oracle, the
//! normalization harness, and the contract algebra (C.1–C.3, C§9) are green. The
//! analyzer walks an [`Expr`], infers a [`Contract`] over-approximating the value
//! it produces, and at each operation site discharges the operation's safety
//! demand ([`analyze_operation`]) — emitting a [`Finding`] for anything that
//! **will** trap (an *error*, from a refuted demand) or that it **cannot prove**
//! safe (a *warning*, from an unproven demand). The soundness contract (§6): an
//! expression the analyzer accepts with no error never traps in the oracle.
//!
//! **Scope so far:** `Const`, `Ref`, `PrimOp`, `TupleCons`, `RecordCons`,
//! `Template` (E11), `Access` (E6), `Match` (E9/E10), and `Apply` (C§7/B5/E10).
//! Closed expressions are constant-folded through the oracle (`eval_prim` /
//! `eval_expr`), so the concordance is *exact*. Analysis runs in the **pure world**
//! (matching the `eval_expr` truth source); world threading and `Lambda`-body /
//! function-shape analysis (C§13.2) are later increments, so an open call's return
//! types as `Top`. Index/slice bounds await C§17 (see `OwedItems.md`). `Write` and
//! mutation are unanalyzed (type as `Top`).
//!
//! Analysis carries a **named-contract environment** ([`ContractEnv`]) alongside the
//! value-contract [`TypeEnv`]: user contracts (`Percent = Range(0, 100)`, C§12.2)
//! resolve in contract-as-pattern position (E9), so they narrow arms and police
//! destructuring irrefutability exactly as the prelude Kind names do.

use std::collections::HashMap;

use crate::ast::{AccessForm, ActKind, Arg, BindingRef, Element, Expr, Field, PrimOp, Ref, TemplatePart};
use crate::contract::{
    Contract, ContractEnv, Kind, OpSafety, Verdict, analyze_operation, disjoint, eval_contract,
    subcontract,
};
use crate::interner::Interner;
use crate::oracle::{Outcome, TrapClass, eval_expr, eval_prim};
use crate::value::ValueRef;

#[cfg(test)]
mod tests;

/// How serious a finding is for acceptance.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    /// The operation is proven to trap on some reachable input — a rejection.
    Error,
    /// Safety could not be proven (nor refuted) — surfaced, but not a rejection.
    Warning,
}

/// A compile-time diagnostic, tagged with the oracle trap class it mirrors (§6).
#[derive(Clone, Debug)]
pub struct Finding {
    pub class: TrapClass,
    pub severity: Severity,
    pub message: String,
}

/// The result of analyzing an expression: the inferred contract, any findings
/// gathered from it and its subexpressions, and whether evaluation can complete
/// *without* producing a value (a `Match` that may fall through — E10). The last
/// drives the expecting-seat demand.
#[derive(Clone, Debug)]
pub struct Analysis {
    pub contract: Contract,
    pub findings: Vec<Finding>,
    pub may_complete: bool,
}

impl Analysis {
    /// An expression that always produces a value.
    fn produced(contract: Contract, findings: Vec<Finding>) -> Analysis {
        Analysis { contract, findings, may_complete: false }
    }

    /// Whether the expression is accepted — no error-level findings.
    pub fn accepted(&self) -> bool {
        self.findings.iter().all(|f| f.severity != Severity::Error)
    }
}

/// An expecting seat (E10) demands `Produced`; if the sub-analysis `may_complete`
/// without a value, that is the expecting-seat trap's compile-time mirror.
fn demand(a: &Analysis, findings: &mut Vec<Finding>) {
    if a.may_complete {
        findings.push(Finding {
            class: TrapClass::ExpectingSeat,
            severity: Severity::Error,
            message: "a value is demanded here, but this expression may complete without one".into(),
        });
    }
}

/// A contract environment: immutable-binding name → its contract.
pub type TypeEnv = HashMap<String, Contract>;

/// Analyze a kernel expression against a contract environment.
pub fn analyze(expr: &Expr, env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
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

        Expr::PrimOp { op, args } => analyze_primop(*op, args, env, cenv, interner),

        Expr::TupleCons(elems) => analyze_tuple(elems, env, cenv, interner),
        Expr::RecordCons(fields) => analyze_record(fields, env, cenv, interner),
        Expr::Template(parts) => analyze_template(parts, env, cenv, interner),
        Expr::Access { target, form, total } => analyze_access(target, form, *total, env, cenv, interner),
        Expr::Match(m) => analyze_match(m, env, cenv, interner),
        Expr::Apply { callee, args } => analyze_apply(callee, args, env, cenv, interner),

        // Not yet analyzed: conservatively typed `Top`, unchecked.
        _ => exact(Contract::Top),
    }
}

fn exact(contract: Contract) -> Analysis {
    Analysis::produced(contract, vec![])
}

fn analyze_primop(op: PrimOp, args: &[Expr], env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let mut inputs = Vec::with_capacity(args.len());
    for a in args {
        let mut r = analyze(a, env, cenv, interner);
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
                    severity: Severity::Warning,
                    message: format!("cannot prove `{op:?}` safe for these operands"),
                }),
            }
            result.output
        }
    };

    Analysis::produced(contract, findings)
}

fn analyze_tuple(elems: &[Element], env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let mut parts = Vec::new();
    let mut exact_shape = true;
    for el in elems {
        match el {
            Element::Expr(e) => {
                let mut r = analyze(e, env, cenv, interner);
                demand(&r, &mut findings); // elements are expecting seats
                findings.append(&mut r.findings);
                parts.push(r.contract);
            }
            // A spread widens the shape beyond what this increment models.
            Element::Spread(e) => {
                findings.append(&mut analyze(e, env, cenv, interner).findings);
                exact_shape = false;
            }
        }
    }
    let contract = if exact_shape { Contract::Tuple(parts) } else { Contract::Top };
    Analysis::produced(contract, findings)
}

fn analyze_record(fields: &[Field], env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let mut pairs = Vec::new();
    let mut exact_shape = true;
    for field in fields {
        match field {
            Field::Field { key, value } => {
                let mut r = analyze(value, env, cenv, interner);
                demand(&r, &mut findings); // field values are expecting seats
                findings.append(&mut r.findings);
                pairs.push((key.clone(), r.contract));
            }
            // Computed keys (E5 finite-key obligation) and spreads widen the shape.
            Field::Computed { key, value } => {
                findings.append(&mut analyze(key, env, cenv, interner).findings);
                findings.append(&mut analyze(value, env, cenv, interner).findings);
                exact_shape = false;
            }
            Field::Spread(e) => {
                findings.append(&mut analyze(e, env, cenv, interner).findings);
                exact_shape = false;
            }
        }
    }
    let contract = if exact_shape { Contract::Record(pairs) } else { Contract::Top };
    Analysis::produced(contract, findings)
}

/// A template always produces a String. **Structure interpolation is total**
/// [user, 2026-07-18]: every value renders (canonical literal forms for data,
/// `<Function>`, `<Indeterminate …>`), so an interpolation carries **no
/// printability demand** — there is nothing here to reject. Interpolations remain
/// ordinary expecting seats, and their subexpressions are analyzed as usual.
fn analyze_template(parts: &[TemplatePart], env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    for part in parts {
        let TemplatePart::Interp(e) = part else { continue };
        let mut r = analyze(e, env, cenv, interner);
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
fn analyze_access(target: &Expr, form: &AccessForm, total: bool, env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let ta = analyze(target, env, cenv, interner);
    demand(&ta, &mut findings); // the receiver is an expecting seat
    findings.extend(ta.findings);
    let tc = ta.contract;

    // Analyze the index/bound subexpressions for their findings and fold values.
    let mut child = |e: &Expr, findings: &mut Vec<Finding>| -> Contract {
        let mut a = analyze(e, env, cenv, interner);
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
    Some(Expr::Access { target: Box::new(Expr::Const(tv.clone())), form: form2, total })
}

/// Field access (E6): prove receiver non-null and field present (demand form).
fn analyze_field(tc: &Contract, name: &str, total: bool, findings: &mut Vec<Finding>, interner: &mut Interner) -> Contract {
    let has_field = Contract::HasField(name.to_string());
    let output = field_output(tc, name);
    let null = Contract::Kind(Kind::Null);

    if matches!(subcontract(tc, &has_field, interner), Verdict::Proven) {
        // Record with the field, non-null — safe.
        return if total { or_null(output) } else { output };
    }
    if total {
        // `?.` totalizes null and absent to null — never traps.
        return or_null(output);
    }
    if disjoint(tc, &has_field) {
        // Every inhabitant either is null (null-receiver) or lacks the field
        // (absent-field) — always traps.
        let could_null = !disjoint(tc, &null);
        let class = if could_null { TrapClass::NullReceiver } else { TrapClass::AbsentField };
        findings.push(Finding {
            class,
            severity: Severity::Error,
            message: format!("field `{name}` access always traps on this receiver"),
        });
        return Contract::Bottom;
    }
    findings.push(Finding {
        class: TrapClass::AbsentField,
        severity: Severity::Warning,
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
            .map(|(_, c)| c.clone())
            .unwrap_or(Contract::Top),
        _ => Contract::Top,
    }
}

fn or_null(c: Contract) -> Contract {
    Contract::Union(Box::new(c), Box::new(Contract::Kind(Kind::Null)))
}

fn analyze_index(tc: &Contract, total: bool, findings: &mut Vec<Finding>, interner: &mut Interner) -> Contract {
    if total {
        return Contract::Top; // `?.[i]` totalizes null / out-of-bounds / non-integer to null
    }
    if matches!(subcontract(tc, &Contract::Kind(Kind::Null), interner), Verdict::Proven) {
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
        severity: Severity::Warning,
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
        severity: Severity::Warning,
        message: "cannot prove receiver sliceable / bounds integer (C§17 owed)".into(),
    });
    Contract::Top
}

// ── Apply (C§7 / B5 / E10) — application ──────────────────────────────────────

/// Analyze an application. Closed calls (known callee value + singleton plain
/// args) fold through the oracle (`eval_expr`) for an exact verdict. Otherwise:
/// each argument spread must be a Tuple (`spread-kind`); the callee must be a
/// function (else operation-safety); and when the callee value is known, its
/// act-kind is checked against the analysis world (`world-admission`) and the
/// argument tuple against its parameter pattern (`argument-obligation`).
///
/// **World context.** This increment analyzes in the **pure world** (matching the
/// `eval_expr` truth source); world threading arrives with `Lambda`-body analysis.
/// The callee's *return* shape and a `Pure`/`Effect` body's completion are not yet
/// derived (no function-shape contract — C§13.2), so an open call types as `Top`.
fn analyze_apply(callee: &Expr, args: &[Arg], env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();

    let ca = analyze(callee, env, cenv, interner);
    demand(&ca, &mut findings); // the callee is an expecting seat
    let cc = ca.contract.clone();
    findings.extend(ca.findings);

    let mut arg_contracts: Vec<Contract> = Vec::new();
    let mut arg_vals: Vec<ValueRef> = Vec::new();
    let mut foldable = true;
    let mut has_spread = false;
    for a in args {
        match a {
            Arg::Expr(e) => {
                let aa = analyze(e, env, cenv, interner);
                demand(&aa, &mut findings);
                match &aa.contract {
                    Contract::Equals(v) => arg_vals.push(v.clone()),
                    _ => foldable = false,
                }
                arg_contracts.push(aa.contract.clone());
                findings.extend(aa.findings);
            }
            Arg::Spread(e) => {
                has_spread = true;
                foldable = false;
                let aa = analyze(e, env, cenv, interner);
                demand(&aa, &mut findings);
                check_spread_kind(&aa.contract, &mut findings, interner);
                findings.extend(aa.findings);
            }
        }
    }

    // Fold a fully-known call through the oracle for an exact verdict.
    let fold_callee = match &cc {
        Contract::Equals(cv) if foldable && !has_spread => Some(cv.clone()),
        _ => None,
    };
    if let Some(cv) = fold_callee {
        let node = Expr::Apply {
            callee: Box::new(Expr::Const(cv)),
            args: arg_vals.into_iter().map(|v| Arg::Expr(Expr::Const(v))).collect(),
        };
        return match eval_expr(&node, interner) {
            Ok(Outcome::Produced(v)) => Analysis::produced(Contract::Equals(v), findings),
            Ok(Outcome::CompletedWithoutValue) => Analysis { contract: Contract::Top, findings, may_complete: true },
            Err(trap) => {
                findings.push(Finding { class: trap.class, severity: Severity::Error, message: trap.message });
                Analysis::produced(Contract::Bottom, findings)
            }
        };
    }

    // A non-function callee always traps operation-safety.
    if disjoint(&cc, &Contract::Kind(Kind::Function)) {
        findings.push(Finding {
            class: TrapClass::OperationSafety,
            severity: Severity::Error,
            message: "callee is not a function".into(),
        });
        return Analysis::produced(Contract::Bottom, findings);
    }

    // With a known callee value, check its act-kind and parameter obligation.
    let may_complete = match &cc {
        Contract::Equals(cv) => analyze_known_callee(cv, &arg_contracts, has_spread, &mut findings, cenv, interner),
        _ => false, // unknown callee: shape not derivable yet (owed)
    };
    Analysis { contract: Contract::Top, findings, may_complete }
}

/// Check a known callee's act-kind (world admission) and argument obligation.
/// Returns whether the call `may_complete` without a value.
fn analyze_known_callee(
    cv: &ValueRef,
    arg_contracts: &[Contract],
    has_spread: bool,
    findings: &mut Vec<Finding>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> bool {
    // Analysis world is pure (see `analyze_apply`); only pure callees are admitted.
    let admit = |kind: ActKind, findings: &mut Vec<Finding>| {
        if !matches!(kind, ActKind::Pure) {
            findings.push(Finding {
                class: TrapClass::WorldAdmission,
                severity: Severity::Error,
                message: format!("a {kind:?} call is not admitted in the pure world"),
            });
        }
    };

    if let Some(closure) = cv.as_closure() {
        admit(closure.lambda.act_kind, findings);
        // Argument obligation: the argument tuple must match the parameter pattern.
        if !has_spread {
            let arg_tuple = Contract::Tuple(arg_contracts.to_vec());
            let params = pattern_contract(&closure.lambda.params, cenv);
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
                    severity: Severity::Warning,
                    message: "cannot prove the arguments match the parameter pattern".into(),
                });
            }
        }
        // A mutator's return is discarded — the call completes without a value.
        return matches!(closure.lambda.act_kind, ActKind::Mutator);
    }
    if let Some(native) = cv.as_native() {
        admit(native.get().act_kind, findings);
    }
    false
}

/// An argument spread must evaluate to a Tuple (E3) — else the spread-kind trap.
fn check_spread_kind(c: &Contract, findings: &mut Vec<Finding>, interner: &mut Interner) {
    let tuple = Contract::Kind(Kind::Tuple);
    if matches!(subcontract(c, &tuple, interner), Verdict::Proven) {
        return;
    }
    if disjoint(c, &tuple) {
        findings.push(Finding {
            class: TrapClass::SpreadKind,
            severity: Severity::Error,
            message: "argument spread of a non-Tuple".into(),
        });
    } else {
        findings.push(Finding {
            class: TrapClass::SpreadKind,
            severity: Severity::Warning,
            message: "cannot prove this argument spread is a Tuple".into(),
        });
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
fn analyze_match(m: &crate::ast::Match, env: &TypeEnv, cenv: &ContractEnv, interner: &mut Interner) -> Analysis {
    use crate::ast::MatchItem;

    let mut findings = Vec::new();

    // The scrutinee is evaluated once, in an expecting seat.
    let scrut = match &m.scrutinee {
        Some(e) => {
            let a = analyze(e, env, cenv, interner);
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

    for item in &m.items {
        match item {
            MatchItem::Bind(b) => {
                let a = analyze(&b.value, &body_env, cenv, interner);
                demand(&a, &mut findings); // a bind RHS is an expecting seat
                findings.extend(a.findings);
                analyze_bind(&b.target, &a.contract, &mut body_env, &mut findings, cenv, interner);
            }
            MatchItem::Stmt(e) => {
                // A statement's value is discarded — *not* an expecting seat.
                let a = analyze(e, &body_env, cenv, interner);
                findings.extend(a.findings);
            }
            MatchItem::Arm(arm) => {
                let pc = arm.pattern.as_ref().map(|p| pattern_contract(p, cenv)).unwrap_or(Contract::Top);
                let narrowed = intersect(&remainder, &pc);

                // Arm-local environment: the outer bindings plus the pattern's.
                let mut arm_env = body_env.clone();
                if let Some(p) = &arm.pattern {
                    bind_pattern(p, &narrowed, &mut arm_env);
                }

                // Guard: a strict Boolean tested seat.
                let mut guarded = false;
                if let Some(g) = &arm.guard {
                    guarded = true;
                    let ga = analyze(g, &arm_env, cenv, interner);
                    demand(&ga, &mut findings);
                    findings.extend(ga.findings);
                    check_tested_seat(&ga.contract, &mut findings, interner);
                }

                // Arm result — an expecting seat.
                let ra = analyze(&arm.result, &arm_env, cenv, interner);
                demand(&ra, &mut findings);
                findings.extend(ra.findings);
                results.push(ra.contract);

                // A guarded arm's success is opaque, so it consumes nothing of the
                // remainder (uncertainty selects, E9); an unguarded arm consumes its
                // whole pattern region — which empties the remainder when the pattern
                // covers all of it (e.g. `_` / a bare binding).
                if !guarded {
                    remainder = if matches!(subcontract(&remainder, &pc, interner), Verdict::Proven) {
                        Contract::Bottom
                    } else {
                        difference(&remainder, &pc)
                    };
                }
            }
        }
    }

    // Exhaustive iff no scrutinee value escapes every arm.
    let exhaustive = matches!(subcontract(&remainder, &Contract::Bottom, interner), Verdict::Proven);
    let contract = union_of(results);
    Analysis { contract, findings, may_complete: !exhaustive }
}

/// The contract of values a pattern matches — a **superset** of the true match set
/// (sound for narrowing by intersection).
fn pattern_contract(pat: &crate::ast::Pat, cenv: &ContractEnv) -> Contract {
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
                let parts = elems
                    .iter()
                    .map(|e| match e {
                        PatElem::Pat(p) => pattern_contract(p, cenv),
                        PatElem::Rest(_) => unreachable!(),
                    })
                    .collect();
                Contract::Tuple(parts)
            }
        }
        Pat::Record { fields, exact } => {
            let named: Vec<&PatField> =
                fields.iter().filter(|f| matches!(f, PatField::Field { .. })).collect();
            let has_rest = fields.iter().any(|f| matches!(f, PatField::Rest(_)));
            if *exact && !has_rest {
                let pairs = named
                    .iter()
                    .map(|f| match f {
                        PatField::Field { key, pat } => (key.clone(), pattern_contract(pat, cenv)),
                        PatField::Rest(_) => unreachable!(),
                    })
                    .collect();
                Contract::Record(pairs)
            } else {
                // Open record: "has at least these fields."
                named
                    .iter()
                    .filter_map(|f| match f {
                        PatField::Field { key, .. } => Some(Contract::HasField(key.clone())),
                        PatField::Rest(_) => None,
                    })
                    .reduce(|a, b| intersect(&a, &b))
                    .unwrap_or(Contract::Kind(Kind::Record))
            }
        }
        Pat::Contract(r) => contract_ref(r, cenv).unwrap_or(Contract::Top),
    }
}

/// Resolve a contract-as-pattern reference (E9). Prelude Kind names, `Top`,
/// `Bottom` and `Failure` resolve structurally; any other name resolves against the
/// **named-contract environment** (C§12.2 — `Percent = Range(0, 100)`). An
/// unresolvable name yields `None`, which the caller widens to `Top` (no
/// narrowing). Resolution is shared with the contract-expression evaluator so
/// patterns and contract expressions agree by construction.
fn contract_ref(r: &Ref, cenv: &ContractEnv) -> Option<Contract> {
    eval_contract(&Expr::Ref(r.clone()), cenv)
}

/// Bind a pattern's names to their narrowed contracts in `env` (best-effort; a
/// name whose position is not tracked binds to `Top`).
fn bind_pattern(pat: &crate::ast::Pat, narrowed: &Contract, env: &mut TypeEnv) {
    use crate::ast::{Pat, PatElem, PatField};
    match pat {
        Pat::Bind(name) => {
            env.insert(name.clone(), narrowed.clone());
        }
        Pat::Tuple(elems) => {
            for (i, e) in elems.iter().enumerate() {
                if let PatElem::Pat(p) = e {
                    let sub = tuple_element(narrowed, i);
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
        Contract::Tuple(parts) => parts.get(i).cloned().unwrap_or(Contract::Top),
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
            let pc = pattern_contract(p, cenv);
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
                    severity: Severity::Warning,
                    message: "cannot prove this destructuring binding irrefutable".into(),
                });
            }
            bind_pattern(p, &intersect(value, &pc), env);
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
            severity: Severity::Warning,
            message: "cannot prove this guard is a Boolean".into(),
        });
    }
}

fn intersect(a: &Contract, b: &Contract) -> Contract {
    match (a, b) {
        (Contract::Top, x) | (x, Contract::Top) => x.clone(),
        // Elementwise on matching tuples, so narrowing reaches sub-patterns.
        (Contract::Tuple(pa), Contract::Tuple(pb)) if pa.len() == pb.len() => {
            Contract::Tuple(pa.iter().zip(pb).map(|(x, y)| intersect(x, y)).collect())
        }
        _ => Contract::Intersection(Box::new(a.clone()), Box::new(b.clone())),
    }
}

fn difference(a: &Contract, b: &Contract) -> Contract {
    Contract::Difference(Box::new(a.clone()), Box::new(b.clone()))
}

fn union_of(mut contracts: Vec<Contract>) -> Contract {
    match contracts.len() {
        0 => Contract::Top, // a Match with no arms only ever completes-without-value
        1 => contracts.pop().unwrap(),
        _ => contracts
            .into_iter()
            .reduce(|a, b| Contract::Union(Box::new(a), Box::new(b)))
            .unwrap(),
    }
}

