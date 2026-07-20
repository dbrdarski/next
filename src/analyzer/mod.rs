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
//! **Scope so far:** the pure expression fragment plus `Template` (E11 printability)
//! and `Access` (E6 demands) — `Const`, `Ref` (against a contract environment),
//! `PrimOp`, `TupleCons`, `RecordCons`, `Template`, `Access`. Closed expressions are
//! constant-folded through the oracle (`eval_prim`/`eval_expr`), so the concordance
//! is *exact*. Index/slice *bounds* reasoning on open receivers awaits the
//! tuple-length family (C§17 owed — see `OwedItems.md`). Worlds, application,
//! `Match`, and mutation are later increments — those nodes type as `Top`, unchecked.

use std::collections::HashMap;

use crate::ast::{AccessForm, BindingRef, Element, Expr, Field, PrimOp, Ref, TemplatePart};
use crate::contract::{Contract, Kind, OpSafety, Verdict, analyze_operation, disjoint, subcontract};
use crate::interner::Interner;
use crate::oracle::{Outcome, TrapClass, eval_expr, eval_prim};
use crate::value::{ValueData, ValueRef};

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

/// The result of analyzing an expression: the inferred contract plus any findings
/// gathered from it and its subexpressions.
#[derive(Clone, Debug)]
pub struct Analysis {
    pub contract: Contract,
    pub findings: Vec<Finding>,
}

impl Analysis {
    /// Whether the expression is accepted — no error-level findings.
    pub fn accepted(&self) -> bool {
        self.findings.iter().all(|f| f.severity != Severity::Error)
    }
}

/// A contract environment: immutable-binding name → its contract.
pub type TypeEnv = HashMap<String, Contract>;

/// Analyze a kernel expression against a contract environment.
pub fn analyze(expr: &Expr, env: &TypeEnv, interner: &mut Interner) -> Analysis {
    match expr {
        // A literal denotes exactly itself.
        Expr::Const(v) => exact(Contract::Equals(v.clone())),

        // An immutable reference takes its bound contract; an unbound name is the
        // unbound-evaluation trap's compile-time mirror.
        Expr::Ref(Ref::Immutable(BindingRef::Name(name))) => match env.get(name) {
            Some(c) => exact(c.clone()),
            None => Analysis {
                contract: Contract::Top,
                findings: vec![Finding {
                    class: TrapClass::UnboundEvaluation,
                    severity: Severity::Error,
                    message: format!("reference to unbound name `{name}`"),
                }],
            },
        },
        // Positional / Location / Mu references are out of scope for this increment.
        Expr::Ref(_) => exact(Contract::Top),

        Expr::PrimOp { op, args } => analyze_primop(*op, args, env, interner),

        Expr::TupleCons(elems) => analyze_tuple(elems, env, interner),
        Expr::RecordCons(fields) => analyze_record(fields, env, interner),
        Expr::Template(parts) => analyze_template(parts, env, interner),
        Expr::Access { target, form, total } => analyze_access(target, form, *total, env, interner),

        // Not yet analyzed: conservatively typed `Top`, unchecked.
        _ => exact(Contract::Top),
    }
}

fn exact(contract: Contract) -> Analysis {
    Analysis { contract, findings: vec![] }
}

fn analyze_primop(op: PrimOp, args: &[Expr], env: &TypeEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let mut inputs = Vec::with_capacity(args.len());
    for a in args {
        let mut r = analyze(a, env, interner);
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

    Analysis { contract, findings }
}

fn analyze_tuple(elems: &[Element], env: &TypeEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let mut parts = Vec::new();
    let mut exact_shape = true;
    for el in elems {
        match el {
            Element::Expr(e) => {
                let mut r = analyze(e, env, interner);
                findings.append(&mut r.findings);
                parts.push(r.contract);
            }
            // A spread widens the shape beyond what this increment models.
            Element::Spread(e) => {
                findings.append(&mut analyze(e, env, interner).findings);
                exact_shape = false;
            }
        }
    }
    let contract = if exact_shape { Contract::Tuple(parts) } else { Contract::Top };
    Analysis { contract, findings }
}

fn analyze_record(fields: &[Field], env: &TypeEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let mut pairs = Vec::new();
    let mut exact_shape = true;
    for field in fields {
        match field {
            Field::Field { key, value } => {
                let mut r = analyze(value, env, interner);
                findings.append(&mut r.findings);
                pairs.push((key.clone(), r.contract));
            }
            // Computed keys (E5 finite-key obligation) and spreads widen the shape.
            Field::Computed { key, value } => {
                findings.append(&mut analyze(key, env, interner).findings);
                findings.append(&mut analyze(value, env, interner).findings);
                exact_shape = false;
            }
            Field::Spread(e) => {
                findings.append(&mut analyze(e, env, interner).findings);
                exact_shape = false;
            }
        }
    }
    let contract = if exact_shape { Contract::Record(pairs) } else { Contract::Top };
    Analysis { contract, findings }
}

/// A template produces a String (when it does not trap). Each interpolation is a
/// printability demand: the oracle's `stringify` prints only String/Number/
/// Boolean/Null and **traps `UnprintableInterpolation` on structures** — the print
/// doctrine for structures is deliberately open (E11: *trap until ruled*), so a
/// structure interpolation is a rejection, not a silent accept.
fn analyze_template(parts: &[TemplatePart], env: &TypeEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    for part in parts {
        let TemplatePart::Interp(e) = part else { continue };
        let mut r = analyze(e, env, interner);
        findings.append(&mut r.findings);
        match printability(&r.contract, interner) {
            Printability::Printable => {}
            Printability::Never => findings.push(Finding {
                class: TrapClass::UnprintableInterpolation,
                severity: Severity::Error,
                message: "interpolating a structure is unruled (E11 — trap until ruled)".into(),
            }),
            Printability::Unknown => findings.push(Finding {
                class: TrapClass::UnprintableInterpolation,
                severity: Severity::Warning,
                message: "cannot prove this interpolation is printable".into(),
            }),
        }
    }
    Analysis { contract: Contract::Kind(Kind::String), findings }
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
fn analyze_access(target: &Expr, form: &AccessForm, total: bool, env: &TypeEnv, interner: &mut Interner) -> Analysis {
    let mut findings = Vec::new();
    let ta = analyze(target, env, interner);
    findings.extend(ta.findings);
    let tc = ta.contract;

    // Analyze the index/bound subexpressions for their findings and fold values.
    let mut child = |e: &Expr, findings: &mut Vec<Finding>| -> Contract {
        let mut a = analyze(e, env, interner);
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
            Ok(Outcome::Produced(v)) => Analysis { contract: Contract::Equals(v), findings },
            Ok(Outcome::CompletedWithoutValue) => Analysis { contract: Contract::Top, findings },
            Err(trap) => {
                findings.push(Finding { class: trap.class, severity: Severity::Error, message: trap.message });
                Analysis { contract: Contract::Bottom, findings }
            }
        };
    }

    // Open path.
    let contract = match form {
        AccessForm::Field(name) => analyze_field(&tc, name, total, &mut findings, interner),
        AccessForm::Index(_) => analyze_index(&tc, total, &mut findings, interner),
        AccessForm::Slice { .. } => analyze_slice(&tc, &mut findings, interner),
    };
    Analysis { contract, findings }
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

enum Printability {
    Printable,
    Never,
    Unknown,
}

/// Whether the oracle's `stringify` accepts a value of this kind.
fn printable_value(v: &ValueRef) -> bool {
    matches!(
        v.data(),
        ValueData::Str(_) | ValueData::Number(_) | ValueData::Boolean(_) | ValueData::Null
    )
}

fn printability(c: &Contract, interner: &mut Interner) -> Printability {
    // A singleton decides exactly (mirrors the oracle on that value).
    if let Contract::Equals(v) = c {
        return if printable_value(v) { Printability::Printable } else { Printability::Never };
    }
    let printable = union([Kind::String, Kind::Number, Kind::Boolean, Kind::Null]);
    if matches!(subcontract(c, &printable, interner), Verdict::Proven) {
        return Printability::Printable;
    }
    // Provably a structure (or an Indeterminate) — every inhabitant traps.
    let unprintable = union([Kind::Tuple, Kind::Record, Kind::Function]);
    if matches!(c, Contract::Indeterminate(_))
        || matches!(subcontract(c, &unprintable, interner), Verdict::Proven)
    {
        return Printability::Never;
    }
    Printability::Unknown
}

/// A right-folded union of the given kinds.
fn union<const N: usize>(kinds: [Kind; N]) -> Contract {
    kinds
        .into_iter()
        .rev()
        .map(Contract::Kind)
        .reduce(|acc, k| Contract::Union(Box::new(k), Box::new(acc)))
        .expect("non-empty")
}
