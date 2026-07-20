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
//! **Scope of this increment:** the pure expression fragment — `Const`, `Ref`
//! (against a contract environment), `PrimOp`, `TupleCons`, `RecordCons`. On this
//! fragment the concordance is *exact*: closed expressions are constant-folded
//! through the oracle's own `eval_prim`, so the analyzer predicts the trap class
//! precisely. Worlds, application, `Match`, access, templates, and mutation are
//! later increments — those nodes type as `Top` and are not yet checked.

use std::collections::HashMap;

use crate::ast::{BindingRef, Element, Expr, Field, PrimOp, Ref};
use crate::contract::{Contract, OpSafety, analyze_operation};
use crate::interner::Interner;
use crate::oracle::{TrapClass, eval_prim};
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
