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
//! Scope: capture-free, zero-/single-parameter. Multi-parameter (argument-tuple
//! projection, §5) and the guards' own path demands are owed; this is not yet wired
//! into `analyze_apply` (the superseded machinery still runs — audit §5).

use crate::analyzer::region::{region_table, select};
use crate::analyzer::{Finding, Severity, TypeEnv, analyze};
use crate::ast::{Pat, PatElem};
use crate::contract::{Contract, ContractEnv};
use crate::env::Binding;
use crate::interner::Interner;
use crate::value::ValueRef;

/// Findings from checking a call to `callee` with argument contracts `args`. Empty ⇒ no
/// finding proved. `Error` ⇒ a definitely-reached row traps (refutation); `Warning` ⇒
/// unproven (a may-region row traps, or safety could not be proven).
pub fn body_check(callee: &ValueRef, args: &[Contract], cenv: &ContractEnv, interner: &mut Interner) -> Vec<Finding> {
    let Some(closure) = callee.as_closure() else { return vec![] };
    let base = capture_env(callee);

    match param_name(&closure.lambda.params) {
        Param::Zero => analyze(&closure.lambda.body, &base, cenv, interner).findings,
        Param::One(name) => {
            let arg = args.first().cloned().unwrap_or(Contract::Top);
            let table = region_table(&closure.lambda.body, &name, cenv);
            let selected = select(&table, &arg);
            let mut findings = Vec::new();
            let mut all_prior_exact = true;
            for sel in &selected {
                let definite = sel.exact && all_prior_exact;
                let mut env = base.clone();
                env.insert(name.clone(), sel.region.clone());
                for f in analyze(&sel.result, &env, cenv, interner).findings {
                    findings.push(if definite { f } else { downgrade(f) });
                }
                all_prior_exact = all_prior_exact && sel.exact;
            }
            findings
        }
        Param::Other => vec![], // multi/complex params — §5 argument-tuple projection owed
    }
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
