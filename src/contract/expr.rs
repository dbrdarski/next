//! Static evaluation of **contract expressions** (Compendium C§12.2 / §292).
//!
//! Contract constructors (`Range`, `Mod`, `Equals`, `Union`, `Difference`,
//! `HasField`, `Geo`, …) are predeclared prelude names, and a named contract is an
//! ordinary binding of a contract expression (`Percent = Range(0, 100)`). This
//! module evaluates such an expression — a kernel [`Expr`] built from those
//! constructor applications, prelude Kind names, structural tuple/record literals,
//! and references to earlier named contracts — into a [`Contract`].
//!
//! **Scope:** in-order evaluation resolves a reference to its already evaluated
//! definition; recursive/mutual source contracts land on the **second pass**
//! ([`eval_recursive_contract_bindings`]) — failed bindings re-evaluated jointly
//! with their names bound to `Contract::Ref`, admissibility-checked as one group
//! (C§9, plan T2.4). Numeric/string arguments must be literals (`Const`); computed
//! contract arguments are owed (C§12.2 static evaluation of arbitrary expressions).

use std::collections::HashMap;

use super::{Contract, Kind};
use crate::ast::{Arg, BindingRef, Element, Expr, Field, Ref};
use crate::interner::Interner;
use crate::value::ValueRef;

/// A name → named-contract binding environment.
pub type ContractEnv = HashMap<String, Contract>;

/// Statically evaluate a contract expression, or `None` if `expr` is not a
/// recognized contract form.
pub fn eval_contract(expr: &Expr, env: &ContractEnv, i: &mut Interner) -> Option<Contract> {
    match expr {
        Expr::Ref(Ref::Immutable(BindingRef::Name(n))) => ref_contract(n, env, i),
        Expr::Apply { callee, args } => apply_contract(callee, args, env, i),
        // A tuple literal of contracts denotes a tuple contract (no spreads yet).
        Expr::TupleCons(elems) => {
            let mut parts = Vec::with_capacity(elems.len());
            for el in elems {
                match el {
                    Element::Expr(e) => parts.push(eval_contract(e, env, i)?),
                    Element::Spread(_) => return None,
                }
            }
            Some(Contract::tuple(parts, i))
        }
        // A record literal of contracts denotes a record contract (static keys).
        Expr::RecordCons(fields) => {
            let mut pairs = Vec::with_capacity(fields.len());
            for f in fields {
                match f {
                    Field::Field { key, value } => {
                        pairs.push((key.clone(), eval_contract(value, env, i)?))
                    }
                    _ => return None,
                }
            }
            Some(Contract::record(pairs, i))
        }
        _ => None,
    }
}

/// A prelude Kind name, `Top`/`Bottom`/`Failure`, or a named contract.
fn ref_contract(name: &str, env: &ContractEnv, i: &mut Interner) -> Option<Contract> {
    Some(match name {
        "Number" => Contract::Kind(Kind::Number),
        "String" => Contract::Kind(Kind::String),
        "Boolean" => Contract::Kind(Kind::Boolean),
        "Null" => Contract::Kind(Kind::Null),
        "Tuple" => Contract::Kind(Kind::Tuple),
        "Record" => Contract::Kind(Kind::Record),
        "Function" => Contract::Kind(Kind::Function),
        "Indeterminate" => Contract::indeterminate(i),
        "Numeric" => Contract::numeric(i),
        "Top" => Contract::Top,
        "Bottom" => Contract::Bottom,
        // The one prelude Failure shape (B6/E9): a record with `path` and `reason`.
        "Failure" => Contract::failure(i),
        _ => return env.get(name).cloned(),
    })
}

fn apply_contract(
    callee: &Expr,
    args: &[Arg],
    env: &ContractEnv,
    i: &mut Interner,
) -> Option<Contract> {
    let Expr::Ref(Ref::Immutable(BindingRef::Name(ctor))) = callee else {
        return None;
    };
    // Contract constructors take plain (non-spread) arguments.
    let args: Option<Vec<&Expr>> = args
        .iter()
        .map(|a| match a {
            Arg::Expr(e) => Some(e),
            Arg::Spread(_) => None,
        })
        .collect();
    let args = args?;

    match (ctor.as_str(), args.as_slice()) {
        ("Range", [lo, hi]) => Some(Contract::Range(num(lo)?, num(hi)?)),
        ("Greater", [m]) => Some(Contract::Greater(num(m)?)),
        ("GreaterEq", [m]) => Some(Contract::GreaterEq(num(m)?)),
        ("Less", [m]) => Some(Contract::Less(num(m)?)),
        ("LessEq", [m]) => Some(Contract::LessEq(num(m)?)),
        ("Mod", [n, r]) => Some(Contract::Mod {
            n: int(n)?,
            r: int(r)?,
        }),
        ("Geo", [b, r]) => Some(Contract::Geo {
            b: num(b)?,
            r: num(r)?,
        }),
        ("Equals", [v]) => Some(Contract::Equals(konst(v)?)),
        ("HasField", [k]) => Some(Contract::HasField(string(k)?)),
        ("Union", [a, b]) => {
            let (a, b) = (eval_contract(a, env, i)?, eval_contract(b, env, i)?);
            Some(Contract::union(a, b, i))
        }
        ("Intersection", [a, b]) => {
            let (a, b) = (eval_contract(a, env, i)?, eval_contract(b, env, i)?);
            Some(Contract::intersection(a, b, i))
        }
        ("Difference", [a, b]) => {
            let (a, b) = (eval_contract(a, env, i)?, eval_contract(b, env, i)?);
            Some(Contract::difference(a, b, i))
        }
        // `Tuple(A, B, …)` — a variadic tuple contract.
        ("Tuple", elems) => {
            let elems: Vec<Contract> = elems
                .iter()
                .map(|e| eval_contract(e, env, i))
                .collect::<Option<_>>()?;
            Some(Contract::tuple(elems, i))
        }
        // `Concat(S₁, S₂, …)` — tuple concatenation (tuple family §1), through the
        // normalizing smart constructor.
        ("Concat", segs) => {
            let segs: Vec<Contract> = segs
                .iter()
                .map(|e| eval_contract(e, env, i))
                .collect::<Option<_>>()?;
            Some(Contract::concat(segs, i))
        }
        _ => None,
    }
}

fn konst(e: &Expr) -> Option<ValueRef> {
    match e {
        Expr::Const(v) => Some(v.clone()),
        _ => None,
    }
}

fn num(e: &Expr) -> Option<crate::rational::Rational> {
    konst(e)?.as_number().cloned()
}

fn int(e: &Expr) -> Option<num_bigint::BigInt> {
    let n = num(e)?;
    n.is_integer().then(|| n.as_ratio().numer().clone())
}

fn string(e: &Expr) -> Option<String> {
    let v = konst(e)?;
    let units = v.as_str_units()?;
    String::from_utf16(units).ok()
}

/// Statically evaluate a sequence of `name = contract-expression` bindings into a
/// [`ContractEnv`], in order (a binding may reference earlier ones). Non-contract
/// bindings are skipped.
pub fn build_contract_env<'a>(
    binds: impl IntoIterator<Item = (&'a str, &'a Expr)>,
    i: &mut Interner,
) -> ContractEnv {
    let mut env = ContractEnv::new();
    for (name, expr) in binds {
        if let Some(c) = eval_contract(expr, &env, i) {
            env.insert(name.to_string(), c);
        }
    }
    env
}

/// The C§9 second pass (plan T2.4). Bindings that failed in-order evaluation are
/// re-evaluated **jointly**, with every failed name bound to [`Contract::Ref`] —
/// this is the whole mechanism behind *"recursive contracts are ordinary named
/// bindings mentioning themselves or their group"*: no special form, and source
/// order is immaterial at the static layer. Exactly two passes, never an
/// iteration: a binding that is not a contract under Ref-seeding stays a runtime
/// binding.
///
/// Only definitions whose `Ref`s stay within the surviving set are kept (a
/// reference to a name that never evaluates as a contract would dangle); the drop
/// loop is bounded by the shrinking set. The result is **checked for
/// admissibility** (C§9 §1: positivity + structural guardedness) — a definition
/// error rejects the *whole* group, because the members define each other: the
/// checker turns the error into a compile finding, and the oracle consumes only
/// admissible definitions (the recursive membership walk terminates only on
/// admissible groups).
pub fn eval_recursive_contract_bindings(
    failed: &[(String, Expr)],
    env: &ContractEnv,
    i: &mut Interner,
) -> Result<Vec<(String, Contract)>, super::recursive::DefError> {
    if failed.is_empty() {
        return Ok(Vec::new());
    }
    let mut seeded = env.clone();
    for (name, _) in failed {
        seeded.insert(name.clone(), Contract::Ref(name.clone()));
    }
    let mut defs: Vec<(String, Contract)> = failed
        .iter()
        .filter_map(|(n, x)| eval_contract(x, &seeded, i).map(|c| (n.clone(), c)))
        .collect();
    loop {
        let names: std::collections::HashSet<String> =
            defs.iter().map(|(n, _)| n.clone()).collect();
        let before = defs.len();
        defs.retain(|(_, c)| refs_within(c, &names));
        if defs.len() == before {
            break;
        }
    }
    if defs.is_empty() {
        return Ok(Vec::new());
    }
    super::recursive::admissible(&super::recursive::RecGroup::new(defs.iter().cloned()))?;
    Ok(defs)
}

/// Whether every [`Contract::Ref`] in `c` names a member of `names`.
fn refs_within(c: &Contract, names: &std::collections::HashSet<String>) -> bool {
    match c {
        Contract::Ref(name) => names.contains(name),
        other => contract_children(other)
            .iter()
            .all(|child| refs_within(child, names)),
    }
}

/// Whether `c` mentions a [`Contract::Ref`] anywhere — the test that routes a
/// consumer through the recursive-group machinery instead of the plain walkers
/// (which treat a bare `Ref` as denoting nothing).
pub fn mentions_ref(c: &Contract) -> bool {
    match c {
        Contract::Ref(_) => true,
        other => contract_children(other).iter().any(|ch| mentions_ref(ch)),
    }
}

/// The immediate contract children of a compound form (leaves yield nothing).
fn contract_children(c: &Contract) -> Vec<&Contract> {
    match c {
        Contract::Union(a, b)
        | Contract::Intersection(a, b)
        | Contract::Difference(a, b)
        | Contract::LengthRestricted(a, b) => vec![a, b],
        Contract::Record(fields) => fields.iter().map(|(_, v)| &**v).collect(),
        Contract::Tuple(elems) | Contract::Concat(elems) => elems.iter().map(|e| &**e).collect(),
        _ => Vec::new(),
    }
}
