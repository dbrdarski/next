//! Static evaluation of **contract expressions** (Compendium C§12.2 / §292).
//!
//! Contract constructors (`Range`, `Mod`, `Equals`, `Union`, `Difference`,
//! `HasField`, `Geo`, …) are predeclared prelude names, and a named contract is an
//! ordinary binding of a contract expression (`Percent = Range(0, 100)`). This
//! module evaluates such an expression — a kernel [`Expr`] built from those
//! constructor applications, prelude Kind names, structural tuple/record literals,
//! and references to earlier named contracts — into a [`Contract`].
//!
//! **Scope:** non-recursive named contracts (a reference resolves to its already
//! evaluated definition). Recursive/mutual source contracts — which would build a
//! [`super::RecGroup`] and carry `Contract::Ref` — are the next increment; here a
//! self/forward reference simply fails to resolve (`None`). Numeric/string
//! arguments must be literals (`Const`); computed contract arguments are owed
//! (C§12.2 static evaluation of arbitrary expressions).

use std::collections::HashMap;

use super::{Contract, Kind};
use crate::ast::{Arg, BindingRef, Element, Expr, Field, Ref};
use crate::value::ValueRef;

/// A name → named-contract binding environment.
pub type ContractEnv = HashMap<String, Contract>;

/// Statically evaluate a contract expression, or `None` if `expr` is not a
/// recognized contract form.
pub fn eval_contract(expr: &Expr, env: &ContractEnv) -> Option<Contract> {
    match expr {
        Expr::Ref(Ref::Immutable(BindingRef::Name(n))) => ref_contract(n, env),
        Expr::Apply { callee, args } => apply_contract(callee, args, env),
        // A tuple literal of contracts denotes a tuple contract (no spreads yet).
        Expr::TupleCons(elems) => {
            let mut parts = Vec::with_capacity(elems.len());
            for el in elems {
                match el {
                    Element::Expr(e) => parts.push(eval_contract(e, env)?),
                    Element::Spread(_) => return None,
                }
            }
            Some(Contract::Tuple(parts))
        }
        // A record literal of contracts denotes a record contract (static keys).
        Expr::RecordCons(fields) => {
            let mut pairs = Vec::with_capacity(fields.len());
            for f in fields {
                match f {
                    Field::Field { key, value } => pairs.push((key.clone(), eval_contract(value, env)?)),
                    _ => return None,
                }
            }
            Some(Contract::Record(pairs))
        }
        _ => None,
    }
}

/// A prelude Kind name, `Top`/`Bottom`/`Failure`, or a named contract.
fn ref_contract(name: &str, env: &ContractEnv) -> Option<Contract> {
    Some(match name {
        "Number" => Contract::Kind(Kind::Number),
        "String" => Contract::Kind(Kind::String),
        "Boolean" => Contract::Kind(Kind::Boolean),
        "Null" => Contract::Kind(Kind::Null),
        "Tuple" => Contract::Kind(Kind::Tuple),
        "Record" => Contract::Kind(Kind::Record),
        "Function" => Contract::Kind(Kind::Function),
        "Top" => Contract::Top,
        "Bottom" => Contract::Bottom,
        // The one prelude Failure shape (B6/E9): a record with `path` and `reason`.
        "Failure" => Contract::Intersection(
            Box::new(Contract::HasField("path".into())),
            Box::new(Contract::HasField("reason".into())),
        ),
        _ => return env.get(name).cloned(),
    })
}

fn apply_contract(callee: &Expr, args: &[Arg], env: &ContractEnv) -> Option<Contract> {
    let Expr::Ref(Ref::Immutable(BindingRef::Name(ctor))) = callee else { return None };
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
        ("Mod", [n, r]) => Some(Contract::Mod { n: int(n)?, r: int(r)? }),
        ("Geo", [b, r]) => Some(Contract::Geo { b: num(b)?, r: num(r)? }),
        ("Equals", [v]) => Some(Contract::Equals(konst(v)?)),
        ("HasField", [k]) => Some(Contract::HasField(string(k)?)),
        ("Union", [a, b]) => Some(Contract::Union(bx(eval_contract(a, env)?), bx(eval_contract(b, env)?))),
        ("Intersection", [a, b]) => {
            Some(Contract::Intersection(bx(eval_contract(a, env)?), bx(eval_contract(b, env)?)))
        }
        ("Difference", [a, b]) => {
            Some(Contract::Difference(bx(eval_contract(a, env)?), bx(eval_contract(b, env)?)))
        }
        // `Tuple(A, B, …)` — a variadic tuple contract.
        ("Tuple", elems) => Some(Contract::Tuple(elems.iter().map(|e| eval_contract(e, env)).collect::<Option<_>>()?)),
        _ => None,
    }
}

fn bx(c: Contract) -> Box<Contract> {
    Box::new(c)
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
pub fn build_contract_env<'a>(binds: impl IntoIterator<Item = (&'a str, &'a Expr)>) -> ContractEnv {
    let mut env = ContractEnv::new();
    for (name, expr) in binds {
        if let Some(c) = eval_contract(expr, &env) {
            env.insert(name.to_string(), c);
        }
    }
    env
}
