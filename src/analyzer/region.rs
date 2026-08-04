//! Region-table computation — `next-region-table-specification-v0-3.md` (v0.3).
//!
//! Branch **reachability**: a lambda body's control flow sorts a parameter's possible
//! values into an ordered table of `(region, exact, result)` rows, read forward from
//! the arms' guards/patterns (§2/§4), plus the **selection walk** (§3) that consumes
//! them — an **exact** row subtracts its region from the remaining domain, an uncertain
//! row consumes nothing. This is reachability only; **not** `InferredAcceptedDomain`
//! (§6 — dissolved: the safe-input set is the outcome of the body check that *consumes*
//! this table, errata E-6/E-7/E-8).
//!
//! Scope of this increment: the **capture-free, single-parameter** fragment — guards
//! mention only the parameter and constants. Case (a) (a supported comparison against a
//! constant → exact) and case (d) (the total `Top`/non-exact fallback) are here; case
//! (b) (comparison against a non-singleton capture) and case (c) (two-variable relation)
//! land with instantiation over captures. Kernel-desugar note: `&&`/`||`/`!` are
//! *Matches*, not operators, so compound and negated guards currently read as case (d)
//! (`Top`, non-exact — sound); a `?:` chain nests, so its else-arm result is a `Match`
//! the body check recurses into rather than a flattened row.

use crate::analyzer::pattern_contract;
use crate::ast::{BindingRef, Expr, Match, MatchItem, Pat, PatElem, PatField, PrimOp, Ref};
use crate::contract::{Contract, ContractEnv, disjoint};
use crate::interner::Interner;
use crate::rational::Rational;

/// A region-table row (§1): where an input may go, its exactness, and the arm's result.
#[derive(Clone, Debug)]
pub struct Row {
    /// The forward-read region over the parameter (pattern ∩ guard).
    pub region: Contract,
    /// `true` iff every contributing leaf is exact — only exact rows consume (§3).
    pub exact: bool,
    pub result: Expr,
    /// A bare-binder pattern's name (`x :: { k when … => … }` — `k` aliases the
    /// parameter in this row); consumers bind it beside the parameter.
    pub binder: Option<String>,
}

/// A selected row's **effective** candidate region (`remaining ∩ region` at selection),
/// its result, and its `exact` bit — the output of the [`select`] walk. `exact` carries
/// the witness discipline downstream (RT-14): only a *definitely reached* row (this row
/// exact **and** every earlier selected row exact) may refute; a may-region row's trap
/// is at most unproven.
#[derive(Clone, Debug)]
pub struct Selected {
    pub region: Contract,
    pub exact: bool,
    pub result: Expr,
    /// The row's parameter-alias binder, if any (see [`Row::binder`]).
    pub binder: Option<String>,
}

/// The region table of `body` over the single parameter `param`. An arm-only `Match`
/// body yields one row per arm; any other body is a single unconditional row `(Top,
/// exact, body)`. A `Match` containing a preceding bind/statement is a block: projecting
/// only its arm results would erase that executable prefix and analyze those results in
/// an environment where the local names were never bound.
pub fn region_table(body: &Expr, param: &str, cenv: &ContractEnv, i: &mut Interner) -> Vec<Row> {
    match body {
        Expr::Match(m) if m.items.iter().all(|item| matches!(item, MatchItem::Arm(_))) => {
            region_rows(m, param, cenv, i)
        }
        other => vec![Row {
            binder: None,
            region: Contract::Top,
            exact: true,
            result: other.clone(),
        }],
    }
}

fn region_rows(m: &Match, param: &str, cenv: &ContractEnv, i: &mut Interner) -> Vec<Row> {
    // Patterns match the scrutinee; they regionalize the parameter only when the
    // scrutinee *is* the parameter (or is absent — a `?:`/tested match carries guards,
    // not patterns). Otherwise the pattern is opaque on the parameter.
    let patterns_on_param = match &m.scrutinee {
        None => true,
        Some(s) => is_param(s, param),
    };
    let mut rows = Vec::new();
    for item in &m.items {
        let MatchItem::Arm(arm) = item else { continue };
        let (pr, pe) = match (&arm.pattern, patterns_on_param) {
            (Some(p), true) => (pattern_contract(p, cenv, i), pattern_exact(p)),
            (Some(_), false) => (Contract::Top, false),
            (None, _) => (Contract::Top, true),
        };
        // A bare-binder pattern over the parameter scrutinee aliases the parameter:
        // `x :: { k when k >= 0 => … }` guards on `k`, which *is* `x` in that arm.
        let guard_param: &str = match (&arm.pattern, patterns_on_param) {
            (Some(Pat::Bind(alias)), true) => alias,
            _ => param,
        };
        let (gr, ge) = match &arm.guard {
            Some(g) => regionalize_guard(g, guard_param, i),
            None => (Contract::Top, true),
        };
        rows.push(Row {
            region: intersect(pr, gr, i),
            exact: pe && ge,
            result: arm.result.clone(),
            binder: match (&arm.pattern, patterns_on_param) {
                (Some(Pat::Bind(alias)), true) => Some(alias.clone()),
                _ => None,
            },
        });
    }
    rows
}

/// The **selection walk** (§3). Carry `remaining` (initially the argument domain); each
/// row is selected when `remaining ∩ region` is not proven empty; an **exact** row then
/// subtracts its region from `remaining`, a non-exact row consumes nothing. First-match
/// is the walk, never baked into the table (§2's no-pre-carving).
///
/// A **known (singleton) argument** takes a precise fast path (§3: "when the exact
/// runtime value is known … the walk resolves to the earliest satisfied [exact] row")
/// via denotational membership — this avoids the accumulated-`Difference` imprecision
/// the general algebra cannot always simplify. Open domains use the general walk, where
/// over-selection is sound (extra branches are carried and joined downstream).
pub fn select(table: &[Row], arg_domain: &Contract, i: &mut Interner) -> Vec<Selected> {
    if let Contract::Equals(v) = arg_domain {
        let mut out = Vec::new();
        for row in table {
            if row.region.contains(v) {
                out.push(Selected {
                    binder: row.binder.clone(),
                    region: Contract::Equals(v.clone()),
                    exact: row.exact,
                    result: row.result.clone(),
                });
                if row.exact {
                    break; // an exact row containing the point consumes it
                }
            }
        }
        return out;
    }

    let mut remaining = arg_domain.clone();
    let mut out = Vec::new();
    for row in table {
        if !disjoint(&remaining, &row.region) {
            out.push(Selected {
                binder: row.binder.clone(),
                region: intersect(remaining.clone(), row.region.clone(), i),
                exact: row.exact,
                result: row.result.clone(),
            });
        }
        if row.exact {
            remaining = Contract::difference(remaining, row.region.clone(), i);
        }
    }
    out
}

// ── Guard regionalization (§2 cases a/d) ──────────────────────────────────────

/// Forward-read a guard as a `(region, exact)` constraint on `param`. Case (a): a
/// supported comparison of `param` against a constant number → exact. Case (d):
/// anything else → `Top`, non-exact (total fallback).
fn regionalize_guard(g: &Expr, param: &str, i: &mut Interner) -> (Contract, bool) {
    let opaque = (Contract::Top, false);
    // The desugared conjunction `a && b` — `Match(∅, [Arm(guard: a, b), Arm(false)])`
    // (E10) — regionalizes to the intersection, exact iff both conjuncts are.
    if let Expr::Match(m) = g
        && m.scrutinee.is_none()
        && let [MatchItem::Arm(first), MatchItem::Arm(second)] = &m.items[..]
        && first.pattern.is_none()
        && second.pattern.is_none()
        && second.guard.is_none()
        && matches!(&second.result, Expr::Const(v) if v.as_boolean() == Some(false))
        && let Some(a) = &first.guard
    {
        let (ra, ea) = regionalize_guard(a, param, i);
        let (rb, eb) = regionalize_guard(&first.result, param, i);
        return (intersect(ra, rb, i), ea && eb);
    }
    let Expr::PrimOp { op, args } = g else {
        return opaque;
    };
    if args.len() != 2 {
        return opaque;
    }
    // The integer test `param % 1 == 0` → `Mod(1, 0)`, exactly: a truncated remainder
    // by 1 is zero iff the operand is an integer, negatives included. Wider moduli
    // disagree with floored `Mod` membership on negatives and stay case (d).
    if *op == PrimOp::Eq
        && let Some(region) = integer_test(&args[0], &args[1], param)
    {
        return (region, true);
    }
    let Some((v, flipped)) = param_vs_const(&args[0], &args[1], param) else {
        return opaque;
    };
    match cmp_region(*op, &v, flipped, i) {
        Some(region) => (region, true),
        None => opaque,
    }
}

/// `param % 1 == 0` (either operand order) — the sound integer-lattice test.
fn integer_test(a: &Expr, b: &Expr, param: &str) -> Option<Contract> {
    let is_rem_one = |e: &Expr| {
        matches!(e, Expr::PrimOp { op: PrimOp::Rem, args }
            if args.len() == 2
                && is_param(&args[0], param)
                && matches!(const_num(&args[1]), Some(n) if n == Rational::from(1)))
    };
    let is_zero = |e: &Expr| matches!(const_num(e), Some(v) if v == Rational::from(0));
    ((is_rem_one(a) && is_zero(b)) || (is_rem_one(b) && is_zero(a))).then(|| Contract::Mod {
        n: num_bigint::BigInt::from(1),
        r: num_bigint::BigInt::from(0),
    })
}

/// `(value, flipped)` when exactly one operand is `param` and the other a constant
/// number; `flipped` when the constant is on the left (`const OP param`).
fn param_vs_const(a: &Expr, b: &Expr, param: &str) -> Option<(Rational, bool)> {
    if is_param(a, param) {
        return const_num(b).map(|v| (v, false));
    }
    if is_param(b, param) {
        return const_num(a).map(|v| (v, true));
    }
    None
}

/// The region of `param OP v` (or `v OP param` when `flipped`), for the supported
/// direct comparison forms; `None` for an unsupported operator (→ case d).
fn cmp_region(op: PrimOp, v: &Rational, flipped: bool, i: &mut Interner) -> Option<Contract> {
    let eq = Contract::Range(v.clone(), v.clone());
    Some(match (op, flipped) {
        (PrimOp::Eq, _) => eq,
        (PrimOp::Ne, _) => Contract::difference(Contract::Top, eq, i),
        (PrimOp::Lt, false) | (PrimOp::Gt, true) => Contract::Less(v.clone()),
        (PrimOp::Le, false) | (PrimOp::Ge, true) => Contract::LessEq(v.clone()),
        (PrimOp::Gt, false) | (PrimOp::Lt, true) => Contract::Greater(v.clone()),
        (PrimOp::Ge, false) | (PrimOp::Le, true) => Contract::GreaterEq(v.clone()),
        _ => return None,
    })
}

// ── Pattern exactness (§4) ────────────────────────────────────────────────────

/// A pattern's contract translation is exact unless it carries a rest (the length is
/// then a may-region). (Non-singleton pins are the other non-exact case — `^name`
/// isn't a kernel `Pat` variant here, so no-rest suffices for this fragment.)
fn pattern_exact(p: &Pat) -> bool {
    match p {
        Pat::Const(_) | Pat::Wild | Pat::Bind(_) | Pat::Contract(_) => true,
        Pat::Tuple(elems) => elems.iter().all(|e| match e {
            PatElem::Rest(_) => false,
            PatElem::Pat(p) => pattern_exact(p),
        }),
        Pat::Record { fields, .. } => fields.iter().all(|f| match f {
            PatField::Rest(_) => false,
            PatField::Field { pat, .. } => pattern_exact(pat),
        }),
    }
}

// ── Small helpers ─────────────────────────────────────────────────────────────

fn is_param(e: &Expr, param: &str) -> bool {
    matches!(e, Expr::Ref(Ref::Immutable(BindingRef::Name(n))) if n == param)
}

fn const_num(e: &Expr) -> Option<Rational> {
    match e {
        Expr::Const(v) => v.as_number().cloned(),
        _ => None,
    }
}

/// `Top ∩ x = x`; otherwise the raw `Intersection` (kept unsimplified — the algebra's
/// `disjoint`/`subcontract` do the reasoning the walk needs).
fn intersect(a: Contract, b: Contract, i: &mut Interner) -> Contract {
    match (a, b) {
        (Contract::Top, x) | (x, Contract::Top) => x,
        (a, b) => Contract::intersection(a, b, i),
    }
}
