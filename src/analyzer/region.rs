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
//! Scope: the single-parameter fragment with **instantiation over captures**
//! ([`region_table_in`]): case (a) — a supported comparison against a constant *or a
//! singleton capture* — is exact; case (b) — a bounded non-singleton capture — is the
//! finite operator transfer's may-region, never exact; case (c) (two-variable
//! relation) and case (d) are the total `Top`/non-exact fallback. Kernel-desugar note: `&&`/`||`/`!` are
//! *Matches*, not operators, so compound and negated guards currently read as case (d)
//! (`Top`, non-exact — sound); a `?:` chain nests, so its else-arm result is a `Match`
//! the body check recurses into rather than a flattened row.

use crate::analyzer::{TypeEnv, pattern_contract};
use crate::ast::{BindingRef, Expr, Match, MatchItem, Pat, PatElem, PatField, PrimOp, Ref};
use crate::contract::{Contract, ContractEnv, Verdict, disjoint, subcontract};
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
    /// The arm's guard, as written, with what its **arrival set** needs: the guard
    /// runs for every input that reaches this row and matches its pattern, so its
    /// own operation demands and its strict Boolean tested seat (E10) are body
    /// demands like any other — the T3.1 "guards' own path demands".
    pub guard: Option<GuardSeat>,
}

/// A guard expression's demand seat (see [`Row::guard`]).
#[derive(Clone, Debug)]
pub struct GuardSeat {
    pub expr: Expr,
    /// The pattern's region alone (`Top` for a guard-only / bare-binder arm) —
    /// the guard's arrivals are `remaining ∩ pattern`, not the combined row region.
    pub pattern_region: Contract,
    /// Whether the pattern alone is exact — with the walk's cumulative exactness,
    /// this gates refutation evidence (RT-14: an over-approximate arrival set
    /// authorizes no refutation).
    pub pattern_exact: bool,
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
    /// **Definite arrival** (RT-14's witness bridge): true only when every earlier
    /// *selected* row was exact (the carried remainder is the true remainder — no
    /// input that stopped earlier is still inside it) **and** this row's own region
    /// is exact (membership in the region is membership in the arm). Refutations
    /// and completion-present claims are licensed only through a definite arrival;
    /// an indefinite one weakens them to the unproven voice.
    pub definite: bool,
}

/// The region table of `body` over the single parameter `param`. An arm-only `Match`
/// body yields one row per arm; any other body is a single unconditional row `(Top,
/// exact, body)`. A `Match` containing a preceding bind/statement is a block: projecting
/// only its arm results would erase that executable prefix and analyze those results in
/// an environment where the local names were never bound.
pub fn region_table(body: &Expr, param: &str, cenv: &ContractEnv, i: &mut Interner) -> Vec<Row> {
    region_table_in(body, param, &TypeEnv::new(), cenv, i)
}

thread_local! {
    /// RT-09 / C§13.4's **instance cache**: `(shape, annotated captured-environment
    /// contract tuple, named-contract environment) → instantiated region table`.
    /// The key is annotated, not coarse — two closures of one shape whose captures
    /// differ (`makeCounter(5)` vs `makeCounter(9)`) are different instances with
    /// different tables. Entries are deterministic facts of their complete key, so
    /// the table persists like the proven-fact cache. (The per-row grounding
    /// certificates C§13.4 lists alongside remain in their own caches.)
    static INSTANCE_TABLES: std::cell::RefCell<
        std::collections::HashMap<InstanceKey, std::rc::Rc<Vec<Row>>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct InstanceKey {
    shape: crate::analyzer::factcache::ShapeKey,
    captures: Vec<crate::intern::Interned<Contract>>,
    named: Vec<(String, crate::intern::Interned<Contract>)>,
}

/// The **instantiated region table of a closure instance** (C§12.3 layer 3), through
/// the RT-09 cache. Derives the single parameter, reads the capture environment, and
/// keys on `(shape, capture contracts in canonical slot order, named contracts)`;
/// a repeated query returns the same allocation. `None` when the closure does not
/// have a single plain parameter (the multi-parameter table has its own path and
/// joins the cache when its capture substitution lands).
pub(crate) fn instance_table(
    callee: &crate::value::ValueRef,
    cenv: &ContractEnv,
    i: &mut Interner,
) -> Option<(String, std::rc::Rc<Vec<Row>>)> {
    let closure = callee.as_closure()?;
    let function = callee.as_fn()?;
    let param = crate::analyzer::single_plain_param(&closure.lambda.params)?;
    let layer2 = crate::analyzer::factcache::layer2(callee)?;
    let caps = crate::analyzer::safety::capture_env(callee);
    let captures: Vec<crate::intern::Interned<Contract>> = function
        .free_vars()
        .iter()
        .filter(|name| !layer2.siblings.contains(*name))
        .map(|name| {
            let c = caps.get(name).map(|a| a.erase(i)).unwrap_or(Contract::Top);
            i.contract(c)
        })
        .collect();
    let mut named: Vec<(String, crate::intern::Interned<Contract>)> = cenv
        .iter()
        .map(|(name, c)| (name.clone(), i.contract(c.clone())))
        .collect();
    named.sort_by(|a, b| a.0.cmp(&b.0));
    let key = InstanceKey {
        shape: layer2.shape,
        captures,
        named,
    };
    if let Some(hit) = INSTANCE_TABLES.with(|t| t.borrow().get(&key).cloned()) {
        return Some((param, hit));
    }
    let table = std::rc::Rc::new(region_table_in(
        &closure.lambda.body,
        &param,
        &caps,
        cenv,
        i,
    ));
    INSTANCE_TABLES.with(|t| t.borrow_mut().insert(key, table.clone()));
    Some((param, table))
}

thread_local! {
    /// RT-09's multi-parameter twin — same key discipline, its own value type.
    static INSTANCE_TABLES_MULTI: std::cell::RefCell<
        std::collections::HashMap<InstanceKey, std::rc::Rc<Vec<RowN>>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The instantiated **multi-parameter** table of a closure instance, through the
/// RT-09 cache — flat plain parameters only (destructuring stays whole-body).
pub(crate) fn instance_table_multi(
    callee: &crate::value::ValueRef,
    cenv: &ContractEnv,
    i: &mut Interner,
) -> Option<(Vec<String>, std::rc::Rc<Vec<RowN>>)> {
    let closure = callee.as_closure()?;
    let function = callee.as_fn()?;
    let params = flat_params(&closure.lambda.params)?;
    if params.len() < 2 {
        return None;
    }
    let layer2 = crate::analyzer::factcache::layer2(callee)?;
    let caps = crate::analyzer::safety::capture_env(callee);
    let captures: Vec<crate::intern::Interned<Contract>> = function
        .free_vars()
        .iter()
        .filter(|name| !layer2.siblings.contains(*name))
        .map(|name| {
            let c = caps.get(name).map(|a| a.erase(i)).unwrap_or(Contract::Top);
            i.contract(c)
        })
        .collect();
    let mut named: Vec<(String, crate::intern::Interned<Contract>)> = cenv
        .iter()
        .map(|(name, c)| (name.clone(), i.contract(c.clone())))
        .collect();
    named.sort_by(|a, b| a.0.cmp(&b.0));
    let key = InstanceKey {
        shape: layer2.shape,
        captures,
        named,
    };
    if let Some(hit) = INSTANCE_TABLES_MULTI.with(|t| t.borrow().get(&key).cloned()) {
        return Some((params, hit));
    }
    let table = std::rc::Rc::new(region_table_multi_in(
        &closure.lambda.body,
        &params,
        &caps,
        i,
    )?);
    INSTANCE_TABLES_MULTI.with(|t| t.borrow_mut().insert(key, table.clone()));
    Some((params, table))
}

/// The **instantiated** region table (C§12.3 layer 3): guards are read after
/// substituting the instance's capture contracts — `caps` — per the regionalization
/// law. A singleton capture is case (a)'s constant (exact); a bounded non-singleton
/// capture feeds case (b)'s finite operator transfer (may-reach, never exact);
/// everything else stays the total case-(d) fallback.
pub fn region_table_in(
    body: &Expr,
    param: &str,
    caps: &TypeEnv,
    cenv: &ContractEnv,
    i: &mut Interner,
) -> Vec<Row> {
    match body {
        Expr::Match(m) if m.items.iter().all(|item| matches!(item, MatchItem::Arm(_))) => {
            region_rows(m, param, caps, cenv, i)
        }
        other => vec![Row {
            binder: None,
            region: Contract::Top,
            exact: true,
            result: other.clone(),
            guard: None,
        }],
    }
}

fn region_rows(
    m: &Match,
    param: &str,
    caps: &TypeEnv,
    cenv: &ContractEnv,
    i: &mut Interner,
) -> Vec<Row> {
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
            Some(g) => regionalize_guard_in(g, guard_param, caps, i),
            None => (Contract::Top, true),
        };
        rows.push(Row {
            region: intersect(pr.clone(), gr, i),
            exact: pe && ge,
            result: arm.result.clone(),
            binder: match (&arm.pattern, patterns_on_param) {
                (Some(Pat::Bind(alias)), true) => Some(alias.clone()),
                _ => None,
            },
            guard: arm.guard.as_ref().map(|g| GuardSeat {
                expr: g.clone(),
                pattern_region: pr,
                pattern_exact: pe,
            }),
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
/// One step of the **ordered remainder walk** (§3), as seen by a consumer. The
/// engine owns the discipline — candidate computation, proven-emptiness, exact
/// consumption with the collapse rule, and **prior-arrival definiteness** (RT-14:
/// true while every earlier *selected* row was exact, so the carried remainder is
/// the true remainder; a row's own exactness is the consumer's facet to combine).
pub(crate) struct Visit<'a> {
    pub row: &'a Row,
    /// The remainder *arriving at* this row (before its consumption).
    pub remaining: &'a Contract,
    /// `remaining ∩ region` — this row's candidate.
    pub candidate: Contract,
    /// The candidate is proven empty (the row is not selected).
    pub empty: bool,
    /// Every earlier selected row was exact.
    pub definite_prior: bool,
}

/// The single-parameter walk engine (Tier-4: the one implementation of the
/// consumption discipline — `select`, the guard demands, coverage remainders, and
/// the unreachable-arm diagnostic are all thin consumers). Returns the final
/// remainder. An **exact** row consumes its region — collapsing outright when the
/// remainder is contained (a `Difference` the walkers cannot see through would
/// keep dead later rows selectable); a non-exact row consumes nothing, and if
/// selected it makes every later arrival indefinite. An unselected row (proven-
/// empty candidate) stops nothing: its region over-approximates its acceptance,
/// so emptiness is decisive and definiteness survives.
pub(crate) fn walk_rows(
    table: &[Row],
    domain: &Contract,
    i: &mut Interner,
    mut visit: impl FnMut(&mut Interner, Visit),
) -> Contract {
    let mut remaining = domain.clone();
    let mut definite = true;
    for row in table {
        let candidate = intersect(remaining.clone(), row.region.clone(), i);
        let empty = disjoint(&remaining, &row.region);
        visit(
            i,
            Visit {
                row,
                remaining: &remaining,
                candidate,
                empty,
                definite_prior: definite,
            },
        );
        if row.exact {
            if !empty {
                remaining = if matches!(subcontract(&remaining, &row.region, i), Verdict::Proven) {
                    Contract::Bottom
                } else {
                    Contract::difference(remaining, row.region.clone(), i)
                };
            }
        } else if !empty {
            definite = false;
        }
    }
    remaining
}

pub fn select(table: &[Row], arg_domain: &Contract, i: &mut Interner) -> Vec<Selected> {
    if let Contract::Equals(v) = arg_domain {
        let mut out = Vec::new();
        let mut definite = true;
        for row in table {
            if row.region.contains(v) {
                out.push(Selected {
                    binder: row.binder.clone(),
                    region: Contract::Equals(v.clone()),
                    exact: row.exact,
                    result: row.result.clone(),
                    definite: definite && row.exact,
                });
                if row.exact {
                    break; // an exact row containing the point consumes it
                }
                // A non-exact row may or may not capture the point at runtime —
                // every later arrival is indefinite.
                definite = false;
            }
        }
        return out;
    }

    let mut out = Vec::new();
    walk_rows(table, arg_domain, i, |_, v| {
        if !v.empty {
            out.push(Selected {
                binder: v.row.binder.clone(),
                region: v.candidate,
                exact: v.row.exact,
                result: v.row.result.clone(),
                definite: v.definite_prior && v.row.exact,
            });
        }
    });
    out
}

// ── Guard regionalization (§2 cases a/d) ──────────────────────────────────────

/// Forward-read a guard as a `(region, exact)` constraint on `param`. Case (a): a
/// supported comparison of `param` against a constant number → exact. Case (d):
/// anything else → `Top`, non-exact (total fallback).
pub(crate) fn regionalize_guard(g: &Expr, param: &str, i: &mut Interner) -> (Contract, bool) {
    regionalize_guard_in(g, param, &TypeEnv::new(), i)
}

/// [`regionalize_guard`] with the instance's capture contracts substituted (the
/// regionalization law's cases (a)/(b); see [`region_table_in`]).
pub(crate) fn regionalize_guard_in(
    g: &Expr,
    param: &str,
    caps: &TypeEnv,
    i: &mut Interner,
) -> (Contract, bool) {
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
        let (ra, ea) = regionalize_guard_in(a, param, caps, i);
        let (rb, eb) = regionalize_guard_in(&first.result, param, caps, i);
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
    // The leaf reading, after capture substitution. Case (a): the operand is a
    // literal, or a capture whose contract is a singleton number — exact. Case (b):
    // a capture with a bounded numeric contract — the finite operator transfer,
    // never exact. Anything else — including a sibling parameter (case (c)) — is
    // the total case-(d) fallback.
    let (operand, flipped) = if is_param(&args[0], param) {
        (guard_operand(&args[1], caps, i), false)
    } else if is_param(&args[1], param) {
        (guard_operand(&args[0], caps, i), true)
    } else {
        return opaque;
    };
    match operand {
        GuardOperand::Const(v) => match cmp_region(*op, &v, flipped, i) {
            Some(region) => (region, true),
            None => opaque,
        },
        GuardOperand::Bounded(c) => (bounded_capture_region(*op, &c, flipped, i), false),
        GuardOperand::Opaque => opaque,
    }
}

/// A guard operand after capture substitution (the regionalization law).
enum GuardOperand {
    /// A literal, or a capture proven to be exactly this number — case (a).
    Const(Rational),
    /// A capture with a (possibly bounded) numeric contract — case (b).
    Bounded(Contract),
    /// Everything else — cases (c)/(d).
    Opaque,
}

fn guard_operand(e: &Expr, caps: &TypeEnv, i: &mut Interner) -> GuardOperand {
    if let Some(v) = const_num(e) {
        return GuardOperand::Const(v);
    }
    if let Expr::Ref(Ref::Immutable(BindingRef::Name(name))) = e
        && let Some(annotated) = caps.get(name)
    {
        let c = annotated.erase(i);
        if let Contract::Equals(v) = &c
            && let Some(n) = v.as_number()
        {
            return GuardOperand::Const(n.clone());
        }
        return GuardOperand::Bounded(c);
    }
    GuardOperand::Opaque
}

/// Case (b)'s **finite operator transfer** (region-table spec §2, patch 0.3.1 — a
/// fixed lookup, not a solver): for a capture with `≤/≥/Range`-shaped numeric
/// bounds, `n < limit` is governed by the capture's **upper** endpoint, `n > limit`
/// by its **lower**, `n == limit` projects the capture's own possible-value
/// contract onto `n`, and `n != limit` is `Top` (for any `n` some represented
/// `limit` may differ). All results are may-regions — never exact — and an
/// endpoint the contract does not expose widens to `Top` (case (d)'s outcome).
fn bounded_capture_region(
    op: PrimOp,
    capture: &Contract,
    flipped: bool,
    i: &mut Interner,
) -> Contract {
    use crate::contract::numeric::{Bound, num_abs};
    let Some(abs) = num_abs(capture) else {
        return Contract::Top;
    };
    // `v OP limit` mirrors to `limit OP' v` — reuse the comparison mirror.
    let op = if flipped { mirror(op) } else { op };
    let upper = || match &abs.iv.high {
        Bound::Incl(u) => Some((u.clone(), true)),
        Bound::Excl(u) => Some((u.clone(), false)),
        Bound::Unbounded => None,
    };
    let lower = || match &abs.iv.low {
        Bound::Incl(l) => Some((l.clone(), true)),
        Bound::Excl(l) => Some((l.clone(), false)),
        Bound::Unbounded => None,
    };
    let _ = i;
    match op {
        PrimOp::Lt => match upper() {
            Some((u, _)) => Contract::Less(u),
            None => Contract::Top,
        },
        PrimOp::Le => match upper() {
            Some((u, true)) => Contract::LessEq(u),
            Some((u, false)) => Contract::Less(u),
            None => Contract::Top,
        },
        PrimOp::Gt => match lower() {
            Some((l, _)) => Contract::Greater(l),
            None => Contract::Top,
        },
        PrimOp::Ge => match lower() {
            Some((l, true)) => Contract::GreaterEq(l),
            Some((l, false)) => Contract::Greater(l),
            None => Contract::Top,
        },
        // `n == limit`: the capture's own possible values, projected onto `n`.
        PrimOp::Eq => capture.clone(),
        // `n != limit`: for any `n`, some represented `limit` may differ.
        PrimOp::Ne => Contract::Top,
        _ => Contract::Top,
    }
}

/// The comparison with its operands swapped (`v OP p` ⟺ `p OP' v`).
fn mirror(op: PrimOp) -> PrimOp {
    match op {
        PrimOp::Lt => PrimOp::Gt,
        PrimOp::Le => PrimOp::Ge,
        PrimOp::Gt => PrimOp::Lt,
        PrimOp::Ge => PrimOp::Le,
        other => other,
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

/// Adapter for the canonical simplifying conjunction (Tier-4: one implementation).
fn intersect(a: Contract, b: Contract, i: &mut Interner) -> Contract {
    Contract::intersect(a, b, i)
}

// ── §5 — the argument-tuple projection (multi-parameter rows) ─────────────────

/// A multi-parameter row (§5): one region per parameter position — a constraint on a
/// bound name becomes a contract at its position, `Top` elsewhere — plus the count of
/// constrained positions. Consumption is positionwise, which is set-exact only when a
/// row constrains at most one position (the complement of a product is not a product);
/// wider rows select but never consume — uncertainty selects (E9).
#[derive(Clone, Debug)]
pub struct RowN {
    pub regions: Vec<Contract>,
    pub exact: bool,
    pub result: Expr,
    pub constrained: usize,
    /// The arm's guard, as written (multi-parameter arms are guard-only) — see
    /// [`Row::guard`].
    pub guard: Option<Expr>,
}

/// A selected multi-parameter row: the per-position **effective** regions
/// (`remaining ∩ region`), and the row's exactness for the RT-14 discipline.
#[derive(Clone, Debug)]
pub struct SelectedN {
    pub regions: Vec<Contract>,
    pub exact: bool,
    pub result: Expr,
    /// Definite arrival — see [`Selected::definite`]; same walk discipline.
    pub definite: bool,
}

/// The flat parameter names of a plain tuple pattern (`(a, b)` → `["a", "b"]`), or
/// `None` for destructuring/rests — those stay on the whole-body path.
pub fn flat_params(params: &Pat) -> Option<Vec<String>> {
    let Pat::Tuple(elems) = params else {
        return None;
    };
    elems
        .iter()
        .map(|e| match e {
            PatElem::Pat(Pat::Bind(n)) => Some(n.clone()),
            _ => None,
        })
        .collect()
}

/// The §5 table for a guarded (scrutinee-less) multi-parameter body — the ternary/
/// `when` chain shape. Pattern-arm bodies stay single-parameter territory (v1).
pub fn region_table_multi(body: &Expr, params: &[String], i: &mut Interner) -> Option<Vec<RowN>> {
    region_table_multi_in(body, params, &TypeEnv::new(), i)
}

/// [`region_table_multi`] with the instance's capture contracts substituted — the
/// same regionalization law as the single-parameter [`region_table_in`].
pub fn region_table_multi_in(
    body: &Expr,
    params: &[String],
    caps: &TypeEnv,
    i: &mut Interner,
) -> Option<Vec<RowN>> {
    let Expr::Match(m) = body else {
        return None;
    };
    if m.scrutinee.is_some() {
        return None;
    }
    let mut rows = Vec::new();
    for item in &m.items {
        let MatchItem::Arm(arm) = item else {
            return None; // binds/statements make this a block — whole-body territory
        };
        if arm.pattern.is_some() {
            return None;
        }
        let (regions, exact) = match &arm.guard {
            Some(g) => regionalize_guard_positional(g, params, caps, i),
            None => (vec![Contract::Top; params.len()], true),
        };
        let constrained = regions
            .iter()
            .filter(|r| !matches!(r, Contract::Top))
            .count();
        rows.push(RowN {
            regions,
            exact,
            result: arm.result.clone(),
            constrained,
            guard: arm.guard.clone(),
        });
    }
    Some(rows)
}

/// A guard's positionwise regionalization: each conjunct lands at its parameter's
/// position; positions the guard does not mention stay `Top`.
fn regionalize_guard_positional(
    g: &Expr,
    params: &[String],
    caps: &TypeEnv,
    i: &mut Interner,
) -> (Vec<Contract>, bool) {
    // The desugared conjunction distributes positionwise.
    if let Expr::Match(m) = g
        && m.scrutinee.is_none()
        && let [MatchItem::Arm(first), MatchItem::Arm(second)] = &m.items[..]
        && first.pattern.is_none()
        && second.pattern.is_none()
        && second.guard.is_none()
        && matches!(&second.result, Expr::Const(v) if v.as_boolean() == Some(false))
        && let Some(a) = &first.guard
    {
        let (ra, ea) = regionalize_guard_positional(a, params, caps, i);
        let (rb, eb) = regionalize_guard_positional(&first.result, params, caps, i);
        let regions = ra
            .into_iter()
            .zip(rb)
            .map(|(x, y)| intersect(x, y, i))
            .collect();
        return (regions, ea && eb);
    }
    // A single-parameter form lands at the one position that mentions it. Sibling
    // parameters are not in `caps`, so a two-parameter relation stays case (c).
    for (idx, p) in params.iter().enumerate() {
        let (region, exact) = regionalize_guard_in(g, p, caps, i);
        if !matches!(region, Contract::Top) {
            let mut regions = vec![Contract::Top; params.len()];
            regions[idx] = region;
            return (regions, exact);
        }
    }
    (vec![Contract::Top; params.len()], false)
}

/// The §3 walk over per-position domains: a row is selected when **every** position's
/// `remaining ∩ region` is not proven empty; an exact row consumes only when it
/// constrains at most one position (subtracting there — or everything, for the
/// unconditional remainder arm).
/// The per-position domains left uncovered after the multi-parameter walk — the same
/// remaining-update discipline as [`select_multi`] (single-position consumption only;
/// product complements are not products). All-`Bottom` means the rows exhaust the
/// domain product, which is what a completion claim's coverage check needs.
pub(crate) fn remaining_multi(
    table: &[RowN],
    domains: &[Contract],
    i: &mut Interner,
) -> Vec<Contract> {
    walk_rows_multi(table, domains, i, |_, _| {})
}

/// The multi-parameter walk step — positionwise remainder, same discipline.
pub(crate) struct VisitN<'a> {
    pub row: &'a RowN,
    pub remaining: &'a [Contract],
    /// Some position's candidate is proven empty (the row is not selected).
    pub empty: bool,
    pub definite_prior: bool,
}

/// The multi-parameter walk engine (§5): consumption is positionwise, set-exact
/// only when a row constrains at most one position — an unconditional exact row
/// takes everything, a one-position exact row consumes at its position, wider
/// rows select but never consume.
pub(crate) fn walk_rows_multi(
    table: &[RowN],
    domains: &[Contract],
    i: &mut Interner,
    mut visit: impl FnMut(&mut Interner, VisitN),
) -> Vec<Contract> {
    let mut remaining: Vec<Contract> = domains.to_vec();
    let mut definite = true;
    for row in table {
        let empty = remaining
            .iter()
            .zip(&row.regions)
            .any(|(rem, reg)| disjoint(rem, reg));
        visit(
            i,
            VisitN {
                row,
                remaining: &remaining,
                empty,
                definite_prior: definite,
            },
        );
        if row.exact && row.constrained == 0 {
            if !empty {
                for rem in &mut remaining {
                    *rem = Contract::Bottom; // the unconditional arm takes everything left
                }
            }
        } else if row.exact && row.constrained == 1 {
            if !empty {
                let p = row
                    .regions
                    .iter()
                    .position(|r| !matches!(r, Contract::Top))
                    .expect("one constrained position");
                remaining[p] = if matches!(
                    subcontract(&remaining[p], &row.regions[p], i),
                    Verdict::Proven
                ) {
                    Contract::Bottom
                } else {
                    Contract::difference(remaining[p].clone(), row.regions[p].clone(), i)
                };
            }
        } else if !empty {
            definite = false;
        }
    }
    remaining
}

pub fn select_multi(table: &[RowN], domains: &[Contract], i: &mut Interner) -> Vec<SelectedN> {
    let mut out = Vec::new();
    walk_rows_multi(table, domains, i, |i, v| {
        if !v.empty {
            let effective: Vec<Contract> = v
                .remaining
                .iter()
                .zip(&v.row.regions)
                .map(|(rem, reg)| intersect(rem.clone(), reg.clone(), i))
                .collect();
            out.push(SelectedN {
                regions: effective,
                exact: v.row.exact,
                result: v.row.result.clone(),
                definite: v.definite_prior && v.row.exact,
            });
        }
    });
    out
}
