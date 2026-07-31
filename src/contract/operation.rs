//! Operation transfer rules — `analyzeOperation` (Compendium C§7, C§16 obligation 3).
//!
//! Every primitive operation has one uniform rule shape:
//!
//! ```text
//! analyze_operation(op, [C₁ … Cₙ]) → { safety, output }
//! ```
//!
//! - **`safety`** is the operation's *own demand* — three-valued like a
//!   subcontract: [`OpSafety::Proven`] (no operand tuple in the inputs can trap),
//!   [`OpSafety::Refuted`] with a concrete witness tuple that *does* trap, or
//!   [`OpSafety::Unproven`]. Soundness is the invariant: `Proven` ⇒ the oracle
//!   never traps; `Refuted(t)` ⇒ the oracle traps on `t`.
//! - **`output`** over-approximates the *image* `{ op(v₁…vₙ) : vᵢ ∈ ⟦Cᵢ⟧ }` —
//!   every value the operation can actually produce is in `⟦output⟧`.
//!
//! Both halves are brute-tested in `tests.rs` against the oracle's value-level
//! primop semantics ([`crate::oracle::eval_prim`]) — the truth source. The proof
//! side uses [`subcontract`] to discharge numeric/string demands; the refutation
//! side samples operand tuples and asks the oracle whether they trap.
//!
//! ## How the rules are organised (three layers, not a 13×N×N grid)
//!
//! Read literally, "per-pair tables" (C§17) would be one arm per (op, form, form) —
//! but ~all of those arms say the same thing, because the numeric forms are
//! projections onto two facets. So:
//!
//! 1. **Algebraic plumbing, uniform across every operation** — `Indeterminate`
//!    propagation ([`with_indet_passthrough`]) and the total-division forms. Handled
//!    once, for all ops.
//! 2. **Exact fold** — all-singleton operands run through the oracle itself
//!    (`analyzer`'s constant-fold path), so exactness costs nothing here.
//! 3. **The leaf rules** ([`base_output`]) — ordered *specific → general* per
//!    operation: a form-preserving rule gets first refusal (Table C: `Geo × exact`
//!    stays `Geo`), then the numeric abstraction ([`super::numeric`], interval ×
//!    congruence) as the **total** fallback.
//!
//! The **audit** is the other way round: `operation_soundness_sweep` walks the full
//! matrix — every operation × every leaf form (with sign variants) — and checks each
//! result against the oracle. Soundness is proven exhaustively there; the
//! `rulebook_*` tests assert the precision claims, since returning `Kind(Number)`
//! everywhere would satisfy soundness alone.
//!
//! ## Deliberately unproven (documented incompleteness, C§17)
//!
//! Each yields a sound coarse answer rather than a silent miss:
//!
//! - **`Geo` beyond scaling** — `Geo + Geo`, `Geo + Range` are not geometric; the
//!   operand projects to its interval (bounded on the side `b` sits).
//! - **`Mod` through `×` by a non-constant**, and through `/`, `%`, `**` — the
//!   congruence is dropped (it is preserved through `+`, `−`, unary `−`, and scaling).
//! - **`**` with non-singleton base *and* exponent** — sign facts only.
//! - **A zero divisor *endpoint*** (`[1,2] / (0,∞)`) — the quotient widens to
//!   unbounded even though it is bounded on one side.
//! - **Strictness through `×` / `/`** — computed endpoints are emitted inclusive
//!   (sound, at most one point wide).
//! - **String *length* through `+`** — needs the tuple family's §5 lift to string
//!   contracts, which does not exist yet; owed there, not here.
//! - **`Difference` with a non-singleton exclusion** — the exclusion is dropped.
//! - **`Union` operands** — read as the interval/congruence hull rather than
//!   distributed per alternative. Sound; the congruence join recovers much of the
//!   precision (`{2} ∪ {6}` keeps `≡ 2 (mod 4)`). Per-alternative distribution is the
//!   open precision question (draft §5, Q1).

use num_bigint::BigInt;

use super::numeric::{self, num_abs};
use super::{Contract, Kind, Verdict, subcontract};
use crate::ast::PrimOp;
use crate::interner::Interner;
use crate::oracle::eval_prim;
use crate::rational::Rational;
use crate::value::{IndetForm, ValueRef};

/// The operation-safety verdict — a subcontract carrying an *n-ary* witness.
#[derive(Clone, Debug)]
pub enum OpSafety {
    /// No operand tuple drawn from the inputs traps.
    Proven,
    /// This operand tuple (one value per input, each in its input's denotation)
    /// makes the oracle trap.
    Refuted(Vec<ValueRef>),
    /// Neither proved safe nor refuted.
    Unproven,
}

/// The result of an operation rule: its safety demand and its image bound.
#[derive(Clone, Debug)]
pub struct OpResult {
    pub safety: OpSafety,
    pub output: Contract,
}

/// Analyze `op` applied to operands satisfying `inputs`.
pub fn analyze_operation(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> OpResult {
    let safety = analyze_safety(op, inputs, interner);
    let output = analyze_output(op, inputs, interner);
    OpResult { safety, output }
}

// ── Safety ───────────────────────────────────────────────────────────────────

fn analyze_safety(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> OpSafety {
    if demand_proven(op, inputs, interner) {
        return OpSafety::Proven;
    }
    if let Some(witness) = refute_safety(op, inputs, interner) {
        return OpSafety::Refuted(witness);
    }
    OpSafety::Unproven
}

/// The complete safety-demand table (C§7), read off the oracle's `apply_prim`.
/// Sound: `true` only when *no* operand tuple can trap.
///
/// **The Indeterminate rule is the load-bearing subtlety.** `apply_prim` checks for an
/// Indeterminate operand **first**: an *arithmetic* op propagates it unchanged and
/// never traps, while an *ordering comparison* traps `UndischargedIndeterminate`.
/// So arithmetic's operand demand is `Number ∪ Indeterminate`, not `Number` —
/// `Indeterminate + 1` is provably **safe**, and reading it as merely unproven (as
/// this table previously did) understated what the analyzer knows.
fn demand_proven(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> bool {
    let sub = |a: &Contract, b: &Contract, i: &mut Interner| matches!(subcontract(a, b, i), Verdict::Proven);
    // The operand kinds arithmetic tolerates: a Number, or any Indeterminate (which
    // short-circuits the whole operation to itself).
    let arith_operand = |c: &Contract, i: &mut Interner| {
        sub(c, &Contract::Kind(Kind::Number), i) || sub(c, &any_indeterminate(), i)
    };
    // An operand that provably *is* an Indeterminate makes an arithmetic op total
    // regardless of what the other operand is (it never gets evaluated numerically).
    let short_circuits = |c: &Contract, i: &mut Interner| sub(c, &any_indeterminate(), i);

    match op {
        // `==`/`!=` accept any values and never trap.
        PrimOp::Eq | PrimOp::Ne => true,

        PrimOp::Neg => match inputs {
            [a] => arith_operand(a, interner),
            _ => false,
        },

        // `+` is numeric addition or String concatenation; either operand being
        // Indeterminate short-circuits it.
        PrimOp::Add => match inputs {
            [a, b] => {
                let string = Contract::Kind(Kind::String);
                short_circuits(a, interner)
                    || short_circuits(b, interner)
                    || (arith_operand(a, interner) && arith_operand(b, interner))
                    || (sub(a, &string, interner) && sub(b, &string, interner))
            }
            _ => false,
        },

        // `-` `*` `/` `%` are arithmetic. Division stays **total** (a zero divisor
        // yields an Indeterminate, not a trap), so it threatens no safety demand.
        PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Rem => match inputs {
            [a, b] => {
                short_circuits(a, interner)
                    || short_circuits(b, interner)
                    || (arith_operand(a, interner) && arith_operand(b, interner))
            }
            _ => false,
        },

        // Ordering comparisons demand `Number` **strictly** — an Indeterminate
        // operand traps (`UndischargedIndeterminate`), so it is *not* admitted here.
        PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge => match inputs {
            [a, b] => {
                let num = Contract::Kind(Kind::Number);
                sub(a, &num, interner) && sub(b, &num, interner)
            }
            _ => false,
        },

        // `**` additionally demands an integer exponent and forbids `0` to a
        // negative power.
        PrimOp::Pow => match inputs {
            [a, b] => {
                if short_circuits(a, interner) || short_circuits(b, interner) {
                    return true;
                }
                arith_operand(a, interner)
                    && sub(b, &integers(), interner)
                    && (nonzero(a, interner) || sub(b, &Contract::GreaterEq(Rational::from(0)), interner))
            }
            _ => false,
        },
    }
}

/// Either Indeterminate form — the operand set arithmetic short-circuits on.
fn any_indeterminate() -> Contract {
    Contract::Union(
        Box::new(Contract::Indeterminate(IndetForm::DivByZero)),
        Box::new(Contract::Indeterminate(IndetForm::ZeroOverZero)),
    )
}

/// Sound: `true` only when `0 ∉ ⟦c⟧`.
fn nonzero(c: &Contract, interner: &mut Interner) -> bool {
    let zero = Contract::Difference(Box::new(Contract::Top), Box::new(Contract::Equals(interner.integer(0))));
    matches!(subcontract(c, &zero, interner), Verdict::Proven)
}

/// The contract of all integers: `x ≡ 0 (mod 1)`.
fn integers() -> Contract {
    Contract::Mod { n: BigInt::from(1), r: BigInt::from(0) }
}

/// Sample one value per input and probe the oracle for a trapping tuple.
fn refute_safety(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> Option<Vec<ValueRef>> {
    let pools: Vec<Vec<ValueRef>> = inputs
        .iter()
        .map(|c| {
            let mut s = super::subcontract::sample(c, interner);
            s.retain(|v| c.contains(v)); // genuine members only
            s
        })
        .collect();
    if pools.iter().any(|p| p.is_empty()) {
        return None; // some operand is unsampleable — cannot exhibit a witness
    }
    let mut tuple = Vec::with_capacity(pools.len());
    find_trap(op, &pools, &mut tuple, interner)
}

/// Depth-first over the cartesian product of the pools; returns the first tuple
/// the oracle traps on.
fn find_trap(
    op: PrimOp,
    pools: &[Vec<ValueRef>],
    tuple: &mut Vec<ValueRef>,
    interner: &mut Interner,
) -> Option<Vec<ValueRef>> {
    match pools {
        [] => eval_prim(op, tuple, interner).is_err().then(|| tuple.clone()),
        [head, rest @ ..] => {
            for v in head {
                tuple.push(v.clone());
                if let Some(w) = find_trap(op, rest, tuple, interner) {
                    return Some(w);
                }
                tuple.pop();
            }
            None
        }
    }
}

// ── Output (image over-approximation) ────────────────────────────────────────

fn analyze_output(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> Contract {
    let base = base_output(op, inputs, interner);
    // Arithmetic passes an Indeterminate operand through unchanged (the oracle's
    // arith-Indeterminate rule), so if any operand can be Indeterminate the image
    // includes that form.
    if is_arith(op) {
        return with_indet_passthrough(inputs, base, interner);
    }
    base
}

fn is_arith(op: PrimOp) -> bool {
    matches!(
        op,
        PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Rem | PrimOp::Pow | PrimOp::Neg
    )
}

fn with_indet_passthrough(inputs: &[Contract], out: Contract, interner: &mut Interner) -> Contract {
    let mut result = out;
    for form in [IndetForm::DivByZero, IndetForm::ZeroOverZero] {
        let iv = interner.indeterminate(form);
        if inputs.iter().any(|c| c.contains(&iv)) {
            result = Contract::Union(Box::new(result), Box::new(Contract::Indeterminate(form)));
        }
    }
    result
}

/// The **leaf** image rules (Layer 3) — every operand here is already free of
/// `Union`/`Bottom`/`Indeterminate` (Layer 1 handled those). Ordered specific →
/// general per operation: a form-preserving rule gets first refusal, and the numeric
/// abstraction is the total fallback.
fn base_output(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> Contract {
    match op {
        // `+` is numeric addition or String concatenation.
        PrimOp::Add => match inputs {
            [a, b] => {
                if let (Some(x), Some(y)) = (num_abs(a), num_abs(b)) {
                    return numeric::to_contract(numeric::abs_add(&x, &y), interner);
                }
                string_or_mixed(a, b, interner)
            }
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Sub => binary_numeric(inputs, interner, numeric::abs_sub),
        PrimOp::Mul => match inputs {
            // Table C — form preservation gets first refusal: scaling a geometric
            // sequence by an exact constant is still geometric (C§7 *scaling*).
            [a, b] => match geo_scaling(a, b).or_else(|| geo_scaling(b, a)) {
                Some(g) => g,
                None => binary_numeric(inputs, interner, numeric::abs_mul),
            },
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Div | PrimOp::Rem => match inputs {
            // Division/remainder are **total**: a possibly-zero divisor yields an
            // Indeterminate rather than trapping, so the image gains those forms.
            [a, b] => {
                let numeric_part = match (num_abs(a), num_abs(b)) {
                    (Some(x), Some(y)) => {
                        let r = if matches!(op, PrimOp::Div) {
                            numeric::abs_div(&x, &y)
                        } else {
                            numeric::abs_rem(&x, &y)
                        };
                        numeric::to_contract(r, interner)
                    }
                    _ => Contract::Kind(Kind::Number),
                };
                with_zero_divisor_forms(a, b, numeric_part, interner)
            }
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Pow => binary_numeric(inputs, interner, numeric::abs_pow),
        PrimOp::Neg => match inputs {
            [a] => match num_abs(a) {
                Some(x) => numeric::to_contract(numeric::abs_neg(&x), interner),
                None => Contract::Kind(Kind::Number),
            },
            _ => Contract::Kind(Kind::Number),
        },
        // A comparison's image is `Kind(Boolean)` — but when the operands' bounds
        // *decide* it, the precise image is the singleton, which is what lets a guard
        // resolve (E10 tested seats / the region walk).
        PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge => match inputs {
            [a, b] => decide_comparison(op, a, b, interner),
            _ => Contract::Kind(Kind::Boolean),
        },
        // `==`/`!=` decide when the operands are the same singleton, or disjoint.
        PrimOp::Eq | PrimOp::Ne => match inputs {
            [a, b] => decide_equality(op, a, b, interner),
            _ => Contract::Kind(Kind::Boolean),
        },
    }
}

fn binary_numeric(
    inputs: &[Contract],
    interner: &mut Interner,
    f: impl Fn(&numeric::NumAbs, &numeric::NumAbs) -> numeric::NumAbs,
) -> Contract {
    match inputs {
        [a, b] => match (num_abs(a), num_abs(b)) {
            (Some(x), Some(y)) => numeric::to_contract(f(&x, &y), interner),
            _ => Contract::Kind(Kind::Number),
        },
        _ => Contract::Kind(Kind::Number),
    }
}

/// `Geo(b, r) × Equals(c)` is `Geo(b·c, r)` — the sequence scaled termwise. `c = 0`
/// collapses it to `Equals(0)`; a non-numeric or non-exact factor declines (`None`),
/// falling through to the general numeric rule.
fn geo_scaling(g: &Contract, factor: &Contract) -> Option<Contract> {
    let Contract::Geo { b, r } = g else { return None };
    let Contract::Equals(v) = factor else { return None };
    let c = v.as_number()?;
    if c.is_zero() {
        return Some(Contract::Equals(v.clone()));
    }
    Some(Contract::Geo { b: b.clone() * c.clone(), r: r.clone() })
}

/// `+` on non-numeric operands: two Strings concatenate; anything unresolved may be
/// either. (The *length* of the concatenation needs the tuple family's §5 lift to
/// string contracts — owed there, not here.)
fn string_or_mixed(a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    match (is_str(a, interner), is_str(b, interner)) {
        (true, true) => Contract::Kind(Kind::String),
        _ => Contract::Union(
            Box::new(Contract::Kind(Kind::Number)),
            Box::new(Contract::Kind(Kind::String)),
        ),
    }
}

/// `/` and `%` are total: when `0` is possible in the divisor the image gains the
/// Indeterminate forms (`0/0` only when the dividend may also be zero).
fn with_zero_divisor_forms(
    a: &Contract,
    b: &Contract,
    numeric_part: Contract,
    interner: &mut Interner,
) -> Contract {
    let zero = interner.integer(0);
    if !b.contains(&zero) {
        return numeric_part;
    }
    let mut out = numeric_part;
    if a.contains(&zero) {
        out = Contract::Union(Box::new(out), Box::new(Contract::Indeterminate(IndetForm::ZeroOverZero)));
    }
    Contract::Union(Box::new(out), Box::new(Contract::Indeterminate(IndetForm::DivByZero)))
}

/// An ordering comparison whose operands' bounds settle it — `Range(0,5) < GreaterEq(10)`
/// is *always* true, so `Equals(true)` is the precise image. Undecided → `Kind(Boolean)`.
fn decide_comparison(op: PrimOp, a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    let boolean = Contract::Kind(Kind::Boolean);
    let (Some(x), Some(y)) = (num_abs(a), num_abs(b)) else { return boolean };
    match numeric::compare_decided(op, &x, &y) {
        Some(v) => Contract::Equals(interner.boolean(v)),
        None => boolean,
    }
}

/// `==`/`!=` decide on proven-equal singletons or proven-disjoint operands.
fn decide_equality(op: PrimOp, a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    let equal = match (a, b) {
        (Contract::Equals(x), Contract::Equals(y)) => Some(x == y),
        _ if super::disjoint(a, b) => Some(false),
        _ => None,
    };
    match equal {
        Some(v) => Contract::Equals(interner.boolean(if matches!(op, PrimOp::Eq) { v } else { !v })),
        None => Contract::Kind(Kind::Boolean),
    }
}

fn is_str(c: &Contract, interner: &mut Interner) -> bool {
    matches!(subcontract(c, &Contract::Kind(Kind::String), interner), Verdict::Proven)
}




