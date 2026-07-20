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

use num_bigint::BigInt;

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

/// Sound: `true` only when *no* operand tuple can trap.
fn demand_proven(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> bool {
    let num = || Contract::Kind(Kind::Number);
    let string = || Contract::Kind(Kind::String);
    let sub = |a: &Contract, b: &Contract, i: &mut Interner| matches!(subcontract(a, b, i), Verdict::Proven);

    match op {
        // `==`/`!=` accept any values and never trap.
        PrimOp::Eq | PrimOp::Ne => true,
        PrimOp::Neg => match inputs {
            [a] => sub(a, &num(), interner),
            _ => false,
        },
        // `+` demands two Numbers *or* two Strings.
        PrimOp::Add => match inputs {
            [a, b] => {
                (sub(a, &num(), interner) && sub(b, &num(), interner))
                    || (sub(a, &string(), interner) && sub(b, &string(), interner))
            }
            _ => false,
        },
        // `-` `*` `/` `%` `<` `<=` `>` `>=` demand two Numbers. Division stays
        // total (0-divisor ⇒ Indeterminate, *not* a trap), so a zero divisor
        // does not threaten safety.
        PrimOp::Sub
        | PrimOp::Mul
        | PrimOp::Div
        | PrimOp::Rem
        | PrimOp::Lt
        | PrimOp::Le
        | PrimOp::Gt
        | PrimOp::Ge => match inputs {
            [a, b] => sub(a, &num(), interner) && sub(b, &num(), interner),
            _ => false,
        },
        // `^` additionally demands an integer exponent and forbids `0` to a
        // negative power.
        PrimOp::Pow => match inputs {
            [a, b] => {
                sub(a, &num(), interner)
                    && sub(b, &integers(), interner)
                    && (nonzero(a, interner) || sub(b, &Contract::GreaterEq(Rational::from(0)), interner))
            }
            _ => false,
        },
    }
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

fn base_output(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> Contract {
    match op {
        PrimOp::Add => match inputs {
            [a, b] => add_output(a, b, interner),
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Sub => match inputs {
            [Contract::Range(l1, h1), Contract::Range(l2, h2)] => {
                Contract::Range(l1.clone() - h2.clone(), h1.clone() - l2.clone())
            }
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Mul => match inputs {
            [Contract::Range(l1, h1), Contract::Range(l2, h2)] => mul_range(l1, h1, l2, h2),
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Neg => match inputs {
            [a] => neg_output(a),
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Div | PrimOp::Rem => match inputs {
            [a, b] => div_output(a, b, interner),
            _ => Contract::Kind(Kind::Number),
        },
        PrimOp::Pow => Contract::Kind(Kind::Number),
        PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge | PrimOp::Eq | PrimOp::Ne => {
            Contract::Kind(Kind::Boolean)
        }
    }
}

fn is_num(c: &Contract, interner: &mut Interner) -> bool {
    matches!(subcontract(c, &Contract::Kind(Kind::Number), interner), Verdict::Proven)
}
fn is_str(c: &Contract, interner: &mut Interner) -> bool {
    matches!(subcontract(c, &Contract::Kind(Kind::String), interner), Verdict::Proven)
}

fn add_output(a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    if let (Contract::Range(l1, h1), Contract::Range(l2, h2)) = (a, b) {
        return Contract::Range(l1.clone() + l2.clone(), h1.clone() + h2.clone());
    }
    match (is_num(a, interner), is_str(a, interner), is_num(b, interner), is_str(b, interner)) {
        (true, _, true, _) => Contract::Kind(Kind::Number),
        (_, true, _, true) => Contract::Kind(Kind::String),
        // Mixed/unknown: `+` produces either a Number or a String.
        _ => Contract::Union(
            Box::new(Contract::Kind(Kind::Number)),
            Box::new(Contract::Kind(Kind::String)),
        ),
    }
}

/// `[l1,h1] · [l2,h2]` is bounded by the min/max of the four corner products.
fn mul_range(l1: &Rational, h1: &Rational, l2: &Rational, h2: &Rational) -> Contract {
    let corners = [
        l1.clone() * l2.clone(),
        l1.clone() * h2.clone(),
        h1.clone() * l2.clone(),
        h1.clone() * h2.clone(),
    ];
    let lo = corners.iter().min().unwrap().clone();
    let hi = corners.iter().max().unwrap().clone();
    Contract::Range(lo, hi)
}

fn neg_output(a: &Contract) -> Contract {
    match a {
        Contract::Range(l, h) => Contract::Range(-h.clone(), -l.clone()),
        Contract::Greater(m) => Contract::Less(-m.clone()),
        Contract::GreaterEq(m) => Contract::LessEq(-m.clone()),
        Contract::Less(m) => Contract::Greater(-m.clone()),
        Contract::LessEq(m) => Contract::GreaterEq(-m.clone()),
        _ => Contract::Kind(Kind::Number),
    }
}

/// `/` and `%` are total: a zero divisor yields an Indeterminate rather than a
/// Number, so the image includes `Indeterminate` forms whenever `0 ∈ ⟦b⟧`.
fn div_output(_a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    let zero = interner.integer(0);
    let number = Contract::Kind(Kind::Number);
    if !b.contains(&zero) {
        return number; // divisor never zero
    }
    let indet = Contract::Union(
        Box::new(Contract::Indeterminate(IndetForm::DivByZero)),
        Box::new(Contract::Indeterminate(IndetForm::ZeroOverZero)),
    );
    Contract::Union(Box::new(number), Box::new(indet))
}
