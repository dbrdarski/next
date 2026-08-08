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
//! 1. **Algebraic plumbing, uniform across every operation** — strict Number
//!    demands and the `Numeric = Number ∪ Indeterminate` output of total
//!    division/remainder.
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
//! - **String seam exactness through `+`** — abstract operands carry the sound
//!   `[left.lo, hi_a + hi_b]` grapheme bound (`concat_image`; T2.5's §5 lift);
//!   the exact seam remains literal-fold territory (`Summary::compose`).
//! - **`Difference` with a non-singleton exclusion** — the exclusion is dropped.
//! - **`Union` operands at the coarse rulebook layer** — read as the
//!   interval/congruence hull rather than distributed per alternative. Sound; the
//!   congruence join recovers much of the precision (`{2} ∪ {6}` keeps `≡ 2 (mod 4)`).
//!   The analyzer separately holds finite source cells and forces their correlated
//!   exact image only when a match routes it (DR-16/DR-17, BR-03/BR-04).

use num_bigint::BigInt;

use super::numeric::{self, num_abs};
use super::{Contract, Kind, Verdict, subcontract};
use crate::ast::PrimOp;
use crate::interner::Interner;
use crate::oracle::{eval_prim, values_equal};
use crate::rational::Rational;
use crate::value::{IndeterminateFormTag, ValueRef};

/// The operation-safety verdict — a subcontract carrying an *n-ary* witness:
/// `Refuted` holds the operand tuple (one value per input, each in its input's
/// denotation) that makes the oracle trap. An alias of the family shape [`Voice`].
pub type OpSafety = crate::contract::Voice<Vec<ValueRef>>;

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
/// Indeterminate values are ordinary values for equality and matching, but their
/// algebra is still open. Every arithmetic or ordering operation is therefore a
/// strict `Number` seat: admitting one would be unsound because the oracle traps
/// `UndischargedIndeterminate`. Division/remainder of two proven Numbers remain
/// total; a zero divisor constructs a specific Indeterminate form.
fn demand_proven(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> bool {
    let sub = |a: &Contract, b: &Contract, i: &mut Interner| {
        matches!(subcontract(a, b, i), Verdict::Proven)
    };
    let number = Contract::Kind(Kind::Number);
    let is_number = |c: &Contract, i: &mut Interner| sub(c, &number, i);

    match op {
        // `==`/`!=` accept any values and never trap.
        PrimOp::Eq | PrimOp::Ne => true,

        PrimOp::Neg => match inputs {
            [a] => is_number(a, interner),
            _ => false,
        },

        // `++` joins two sequences of the **same** kind — two Strings or two Tuples.
        // Mixed operands are refused: there is no meaning for `"a" ++ [1]`.
        PrimOp::Concat => match inputs {
            [a, b] => {
                (is_str(a, interner) && is_str(b, interner))
                    || (is_tuple(a, interner) && is_tuple(b, interner))
            }
            _ => false,
        },

        // `+` `-` `*` `/` `%` require Number operands. Division/remainder stay total
        // within that domain: a zero divisor constructs an Indeterminate.
        PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Rem => match inputs {
            [a, b] => is_number(a, interner) && is_number(b, interner),
            _ => false,
        },

        // Ordering comparisons demand `Number` **strictly** — an Indeterminate
        // operand traps (`UndischargedIndeterminate`), so it is *not* admitted here.
        PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge => match inputs {
            [a, b] => is_number(a, interner) && is_number(b, interner),
            _ => false,
        },

        // `**` additionally demands an integer exponent and forbids `0` to a
        // negative power.
        PrimOp::Pow => match inputs {
            [a, b] => {
                is_number(a, interner)
                    && sub(b, &integers(), interner)
                    && (nonzero(a, interner)
                        || sub(b, &Contract::GreaterEq(Rational::from(0)), interner))
            }
            _ => false,
        },
    }
}

/// Sound: `true` only when `0 ∉ ⟦c⟧`.
fn nonzero(c: &Contract, interner: &mut Interner) -> bool {
    let zero = interner.integer(0);
    let zero = Contract::not_equals(zero, interner);
    matches!(subcontract(c, &zero, interner), Verdict::Proven)
}

/// The contract of all integers: `x ≡ 0 (mod 1)`.
fn integers() -> Contract {
    Contract::Mod {
        n: BigInt::from(1),
        r: BigInt::from(0),
    }
}

/// Sample one value per input and probe the oracle for a trapping tuple.
fn refute_safety(
    op: PrimOp,
    inputs: &[Contract],
    interner: &mut Interner,
) -> Option<Vec<ValueRef>> {
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
        [] => eval_prim(op, tuple, interner)
            .is_err()
            .then(|| tuple.clone()),
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

/// Flatten a contract into its finite point set, or `None` when it is not one.
pub(crate) fn point_set(c: &Contract) -> Option<Vec<Contract>> {
    match c {
        Contract::Equals(_) => Some(vec![c.clone()]),
        Contract::Union(a, b) => {
            let mut out = point_set(a)?;
            out.extend(point_set(b)?);
            Some(out)
        }
        Contract::Bottom => Some(Vec::new()),
        _ => None,
    }
}

/// The **exact image** of `op` over finite point operands: apply the leaf rule to
/// every combination and join. Exact by construction — each combination is a
/// singleton application, and the join is their union. `None` when an operand is not
/// a finite point set. There is no semantic fuel/budget cutoff: a finite represented
/// product is the routing work (BR-16), not a search over unknowns.
/// The combination driver over operand point sets that are already resolved — the form
/// a **chained** image needs, since its operands are produced by forcing a nested image
/// rather than by reading a contract.
pub(crate) fn exact_image_over(
    op: PrimOp,
    sets: &[Vec<Contract>],
    interner: &mut Interner,
) -> Option<Contract> {
    if sets.iter().any(Vec::is_empty) {
        return None;
    }
    let mut combos: Vec<Vec<Contract>> = vec![Vec::new()];
    for set in sets {
        let mut next = Vec::with_capacity(combos.len() * set.len());
        for prefix in &combos {
            for point in set {
                let mut t = prefix.clone();
                t.push(point.clone());
                next.push(t);
            }
        }
        combos = next;
    }
    let mut out: Option<Contract> = None;
    for tuple in combos {
        let image = base_output(op, &tuple, interner);
        out = Some(match out {
            None => image,
            Some(acc) => Contract::union(acc, image, interner),
        });
    }
    out
}

fn analyze_output(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> Contract {
    // Always the coarse reading. The exact image is **held**, not substituted here —
    // a result demand never needs it (DR-09), and the one judgment that does (routing)
    // forces it at the scrutinee (`domain::HeldImage`).
    base_output(op, inputs, interner)
}

/// The **leaf** image rules (Layer 3) — every operand here is already free of
/// `Union`/`Bottom` (Layer 1 handled those). Ordered specific →
/// general per operation: a form-preserving rule gets first refusal, and the numeric
/// abstraction is the total fallback.
fn base_output(op: PrimOp, inputs: &[Contract], interner: &mut Interner) -> Contract {
    match op {
        // `+` is numeric addition only; `++` carries the String rail and its
        // grapheme-seam bound (T2.5's §5 lift).
        PrimOp::Add => binary_numeric(inputs, interner, numeric::abs_add),
        // Two Tuples concatenate through the family's own smart constructor — the
        // very shape `[...a, ...b]` already produces, so a `++` chain carries exact
        // segment structure rather than collapsing to `Kind(Tuple)`.
        PrimOp::Concat => match inputs {
            [a, b] if is_tuple(a, interner) && is_tuple(b, interner) => {
                Contract::concat([a.clone(), b.clone()], interner)
            }
            [a, b] => string_or_mixed(a, b, interner),
            _ => Contract::Kind(Kind::String),
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
            // Division/remainder are total over Number operands: a possibly-zero
            // divisor means the image is Numeric rather than strictly Number.
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
                with_zero_divisor_form(op, b, numeric_part, interner)
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
    let Contract::Geo { b, r } = g else {
        return None;
    };
    let Contract::Equals(v) = factor else {
        return None;
    };
    let c = v.as_number()?;
    if c.is_zero() {
        return Some(Contract::Equals(v.clone()));
    }
    Some(Contract::Geo {
        b: b.clone() * c.clone(),
        r: r.clone(),
    })
}

/// `+` on non-numeric operands: two Strings concatenate; anything unresolved may be
/// either. (The *length* of the concatenation needs the tuple family's §5 lift to
/// string contracts — owed there, not here.)
fn string_or_mixed(a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    let string = Contract::Kind(Kind::String);
    let number = Contract::Kind(Kind::Number);
    match (is_str(a, interner), is_str(b, interner)) {
        (true, true) => concat_image(a, b, interner),
        // `+` completes only as Number+Number or String+String, and the image ranges
        // over completing evaluations — so one operand disjoint from String forces
        // the numeric rail, and dually. (`1 + x` can never concatenate.)
        _ if super::disjoint(a, &string) || super::disjoint(b, &string) => number,
        _ if super::disjoint(a, &number) || super::disjoint(b, &number) => string,
        _ => Contract::union(number, string, interner),
    }
}

/// `/` and `%` are total over Numbers: when `0` is possible in the divisor the
/// image gains the operation's Indeterminate form. Exact operands are
/// constant-folded by the analyzer, so this form contract is the sound
/// non-singleton approximation over every retained operand.
fn with_zero_divisor_form(
    op: PrimOp,
    b: &Contract,
    numeric_part: Contract,
    interner: &mut Interner,
) -> Contract {
    let zero = interner.integer(0);
    if !b.contains(&zero) {
        return numeric_part;
    }
    let form = match op {
        PrimOp::Div => IndeterminateFormTag::DivZero,
        PrimOp::Rem => IndeterminateFormTag::ModZero,
        _ => unreachable!("zero-divisor forms exist only for division and remainder"),
    };
    Contract::union(numeric_part, Contract::Indeterminate(form), interner)
}

/// An ordering comparison whose operands' bounds settle it — `Range(0,5) < GreaterEq(10)`
/// is *always* true, so `Equals(true)` is the precise image. Undecided → `Kind(Boolean)`.
fn decide_comparison(op: PrimOp, a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    let boolean = Contract::Kind(Kind::Boolean);
    let (Some(x), Some(y)) = (num_abs(a), num_abs(b)) else {
        return boolean;
    };
    match numeric::compare_decided(op, &x, &y) {
        Some(v) => Contract::Equals(interner.boolean(v)),
        None => boolean,
    }
}

/// `==`/`!=` decide on proven-equal singletons or proven-disjoint operands.
fn decide_equality(op: PrimOp, a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    let equal = match (a, b) {
        // Same value = same pointer, including closed function graphs.
        (Contract::Equals(x), Contract::Equals(y)) => Some(values_equal(x, y)),
        _ if super::disjoint(a, b) => Some(false),
        _ => None,
    };
    match equal {
        Some(v) => {
            Contract::Equals(interner.boolean(if matches!(op, PrimOp::Eq) { v } else { !v }))
        }
        None => Contract::Kind(Kind::Boolean),
    }
}

fn is_tuple(c: &Contract, interner: &mut Interner) -> bool {
    matches!(
        subcontract(c, &Contract::Kind(Kind::Tuple), interner),
        Verdict::Proven
    )
}

fn is_str(c: &Contract, interner: &mut Interner) -> bool {
    matches!(
        subcontract(c, &Contract::Kind(Kind::String), interner),
        Verdict::Proven
    )
}

/// The `String ++ String` image with its **derived length** (E8 / tuple-family §5,
/// plan T2.5): the grapheme count of `a ++ b` lies in `[len(a).lo, len(a).hi +
/// len(b).hi]` — `concat_len_bound`'s law. The floor is the **left** operand's
/// minimum only: clustering merges rightward-in, so a leading joiner on the right
/// can absorb into the left's trailing state and `count(b)` is not a lower bound;
/// the ceiling is the plain sum, since merges only reduce. Exact literal seams fold
/// upstream through the oracle (the analyzer's constant-fold path); this is the
/// abstract-operand transfer, `Approx`-stamped by construction, and it degrades to
/// the bare `Kind(String)` whenever the bounds say nothing.
fn concat_image(a: &Contract, b: &Contract, interner: &mut Interner) -> Contract {
    let group = super::recursive::RecGroup::new([]);
    let la = super::length::len(&group, a, interner);
    let lb = super::length::len(&group, b, interner);
    let (alo, ahi) = nat_bounds(&la.contract);
    let (_, bhi) = nat_bounds(&lb.contract);
    let (lo, hi) = super::grapheme::concat_len_bound((alo, ahi), (0, bhi));
    let string = Contract::Kind(Kind::String);
    let length = match (lo, hi) {
        (0, None) => return string,
        (lo, None) => Contract::intersection(
            Contract::GreaterEq(Rational::from(lo as i64)),
            integers(),
            interner,
        ),
        (lo, Some(hi)) => Contract::intersection(
            Contract::Range(Rational::from(lo as i64), Rational::from(hi as i64)),
            integers(),
            interner,
        ),
    };
    Contract::length_restricted(string, length, interner)
}

/// Sound natural-number bounds `[lo, hi]` read from a length contract (`hi = None`
/// unbounded). Anything unreadable widens to `(0, None)` — never a wrong bound.
fn nat_bounds(length: &Contract) -> (usize, Option<usize>) {
    let Some(abs) = super::numeric::num_abs(length) else {
        return (0, None);
    };
    let lo = match &abs.iv.low {
        super::numeric::Bound::Incl(r) if r.is_integer() && *r >= Rational::from(0) => {
            usize::try_from(r.as_ratio().numer().clone()).unwrap_or(0)
        }
        super::numeric::Bound::Excl(r) if r.is_integer() && *r >= Rational::from(0) => {
            usize::try_from(r.as_ratio().numer().clone() + 1).unwrap_or(0)
        }
        _ => 0,
    };
    let hi = match &abs.iv.high {
        super::numeric::Bound::Incl(r) if r.is_integer() && *r >= Rational::from(0) => {
            usize::try_from(r.as_ratio().numer().clone()).ok()
        }
        super::numeric::Bound::Excl(r) if r.is_integer() && *r > Rational::from(0) => {
            usize::try_from(r.as_ratio().numer().clone() - 1).ok()
        }
        super::numeric::Bound::Unbounded => None,
        _ => None,
    };
    (lo, hi)
}
