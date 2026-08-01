//! The demand core — C§13.1 (plan T1.2).
//!
//! The model, quoted, because two of its clauses are easy to get backwards and this
//! implementation got both wrong in planning before the section was read:
//!
//! > Demands propagate backward **untransformed as subscriptions**; resolution is
//! > **forward** through the operation rules (each carrying its C§7 safety verdict);
//! > adjudication **where the demand was asked**, three-valued. Two-variable operations
//! > are ordinary nodes. **Eager preimage transformation is an optimization**
//! > (short-circuiting; origin-phrased diagnostics). **No stall concept.**
//!
//! Three consequences that shape every function here:
//!
//! 1. **A demand carries no contract backward.** It is a *subscription* naming an origin —
//!    "whatever this produces, I have a question about it". Nothing is transformed on the
//!    way back, so nothing accumulates on the way back.
//! 2. **Resolution is forward, through the operation rules** — the C§7 rulebook
//!    (`contract::operation`, built as F0). This is the *only* direction in which a
//!    contract is computed, and it is computed for the demanded origin, not for every
//!    subexpression in sight.
//! 3. **Adjudication happens at the ask site**, three-valued. Not at the origin. The
//!    origin supplies; the asker judges.
//!
//! **Eager preimage is explicitly an optimization**, not the mechanism — it buys
//! short-circuiting and origin-phrased diagnostics. It is not implemented here, and its
//! absence costs precision in no case: the forward resolution answers the same question.
//!
//! **"No stall concept"** is the clause that keeps this honest. A demand is never parked
//! awaiting more information, and there is no state meaning "come back when you know
//! more". A demand that cannot be resolved is **unproven**, terminally, for this
//! compilation. That is what forbids the slide this module was flagged for: an
//! unadjudicated demand accumulating partial per-path information, joined across paths,
//! then widened over loops. There is no partial state to accumulate, because there is no
//! stall to accumulate it in.

use crate::analyzer::refute::{ClaimVerdict, check_return_claim};
use crate::contract::{Contract, ContractEnv};
use crate::interner::Interner;
use crate::value::ValueRef;

/// A subscription: the question `asker` has about what `origin` produces.
///
/// Deliberately *not* "a contract pushed backward". The demanded contract rides with the
/// ask, and is checked when the origin resolves forward — per C§13.1, demands propagate
/// untransformed.
#[derive(Debug, Clone)]
pub struct Demand {
    /// The origin subscribed to — the function whose result is in question.
    pub origin: ValueRef,
    /// The input domain the origin is being asked about (its row-set `I`).
    pub domain: Vec<Contract>,
    /// The contract the asker requires. Checked at the ask site, never transformed en route.
    pub required: Contract,
    /// Where the question was asked, for the diagnostic. C§13.1 puts adjudication here.
    pub asker: String,
}

/// Adjudicate a demand, three-valued.
///
/// Resolution runs forward through the operation rules over the origin's body, and
/// recursion closes through the **same** global fact graph the safety and completion
/// claims use (C§13.2a) — a return question is a third claim over one graph, never a
/// second graph. `ClaimVerdict::Unproven` is terminal for this compilation: there is no
/// stall. A represented completing execution that violates `required` remains a concrete
/// `Refuted` witness rather than being collapsed into that third voice.
pub fn adjudicate(d: &Demand, cenv: &ContractEnv, interner: &mut Interner) -> ClaimVerdict {
    check_return_claim(&d.origin, &d.domain, &d.required, cenv, interner)
}

/// Whether `callee` over `domain` provably returns a value satisfying `required`.
///
/// The convenience entry for the one consumer that exists today — the `where`-declared
/// return contract (E11). Left thin on purpose: additional demand origins (operand seats,
/// element positions, destructuring right-sides) are the same `Demand` through the same
/// `adjudicate`, and each lands with the seat that needs it, not ahead of it.
pub fn returns(
    callee: &ValueRef,
    domain: &[Contract],
    required: &Contract,
    asker: &str,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> ClaimVerdict {
    let d = Demand {
        origin: callee.clone(),
        domain: domain.to_vec(),
        required: required.clone(),
        asker: asker.to_string(),
    };
    adjudicate(&d, cenv, interner)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::Kind;
    use crate::oracle::run_source_in;
    use crate::rational::Rational;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    #[test]
    fn a_satisfied_return_demand_is_proven() {
        let mut i = Interner::new();
        let g = f("f = (n) => n + 1\nf", &mut i);
        let v = returns(
            &g,
            &[Contract::Kind(Kind::Number)],
            &Contract::Kind(Kind::Number),
            "where f",
            &ContractEnv::new(),
            &mut i,
        );
        assert!(matches!(v, ClaimVerdict::Proven), "Number + Number produces a Number: {v:?}");
    }

    /// `f(0) = 1` is a represented completing execution, so the false String claim is
    /// refuted with that concrete evidence rather than collapsed into Unproven.
    #[test]
    fn an_unsatisfied_return_demand_preserves_its_realized_refutation() {
        let mut i = Interner::new();
        let g = f("f = (n) => n + 1\nf", &mut i);
        let v = returns(
            &g,
            &[Contract::Kind(Kind::Number)],
            &Contract::Kind(Kind::String),
            "where f",
            &ContractEnv::new(),
            &mut i,
        );
        match v {
            ClaimVerdict::Refuted(witness) => {
                assert_eq!(witness.arguments.len(), 1);
                assert!(!Contract::Kind(Kind::String).contains(&witness.produced));
            }
            other => panic!("the represented counterexample must survive adjudication: {other:?}"),
        }
    }

    /// Factorial produces only positive values on the represented completing samples, but
    /// over all Numbers the abstract multiplication rule cannot prove positivity. With no
    /// concrete counterexample and no proof, the result is the honest third voice.
    #[test]
    fn an_unsettled_return_demand_without_a_witness_is_unproven() {
        let mut i = Interner::new();
        let g = f(
            "factorial = (n) => n == 0 ? 1 : n * factorial(n - 1)\nfactorial",
            &mut i,
        );
        let v = returns(
            &g,
            &[Contract::Kind(Kind::Number)],
            &Contract::Greater(Rational::from(0)),
            "where factorial",
            &ContractEnv::new(),
            &mut i,
        );
        assert!(matches!(v, ClaimVerdict::Unproven), "no proof and no witness: {v:?}");
    }

    /// Recursion closes through the fact graph rather than unfolding — and **proves**,
    /// which it only does because the return claim is evaluated by the §5 partition. Each
    /// row carries its own narrowing, so the recursive argument stays inside the domain
    /// the hypothesis is stated over. Analyzed whole, this returns unproven. If this were
    /// unfolding it would not return at all.
    #[test]
    fn a_recursive_return_demand_closes_through_the_fact_graph() {
        let mut i = Interner::new();
        let g = f("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut i);
        let v = returns(
            &g,
            &[Contract::Kind(Kind::Number)],
            &Contract::Kind(Kind::Number),
            "where f",
            &ContractEnv::new(),
            &mut i,
        );
        assert!(matches!(v, ClaimVerdict::Proven), "recursion closes on the fact and proves: {v:?}");
    }
}
