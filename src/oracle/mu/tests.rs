//! Algorithm A conformance (μ-Canonicalization Spec §7): MU-01 (vacuous-μ
//! erasure), MU-03 (minimal-group split), MU-06 (canonical form invariant under
//! renaming and member permutation).

use std::collections::BTreeMap;

use super::canonicalize_group;
use crate::ast::{BindTarget, Expr, Item};
use crate::desugar::Desugarer;
use crate::interner::Interner;
use crate::lex::lex;
use crate::parse::parse_program;

/// Desugar a program and return its top-level `name = value` bindings.
fn bindings(src: &str) -> Vec<(String, Expr)> {
    let mut interner = Interner::new();
    let prog = parse_program(lex(src).unwrap()).unwrap();
    let module = Desugarer::new(&mut interner).program(&prog).unwrap();
    module
        .items
        .iter()
        .filter_map(|it| match it {
            Item::Bind(b) => match &b.target {
                BindTarget::Name(n) => Some((n.clone(), b.value.clone())),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

fn keys(src: &str) -> BTreeMap<String, String> {
    canonicalize_group(&bindings(src))
}

/// The multiset of canonical code values (names dropped) — the rename/permute
/// invariant.
fn codes(src: &str) -> Vec<String> {
    let mut v: Vec<String> = keys(src).into_values().collect();
    v.sort();
    v
}

#[test]
fn mu01_non_recursive_binding_has_no_mu() {
    // A binding that does not reference itself is plain code — no μ introduced.
    let k = keys("a = (n) => n + 1");
    assert!(!k["a"].contains("mu["), "no μ for a non-recursive binding: {}", k["a"]);
}

#[test]
fn self_recursion_introduces_a_single_slot_mu() {
    let k = keys("f = (n) => n == 0 ? 0 : f(n - 1)");
    assert!(k["f"].contains("mu[1]"), "self-recursion is a 1-slot μ: {}", k["f"]);
    assert!(k["f"].contains("μ⟨0,0⟩"), "the self-reference is a μ-ref");
}

#[test]
fn mu03_minimal_group_splits_out_acyclic_neighbour() {
    // {a, b} mutually recurse (a 2-slot μ); c references a but a does not
    // reference c, so c is NOT bound into the μ (law 3 / law 1).
    let k = keys("a = () => b\nb = () => a\nc = () => a");
    assert!(k["a"].starts_with("mu[2]"), "a is a 2-slot μ member: {}", k["a"]);
    assert!(k["b"].starts_with("mu[2]"), "b is a 2-slot μ member: {}", k["b"]);
    // c is NOT itself a μ-group member — its key is plain code that *references*
    // the group by canonical key (law 3 / law 1: the acyclic neighbour splits out).
    assert!(!k["c"].starts_with("mu["), "c is not μ-bound: {}", k["c"]);
    assert!(k["c"].contains("k[mu["), "c references the group by canonical key: {}", k["c"]);
}

#[test]
fn mu06_invariant_under_renaming() {
    // Renaming the group members must not change the canonical codes.
    let a = codes("isEven = (n) => n == 0 ? true : isOdd(n - 1)\nisOdd = (n) => n == 0 ? false : isEven(n - 1)");
    let b = codes("evenP = (n) => n == 0 ? true : oddP(n - 1)\noddP = (n) => n == 0 ? false : evenP(n - 1)");
    assert_eq!(a, b, "canonical codes invariant under renaming");
}

#[test]
fn mu06_invariant_under_member_permutation() {
    // Reordering the bindings must not change the canonical codes (law 5).
    let a = codes("p = (n) => n == 0 ? 1 : q(n - 1)\nq = (n) => n == 0 ? 2 : p(n - 1)");
    let b = codes("q = (n) => n == 0 ? 2 : p(n - 1)\np = (n) => n == 0 ? 1 : q(n - 1)");
    assert_eq!(a, b, "canonical codes invariant under member permutation");
}

#[test]
fn distinct_groups_have_distinct_codes() {
    // Sanity: a genuinely different body yields a different canonical code.
    let a = codes("f = (n) => n == 0 ? 0 : f(n - 1)");
    let b = codes("g = (n) => n == 0 ? 1 : g(n - 1)");
    assert_ne!(a, b);
}
