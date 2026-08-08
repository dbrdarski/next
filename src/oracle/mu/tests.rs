//! Recursive construction-window regressions plus the value-identity properties
//! formerly (and incorrectly) assigned to a serialized group template.

use super::group_windows;
use crate::ast::{BindTarget, Expr, Item};
use crate::desugar::Desugarer;
use crate::interner::Interner;
use crate::lex::lex;
use crate::oracle::run_source_in;
use crate::parse::parse_program;

/// Desugar a program and return `(item index, name, initializer)` triples.
fn bindings(src: &str) -> Vec<(usize, String, Expr)> {
    let mut interner = Interner::new();
    let prog = parse_program(lex(src).unwrap()).unwrap();
    let module = Desugarer::new(&mut interner).program(&prog).unwrap();
    module
        .items
        .iter()
        .enumerate()
        .filter_map(|(item, it)| match it {
            Item::Bind(b) => match &b.target {
                BindTarget::Name(name) => Some((item, name.clone(), b.value.clone())),
                BindTarget::Pattern(_) => None,
            },
            _ => None,
        })
        .collect()
}

#[test]
fn mu01_non_recursive_binding_has_no_construction_window() {
    assert!(group_windows(&bindings("a = (n) => n + 1")).is_empty());
}

#[test]
fn self_recursion_introduces_a_single_member_window() {
    let windows = group_windows(&bindings("f = (n) => n == 0 ? 0 : f(n - 1)"));
    assert_eq!(windows.len(), 1);
    assert_eq!(windows[0].start, 0);
    assert_eq!(windows[0].end, 0);
    assert_eq!(windows[0].members, [(0, "f".to_string())]);
}

#[test]
fn mu03_minimal_window_splits_out_acyclic_neighbour() {
    let windows = group_windows(&bindings("a = () => b\nb = () => a\nc = () => a"));
    assert_eq!(windows.len(), 1);
    assert_eq!(windows[0].start, 0);
    assert_eq!(windows[0].end, 1);
    assert_eq!(
        windows[0].members,
        [(0, "a".to_string()), (1, "b".to_string())]
    );
}

#[test]
fn mu06_value_identity_is_invariant_under_renaming() {
    let mut interner = Interner::new();
    let is_even = run_source_in(
        "isEven = (n) => n == 0 ? true : isOdd(n - 1)\n\
         isOdd = (n) => n == 0 ? false : isEven(n - 1)\n\
         isEven",
        &mut interner,
    )
    .unwrap()
    .0;
    let renamed = run_source_in(
        "evenP = (k) => k == 0 ? true : oddP(k - 1)\n\
         oddP = (k) => k == 0 ? false : evenP(k - 1)\n\
         evenP",
        &mut interner,
    )
    .unwrap()
    .0;
    assert!(is_even.ptr_eq(&renamed));
}

#[test]
fn mu06_value_identity_is_invariant_under_member_permutation() {
    let mut interner = Interner::new();
    let first = run_source_in(
        "p = (n) => n == 0 ? 1 : q(n - 1)\n\
         q = (n) => n == 0 ? 2 : p(n - 1)\n\
         p",
        &mut interner,
    )
    .unwrap()
    .0;
    let permuted = run_source_in(
        "q = (n) => n == 0 ? 2 : p(n - 1)\n\
         p = (n) => n == 0 ? 1 : q(n - 1)\n\
         p",
        &mut interner,
    )
    .unwrap()
    .0;
    assert!(first.ptr_eq(&permuted));
}

#[test]
fn distinct_recursive_functions_have_distinct_values() {
    let mut interner = Interner::new();
    let zero = run_source_in("f = (n) => n == 0 ? 0 : f(n - 1)\nf", &mut interner)
        .unwrap()
        .0;
    let one = run_source_in("g = (n) => n == 0 ? 1 : g(n - 1)\ng", &mut interner)
        .unwrap()
        .0;
    assert!(!zero.ptr_eq(&one));
}
