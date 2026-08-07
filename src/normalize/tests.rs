//! The property harness (Part I): `eval ∘ normalize = eval` and idempotence,
//! checked against the oracle over a corpus of programs, plus per-rule checks of
//! the template normalizations.

use super::*;
use crate::desugar::Desugarer;
use crate::interner::Interner;
use crate::lex::lex;
use crate::oracle::{Oracle, TrapClass};
use crate::parse::{parse_expression, parse_program};
use crate::value::ValueRef;

/// The evaluation outcome, comparable across the original and normalized forms
/// (same interner ⇒ values are pointer-comparable; traps compare by class).
type Observed = Result<ValueRef, TrapClass>;

fn run(module: &Module, interner: &mut Interner) -> Observed {
    Oracle::new(interner)
        .run_module(module)
        .map_err(|t| t.class)
}

/// Desugar a program, evaluate both it and its normalization, and confirm the
/// two outcomes agree (`eval ∘ normalize = eval`) — then confirm `normalize` is
/// idempotent on the kernel form.
fn assert_normalization_sound(src: &str) {
    let mut interner = Interner::new();
    let sprogram = parse_program(lex(src).expect("lex")).expect("parse");
    let module = Desugarer::new(&mut interner)
        .program(&sprogram)
        .expect("desugar");

    let normalized = normalize_module(&module, &mut interner);

    // eval ∘ normalize = eval
    let original = run(&module, &mut interner);
    let after = run(&normalized, &mut interner);
    assert_eq!(
        original, after,
        "normalization changed evaluation for:\n{src}"
    );

    // idempotence: normalize(normalize(m)) == normalize(m)
    let twice = normalize_module(&normalized, &mut interner);
    assert_eq!(
        twice, normalized,
        "normalization is not idempotent for:\n{src}"
    );
}

/// The corpus: a spread of programs exercising every node kind. Any future rule
/// that changes what these evaluate to is caught here.
const CORPUS: &[&str] = &[
    // arithmetic / exactness / Indeterminate values
    "0.1 + 0.2 == 0.3",
    "1 / 3 + 1 / 3 + 1 / 3",
    "1 / 0",
    "2 ** 10 - 1",
    // truthiness desugarings
    "false ?? 7",
    "~false || 7",
    "!~null",
    "true ? 1 : 2",
    // functions / recursion / hasks / pipes
    "factorial = (n) => n == 0 ? 1 : n * factorial(n - 1)\nfactorial(5)",
    "isEven = (n) => n == 0 ? true : isOdd(n - 1)\nisOdd = (n) => n == 0 ? false : isEven(n - 1)\nisEven(8)",
    "inc = # _ + 1\n5 |> inc",
    // match / patterns
    "v = 3\nv :: {\n 0 => \"z\"\n n when n > 0 => \"pos\"\n _ => \"neg\"\n }",
    "head = (t) => t :: { [h, ..._] => h }\nhead([10, 20])",
    // construction / access / slices / strings
    "{ ...{ a: 1 }, a: 9 }.a",
    "[1, 2, 3, 4][-2...]",
    "\"a\u{1F600}b\"[1]",
    // templates (the rule's target)
    "`hello`",
    "`x = ${1 / 2}`",
    "`a${1}b${2}c`",
    "greet = (n) => `hi ${n}`\ngreet(\"there\")",
    // mutation
    "@state count = 0\n@mutate inc = () => { count := count + 1 }\ninc()\ninc()\ncount",
];

#[test]
fn normalization_preserves_evaluation_over_corpus() {
    for src in CORPUS {
        assert_normalization_sound(src);
    }
}

/// **The wiring pin.** Normalization is evaluation-preserving *by construction*, so no
/// amount of running programs can tell whether the pipeline actually applies it — unwire
/// it and every other row in this file still passes. This row observes the **form**
/// instead: lowering a literal template must yield a `Const`, where bare desugaring
/// leaves a `Template`. It is the only test that fails if the front ends stop routing
/// through `lower_program`.
#[test]
fn the_pipeline_lowers_through_normalization() {
    fn last_expr(m: &Module) -> &Expr {
        match m.items.last() {
            Some(Item::Stmt(e)) | Some(Item::Bind(crate::ast::Bind { value: e, .. })) => e,
            other => panic!("expected a trailing expression, got {other:?}"),
        }
    }

    let src = "`hello`\n";
    let mut interner = Interner::new();
    let sprogram = parse_program(lex(src).expect("lex")).expect("parse");

    let raw = Desugarer::new(&mut interner)
        .program(&sprogram)
        .expect("desugar");
    assert!(
        matches!(last_expr(&raw), Expr::Template(_)),
        "bare desugaring keeps the template node: {:?}",
        last_expr(&raw)
    );

    let lowered = crate::desugar::lower_program(&sprogram, &mut interner).expect("lower");
    assert!(
        matches!(last_expr(&lowered), Expr::Const(_)),
        "lowering must fold a literal template to a constant: {:?}",
        last_expr(&lowered)
    );

    // And lowering is exactly desugar-then-normalize, not some other pass.
    let expected = normalize_module(&raw, &mut interner);
    assert_eq!(lowered, expected, "lowering is desugar ∘ normalize");
}

// ── Per-rule checks of the template normalizations ───────────────────────────

fn normalize_src_expr(src: &str) -> Expr {
    let mut interner = Interner::new();
    let sexpr = parse_expression(lex(src).unwrap()).unwrap();
    let kernel = Desugarer::new(&mut interner).expr(&sexpr).unwrap();
    normalize_expr(&kernel, &mut interner)
}

#[test]
fn literal_template_folds_to_a_constant() {
    // `hello` has no interpolations ⇒ it is the string constant "hello".
    assert!(matches!(normalize_src_expr("`hello`"), Expr::Const(_)));
    // an empty template folds to the empty string constant
    assert!(matches!(normalize_src_expr("``"), Expr::Const(_)));
}

#[test]
fn interpolated_template_stays_a_template_with_folded_segments() {
    // `a${1}b${2}c` keeps its interps; literal runs stay single segments.
    match normalize_src_expr("`a${1}b${2}c`") {
        Expr::Template(parts) => {
            // segment, interp, segment, interp, segment — no two adjacent segments
            let mut prev_was_segment = false;
            for p in &parts {
                let is_seg = matches!(p, TemplatePart::Segment(_));
                assert!(
                    !(is_seg && prev_was_segment),
                    "adjacent segments not folded"
                );
                prev_was_segment = is_seg;
            }
            assert!(parts.iter().any(|p| matches!(p, TemplatePart::Interp(_))));
        }
        other => panic!("expected a template, got {other:?}"),
    }
}

#[test]
fn fold_segments_merges_adjacent() {
    // Directly exercise the fold on a hand-built part list (adjacency rarely
    // arises from parsing, so construct it).
    let s = |t: &str| TemplatePart::Segment(t.to_string());
    let folded = super::fold_segments(vec![s("a"), s("b"), s("c")]);
    assert_eq!(folded, vec![s("abc")]);
}

#[test]
fn normalize_is_identity_when_no_rule_applies() {
    // A program with no templates normalizes to a structurally-equal kernel form.
    let mut interner = Interner::new();
    let sexpr = parse_expression(lex("(n) => n * 2 + 1").unwrap()).unwrap();
    let kernel = Desugarer::new(&mut interner).expr(&sexpr).unwrap();
    let normalized = normalize_expr(&kernel, &mut interner);
    assert_eq!(kernel, normalized);
}
