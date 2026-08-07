//! The property harness (Part I): `eval ∘ normalize = eval` and idempotence,
//! checked against the oracle over a corpus of programs, plus per-rule checks of
//! the template normalizations.

use super::*;
use crate::desugar::Desugarer;
use crate::interner::Interner;
use crate::lex::lex;
use crate::oracle::{Oracle, TrapClass};
use crate::parse::{parse_expression, parse_program};

/// The evaluation outcome, compared **across interners**: the rendered value, or
/// the trap class, or exhaustion.
///
/// Rendering rather than pointer-comparing is the whole point. The two runs must
/// not share an interner: a lambda the phase rewrote canonicalizes to the same
/// shape as the one it came from, so a shared interner hands the second run the
/// *first* run's closure and it re-executes the original body. The harness would
/// then be comparing a run against itself, and every body-level rewrite — sound
/// or not — would pass.
#[derive(PartialEq, Eq, Debug)]
enum Observed {
    Value(String),
    Trap(TrapClass),
    Exhausted,
}

/// Lower `src`, optionally normalize, and run — each call in its own interner.
fn observe(src: &str, normalized: bool, fuel: Option<u64>) -> Observed {
    let mut interner = Interner::new();
    let sprogram = parse_program(lex(src).expect("lex")).expect("parse");
    let module = Desugarer::new(&mut interner)
        .program(&sprogram)
        .expect("desugar");
    let module = if normalized {
        normalize_module(&module, &mut interner)
    } else {
        module
    };

    let env = crate::oracle::harness::prelude_env(&mut interner);
    let mut oracle = match fuel {
        Some(f) => Oracle::new_fueled(&mut interner, f),
        None => Oracle::new(&mut interner),
    };
    let result = oracle.run_module_in(&module, &env);
    if oracle.out_of_fuel {
        return Observed::Exhausted;
    }
    match result {
        Ok(value) => Observed::Value(crate::oracle::render_value(&value, false)),
        Err(trap) => Observed::Trap(trap.class),
    }
}

/// Desugar a program, evaluate both it and its normalization, and confirm the
/// two outcomes agree (`eval ∘ normalize = eval`) — then confirm `normalize` is
/// idempotent on the kernel form.
fn assert_normalization_sound(src: &str) {
    assert_eq!(
        observe(src, false, None),
        observe(src, true, None),
        "normalization changed evaluation for:\n{src}"
    );

    // idempotence: normalize(normalize(m)) == normalize(m)
    let mut interner = Interner::new();
    let sprogram = parse_program(lex(src).expect("lex")).expect("parse");
    let module = Desugarer::new(&mut interner)
        .program(&sprogram)
        .expect("desugar");
    let normalized = normalize_module(&module, &mut interner);
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
    // the arithmetic slice (A12) — chains the rewrite actually rearranges
    "f = (x, y) => 1 + x - y + 2 * x + 5\nf(3, 2)",
    "g = (x) => -x + x + 3 * x - 1\ng(4)",
    "h = (a, b) => (a - b) * (2 * 3)\nh(9, 4)",
    "k = (x) => x * 2 + x * 3 - x\nk(7)",
    "1 / 3 * 3 - 1",
    // and chains whose operands are anchored, where it must *not* rearrange
    "p = () => 2\nq = () => 5\nr = () => p() - q() + p()\nr()",
    "s = (n) => n <= 0 ? 0 : s(n - 1) + n\ns(6)",
    // the string rail must stay out of it entirely
    "a = \"x\"\nb = \"y\"\na ++ b ++ a",
];

/// Programs whose *divergence* is the observable: each must exhaust or complete
/// identically before and after normalization, at every budget. §8 names this
/// method — "divergence included — fuel-differential testing in the harness" —
/// because an evaluation-order rewrite is invisible to any test that only ever
/// runs to completion.
///
/// **Scope [user, 2026-08-07].** The law is claimed for programs the analyzer
/// *accepts*. Under Principle 9 an accepted program cannot hang, and safety
/// analysis means it cannot trap, so in pure code there is no bottom left for
/// operand order to distinguish — reordering there is unobservable and legal.
/// Rows that pit a diverging operand against a trapping one therefore no longer
/// belong: both are programs that do not compile. Effect order, which *is*
/// observable, is checked directly by [`normalization_preserves_effect_order`].
const DIVERGENCE_CORPUS: &[&str] = &[
    // zero-annihilation must not fire: the loop still runs. This one is
    // world-independent — the coefficient is kept whether or not anchoring
    // applies — so it holds in pure code too.
    "loop = (x) => loop(x)\nz = (x) => 0 * loop(x)\nz(1)",
    // a terminating control, so the budgets below are not all exhaustion.
    "work = (n) => n == 0 ? 0 : work(n - 1)\nwork(50) + work(50)",
];

/// The budgets to sweep. Small enough that the tail ones straddle the boundary
/// where a doubled call stops fitting — which is the whole point.
const FUEL_BUDGETS: &[u64] = &[50, 200, 800, 3_000, 6_000];

#[test]
fn normalization_preserves_evaluation_over_corpus() {
    for src in CORPUS {
        assert_normalization_sound(src);
    }
}

/// Act bodies are where order is observable, and the property is direct: the
/// emitted output must be identical before and after normalization.
#[test]
fn normalization_preserves_effect_order() {
    const ACT_CORPUS: &[&str] = &[
        "@effect p = () => { println(\"P\") }\n\
         @effect q = () => { println(\"Q\") }\n\
         @effect e = () => { p()\n q() }\n\
         e()\n",
        "@effect p = () => { println(\"P\") }\n\
         @effect q = () => { println(\"Q\") }\n\
         @effect e = () => { q()\n p()\n q() }\n\
         e()\n",
        "@state n = 0\n\
         @mutate bump = () => { n := n + 1 }\n\
         @effect e = () => { bump()\n println(`${n}`)\n bump() }\n\
         e()\n",
    ];
    for src in ACT_CORPUS {
        let mut interner = Interner::new();
        let sprogram = parse_program(lex(src).expect("lex")).expect("parse");
        let raw = Desugarer::new(&mut interner)
            .program(&sprogram)
            .expect("desugar");
        let normalized = normalize_module(&raw, &mut interner);

        let mut run = |module: &Module| {
            let io = std::rc::Rc::new(std::cell::RefCell::new(crate::oracle::HostIo::default()));
            let env = crate::oracle::harness::prelude_env(&mut interner);
            crate::oracle::harness::install_host_effects(&mut interner, &env, &io);
            let _ = Oracle::new(&mut interner).run_module_in(module, &env);
            io.borrow().output.clone()
        };
        let before = run(&raw);
        let after = run(&normalized);
        assert_eq!(
            before, after,
            "normalization changed effect order for:\n{src}"
        );
        assert!(!before.is_empty(), "the row emitted nothing: {src}");
    }
}

#[test]
fn normalization_preserves_divergence_at_every_budget() {
    for src in DIVERGENCE_CORPUS {
        for &fuel in FUEL_BUDGETS {
            assert_eq!(
                observe(src, false, Some(fuel)),
                observe(src, true, Some(fuel)),
                "normalization changed the outcome at fuel {fuel} for:\n{src}"
            );
        }
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
    // No template, no arithmetic ⇒ a structurally-equal kernel form.
    let mut interner = Interner::new();
    let sexpr = parse_expression(lex("(n) => [n, n.field, g(n)]").unwrap()).unwrap();
    let kernel = Desugarer::new(&mut interner).expr(&sexpr).unwrap();
    let normalized = normalize_expr(&kernel, &mut interner);
    assert_eq!(kernel, normalized);
}

// ── Per-rule checks of the arithmetic slice (μ §8) ───────────────────────────

/// Do two spellings share a normal form? One interner, so the constants the
/// rewrite mints are pointer-comparable.
fn same_normal_form(a: &str, b: &str) -> bool {
    let mut interner = Interner::new();
    let mut norm = |src: &str| {
        let sexpr = parse_expression(lex(src).unwrap()).unwrap();
        let kernel = Desugarer::new(&mut interner).expr(&sexpr).unwrap();
        normalize_expr(&kernel, &mut interner)
    };
    norm(a) == norm(b)
}

#[test]
fn the_arithmetic_slice_governs_the_lowered_form() {
    // The three permitted rewrites, now visible to the oracle and the analyzer.
    assert!(same_normal_form("(a, b) => a + b", "(a, b) => b + a")); // reordering
    assert!(same_normal_form("(a) => a + 1 + 2", "(a) => a + 3")); // constant folding
    assert!(same_normal_form("(x) => x + x", "(x) => 2 * x")); // H-05
    assert!(same_normal_form(
        "(x, y) => 2 * x + 3 * y",
        "(x, y) => 3 * y + 2 * x"
    ));
    // `-x` normalizes to `(-1) * x`, so the two negation spellings agree.
    assert!(same_normal_form("(x, y) => -x + y", "(x, y) => y - x"));
}

#[test]
fn the_permanent_exclusions_do_not_fire() {
    // MU-10, read at the phase: each pair must stay *distinct*.
    assert!(!same_normal_form("(x) => x + 0", "(x) => x")); // identity elimination
    assert!(!same_normal_form("(f, x) => 0 * f(x)", "(f, x) => 0")); // zero-annihilation
    assert!(!same_normal_form("(x) => x - x", "(x) => 0")); // cancellation
    // …but the cancelled chain still reorders, so its spellings agree.
    assert!(same_normal_form("(x) => -x + x", "(x) => x - x"));
}
