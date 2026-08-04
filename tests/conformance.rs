//! The conformance & regression suite, keyed by the **stable IDs** of
//! `next-test-suite-specification-v0-1.md`.
//!
//! One test per ID (grep the ID to find it). This is the *conformance* layer —
//! the detailed structural/property tests live in the unit-test modules
//! (`desugar::tests` for D-row structure, `normalize::tests` for the H-row
//! generators, `oracle::tests` for μ/PR details) and are referenced per row.
//!
//! Verdict vocabulary: `VALUE v` · `TRAP class` · `LEX-ERROR` / `PARSE-ERROR` ·
//! `DESUGAR≡` · registers `PENDING-§5`, `PIN-UNICODE`, `RECOVER`. Phase A ships
//! as `#[ignore]`d stubs with recorded verdicts, per the spec's implementation
//! note. Test IDs are stable; never delete a case — supersede with a note.

use next::desugar::Desugarer;
use next::interner::Interner;
use next::lex::lex;
use next::oracle::harness::{check_source, prelude_env, run_with_io};
use next::oracle::{Oracle, TrapClass, run_program_commits, run_program_value};
use next::parse::parse_program;
use next::rational::Rational;
use next::value::ValueRef;

// ── Shared helpers ───────────────────────────────────────────────────────────

fn eval(src: &str) -> ValueRef {
    run_program_value(src).expect("evaluated without trapping")
}

fn vtrue(src: &str) {
    assert_eq!(
        eval(src).as_boolean(),
        Some(true),
        "expected VALUE true: {src}"
    );
}

fn trap(src: &str) -> TrapClass {
    run_program_value(src).expect_err("expected a trap").class
}

fn lex_error(src: &str) -> bool {
    lex(src).is_err()
}

fn parse_error(src: &str) -> bool {
    match lex(src) {
        Err(_) => false, // must be a *parse* error, not a lex error
        Ok(toks) => parse_program(toks).is_err(),
    }
}

/// Rejected at any front-end or evaluation stage (spec rows that allow either).
fn rejected_any_stage(src: &str) -> bool {
    let Ok(toks) = lex(src) else { return true };
    let Ok(sp) = parse_program(toks) else {
        return true;
    };
    let mut i = Interner::new();
    if Desugarer::new(&mut i).program(&sp).is_err() {
        return true;
    }
    run_program_value(src).is_err()
}

/// Evaluate in a caller-supplied interner (pointer observability across runs).
fn eval_in(interner: &mut Interner, src: &str) -> ValueRef {
    let toks = lex(src).expect("lex ok");
    let sp = parse_program(toks).expect("parse ok");
    let module = Desugarer::new(interner).program(&sp).expect("desugar ok");
    let env = prelude_env(interner);
    let mut oracle = Oracle::new(interner);
    oracle
        .run_module_in(&module, &env)
        .expect("evaluated without trapping")
}

fn num_eq(v: &ValueRef, n: i64) {
    assert_eq!(v.as_number(), Some(&Rational::from(n)), "expected {n}");
}

fn str_of(v: &ValueRef) -> String {
    String::from_utf16_lossy(v.as_str_units().expect("a string"))
}

// ═════════════════════════════════════════════════════════════════════════════
// Phase 0 — Value layer (numbers, interning, function equality)
// ═════════════════════════════════════════════════════════════════════════════

mod phase0 {
    use super::*;

    #[test]
    fn n01_exactness_flagship() {
        vtrue("0.1 + 0.2 == 0.3");
    }

    #[test]
    fn n02_third_times_three() {
        vtrue("(1/3) * 3 == 1");
    }

    #[test]
    fn n03_b2_printing() {
        // decimal iff the reduced denominator's primes ⊆ {2, 5}
        let r = |n: i64, d: i64| Rational::new(n.into(), d.into()).to_string();
        assert_eq!(r(1, 2), "0.5");
        assert_eq!(r(3, 20), "0.15");
        assert_eq!(r(1, 8), "0.125");
        assert_eq!(r(1, 3), "1/3");
        assert_eq!(r(-1, 2), "-0.5");
        assert_eq!(r(5, 1), "5");
    }

    #[test]
    fn n04_literal_forms() {
        vtrue("1e-2 == 1/100");
        vtrue(".5 == 1/2");
        vtrue("0xFF == 255");
        vtrue("1_000 == 1000");
    }

    #[test]
    fn n05_banned_literals_lex_error() {
        assert!(lex_error("123n"), "bigint suffix is banned, hinted");
        assert!(lex_error("017"), "legacy octal / leading zeros are banned");
        assert!(lex_error("x = 5."), "trailing-dot numerals are banned");
    }

    #[test]
    fn i01_tuple_interning() {
        vtrue("[1, 2] == [1, 2]");
        let mut i = Interner::new();
        let a = eval_in(&mut i, "[1, 2]");
        let b = eval_in(&mut i, "[1, 2]");
        assert!(a.ptr_eq(&b), "same value = same pointer");
    }

    #[test]
    fn i02_record_field_order_not_identity() {
        vtrue("{a: 1, b: 2} == {b: 2, a: 1}");
        let mut i = Interner::new();
        let a = eval_in(&mut i, "{a: 1, b: 2}");
        let b = eval_in(&mut i, "{b: 2, a: 1}");
        assert!(a.ptr_eq(&b));
    }

    #[test]
    fn i03_canonical_reduction() {
        let mut i = Interner::new();
        let a = eval_in(&mut i, "2/4");
        let b = eval_in(&mut i, "1/2");
        assert!(a.ptr_eq(&b), "2/4 and 1/2 intern to one value");
    }

    #[test]
    fn i04_structural_sharing() {
        let mut i = Interner::new();
        let a = eval_in(&mut i, "\"abc\"");
        let b = eval_in(&mut i, "\"abc\"");
        assert!(a.ptr_eq(&b));
        // Equal nested structures share subtrees.
        let outer = eval_in(&mut i, "[[1, 2], 3]");
        let inner = eval_in(&mut i, "[1, 2]");
        assert!(
            outer.as_tuple().unwrap()[0].ptr_eq(&inner),
            "shared subtree"
        );
    }

    #[test]
    fn fe01_binding_alias() {
        vtrue("f = x => x + 1\ng = f\nf == g");
    }

    #[test]
    fn fe02_same_code_equal_captures() {
        vtrue("makeAdder = n => x => x + n\nmakeAdder(1) == makeAdder(1)");
        assert_eq!(
            eval("makeAdder = n => x => x + n\nmakeAdder(1) == makeAdder(2)").as_boolean(),
            Some(false),
        );
    }

    #[test]
    fn fe03_spelling_variants_across_source_sites() {
        // PENDING-§5 target behavior: flips to true when the canonicalizer keys
        // interning. (The register forbids asserting the interim inequality as
        // desired — so this asserts the FINAL expectation.)
        vtrue("f = x => x + 1\ng = y => y + 1\nf == g");
    }

    #[test]
    fn fe04_self_reference_pair() {
        // (F7 flag retired — closures compare equal via the value-graph
        // bisimulation; PENDING-§5 covers only the interning mechanism.)
        vtrue("y = [() => y]\nz = [() => z]\ny == z");
    }

    #[test]
    fn fe05_group_pair() {
        // RULED — shape identity [user, 2026-07-17]; mechanism PENDING-§5.
        vtrue("a = [() => b]\nb = [() => a]\na2 = [() => b]\na == a2");
    }

    #[test]
    fn fe06_symmetric_collapse() {
        // RULED — the two-steps-of-y principle.
        vtrue("a = [() => b]\nb = [() => a]\ny = [() => y]\na == b");
        vtrue("a = [() => b]\nb = [() => a]\ny = [() => y]\na == y");
    }

    #[test]
    fn fe07_act_kind_is_part_of_the_key() {
        // Same params/body/captures but different actKind ⇒ unequal
        // [companion review 2026-07-21].
        assert_eq!(
            eval("f = () => 1\n@effect g = () => 1\nf == g").as_boolean(),
            Some(false),
        );
    }

    #[test]
    fn mu19_same_group_construction_reference_is_legal() {
        // A reference to another group member *within construction* is an internal
        // μ edge, never a read — the mutual group constructs without trapping.
        num_eq(
            &eval("a = [() => b]\nb = [() => a]\na[0]()[0]()[0]()\n1"),
            1,
        );
    }

    #[test]
    fn mu18_open_member_observation_traps() {
        // a = [() => b]; seen = a == a; b = [() => a]  → TRAP unbound-evaluation.
        assert_eq!(
            trap("a = [() => b]\nseen = a == a\nb = [() => a]\nseen"),
            TrapClass::UnboundEvaluation,
        );
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// Phase 1 — Lexer & parser (grammar v0.1; P-01…P-15 are the E2 worked parses)
// ═════════════════════════════════════════════════════════════════════════════

mod phase1 {
    use super::*;

    #[test]
    fn p01_forward_pipes_left_associate() {
        // a |> f |> g ≡ g(f(a))
        let v = eval("f = x => x + 1\ng = x => x * 2\na = 3\n[a |> f |> g, g(f(a))]");
        let t = v.as_tuple().unwrap();
        assert!(t[0].ptr_eq(&t[1]));
        num_eq(&t[0], 8);
    }

    #[test]
    fn p02_backward_pipes_right_associate() {
        // f <| g <| x ≡ f(g(x))
        let v = eval("f = x => x + 1\ng = x => x * 2\n[f <| g <| 3, f(g(3))]");
        let t = v.as_tuple().unwrap();
        assert!(t[0].ptr_eq(&t[1]));
        num_eq(&t[0], 7);
    }

    #[test]
    fn p03_pipe_mixing_ban() {
        assert!(
            parse_error("a |> f <| b"),
            "unparenthesized |>/<| mixing is a parse error"
        );
    }

    #[test]
    fn p04_two_whole_hask_stages() {
        // values |> # f(_, k) |> g — a hask stage in a pipeline
        let v = eval("f = (a, b) => a + b\ng = x => x * 2\nk = 10\n1 |> # f(_, k) |> g");
        num_eq(&v, 22);
    }

    #[test]
    fn p05_hask_body_extends_through_tighter_tiers() {
        let v = eval("h = # _ * 2 + 1\nh(3)");
        num_eq(&v, 7);
    }

    #[test]
    fn p06_hask_binds_whole_ternary() {
        assert_eq!(
            str_of(&eval("h = # _ > 0 ? \"pos\" : \"neg\"\nh(1)")),
            "pos"
        );
        assert_eq!(
            str_of(&eval("h = # _ > 0 ? \"pos\" : \"neg\"\nh(-1)")),
            "neg"
        );
    }

    #[test]
    fn p07_grouped_match_hask() {
        let v = eval("h = #( _ :: { 1 => \"one\"\n_ => \"other\" } )\nh(1)");
        assert_eq!(str_of(&v), "one");
    }

    #[test]
    fn p08_immediate_hask_invocation_needs_grouping() {
        let v = eval("f = x => x + 1\n(# f(_))(3)");
        num_eq(&v, 4);
    }

    #[test]
    fn p09_pipe_binds_tighter_than_match() {
        // a |> b :: {…} ≡ (a |> b) :: {…}
        let v = eval("b = x => x + 1\n2 |> b :: { 3 => \"y\"\n_ => \"n\" }");
        assert_eq!(str_of(&v), "y");
    }

    #[test]
    fn p10_match_left_of_pipe() {
        // x :: {…} |> f pipes the match result
        let v = eval("f = x => x * 2\n1 :: { 1 => 5\n_ => 0 } |> f");
        num_eq(&v, 10);
    }

    #[test]
    fn p11_defaulting_groups_left() {
        // a ?? b || c ≡ (a ?? b) || c — right grouping would give false here.
        assert_eq!(str_of(&eval("false ?? \"b\" || \"c\"")), "c");
    }

    #[test]
    fn p12_neg_binds_looser_than_pow() {
        // -x ** 2 ≡ -(x ** 2). (Bound on one line: a bare `-x ** 2` continuation
        // line would attach to the previous statement — the §1.1 stated hazard,
        // P-23's leading-`-` lint case.)
        let v = eval("x = 2\ny = -x ** 2\ny");
        num_eq(&v, -4);
    }

    #[test]
    fn p13_negative_exponent_legal() {
        vtrue("2 ** -3 == 1/8");
    }

    #[test]
    fn p14_from_end_slice() {
        vtrue("t = [1, 2, 3]\nt[-2...] == [2, 3]");
    }

    #[test]
    fn p15_total_chain_parses() {
        // u?.name.first parses (its semantics are O-03's row).
        assert!(!parse_error("u?.name.first"), "must parse");
    }

    #[test]
    fn p16_ternary_dot5_lookahead() {
        // a ?.5 : b — T1: no `?.` token is minted before a digit.
        let v = eval("x = true\nx ?.5 : 9");
        assert_eq!(v.as_number(), Some(&Rational::new(1.into(), 2.into())));
    }

    #[test]
    fn p17_slice_lexes_through_dots() {
        // t[1...3] lexes as `1` `...` `3` (trailing-dot ban synergy).
        vtrue("t = [9, 8, 7, 6]\nt[1...3] == [8, 7]");
    }

    #[test]
    fn p18_arrow_returning_empty_record() {
        let v = eval("f = x => {}\nf(1)");
        assert_eq!(
            v.as_record().map(|r| r.len()),
            Some(0),
            "x => {{}} yields an empty Record"
        );
    }

    #[test]
    fn p19_empty_act_block() {
        // @effect f = () => { } — the 1.0.3 brace exception: an empty act Block.
        let (v, _io) = run_with_io("@effect f = () => { }\nf()").expect("runs");
        assert!(
            v.is_null(),
            "program ends in an effect statement; value null"
        );
    }

    #[test]
    fn p20_two_statements_one_line() {
        assert!(parse_error("x = 1 y = 2"), "L1: one statement per line");
    }

    #[test]
    fn p21_two_arms_one_line() {
        assert!(
            parse_error("x = 1 :: { 1 => 1 2 => 2 }"),
            "L2: one arm per line"
        );
    }

    #[test]
    fn p22_when_where_are_not_reserved() {
        let v = eval("when = 5\nwhere = 2\nwhen + where");
        num_eq(&v, 7);
    }

    #[test]
    fn p23_operator_leading_continuation() {
        let v = eval("f = x => x + 1\n1\n  |> f");
        num_eq(&v, 2);
    }

    #[test]
    fn p24_template_brace_depth() {
        // `a${ {b: "}"} }c` — one interpolation; the inner brace-string does not
        // close it. Renders the record canonically.
        let v = eval("`a${ {b: \"}\"} }c`");
        assert_eq!(str_of(&v), "a{b: \"}\"}c");
    }

    #[test]
    fn p25_comments_do_not_nest() {
        let v = eval("x = 1 /* /* */\nx");
        num_eq(&v, 1);
    }

    #[test]
    fn p26_no_elision_no_duplicate_keys() {
        assert!(parse_error("x = [1, , 3]"), "elision is banned");
        assert!(
            parse_error("x = { a: 1, a: 2 }"),
            "duplicate literal keys are banned"
        );
    }

    #[test]
    fn p27_import_forms_parse() {
        assert!(
            !parse_error("import { area } from Geometry"),
            "named import parses"
        );
        assert!(!parse_error("import Oddo.Utils"), "module import parses");
    }

    #[test]
    fn p27b_headerless_export_rejected() {
        // E12: the header is required iff the file exports anything (desugar-level).
        assert!(rejected_any_stage("export x = 1"));
    }

    #[test]
    fn p28_value_side_act_annotation_banned() {
        assert!(
            parse_error("name = @effect (x) => {}"),
            "value-side @ does not exist"
        );
    }

    #[test]
    fn p29_middle_rest_legal_two_rests_banned() {
        vtrue("[_, x, ..._, y] = [1, 2, 3, 4, 5]\nx == 2 && y == 5");
        assert!(parse_error("[...a, ...b] = t"), "one rest per level");
    }

    #[test]
    fn p30_alternation_is_binding_free() {
        // A named capture inside an alternative REJECTs (parse- or analyzer-phase;
        // either, with the right message).
        assert!(rejected_any_stage("v = 1\nv :: { 1 | x => 2 }"));
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// Phase 2 — Desugar equivalences (AST §4; structural facet in desugar::tests)
// ═════════════════════════════════════════════════════════════════════════════

mod phase2 {
    use super::*;

    #[test]
    fn d01_ternary() {
        // Ruled row: `c ? t : e` ≡ Match(∅, [Arm(guard: c, t), Arm(e)]) — the
        // condition is a strict tested seat (T-10); single evaluation holds
        // because the condition occurs exactly once, in the guard.
        num_eq(&eval("true ? 1 : 2"), 1);
        num_eq(&eval("false ? 1 : 2"), 2);
    }

    #[test]
    fn d02_conjunction() {
        num_eq(&eval("true && 5"), 5);
        assert_eq!(eval("false && 5").as_boolean(), Some(false));
        // RULED [2026-07-22]: the left operand is a strict tested seat.
        assert_eq!(trap("0 && 1"), TrapClass::TestedSeat);
    }

    #[test]
    fn d03_disjunction() {
        // Ruled row: `a || b` ≡ Match(∅, [Arm(guard: a, true), Arm(b)]).
        num_eq(&eval("false || 5"), 5);
        assert_eq!(eval("true || 5").as_boolean(), Some(true));
        // RULED [2026-07-22]: the left operand is a strict tested seat.
        assert_eq!(trap("1 || 9"), TrapClass::TestedSeat);
    }

    #[test]
    fn d04_escaped_or_falsy_set() {
        // ~a || b — the falsy set is {false, null} exactly; 0 is truthy.
        num_eq(&eval("~0 || 5"), 0);
        num_eq(&eval("~null || 5"), 5);
    }

    #[test]
    fn d05_escaped_and() {
        num_eq(&eval("~0 && 5"), 5);
        assert!(eval("~null && 5").is_null());
    }

    #[test]
    fn d06_not() {
        vtrue("!false");
        assert_eq!(eval("!true").as_boolean(), Some(false));
        // RULED [2026-07-22]: the operand is a strict tested seat.
        assert_eq!(trap("!5"), TrapClass::TestedSeat);
    }

    #[test]
    fn d07_loosened_not() {
        // !~x — falsy-set negation: 0 is truthy, null is falsy.
        assert_eq!(eval("!~0").as_boolean(), Some(false));
        vtrue("!~null");
    }

    #[test]
    fn d08_nullish_scrutinee_evaluated_once() {
        // The side-effect counter proves single evaluation.
        let (v, io) = run_with_io("x = println(\"e\") ?? 5\nx").expect("runs");
        num_eq(&v, 5); // println returns null → coalesces to 5
        assert_eq!(io.output.len(), 1, "the scrutinee ran exactly once");
    }

    #[test]
    fn d09_block_body_is_scrutineeless_match() {
        // A block is a Match with implicit scrutinee; it PRODUCES via a `=>`
        // unconditional-exit arm statement (grammar §2), not via a trailing
        // expression (which is a discarded Stmt — the goes-nowhere lint).
        num_eq(&eval("f = x => { y = x + 1\n=> y * 2 }\nf(3)"), 8);
        // A guarded exit selects.
        num_eq(&eval("f = x => { when x > 0 => x\n=> 0 - x }\nf(-3)"), 3);
    }

    #[test]
    fn d10_alternation_expands_to_arms() {
        assert_eq!(
            str_of(&eval("3 :: { 1 | 3 => \"hit\"\n_ => \"miss\" }")),
            "hit"
        );
        assert_eq!(
            str_of(&eval("2 :: { 1 | 3 => \"hit\"\n_ => \"miss\" }")),
            "miss"
        );
    }

    #[test]
    fn d11_pin_is_equality_guard() {
        assert_eq!(
            str_of(&eval("target = 5\n5 :: { ^target => \"eq\"\n_ => \"ne\" }")),
            "eq"
        );
        assert_eq!(
            str_of(&eval("target = 5\n4 :: { ^target => \"eq\"\n_ => \"ne\" }")),
            "ne"
        );
    }

    #[test]
    fn d12_compound_write() {
        let src = "
            @state x = 1
            @mutate add = () => { x +:= 2 }
            add()
            x
        ";
        num_eq(&eval(src), 3);
    }

    #[test]
    fn d13_path_write() {
        // a.b.c := v ≡ read → functional update → one Write.
        let src = "
            @state obj = { a: { b: 1 } }
            @mutate set = () => { obj.a.b := 5 }
            set()
            obj.a.b
        ";
        num_eq(&eval(src), 5);
    }

    #[test]
    fn d14_splice_write() {
        // items[1...3] := r ≡ splice Write.
        let src = "
            @state items = [1, 2, 3, 4]
            @mutate splice = () => { items[1...3] := [9] }
            splice()
            items
        ";
        vtrue(&format!("{src} == [1, 9, 4]"));
    }

    #[test]
    fn d15_hask_forms() {
        num_eq(&eval("f = (a, b) => a + b\nk = 2\n(# f(_, k))(5)"), 7);
        num_eq(&eval("(# _1 + _1)(4)"), 8); // hole reuse
        // ^_ escape from an arm block and nested-# fresh numbering are covered
        // structurally in desugar::tests (hask_* rows).
    }

    #[test]
    fn d16_pipes_are_application() {
        num_eq(&eval("f = x => x + 1\n3 |> f"), 4);
        num_eq(&eval("f = x => x + 1\nf <| 3"), 4);
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// Phase 3 — Oracle semantics
// ═════════════════════════════════════════════════════════════════════════════

mod phase3 {
    use super::*;

    // ── T-01…T-13: one minimal program per trap class (renumbered — erratum
    //    2026-07-18; the former fourteenth, unprintable-interpolation, is deleted
    //    by the total-interpolation ruling — see PR-01…05). ─────────────────────

    #[test]
    fn t01_unbound_evaluation() {
        assert_eq!(trap("f()\nf = () => 1"), TrapClass::UnboundEvaluation);
    }

    #[test]
    fn t02_world_admission() {
        // An effect called from a pure function; a Write outside a mutator.
        let err = run_with_io("f = () => println(\"x\")\nf()").expect_err("must trap");
        assert_eq!(err.class, TrapClass::WorldAdmission);
        assert_eq!(trap("x := 1"), TrapClass::WorldAdmission);
    }

    #[test]
    fn t03_expecting_seat() {
        assert_eq!(trap("x = (5 :: { 1 => 2 })\nx"), TrapClass::ExpectingSeat);
    }

    #[test]
    fn t04_argument_obligation() {
        assert_eq!(trap("((a, b) => a)(1)"), TrapClass::ArgumentObligation);
    }

    #[test]
    fn t05_operation_safety() {
        assert_eq!(trap("1 + \"a\""), TrapClass::OperationSafety);
    }

    #[test]
    fn t06_undischarged_indeterminate() {
        assert_eq!(trap("(1/0) < 3"), TrapClass::UndischargedIndeterminate);
    }

    #[test]
    fn t07_null_receiver() {
        assert_eq!(trap("null.x"), TrapClass::NullReceiver);
    }

    #[test]
    fn t08_absent_field() {
        assert_eq!(trap("{a: 1}.b"), TrapClass::AbsentField);
    }

    #[test]
    fn t09_index_bounds() {
        assert_eq!(trap("[1, 2][5]"), TrapClass::IndexBounds);
        assert_eq!(trap("[1, 2][-3]"), TrapClass::IndexBounds);
    }

    #[test]
    fn t10_tested_seat() {
        // RULED [user, 2026-07-22]: plain ternary conditions, `&&`/`||` left
        // operands, and `!` operands are strict tested seats — trap tested-seat
        // on non-Booleans regardless of result position (guard-based lowering).
        assert_eq!(trap("5 ? 1 : 2"), TrapClass::TestedSeat);
        assert_eq!(trap("y = 5 ? 1 : 2\ny"), TrapClass::TestedSeat);
    }

    /// The catalog-conforming half of T-10 that is stable under either ruling:
    /// a guard seat IS strict — a non-Boolean *arm guard* traps tested-seat.
    #[test]
    fn t10a_non_boolean_guard_traps() {
        assert_eq!(trap("1 :: { _ when 5 => 2 }"), TrapClass::TestedSeat);
    }

    #[test]
    fn t11_refuted_binding() {
        assert_eq!(trap("[a, b] = [1]\na"), TrapClass::RefutedBinding);
    }

    #[test]
    fn t12_spread_kind() {
        assert_eq!(trap("[...5]"), TrapClass::SpreadKind);
        assert_eq!(trap("{ ...[1] }"), TrapClass::SpreadKind);
    }

    #[test]
    fn t13_computed_key() {
        assert_eq!(trap("{ [5]: 1 }"), TrapClass::ComputedKey);
    }

    // ── PR-01…05 (detail assertions live in oracle::tests::pr0*) ─────────────

    #[test]
    fn pr01_tuple_literal_rendering() {
        assert_eq!(str_of(&eval("`${[1, 1/3]}`")), "[1, 1/3]");
    }

    #[test]
    fn pr02_record_sorted_keys() {
        assert_eq!(str_of(&eval("`${{b: 2, a: 1}}`")), "{a: 1, b: 2}");
    }

    #[test]
    fn pr03_inner_strings_quoted() {
        assert_eq!(str_of(&eval("`${[\"x\"]}`")), "[\"x\"]");
    }

    #[test]
    fn pr04_function_and_indeterminate_forms() {
        assert_eq!(str_of(&eval("f = x => x\n`${f}`")), "<Function>");
        assert_eq!(str_of(&eval("`${1/0}`")), "<Indeterminate _/0>");
        assert_eq!(str_of(&eval("`${2/0}`")), "<Indeterminate _/0>");
        assert_eq!(str_of(&eval("`${1%0}`")), "<Indeterminate _%0>");
        assert_eq!(str_of(&eval("`${0%0}`")), "<Indeterminate 0%0>");
    }

    #[test]
    fn pr05_parse_print_identity() {
        // The full one-interner pointer-law sweep is oracle::tests::pr05_…;
        // here one canonical round-trip.
        let mut i = Interner::new();
        let original = eval_in(&mut i, "{b: 2, a: 1}");
        let printed = eval_in(&mut i, "`${{b: 2, a: 1}}`");
        let reparsed = eval_in(&mut i, &str_of(&printed));
        assert!(original.ptr_eq(&reparsed));
    }

    #[test]
    fn pr06_top_level_string_raw() {
        // Top-level String interpolates raw (no quotes) — outside PR-05's law.
        assert_eq!(str_of(&eval("`${\"abc\"}`")), "abc");
    }

    #[test]
    fn pr07_non_ident_keys_computed_syntax() {
        // Non-IDENT keys → computed-key syntax, UTF-16 order, reparses.
        assert_eq!(
            str_of(&eval("`${{a: 1, [\"a-b\"]: 2, [\"two words\"]: 3}}`")),
            "{a: 1, [\"a-b\"]: 2, [\"two words\"]: 3}",
        );
    }

    #[test]
    fn pr08_lone_surrogate_lossless() {
        // A lone surrogate unit escapes individually (`\uD800`), never U+FFFD.
        assert_eq!(str_of(&eval(r#"`${["\uD800"]}`"#)), r#"["\uD800"]"#);
    }

    #[test]
    fn pr09_aggregate_with_function_deterministic() {
        // Deterministic display text; not claimed parseable.
        assert_eq!(str_of(&eval("`${[1, () => 1]}`")), "[1, <Function>]");
    }

    // ── O: access & slices ───────────────────────────────────────────────────

    #[test]
    fn o01_stored_null_is_data() {
        assert!(eval("{a: null}.a").is_null());
        assert_eq!(trap("{a: null}.a.b"), TrapClass::NullReceiver);
    }

    #[test]
    fn o02_one_step_totals() {
        assert!(eval("u = null\nu?.name").is_null());
        assert!(eval("{a: 1}?.b").is_null());
        assert!(eval("[1]?.[9]").is_null());
    }

    #[test]
    fn o03_null_travels_then_traps_at_next_hop() {
        assert_eq!(trap("u = null\nu?.name.first"), TrapClass::NullReceiver);
    }

    #[test]
    fn o04_clamped_slices() {
        let mut i = Interner::new();
        let t = eval_in(&mut i, "t = [1, 2, 3]\nt");
        let clamped = eval_in(&mut i, "t = [1, 2, 3]\nt[...10]");
        assert!(
            clamped.ptr_eq(&t),
            "clamp to the whole tuple = same pointer"
        );
        vtrue("t = [1, 2, 3]\nt[5...] == []");
        vtrue("t = [1, 2, 3]\nt[2...2] == []");
        vtrue("t = [1, 2, 3]\nt[-2...] == [2, 3]");
        let ident = eval_in(&mut i, "t = [1, 2, 3]\nt[...]");
        assert!(ident.ptr_eq(&t), "identity slice = same pointer");
    }

    #[test]
    fn o05_partition_identity() {
        vtrue("t = [1, 2, 3]\nk = 1\n[...t[...k], ...t[k...]] == t");
    }

    #[test]
    fn o06_from_end_index() {
        num_eq(&eval("[1, 2, 3][-1]"), 3);
        assert_eq!(trap("[][-1]"), TrapClass::IndexBounds);
    }

    // ── S: graphemes (PIN-UNICODE — pinned unicode-segmentation version) ─────

    #[test]
    fn s01_grapheme_length_and_index() {
        vtrue("String.length(\"👨‍👩‍👧\") == 1");
        vtrue("s = \"👨‍👩‍👧\"\ns[0] == s");
        vtrue("s = \"ab👨‍👩‍👧\"\ns[-1] == \"👨‍👩‍👧\"");
    }

    #[test]
    fn s02_unit_and_point_views_differ() {
        // Lengths differ from the grapheme length on astral/ZWJ cases.
        let units = eval("String.units(\"👨‍👩‍👧\")");
        let points = eval("String.points(\"👨‍👩‍👧\")");
        assert_eq!(units.as_tuple().map(|t| t.len()), Some(8), "UTF-16 units");
        assert_eq!(points.as_tuple().map(|t| t.len()), Some(5), "code points");
        // grapheme length is 1 (S-01) — both views exceed it.
    }

    #[test]
    fn s03_slicing_never_splits_clusters() {
        vtrue("s = \"a👨‍👩‍👧b\"\ns[1...2] == \"👨‍👩‍👧\"");
        vtrue("s = \"a👨‍👩‍👧b\"\ns[...2] == \"a👨‍👩‍👧\"");
        vtrue("s = \"e\\u{301}x\"\ns[0...1] == \"e\\u{301}\"");
    }

    // ── X: the falsy-set distinctions ────────────────────────────────────────

    #[test]
    fn x01_zero_is_truthy() {
        num_eq(&eval("~0 || 5"), 0);
    }

    #[test]
    fn x02_nullish_vs_escaped_or_on_false() {
        assert_eq!(eval("a = false\na ?? \"b\"").as_boolean(), Some(false));
        assert_eq!(str_of(&eval("a = false\n~a || \"b\"")), "b");
    }

    // ── M: mutator staging ───────────────────────────────────────────────────

    #[test]
    fn m01_read_your_writes() {
        let src = "
            @state x = 0
            @mutate f = () => { x := 5\nx := x + 1 }
            f()
            x
        ";
        num_eq(&eval(src), 6);
    }

    #[test]
    fn m02_nested_join_publishes_once() {
        let src = "
            @state x = 0
            @mutate inner = () => { x := 10 }
            @mutate outer = () => { inner()\nx := x + 1 }
            outer()
            x
        ";
        let (v, commits) = run_program_commits(src).expect("runs");
        num_eq(&v, 11);
        assert_eq!(commits, 1, "one publish at outermost completion");
    }

    #[test]
    fn m03_equality_guard_no_op_write() {
        let src = "
            @state x = 5
            @mutate f = () => { x := 2 + 3 }
            f()
            x
        ";
        let (v, commits) = run_program_commits(src).expect("runs");
        num_eq(&v, 5);
        assert_eq!(commits, 0, "an equal write commits nothing (pointer guard)");
    }

    #[test]
    fn m04_diverging_outer_publishes_nothing() {
        // The outer mutator diverges after the inner completed: the inner's write
        // joined the outer transaction, the outer never completes, so nothing
        // publishes — DIVERGES with σ unchanged (zero commits).
        let src = "
            @state x = 0
            spin = (n) => spin(n)
            @mutate inner = () => { x := 1 }
            @mutate outer = () => {
             inner()
             spin(0)
            }
            outer()
        ";
        match next::oracle::run_program_bounded(src, 10_000) {
            next::oracle::BoundedRun::Diverged { commits } => {
                assert_eq!(commits, 0, "a never-completed mutator publishes nothing");
            }
            other => panic!("expected DIVERGES, got {other:?}"),
        }
    }

    #[test]
    fn m05_mutator_returns_nothing() {
        let src = "
            @state x = 0
            @mutate f = () => { x := 1 }
            y = f()
            y
        ";
        assert_eq!(trap(src), TrapClass::ExpectingSeat);
        // A bare call at a statement seat is fine.
        let ok = "
            @state x = 0
            @mutate f = () => { x := 1 }
            f()
            x
        ";
        num_eq(&eval(ok), 1);
    }

    #[test]
    fn m06_effect_sees_published_state() {
        let src = "
            @state x = 0
            @mutate f = () => { x := 7 }
            f()
            x + 1
        ";
        num_eq(&eval(src), 8);
    }

    // ── FL: Failure as plain data (B6) ───────────────────────────────────────

    #[test]
    fn fl01_unguarded_failure_access_traps() {
        let err = run_with_io("data = readFile(\"cfg\")\ndata.body").expect_err("must trap");
        assert_eq!(err.class, TrapClass::AbsentField);
    }

    #[test]
    fn fl02_then_catch_over_pipes() {
        let src = "
            then  = (f) => (r) => r :: {
                Failure => r
                _ => f(r)
            }
            catch = (h) => (r) => r :: {
                Failure => h(r)
                _ => r
            }
            happy = 5 |> then((x) => x + 1) |> catch((e) => 0)
            sad = readFile(\"x\") |> then((c) => 1) |> catch((e) => 99)
            [happy, sad]
        ";
        let (v, _) = run_with_io(src).expect("runs");
        let t = v.as_tuple().unwrap();
        num_eq(&t[0], 6);
        num_eq(&t[1], 99);
    }

    #[test]
    fn fl03_failure_is_inert_data() {
        let src = "
            d = readFile(\"x\")
            y = 1 + 1
            d :: {
                Failure => \"failed\"
                _ => \"ok\"
            }
        ";
        let (v, _) = run_with_io(src).expect("runs");
        assert_eq!(str_of(&v), "failed");
    }

    // ── MOD: modules (top-level world active; linking remains staged) ───────

    #[test]
    fn mod01_act_call_at_module_top_level_rejected() {
        let (verdict, _) = check_source(
            "module M\n\
             export result = println(\"no\")\n",
        )
        .expect("the module parses and checks");
        assert!(
            !verdict.accepted(),
            "an act call at module top level must reject"
        );
        assert!(
            verdict
                .findings
                .iter()
                .any(|f| f.class == TrapClass::WorldAdmission),
            "MOD-01 rejects through the world-admission concordance: {:?}",
            verdict.findings
        );
    }

    #[test]
    fn mod02_entry_top_level_is_effect_world() {
        let (_, io) = run_with_io("println(\"hi\")").expect("entry file runs effects");
        assert_eq!(io.output, vec!["hi".to_string()]);
    }

    const COUNTER: &str = "module Counter\n\
        export @state count = 0\n\
        export @mutate increment = () => {\n\
         count := count + 1\n\
        }\n";

    #[test]
    fn mod03_store_module_live_read() {
        // Import the binding itself: the slot is the same location, so the read
        // after the imported mutator fires sees the new value — live.
        let (v, _) = next::link::run_project(&[
            COUNTER,
            "import { count, increment } from Counter\n\
             increment()\n\
             count\n",
        ])
        .expect("the project links and runs");
        num_eq(&v, 1);
    }

    #[test]
    fn mod04_module_alias_is_live() {
        // `m = Counter` aliases the namespace; `m.count` and `Counter.count` are the
        // same live binding after mutation.
        let (v, _) = next::link::run_project(&[
            COUNTER,
            "import Counter\n\
             import { increment } from Counter\n\
             m = Counter\n\
             increment()\n\
             [m.count, Counter.count]\n",
        ])
        .expect("the project links and runs");
        let t = v.as_tuple().expect("a pair");
        assert!(t[0].ptr_eq(&t[1]), "one binding, one value");
        num_eq(&t[0], 1);
    }

    #[test]
    fn mod05_duplicate_module_names_error() {
        // Two files declaring `module X` — one project-wide error naming both.
        let err = next::link::run_project(&[
            "module X\nexport a = 1\n",
            "module X\nexport b = 2\n",
            "0\n",
        ])
        .expect_err("duplicate module names are a project error");
        match err {
            next::link::ProjectError::Link(next::link::LinkError::DuplicateModule {
                name,
                first,
                second,
            }) => {
                assert_eq!(name, "X");
                assert_eq!((first, second), (0, 1));
            }
            other => panic!("expected the duplicate-module error, got {other:?}"),
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// Phase 4 — Normalization harness (full generators live in normalize::tests)
// ═════════════════════════════════════════════════════════════════════════════

mod phase4 {
    use super::*;
    use next::ast::{Expr, Item};
    use next::normalize::normalize_expr;

    /// Desugar a one-expression program and return the kernel expression.
    fn lower(i: &mut Interner, src: &str) -> Expr {
        let toks = lex(src).expect("lex ok");
        let sp = parse_program(toks).expect("parse ok");
        let module = Desugarer::new(i).program(&sp).expect("desugar ok");
        match module.items.into_iter().next_back() {
            Some(Item::Stmt(e)) | Some(Item::Bind(next::ast::Bind { value: e, .. })) => e,
            other => panic!("expected an expression statement, got {other:?}"),
        }
    }

    const SAMPLES: &[&str] = &[
        "1 + 2 * 3",
        "x => x + x",
        "x => 0 * x",
        "(a, b) => a * b + b * a",
        "x => x - x + 1",
        "[1, 2 + 3, \"s\"]",
    ];

    #[test]
    fn h01_eval_normalize_eval() {
        // eval ∘ normalize = eval, over the sample set (the generated space is
        // normalize::tests's job).
        for src in SAMPLES {
            let mut i = Interner::new();
            let e = lower(&mut i, src);
            let n = normalize_expr(&e, &mut i);
            let a = next::oracle::eval_expr(&e, &mut i);
            let b = next::oracle::eval_expr(&n, &mut i);
            match (a, b) {
                (
                    Ok(next::oracle::Outcome::Produced(x)),
                    Ok(next::oracle::Outcome::Produced(y)),
                ) => {
                    assert!(
                        next::oracle::values_equal(&x, &y),
                        "eval changed under normalize for {src}",
                    );
                }
                (a, b) => panic!("unexpected outcomes for {src}: {a:?} vs {b:?}"),
            }
        }
    }

    #[test]
    fn h02_idempotence() {
        for src in SAMPLES {
            let mut i = Interner::new();
            let e = lower(&mut i, src);
            let once = normalize_expr(&e, &mut i);
            let twice = normalize_expr(&once, &mut i);
            assert_eq!(once, twice, "normalize must be idempotent for {src}");
        }
    }

    #[test]
    fn h03_per_rule_brute_force_reference() {
        // The per-rule enumerated sweeps are normalize::tests (H-03's generators);
        // this row spot-checks one rule through the canonical-code observation:
        // commutative reordering collapses spellings to one canonical body.
        vtrue("f = x => 3 + x * 2\ng = x => x * 2 + 3\nf == g");
    }

    #[test]
    fn h04_mutator_barrier() {
        // A program whose meaning would change if a box read moved across a Write:
        // normalization must not move it — eval equal pre/post.
        let src = "
            @state x = 1
            @mutate f = () => { y = x\nx := 10\nz = x\nx := y + z }
            f()
            x
        ";
        num_eq(&eval(src), 11); // y=1, z=10 (read-your-writes), publish 11
        // The structural no-cross law is normalize::tests's H-04 case.
    }

    #[test]
    fn h05_polynomial_nf_canonical_body() {
        // x => x + x and x => 2 * x share one canonical body. (The register
        // marked the == observation PENDING-§5; the canonical-code comparison
        // already realizes it — asserting the final expectation, which the
        // register permits.)
        vtrue("f = x => x + x\ng = x => 2 * x\nf == g");
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// Phase A — Analyzer verdict suite. Whole-program analysis and worlds now exist;
// these broad rows remain stubs for their recorded demand/family/grounding gates.
// ═════════════════════════════════════════════════════════════════════════════

mod phase_a {
    use super::*;

    /// Live A-VER subset: a boundary union rejects field access until an exhaustive
    /// contract-pattern match narrows the receiver. This is the program-level counterpart
    /// of E9 remainder semantics feeding the declared return demand.
    #[test]
    fn a_ver_union_boundary_narrowing_and_indeterminate_discharge() {
        let contracts = "Response = {body: String}\n\
            Result = Union(Response, Failure)\n";
        let direct = check_source(&format!(
            "{contracts}get where (Result) => String\n\
             get = (data) => data.body\n"
        ))
        .expect("the direct-access case parses and checks")
        .0;
        assert!(
            !direct.accepted(),
            "Failure does not promise `body`, so direct access rejects"
        );

        let narrowed = check_source(&format!(
            "{contracts}get where (Result) => String\n\
             get = (data) => data :: {{\n\
              Response => data.body\n\
              Failure => \"failed\"\n\
             }}\n"
        ))
        .expect("the narrowed case parses and checks")
        .0;
        assert!(
            narrowed.accepted(),
            "both exhaustive arms produce String after receiver narrowing: {narrowed:#?}"
        );

        let indeterminate = check_source(
            "safe where (Number, Number) => Top\n\
             safe = (a, b) => (a / b) :: {\n\
              Indeterminate => \"undefined\"\n\
              value => value\n\
             }\n",
        )
        .expect("the Indeterminate discharge case parses and checks")
        .0;
        assert!(
            indeterminate.accepted(),
            "the ordinary Indeterminate contract arm discharges division: {indeterminate:#?}"
        );
    }

    /// A-VER subset: the Failure-overlap wrapper demand (B6 [1.0.2]). At a declared
    /// fallible boundary `Union(T, Failure)`, a success alternative not proven disjoint
    /// from `Failure` could inhabit the failure rail and be swallowed by its discharge
    /// match — the explicit success wrapper is demanded where the union is formed.
    #[test]
    fn a_ver_failure_overlap_wrapper_demand() {
        const ADAPTER_BODY: &str = "parse = (raw) => raw :: {\n\
             Ok => raw\n\
             _ => {path: \"adapter\", reason: \"malformed\"}\n\
            }\n";

        let overlapping = check_source(&format!(
            "Ok = HasField(\"value\")\n\
             parse where (Record) => Union(Ok, Failure)\n\
             {ADAPTER_BODY}"
        ))
        .expect("the overlapping-boundary case parses and checks")
        .0;
        assert!(
            !overlapping.accepted(),
            "an open success shape is not proven disjoint from Failure: {overlapping:#?}"
        );

        let wrapped = check_source(&format!(
            "Ok = {{value: Record}}\n\
             parse where (Record) => Union(Ok, Failure)\n\
             {ADAPTER_BODY}"
        ))
        .expect("the wrapped-boundary case parses and checks")
        .0;
        assert!(
            wrapped.accepted(),
            "the exact success wrapper is proven disjoint and accepts: {wrapped:#?}"
        );
    }

    /// A-NEG — the negative battery (Part D§6 / Part I), the anti-regression
    /// tripwire, under the stamped Principle 9 (the former GRAY verdicts are now
    /// rejections). Live rows assert today's true verdicts; the pinned twins below
    /// each name the one certificate their acceptance awaits.
    #[test]
    fn a_neg_negative_battery() {
        let accepts = |src: &str| {
            let v = check_source(src).expect("parses and checks").0;
            assert!(v.accepted(), "must accept: {src}\n{:#?}", v.findings);
        };
        let rejects = |src: &str| {
            let v = check_source(src).expect("parses and checks").0;
            assert!(!v.accepted(), "must reject: {src}");
        };

        // factorial — proven over its natural domain (also GR-02).
        accepts(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\nfact where (Nat) => Number\n\
             fact = (n) => n == 0 ? 1 : n * fact(n - 1)\nx = fact(5)\n",
        );
        // countdown−2 — the drift-pair grid (also GR-18).
        accepts("countdown = (n) => n == 0 ? 0 : countdown(n - 2)\nx = countdown(10)\n");
        rejects("countdown = (n) => n == 0 ? 0 : countdown(n - 2)\nx = countdown(7)\n");
        // broken fibonacci — mixed drifts, missing base: the rejection smoke test.
        rejects("f = (n) => n == 0 ? 1 : f(n - 1) + f(n - 2)\nx = f(1)\n");
        // collatz — the former gray flagship; unproven now rejects.
        rejects(
            "collatz = (n) => n == 1 ? 1 : (n % 2 == 0 ? collatz(n / 2) : collatz(3 * n + 1))\n\
             x = collatz(7)\n",
        );
        // the −4 trap — parity self-loops away from the base; the aligned start lands.
        rejects("f = (n) => n == 0 ? 0 : f(n - 4)\nx = f(7)\n");
        accepts("f = (n) => n == 0 ? 0 : f(n - 4)\nx = f(8)\n");
        // isEven/isOdd — the terminating pair closes (group orbit); the +1 variant rejects.
        accepts(
            "isEven = (n) => n <= 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n <= 0 ? false : isEven(n - 1)\nx = isEven(4)\n",
        );
        rejects(
            "isEven = (n) => n <= 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n <= 0 ? false : isEven(n + 1)\nx = isEven(4)\n",
        );
        // Hofstadter Q — value-dependent steps: honestly unproven, rejects.
        rejects("q = (n) => n <= 2 ? 1 : q(n - q(n - 1)) + q(n - q(n - 2))\nx = q(5)\n");
    }

    /// Specimen 6, resolved by the spec: `collatz(64)` and `collatz(27)` are **both
    /// unproven** — the Pow2 basin derivation is deferred by the D-4 ruling
    /// [user, 1.0.12], so no candidate source exists and unproven rejects under the
    /// stamp. (The worked-examples grid's "collatz(64) compiles" predates the ruling;
    /// the grid doc's own rule resolves the discrepancy toward the spec, logged in
    /// DECISIONS 2026-08-04.)
    #[test]
    fn a_neg_collatz_64_honestly_unproven() {
        let v = check_source(
            "collatz = (n) => n == 1 ? 1 : (n % 2 == 0 ? collatz(n / 2) : collatz(3 * n + 1))\n\
             x = collatz(64)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !v.accepted(),
            "no candidate source — unproven rejects: {v:#?}"
        );
    }

    /// Released 2026-08-04: the nested landing-zone certificate (grid §6's closed
    /// form) grounds the bare call — safety and completion close through the zone
    /// envelope, the return through the (90, 101] induction, termination through the
    /// climb/lap counts. GR specimen 7's "proven — the negative battery's baseline".
    #[test]
    fn a_neg_mccarthy_91_accepts() {
        let v = check_source("m = (n) => n > 100 ? n - 10 : m(m(n + 11))\nx = m(1)\n")
            .expect("parses and checks")
            .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }

    /// Released 2026-08-04: the joint lexicographic certificate (GR-13/14) grounds
    /// Ackermann — point floors from the `== 0` guards, gated unit decreases, and the
    /// nested call's membership through the return half (`GE(1) ∧ Mod(1,0)` over the
    /// `[Nat, Nat]` envelope).
    #[test]
    fn a_neg_ackermann_accepts() {
        let v = check_source(
            "ack = (m, n) => m == 0 ? n + 1 : (n == 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)))\n\
             x = ack(2, 2)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }

    /// Non-tail mutual (`1 + g(n − 1)`): released by the Add-image sharpening — the
    /// return induction always closed; its proposal was poisoned by the mixed
    /// `Number ∪ String` image for `1 + <pinned>`, which a Number operand rules out.
    #[test]
    fn a_neg_non_tail_mutual_accepts() {
        let v = check_source(
            "f = (n) => n <= 0 ? 0 : 1 + g(n - 1)\ng = (n) => n <= 0 ? 0 : 1 + f(n - 1)\n\
             x = f(4)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }

    /// gcd, released: the §5 multi-parameter partition carries `b ≠ 0` to the
    /// divisor, the Rem image keeps integrality, the modulo-descent certificate
    /// grounds the recursion, and the mod-orbit envelope closes bare concrete calls.
    #[test]
    fn a_neg_gcd_accepts() {
        let v = check_source("gcd = (a, b) => b == 0 ? a : gcd(b, a % b)\nx = gcd(12, 8)\n")
            .expect("parses and checks")
            .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }

    /// A-ACC's **runtime-trace layer** (the doc's own split): the canonical family
    /// trace runs in the oracle today. (`rest == []` spells the transcript's
    /// `rest.length > 0` test — no Tuple module exists yet.)
    #[test]
    fn a_acc_runtime_trace_layer() {
        const LIST: &str = "nums = [1, 2, 3, 4]\n\
            makeLinkedList = (value, ...rest) =>\n\
             { value: value, next: rest == [] ? null : makeLinkedList(...rest) }\n\
            x = makeLinkedList(...nums)\n";
        vtrue(&format!("{LIST}x.next.next.next.value == 4"));
        vtrue(&format!("{LIST}x.next.next.next.next == null"));
        assert_eq!(
            trap(&format!("{LIST}x.next.next.next.next.value")),
            TrapClass::NullReceiver,
            ".value on the null tail traps"
        );
    }

    #[test]
    #[ignore = "A-ACC pin: the contract-claim layer (Recursion/UniformFamily foresight — builder, map, reverse, zip, rotate r.next⁷.top ⊑ Equals(\"y\"), …) is the Part-D families candidate's battery; expectation-only until that adoption gate opens"]
    fn a_acc_contract_claim_layer() {
        unreachable!("the families candidate is design-gated (Part D adoption)");
    }

    /// A-SND — the executable soundness harness, v1 (**evidence, not proof** — the
    /// C§16 per-rule discharge is Tier-5 and stays owed): every analyzer-accepted
    /// corpus program runs trap-free in the bounded oracle. Divergence is not a trap;
    /// world-driven loops are excluded only because the bounded runner installs no
    /// host effects yet. Layer (2) — sampled operation transfers within claimed
    /// outputs — is discharged per rule by `contract::tests::operation_soundness_sweep`
    /// (brute-forced against the oracle).
    #[test]
    fn a_snd_soundness_harness() {
        let corpus: &[&str] = &[
            "countDown = (n) => n == 0 ? 0 : countDown(n - 1)\nx = countDown(5)\nx\n",
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\nfact where (Nat) => Number\n\
             fact = (n) => n == 0 ? 1 : n * fact(n - 1)\nx = fact(5)\nx\n",
            "f = (n) => n == 0 ? 0 : f(n - 2)\nx = f(6)\nx\n",
            "isEven = (n) => n <= 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n <= 0 ? false : isEven(n - 1)\nx = isEven(4)\nx\n",
            "f where (Number, Number) => Number\n\
             f = (a, b) => 2 * a + b <= 0 ? 0 : f(a - 1, b + 1)\nx = f(5, 0)\nx\n",
            "g = (n) => n :: {\n 0 => 1\n _ => 2\n}\nx = g(5)\nx\n",
        ];
        for src in corpus {
            let v = check_source(src).expect("parses and checks").0;
            assert!(v.accepted(), "a corpus member must be accepted: {src}");
            // Completed — or Diverged — is fine; only a trap refutes soundness.
            if let next::oracle::BoundedRun::Trapped(t) =
                next::oracle::run_program_bounded(src, 100_000)
            {
                panic!("an accepted program trapped: {src}\n{t:?}")
            }
        }
    }

    /// A-VER's remaining broad cases, live: the comparison-chain hint rides the
    /// operand rejection; exhaustiveness is judged over the E9 remainder relative to
    /// the actual input; act-kind admission over a union of callees rejects a
    /// possibly-Effect callee in Mutator world.
    #[test]
    fn a_ver_remaining_cases() {
        use next::analyzer::Severity;
        // `1 < 2 < 3` — REJECT (Boolean into a relational operand) with the hint.
        let chain = check_source("x = 1 < 2 < 3\n")
            .expect("parses and checks")
            .0;
        assert!(!chain.accepted(), "the chain self-refutes");
        assert!(
            chain
                .findings
                .iter()
                .any(|f| f.severity == Severity::Warning && f.message.contains("did you mean")),
            "the chain hint rides the rejection: {:#?}",
            chain.findings
        );

        // Exhaustiveness over the remainder: `f(0)` is fully consumed by the exact
        // arm; `f(5)` falls through and the expecting seat rejects.
        let covered = check_source("f = (n) => n :: {\n 0 => 1\n}\nx = f(0)\n")
            .expect("parses and checks")
            .0;
        assert!(covered.accepted(), "{:#?}", covered.findings);
        let uncovered = check_source("f = (n) => n :: {\n 0 => 1\n}\nx = f(5)\n")
            .expect("parses and checks")
            .0;
        assert!(!uncovered.accepted(), "the remainder is non-empty at 5");

        // A union of callees with a possibly-Effect alternative, called in Mutator
        // world — rejected through the world-admission concordance.
        let union = check_source(
            "@effect e = () => {\n => 0\n}\np = () => 0\n\
             @mutate m = (c) => {\n g = c ? e : p\n g()\n}\nm(true)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !union.accepted(),
            "possibly-Effect in Mutator world rejects"
        );
        assert!(
            union
                .findings
                .iter()
                .any(|f| f.class == TrapClass::WorldAdmission),
            "the rejection is the admission matrix's: {:#?}",
            union.findings
        );
    }

    #[test]
    fn a_lnt_lint_tier() {
        use next::analyzer::Severity;
        let warn = |src: &str, needle: &str| {
            let v = check_source(src).expect("parses and checks").0;
            assert!(v.accepted(), "a lint never rejects: {src}");
            assert!(
                v.findings
                    .iter()
                    .any(|f| f.severity == Severity::Warning && f.message.contains(needle)),
                "missing the {needle:?} lint for {src:?}: {:#?}",
                v.findings
            );
        };
        warn("1 + 1\n", "goes nowhere");
        warn(
            "@effect fetch = () => {\n => {path: \"p\", reason: \"r\"}\n}\nfetch()\n",
            "discarded",
        );
        warn("t = [1, 2]\nx = t[...]\n", "identity slice");
        warn("x = {a: 1}?.a\n", "redundant `?.`");
        warn("x = ~true ? 1 : 2\n", "redundant `~`");
        warn("b = true\nx = b || 1\n", "||");
        warn("x = 1\n - 2\n", "leading-minus");
        warn(
            "module A.Main\nimport A.Utils\nexport z = 1\n",
            "self-prefix",
        );
    }

    /// A-WRK — the recovered worked-example grids, verified (grids 1–7; the doc's own
    /// note gates grids 8–9 on the Part-D families candidate). Grid rows already live
    /// elsewhere (countdown−2, broken fibonacci, collatz, the −4 trap in A-NEG/GR-18;
    /// McCarthy 91 pinned) are not duplicated here.
    #[test]
    fn a_wrk_worked_example_grids() {
        let accepts = |src: &str| {
            let v = check_source(src).expect("parses and checks").0;
            assert!(v.accepted(), "must accept: {src}\n{:#?}", v.findings);
        };
        let rejects = |src: &str| {
            let v = check_source(src).expect("parses and checks").0;
            assert!(!v.accepted(), "must reject: {src}");
        };

        // Grid 1 — factorial: the orbit hits 0 iff the start is a non-negative integer.
        rejects("f = (n) => n == 0 ? 1 : n * f(n - 1)\nx = f(-3)\n");
        rejects("f = (n) => n == 0 ? 1 : n * f(n - 1)\nx = f(2.5)\n");

        // Grid 1 — the `where` triple: exactly-derived and stricter-than-derived
        // accept (C§12.1 split variance; the recursion's visited domain closes through
        // the unbounded envelope `GE(0) ∧ Mod(1,0)`); looser-than-derived rejects —
        // it promises −5 and the body cannot ground there.
        accepts(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\nf where (Nat) => Number\n\
             f = (n) => n == 0 ? 1 : n * f(n - 1)\n",
        );
        accepts(
            "Strict = Intersection(GreaterEq(1), Mod(1, 0))\nf where (Strict) => Number\n\
             f = (n) => n == 0 ? 1 : n * f(n - 1)\n",
        );
        rejects(
            "Loose = GreaterEq(-5)\nf where (Loose) => Number\n\
             f = (n) => n == 0 ? 1 : n * f(n - 1)\n",
        );

        // Grid 7 — the same-bases pair: point bases {0, 0}, unit hops; both members
        // derive `GE(0) ∧ Mod(1,0)`, exactly factorial's contract. A negative start
        // descends below both bases forever and rejects.
        const PAIR: &str = "isEven = (n) => n :: {\n 0 => true\n _ => isOdd(n - 1)\n}\n\
            isOdd = (n) => n :: {\n 0 => false\n _ => isEven(n - 1)\n}\n";
        accepts(&format!("{PAIR}x = isEven(4)\n"));
        rejects(&format!("{PAIR}x = isEven(-1)\n"));
    }

    /// Grid 1's guard-narrowing call: the compound guard regionalizes — the
    /// desugared `&&` intersects its conjuncts and `k % 1 == 0` is the sound
    /// integer test — and the binder `k` aliases the parameter in its row.
    #[test]
    fn a_wrk_guard_narrowing_accepts() {
        let v = check_source(
            "f = (n) => n == 0 ? 1 : n * f(n - 1)\ncheck = (x) => x :: {\n\
              k when k >= 0 && k % 1 == 0 => f(k)\n _ => 0\n}\ny = check(7)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }

    /// Grid 7's different-bases variant, released: the threading lattices — after k
    /// unit hops the state is (member_k, n − k), so each member's admitted starts sit
    /// on a parity lattice anchored at an exit; off both lattices the recursion
    /// threads between the bases forever and rejects.
    #[test]
    fn a_wrk_threading_variant() {
        const PAIR: &str = "isEven = (n) => n :: {\n 0 => true\n _ => isOdd(n - 1)\n}\n\
            isOdd = (n) => n :: {\n 1 => true\n _ => isEven(n - 1)\n}\n";
        let even = check_source(&format!("{PAIR}x = isEven(4)\n"))
            .expect("parses and checks")
            .0;
        assert!(even.accepted(), "{:#?}", even.findings);
        let odd = check_source(&format!("{PAIR}x = isEven(3)\n"))
            .expect("parses and checks")
            .0;
        assert!(
            !odd.accepted(),
            "isEven(3) threads between the bases forever"
        );
    }

    #[test]
    #[ignore = "A-WRK pin: grids 8–9 (makeLinkedList, pairUp ×3, rotate) are the Part-D families candidate's battery — expectation-only until that adoption gate opens (D§9)"]
    fn a_wrk_family_grids() {
        unreachable!("the families candidate is design-gated (Part D adoption)");
    }
}

// ── Phase GR — grounding verdicts under the stamped Principle 9 ─────────────────
//
// First measured batch (suite spec Phase GR; specimen numbers from
// `next-grounding-specification-v0-5.md` §15). Under the stamp [user, 2026-08-03]
// unproven termination is an error, so every "unproven" specimen is a rejection row.
// Recursive named contracts (C§9 / plan T2.4): ordinary named bindings mentioning
// themselves or their group — no special form, source order immaterial at the static
// layer. Admissibility violations are definition errors; membership at a runtime
// contract-as-pattern resolves through the group walk.
mod recursive_contracts {
    use super::*;

    /// The flagship shape: a self-recursive list contract, guarded through a Record
    /// constructor. Runtime membership walks the group; non-members fall through.
    #[test]
    fn rc_runtime_membership_through_the_group() {
        let mut i = Interner::new();
        let v = eval_in(
            &mut i,
            "IntList = Union(Null, {value: Number, next: IntList})\n\
             l = {value: 1, next: {value: 2, next: null}}\n\
             l :: { IntList => \"yes\"\n _ => \"no\" }\n",
        );
        assert_eq!(str_of(&v), "yes");

        let v = eval_in(
            &mut i,
            "IntList = Union(Null, {value: Number, next: IntList})\n\
             l = {value: 1, next: 5}\n\
             l :: { IntList => \"yes\"\n _ => \"no\" }\n",
        );
        assert_eq!(str_of(&v), "no");
    }

    /// A mutual group: `A` and `B` define each other; the second pass evaluates
    /// them jointly and the membership walk resolves cross-references.
    #[test]
    fn rc_mutual_group_membership() {
        let mut i = Interner::new();
        let v = eval_in(
            &mut i,
            "A = Union(Null, B)\nB = {next: A}\n\
             x = {next: {next: null}}\n\
             x :: { A => \"in\"\n _ => \"out\" }\n",
        );
        assert_eq!(str_of(&v), "in");
    }

    /// C§9's two definition errors, verbatim: a negative occurrence has no least
    /// fixpoint; an unguarded cycle has no well-founded inclusion induction. Both
    /// reject at check with the definition named.
    #[test]
    fn rc_definition_errors_reject() {
        let v = check_source("Bad = Difference(Top, Bad)\nx = 1\n")
            .expect("parses and checks")
            .0;
        assert!(!v.accepted(), "negative polarity is a definition error");
        assert!(
            v.errors().any(|e| e.message.contains("negative polarity")),
            "{:?}",
            v.findings
        );

        let v = check_source("R = Union(Number, R)\nx = 1\n")
            .expect("parses and checks")
            .0;
        assert!(!v.accepted(), "an unguarded cycle is a definition error");
        assert!(
            v.errors()
                .any(|e| e.message.contains("crosses no Tuple/Record")),
            "{:?}",
            v.findings
        );
    }

    /// The admissible definition checks clean: the contract binding is static, not
    /// an executable item, and the module accepts.
    #[test]
    fn rc_admissible_definition_accepts() {
        let v = check_source("IntList = Union(Null, {value: Number, next: IntList})\nx = 1\n")
            .expect("parses and checks")
            .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }
}

mod phase_gr {
    use super::*;

    /// GR-05 / specimen 9: constant unit drift with landing — proven. The concrete
    /// call needs no contracts: the derived orbit envelope closes it.
    #[test]
    fn gr05_unit_descent_grounds_bare_and_declared() {
        let bare =
            check_source("countDown = (n) => n == 0 ? 0 : countDown(n - 1)\nx = countDown(5)\n")
                .expect("parses and checks")
                .0;
        assert!(bare.accepted(), "the orbit envelope closes it: {bare:#?}");

        let declared = check_source(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\n\
             countDown where (Nat) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n\
             x = countDown(5)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            declared.accepted(),
            "coverage resolves the call: {declared:#?}"
        );
    }

    /// GR-18: the step-2 grid — an aligned start lands (6 → 4 → 2 → 0); a misaligned
    /// start misses the base forever and stays rejected.
    #[test]
    fn gr18_point_base_grid() {
        let aligned = check_source("f = (n) => n == 0 ? 0 : f(n - 2)\nx = f(6)\n")
            .expect("parses and checks")
            .0;
        assert!(
            aligned.accepted(),
            "6 sits on the base's lattice: {aligned:#?}"
        );

        let misaligned = check_source("f = (n) => n == 0 ? 0 : f(n - 2)\nx = f(5)\n")
            .expect("parses and checks")
            .0;
        assert!(
            !misaligned.accepted(),
            "5 misses the base forever: {misaligned:#?}"
        );
    }

    /// GR-11 (period-1) and GR-23a's ascending mirror: refuted with the written start
    /// as witness — including divergence hidden behind a helper.
    #[test]
    fn gr11_gr23a_refutations() {
        let period1 = check_source("loop = (n) => loop(n)\nx = loop(1)\n")
            .expect("parses and checks")
            .0;
        assert!(
            !period1.accepted(),
            "the period-1 orbit refutes: {period1:#?}"
        );

        let ascending = check_source("up = (n) => n == 0 ? 0 : up(n + 1)\nx = up(5)\n")
            .expect("parses and checks")
            .0;
        assert!(
            !ascending.accepted(),
            "drift away from the base refutes: {ascending:#?}"
        );

        let transitive = check_source("g = (m) => g(m)\nf = (n) => g(n)\nx = f(1)\n")
            .expect("parses and checks")
            .0;
        assert!(
            !transitive.accepted(),
            "a helper does not hide divergence: {transitive:#?}"
        );
    }

    /// Specimen 7 (§3 + the C§10 core): McCarthy 91 — **proven, all reals** through
    /// the nested landing-zone certificate (grid §6's closed form: zone (100, 111],
    /// candidate return (90, 101], feed-back induction, laps net +1). Both the bare
    /// call and the real-valued declared domain accept; the region base means no
    /// grid condition.
    #[test]
    fn gr_specimen7_mccarthy_91_proven() {
        let bare = check_source("m = (n) => n > 100 ? n - 10 : m(m(n + 11))\nx = m(1)\n")
            .expect("parses and checks")
            .0;
        assert!(
            bare.accepted(),
            "the zone certificate grounds it: {bare:#?}"
        );

        let real = check_source(
            "m where (Number) => Number\n\
             m = (n) => n > 100 ? n - 10 : m(m(n + 11))\n\
             x = m(0.5)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            real.accepted(),
            "proven for all reals — no grid condition on a region base: {real:#?}"
        );
    }

    /// Specimen 5 (GR-13/14): Ackermann — **proven** by the joint lexicographic
    /// certificate: dictionary `(m, n)`, point floors from the `== 0` guards (the
    /// negated test gates each unit decrease on the integer lattice), and the nested
    /// `ack(m, n − 1)` argument obtaining domain membership from the induction
    /// hypothesis's return half. Both the bare call and a declared Nat domain accept;
    /// the ascending twin (`g(n + 1)`) stays rejected — descent is never assumed
    /// from the hypothesis (GR-13's own counterexample).
    #[test]
    fn gr_specimen5_ackermann_proven() {
        let bare = check_source(
            "ack = (m, n) => m == 0 ? n + 1 : (n == 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)))\n\
             x = ack(2, 2)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            bare.accepted(),
            "the joint lex certificate grounds it: {bare:#?}"
        );

        let ascending = check_source("g = (n) => n == 0 ? 0 : g(n + 1)\nx = g(1)\n")
            .expect("parses and checks")
            .0;
        assert!(
            !ascending.accepted(),
            "descent-from-hypothesis stays rejected: {ascending:#?}"
        );
    }

    /// GR-04 / specimen 6: collatz admits no candidate — honestly unproven, and under
    /// the stamp unproven termination is an error.
    #[test]
    fn gr04_collatz_unproven_rejects() {
        let collatz = check_source(
            "collatz = (n) => n == 1 ? 1 : (n % 2 == 0 ? collatz(n / 2) : collatz(3 * n + 1))\n\
             x = collatz(27)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !collatz.accepted(),
            "no candidate source — unproven rejects: {collatz:#?}"
        );
    }

    /// GR-15a/16: the program-expressed compound measure `2a + b` grounds the
    /// two-parameter recursion, and the concrete call resolves through the declared
    /// fact by coverage.
    #[test]
    fn gr15a_compound_measure_grounds() {
        let pair = check_source(
            "f where (Number, Number) => Number\n\
             f = (a, b) => 2 * a + b <= 0 ? 0 : f(a - 1, b + 1)\n\
             x = f(5, 0)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            pair.accepted(),
            "the compound measure descends and lands: {pair:#?}"
        );
    }

    /// Specimen 2: factorial over its natural domain — safety, return, termination,
    /// and the concrete call all compose.
    #[test]
    fn gr02_factorial_composes() {
        let fact = check_source(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\n\
             fact where (Nat) => Number\n\
             fact = (n) => n == 0 ? 1 : n * fact(n - 1)\n\
             x = fact(5)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(fact.accepted(), "the whole pipeline composes: {fact:#?}");
    }

    /// GR-07 (mutual): the bare pair closes with no contracts — the **group orbit**
    /// derives one shared envelope from the cross-call drifts and half-line stops,
    /// the joint induction proves both facts over it, and the shared-measure
    /// certificate grounds termination. (This row rejected until 2026-08-04; its
    /// flip is the group-orbit landing.)
    #[test]
    fn gr07_mutual_pair_closes_through_the_group_orbit() {
        let mutual = check_source(
            "isEven = (n) => n <= 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n <= 0 ? false : isEven(n - 1)\n\
             x = isEven(4)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            mutual.accepted(),
            "the group orbit closes the bare pair: {mutual:#?}"
        );
    }
}

// GR-24 rows appended with the WorldDecided landing (2026-08-04).
mod phase_gr_world {
    use super::*;

    /// GR-24 (specimens 13/14/16 shapes): the polling loop classifies world-decided —
    /// every cycle observes the world afresh and a completing arm exists for the
    /// observation to select — while the stale-carried and decorative variants stay
    /// honestly rejected.
    #[test]
    fn gr24_world_decided_polling_and_its_counterexamples() {
        let poll = check_source(
            "@effect poll = () => {\n\
              readFile(\"q\") :: {\n\
               Failure => poll()\n\
               data => data\n\
              }\n\
             }\n\
             poll()\n",
        )
        .expect("parses and checks")
        .0;
        assert!(poll.accepted(), "the world decides this loop: {poll:#?}");

        let stale = check_source(
            "@effect loop = (msg) => {\n\
              msg == \"quit\" ? 0 : loop(msg)\n\
             }\n\
             loop(\"go\")\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !stale.accepted(),
            "stale-carried is not world-decided: {stale:#?}"
        );

        let decorative = check_source(
            "@effect flip = () => {\n\
              readFile(\"b\") :: {\n\
               Failure => flip()\n\
               _ => flip()\n\
              }\n\
             }\n\
             flip()\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !decorative.accepted(),
            "the decorative branch seeds nothing: {decorative:#?}"
        );
    }
}
