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

    /// **Element representation [user ruling, 2026-08-06]: the two views differ.**
    /// `points` yields Strings — every code point is a well-formed String, so a
    /// point compares and matches directly. `units` yields Numbers — a lone
    /// surrogate half is not a String, and E8 forbids minting one.
    #[test]
    fn s02b_points_are_strings_units_are_numbers() {
        vtrue("p = String.points(\"e\\u{301}\")\np[0] == \"e\"");
        vtrue("p = String.points(\"e\\u{301}\")\np[1] == \"\\u{301}\"");
        vtrue("p = String.points(\"👋\")\np[0] == \"👋\"");
        // The astral point survives as one String even though it is two units.
        vtrue("u = String.units(\"👋\")\nu[0] == 55357");
        vtrue("u = String.units(\"👋\")\nu[1] == 56395");
        // A point is itself a String, so string ops apply to it.
        vtrue("p = String.points(\"héllo\")\nString.length(p[1]) == 1");
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
// Instantiated region tables (region-table spec §2, cases (a)/(b) over captures —
// plan T3.1): guards read after substituting the instance's capture contracts.
mod region_instantiation {
    use super::*;

    /// W-1's shape at module level: a captured constant threshold instantiates the
    /// table, `n <= limit` is case (a) exact, and the `LessEq(5)` return claim
    /// proves — with the `where` *preceding* the binding (the pre-pass makes source
    /// position immaterial). The wrong claim stays rejected (`n` at 5 escapes
    /// `LessEq(4)`).
    #[test]
    fn rt_w1_singleton_capture_instantiates_exact_rows() {
        let v = check_source(
            "f where (Number) => LessEq(5)
             limit = 5
             f = (n) => n <= limit ? n : 0
             x = 1
",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);

        let wrong = check_source(
            "limit = 5
             f where (Number) => LessEq(4)
             f = (n) => n <= limit ? n : 0
             x = 1
",
        )
        .expect("parses and checks")
        .0;
        assert!(!wrong.accepted(), "n = 5 escapes LessEq(4)");
    }
}

// Check-mode project analysis (E12/C§14): the same static whole-program
// resolution as run_project, feeding the program checker — nothing evaluated.
mod project_check {
    use next::link::{ProjectError, check_project};

    const MATH: &str = "module Math
        export double = (n) => n * 2
        export Nat = Intersection(GreaterEq(0), Mod(1, 0))
";

    /// Clean cross-module use checks; a cross-module trap is caught at the
    /// importer's seat with the precise operand error.
    #[test]
    fn pc_cross_module_check_and_trap() {
        let v = check_project(&[
            MATH,
            "import { double } from Math
y = double(2)
",
        ])
        .expect("links");
        assert!(v.accepted());

        let bad = check_project(&[
            MATH,
            "import { double } from Math
y = double(\"s\")
",
        ])
        .expect("links");
        assert!(!bad.accepted(), "the String argument must reject");
    }

    /// An imported **named contract** seeds the importer's environment: the
    /// declared-domain recursion proves through `Nat` exactly as it would with a
    /// local definition, and the whole-module alias value path checks too.
    #[test]
    fn pc_contract_import_and_alias() {
        let v = check_project(&[
            MATH,
            "import { Nat } from Math
             f where (Nat) => Number
             f = (n) => n == 0 ? 0 : f(n - 1)
             x = 1
",
        ])
        .expect("links");
        assert!(v.accepted(), "the imported contract carries the domain");

        let alias = check_project(&[
            MATH,
            "import Math
m = Math
y = m.double(2)
",
        ])
        .expect("links");
        assert!(alias.accepted());
    }

    /// Link errors stay hard project errors in check mode.
    #[test]
    fn pc_link_errors_hard_fail() {
        let e = check_project(&[
            MATH,
            "import { nope } from Math
x = 1
",
        ]);
        assert!(matches!(e, Err(ProjectError::Link(_))));
    }
}

// The factory instance flow (C§13.2, the exact-singleton cut): a body-nested
// lambda whose free variables are all singletons constructs its closure during
// analysis (construction evaluates nothing), so factory products are known
// instances at their call seats.
mod factory_instances {
    use super::*;

    /// The chain the region-instantiation slice left as residue: the product of
    /// `makeCounter(5)` is a constructed, interned closure with `limit = 5`, and
    /// the call through it resolves — safety, regions, completion, the lot.
    #[test]
    fn fi_factory_product_resolves_at_its_seat() {
        let v = check_source(
            "makeCounter = (limit) => (n) => n <= limit ? n : 0
             c = makeCounter(5)
             y = c(3)
             x = 1
",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }

    /// The sound direction: a product whose captured value makes the body trap is
    /// caught at the product's seat with the precise operation error.
    #[test]
    fn fi_trapping_product_rejects() {
        let v = check_source(
            "make = (k) => (n) => n + k
             g = make(\"s\")
             y = g(1)
             x = 1
",
        )
        .expect("parses and checks")
        .0;
        assert!(!v.accepted());
        assert!(
            v.errors().any(|e| e.message.contains("Number operand")),
            "{:#?}",
            v.findings
        );
    }
}

// Multi-parameter capture substitution (region-table spec §2 over flat params).
mod region_instantiation_multi {
    use super::*;

    /// The single-parameter W-1 flip, at arity two: the captured threshold reads
    /// exactly into position `a`'s row region, so the row narrows and the
    /// `LessEq(5)` return claim proves; the wrong claim stays rejected.
    #[test]
    fn rt_multi_singleton_capture_instantiates() {
        let v = check_source(
            "limit = 5\n\
             f where (Number, LessEq(0)) => LessEq(5)\n\
             f = (a, b) => a <= limit ? a : b\n\
             x = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);

        let wrong = check_source(
            "limit = 5\n\
             f where (Number, LessEq(0)) => LessEq(4)\n\
             f = (a, b) => a <= limit ? a : b\n\
             x = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(!wrong.accepted(), "a = 5 escapes LessEq(4)");
    }
}

// **Contract-level analysis instances (C§13.2, landed 2026-08-06).** A function value
// produced with a capture that is *not* a single value carries its instance — shape +
// capture **contracts** — as metadata beside the coarse `Kind(Function)`, and a call site
// resolves through it. The spec's own example is this case ("contract-level for factory
// products like `makeAdder(someInput)`"; "callables … arrive at call sites with instances
// recoverable — plumbing, not a contract constructor").
mod contract_level_instances {
    use super::*;

    /// A `where` over a domain that is not enumerable as points, on a function that
    /// builds a helper from its own argument and calls it. Before the instance landed,
    /// this was rejected with "callee not resolved to a known function".
    #[test]
    fn cli_a_factory_product_from_a_declared_domain_is_callable() {
        for domain in ["Number", "Range(100, 200)", "GreaterEq(0)"] {
            let src = format!(
                "makeCounter = (limit) => (n) => n <= limit ? n : limit\n\
                 build where ({domain}) => Number\n\
                 build = (k) => {{\n  c = makeCounter(k)\n  => c(3)\n}}\n\
                 x = build(7)\nx\n"
            );
            let v = check_source(&src).expect("parses and checks").0;
            assert!(v.accepted(), "where ({domain}): {:#?}", v.findings);
        }
    }

    /// The sound direction: the instance carries the capture's **contract**, so a body
    /// that misuses it is refuted — and named precisely, not as an unresolved callee.
    #[test]
    fn cli_a_bad_capture_contract_is_refuted_at_the_operation() {
        let src = "makeAdder = (k) => (n) => n + k\n\
                   bad where (String) => Number\n\
                   bad = (s) => makeAdder(s)(1)\n\
                   x = 1\nx\n";
        let v = check_source(src).expect("parses and checks").0;
        assert!(!v.accepted(), "`1 + aString` must be refuted");
        assert!(
            v.findings.iter().any(|f| f.message.contains("Add")),
            "the diagnostic names the operation, not a missing callee: {:#?}",
            v.findings
        );
    }

    /// The same shape with a sound capture contract proves, and runs.
    #[test]
    fn cli_the_sound_twin_proves_and_runs() {
        let src = "makeAdder = (k) => (n) => n + k\n\
                   good where (Number) => Number\n\
                   good = (k) => makeAdder(k)(1)\n\
                   x = good(5)\nx\n";
        assert!(check_source(src).expect("parses").0.accepted());
        assert_eq!(
            next::oracle::run_source(src)
                .unwrap()
                .0
                .as_number()
                .unwrap()
                .to_string(),
            "6"
        );
    }
}

// **Union remainders empty out** (2026-08-07). An ordered walk subtracts each exact
// arm's region from the remainder; without distributing difference over union arms the
// remainder became a stack of `Difference` nodes the emptiness check could not see
// through, so *three* exact point arms exactly covering a three-member union were not
// proven exhaustive while two were. `(X ∪ Y) ∖ Z = (X ∖ Z) ∪ (Y ∖ Z)` is exact, so
// distributing loses nothing.
mod union_remainders {
    use super::*;

    fn arms_cover(members: &[&str], arms: &[&str]) -> bool {
        let domain = members.iter().take(members.len() - 1).rev().fold(
            format!("Equals({})", members[members.len() - 1]),
            |acc, m| format!("Union(Equals({m}), {acc})"),
        );
        let arm_src = arms
            .iter()
            .map(|a| format!("  {a} => 0"))
            .collect::<Vec<_>>()
            .join("\n");
        let src = format!(
            "D = {domain}\nf where (D) => Number\nf = (p) => p :: {{\n{arm_src} }}\nx = 1\nx\n"
        );
        check_source(&src).expect("parses and checks").0.accepted()
    }

    /// Two, three and four exact point arms exactly covering their domain — every one
    /// exhaustive. Three was the first that failed before the fix.
    #[test]
    fn ur_n_point_arms_consume_an_n_member_union() {
        assert!(arms_cover(&["1", "2"], &["1", "2"]), "2 members");
        assert!(arms_cover(&["1", "2", "3"], &["1", "2", "3"]), "3 members");
        assert!(
            arms_cover(&["1", "2", "3", "4"], &["1", "2", "3", "4"]),
            "4 members"
        );
    }

    /// Strings behave identically — the gap was never numeric.
    #[test]
    fn ur_string_enums_too() {
        assert!(
            arms_cover(&["\"a\"", "\"b\"", "\"c\""], &["\"a\"", "\"b\"", "\"c\""]),
            "3 string members"
        );
    }

    /// The sound converse: a genuinely uncovered member is still not exhaustive.
    #[test]
    fn ur_a_missing_arm_is_still_caught() {
        assert!(
            !arms_cover(&["1", "2", "3"], &["1", "2"]),
            "arm 3 missing — must not be proven exhaustive"
        );
    }
}

// **Held operation images, forced by routing** [author, 2026-08-07]. An operation over
// finite point operands holds its exact image — ingredients only, uncomputed — beside the
// coarse contract. A *result* demand never forces it (DR-09 stops at the producer); the
// **routing** judgment does, at the scrutinee, forcing one node rather than re-running the
// judgment. The forced image is a subset of the coarse contract, so the walk can only
// sharpen. No search, no budget, no inversion, no mode.
mod exact_images {
    use super::*;

    const HEAD: &str = "Plan = Union(Equals(\"basic\"), Union(Equals(\"pro\"), Equals(\"enterprise\")))\n\
         Size = Union(Equals(\"small\"), Equals(\"large\"))\n\
         price where (Plan, Size) => Numeric\n\
         price = (plan, size) => {\n\
           rate = plan :: { \"basic\" => 1\n    \"pro\" => 3\n    \"enterprise\" => 5 }\n\
           seats = size :: { \"small\" => 2\n    \"large\" => 4 }\n\
           subtotal = rate * seats\n";

    /// The author's worked example: `subtotal = rate * seats` over `{1,3,5} × {2,4}`
    /// produces exactly `{2,4,6,10,12,20}`, and six point arms cover it. The coarse
    /// hull is an interval, which point arms can never consume; the exact image can.
    #[test]
    fn ei_six_arms_cover_the_exact_product() {
        let src = format!(
            "{HEAD}  => subtotal :: {{ 2 => rate + seats\n\
               4 => seats * 10\n    6 => subtotal - rate\n    10 => rate * 2\n\
               12 => subtotal + seats\n    20 => subtotal }}\n}}\n\
             x = price(\"pro\", \"large\")\nx\n"
        );
        let v = check_source(&src).expect("parses and checks").0;
        assert!(v.accepted(), "{:#?}", v.findings);
        assert_eq!(
            next::oracle::run_source(&src)
                .unwrap()
                .0
                .as_number()
                .unwrap()
                .to_string(),
            "16"
        );
    }

    /// The sound converse: drop one arm and the product is genuinely uncovered, so the
    /// exact retry must *also* fail. The retry improves precision, never soundness.
    #[test]
    fn ei_a_missing_arm_is_still_refused() {
        let src = format!(
            "{HEAD}  => subtotal :: {{ 2 => rate + seats\n\
               4 => seats * 10\n    6 => subtotal - rate\n    10 => rate * 2\n\
               12 => subtotal + seats }}\n}}\n\
             x = price(\"pro\", \"large\")\nx\n"
        );
        assert!(
            !check_source(&src).expect("parses and checks").0.accepted(),
            "20 is producible and uncovered"
        );
    }

    /// **Chained images** (2026-08-07). An operand that itself holds an image is carried
    /// *as that image*, so a chain stays exact instead of collapsing at the first coarse
    /// step. `p ∈ {1,2,5}` → `a = p*2` is `{2,4,10}` but hulls to `{2,4,6,8,10}`; without
    /// chaining `b = a*10` would read that hull and give `{20,40,60,80,100}`, which the
    /// three arms do not cover.
    #[test]
    fn ei_a_two_step_chain_stays_exact() {
        let src = "Plan = Union(Equals(1), Union(Equals(2), Equals(5)))\n\
                   f where (Plan) => Number\n\
                   f = (p) => {\n  a = p * 2\n  b = a * 10\n\
                     => b :: { 20 => 1\n    40 => 2\n    100 => 3 }\n}\n\
                   x = f(2)\nx\n";
        let v = check_source(src).expect("parses and checks").0;
        assert!(v.accepted(), "{:#?}", v.findings);
        assert_eq!(
            next::oracle::run_source(src)
                .unwrap()
                .0
                .as_number()
                .unwrap()
                .to_string(),
            "2"
        );
    }

    /// Three steps, mixing `*` and `+`.
    #[test]
    fn ei_a_three_step_chain_stays_exact() {
        let src = "Plan = Union(Equals(1), Union(Equals(2), Equals(5)))\n\
                   f where (Plan) => Number\n\
                   f = (p) => {\n  a = p * 2\n  b = a * 10\n  c = b + 1\n\
                     => c :: { 21 => 1\n    41 => 2\n    101 => 3 }\n}\n\
                   x = f(5)\nx\n";
        let v = check_source(src).expect("parses and checks").0;
        assert!(v.accepted(), "{:#?}", v.findings);
        assert_eq!(
            next::oracle::run_source(src)
                .unwrap()
                .0
                .as_number()
                .unwrap()
                .to_string(),
            "3"
        );
    }

    /// The sound converse through a chain: drop an arm and it is still refused.
    #[test]
    fn ei_a_chain_with_a_missing_arm_is_refused() {
        let src = "Plan = Union(Equals(1), Union(Equals(2), Equals(5)))\n\
                   f where (Plan) => Number\n\
                   f = (p) => {\n  a = p * 2\n  b = a * 10\n\
                     => b :: { 20 => 1\n    40 => 2 }\n}\n\
                   x = f(2)\nx\n";
        assert!(!check_source(src).expect("parses and checks").0.accepted());
    }

    /// The original A6 flagship, which the hull rejected: total over its domain, and
    /// now accepted.
    #[test]
    fn ei_the_a6_flagship_is_accepted() {
        let src = "Plan = Union(Equals(\"free\"), Equals(\"pro\"))\n\
                   f where (Plan) => Number\n\
                   f = (p) => {\n  rate = p :: { \"pro\" => 2\n    _ => 1 }\n\
                     doubled = rate * 2\n  => doubled :: { 2 => 10\n    4 => 20 }\n}\n\
                   a = f(\"pro\")\nb = f(\"free\")\nb\n";
        let v = check_source(src).expect("parses and checks").0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }
}

// **The exact-image retry reaches nested seats** (A6 residue, settled 2026-08-07). The
// retry is wired at the `where`'s completion judgment only. It needs no wiring at the
// application path's own `safety::completes` callers, because the retry re-runs the *whole*
// body analysis in exact mode, so every nested seat inherits it — and outside a `where` no
// branch set exists at all (arguments are points), so there is nothing for them to retry.
mod exact_image_reach {
    use super::*;

    /// A union argument crossing a **call boundary**, where the hull is genuinely
    /// insufficient: `rate ∈ {1,2,5}` has mixed parity, so the hull of `rate * 2` is
    /// `{2,4,6,8,10}` while the truth is `{2,4,10}`. The three arms cover the truth and
    /// not the hull, so this passes only if the callee's completion is judged under the
    /// exact image — which it is, inherited from the `where`-level retry.
    #[test]
    fn eir_a_union_argument_across_a_call_is_covered() {
        let src = "Plan = Union(Equals(\"basic\"), Union(Equals(\"pro\"), Equals(\"enterprise\")))\n\
                   helper = (r) => {\n  d = r * 2\n  => d :: { 2 => 10\n    4 => 20\n    10 => 50 }\n}\n\
                   price where (Plan) => Number\n\
                   price = (plan) => {\n  rate = plan :: { \"basic\" => 1\n    \"pro\" => 2\n    \"enterprise\" => 5 }\n\
                     => helper(rate)\n}\n\
                   x = price(\"pro\")\nx\n";
        let v = check_source(src).expect("parses and checks").0;
        assert!(v.accepted(), "{:#?}", v.findings);
        assert_eq!(
            next::oracle::run_source(src)
                .unwrap()
                .0
                .as_number()
                .unwrap()
                .to_string(),
            "20"
        );
    }
}

// **A7 [user ruling, 2026-08-05]: `where` extends to a binding proven to hold an exact
// function value** — a factory product, not only a directly-written function. Only names a
// `where` actually mentions are resolved this way; every other binding is untouched.
mod where_on_products {
    use super::*;

    const MK: &str = "makeCounter = (limit) => (n) => n <= limit ? n : limit\n";

    /// The ruling's motivating case: `c = makeCounter(5)` then `c where (Number) => Number`.
    /// Errored with "names no function binding in this module" before.
    #[test]
    fn wp_a_where_attaches_to_a_factory_product() {
        let src = format!("{MK}c where (Number) => Number\nc = makeCounter(5)\nx = c(3)\nx\n");
        let v = check_source(&src).expect("parses and checks").0;
        assert!(v.accepted(), "{:#?}", v.findings);
        assert_eq!(
            next::oracle::run_source(&src)
                .unwrap()
                .0
                .as_number()
                .unwrap()
                .to_string(),
            "3"
        );
    }

    /// The declaration is verified, not assumed: a product whose body traps over the
    /// declared domain is refuted at the operation.
    #[test]
    fn wp_a_trapping_product_is_refuted() {
        let src = "makeAdder = (k) => (n) => n + k\n\
                   bad where (Number) => Number\nbad = makeAdder(\"s\")\nx = 1\nx\n";
        let v = check_source(src).expect("parses and checks").0;
        assert!(!v.accepted());
        assert!(
            v.findings.iter().any(|f| f.message.contains("Add")),
            "named at the operation: {:#?}",
            v.findings
        );
    }

    /// A binding that is not a function still gets the ordinary malformed-`where`
    /// diagnostic — the extension resolves function values, it does not weaken the check.
    #[test]
    fn wp_a_non_function_binding_still_errors() {
        let src = "n = 1 + 1\nn where (Number) => Number\nx = 1\nx\n";
        let v = check_source(src).expect("parses and checks").0;
        assert!(!v.accepted());
        assert!(
            v.findings
                .iter()
                .any(|f| f.message.contains("names no function binding")),
            "{:#?}",
            v.findings
        );
    }

    /// The scope guard: resolution runs only for names a `where` mentions. An ordinary
    /// executable binding of a recursive call must not be dragged into the declaration
    /// pre-pass — measured as a regression on this exact program.
    #[test]
    fn wp_ordinary_bindings_are_untouched() {
        let v = check_source(
            "f = (n) => n <= 0 ? 0 : 1 + g(n - 1)\ng = (n) => n <= 0 ? 0 : 1 + f(n - 1)\n\
             x = f(4)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }
}

// **`++` is String concatenation; `+` is numeric** [author ruling, 2026-08-07]. One token
// across both rails made μ §8's frozen arithmetic slice unsound: commutative reordering
// reverses concatenation, and `x + x → 2 * x` turns a producing computation into a trap.
// Splitting the operators restores the slice's master law — "preserve the produced value
// for all inputs" — without amending the rewrite list.
mod concat_operator {
    /// `++` concatenates; `+` on Strings now traps.
    #[test]
    fn co_the_two_rails_are_separate() {
        assert_eq!(
            next::oracle::run_source("r = \"x\" ++ \"y\"\nr\n")
                .unwrap()
                .0
                .as_string_lossy()
                .unwrap(),
            "xy"
        );
        assert!(
            next::oracle::run_source("r = \"a\" + \"b\"\nr\n").is_err(),
            "`+` no longer accepts Strings"
        );
        assert!(
            next::oracle::run_source("r = 1 ++ 2\nr\n").is_err(),
            "`++` no longer accepts Numbers"
        );
    }

    /// **The regression this closes.** With one overloaded `+`, `s + "y"` and `"y" + s`
    /// canonicalized to the same shape and interned to one value — so defining an
    /// unrelated function changed what another computed: `g("x")` returned `"xy"` when
    /// `f` was defined above it, and `"yx"` when it was not.
    #[test]
    fn co_concatenation_order_survives_canonicalization() {
        let src =
            "f = (s) => s ++ \"y\"\ng = (s) => \"y\" ++ s\nr = [f == g, f(\"x\"), g(\"x\")]\nr\n";
        let out = format!("{:?}", next::oracle::run_source(src).unwrap().0);
        assert!(
            out.contains("false"),
            "the two functions must not be equal: {out}"
        );
        let alone = next::oracle::run_source("g = (s) => \"y\" ++ s\nr = g(\"x\")\nr\n")
            .unwrap()
            .0
            .as_string_lossy()
            .unwrap();
        let after = next::oracle::run_source(
            "f = (s) => s ++ \"y\"\ng = (s) => \"y\" ++ s\nr = g(\"x\")\nr\n",
        )
        .unwrap()
        .0
        .as_string_lossy()
        .unwrap();
        assert_eq!(alone, "yx");
        assert_eq!(
            after, alone,
            "defining `f` must not change what `g` computes"
        );
    }

    /// `s ++ s` is not `2 * s` — the H-05 rewrite cannot reach the String rail now.
    #[test]
    fn co_h05_cannot_reach_strings() {
        let src = "h = (s) => s ++ s\nd = (s) => 2 * s\nr = [h == d, h(\"a\")]\nr\n";
        let out = format!("{:?}", next::oracle::run_source(src).unwrap().0);
        assert!(out.contains("false"), "distinct functions: {out}");
    }
}

// **The `where`-isolation invariant** [author, 2026-08-06]: E11 makes a `where` a
// verified assertion — "never trusted, never a mode … hence no new caller obligations."
// So the presence of a signature must never change what a *call site* concludes. Before
// the one-predicate repair, graph discovery discharged a dependency from a covering
// published fact while body verification accepted only graph-derived hypotheses, so a
// `where` (an easy way to seed a wide proven fact) silently changed a call's verdict.
mod where_isolation {
    use super::*;

    const MK: &str = "makeCounter = (limit) => (n) => n <= limit ? n : limit\n";
    const BODY: &str = "build = (k) => {\n  c = makeCounter(k)\n  => c(3)\n}\n";

    fn errors(src: &str) -> Vec<String> {
        check_source(src)
            .expect("parses and checks")
            .0
            .findings
            .iter()
            .filter(|f| f.severity == next::analyzer::Severity::Error)
            .map(|f| f.message.clone())
            .collect()
    }

    /// The invariant, stated as a test: **adding a call must not change the verdict**,
    /// whatever the declared domain is. For each `where` domain, the errors of
    /// `(where + call)` must equal the errors of `(where, no call)` — the call site
    /// contributes nothing of its own.
    #[test]
    fn wi_a_call_adds_no_error_under_any_declared_domain() {
        for domain in [
            "Number",
            "Equals(7)",
            "Union(Equals(7), Equals(9))",
            "Range(100, 200)",
            "Union(Equals(1), Equals(2))",
        ] {
            let with_call =
                format!("{MK}build where ({domain}) => Number\n{BODY}x = build(7)\nx\n");
            let no_call = format!("{MK}build where ({domain}) => Number\n{BODY}x = 1\nx\n");
            assert_eq!(
                errors(&with_call),
                errors(&no_call),
                "`where ({domain})` changed the call site's verdict"
            );
        }
    }

    /// The other half: with **no** `where` at all, the same call is accepted. So the
    /// signature neither creates nor removes a caller obligation.
    #[test]
    fn wi_the_bare_call_is_accepted() {
        let bare = format!("{MK}{BODY}x = build(7)\nx\n");
        assert!(errors(&bare).is_empty(), "{:?}", errors(&bare));
    }
}

// A factory product applied **inside a function body** (2026-08-06 defect fix). The
// produced voice is a separate judgment class (§1.6) — collapsing it to `Top` while
// the safety voice was coarse made a function returned by a nested call unresolvable.
mod nested_factory_application {
    use super::*;

    const MK: &str = "makeCounter = (limit) => (n) => n <= limit ? n : limit\n";

    /// The minimal repro: no parameters, no `where`, every value a literal. Rejected
    /// before the fix with "callee not resolved to a known function"; runs to 3.
    #[test]
    fn nf_factory_applied_in_a_body_resolves() {
        let src = format!("{MK}build = () => makeCounter(7)(3)\nx = build()\nx\n");
        let v = check_source(&src).expect("parses and checks").0;
        assert!(v.accepted(), "{:#?}", v.findings);
        assert_eq!(
            next::oracle::run_source(&src)
                .unwrap()
                .0
                .as_number()
                .unwrap()
                .to_string(),
            "3"
        );
    }

    /// The same through a block binding, and through a parameter — both were rejected.
    #[test]
    fn nf_two_step_and_parameterized_forms_resolve() {
        let block =
            format!("{MK}build = () => {{\n  c = makeCounter(7)\n  => c(3)\n}}\nx = build()\nx\n");
        assert!(check_source(&block).expect("parses").0.accepted());
        let param = format!("{MK}build = (k) => makeCounter(k)(3)\nx = build(7)\nx\n");
        assert!(check_source(&param).expect("parses").0.accepted());
    }

    /// The control that always worked — the product bound at module level — still does.
    #[test]
    fn nf_module_level_factory_still_resolves() {
        let src = format!("{MK}c = makeCounter(7)\nx = c(3)\nx\n");
        assert!(check_source(&src).expect("parses").0.accepted());
    }
}

// The uncalled-unsafe lint [user ruling, 2026-08-05: warning/lint domain]. An
// unreferenced function raises no seat demand (late-resolution), but a body proven
// to trap is advised at the definition — never an error, never silent.
mod uncalled_unsafe {
    use super::*;
    use next::analyzer::Severity;

    #[test]
    fn uu_uncalled_trapping_body_warns_and_compiles() {
        let v = check_source("f = (n) => n + \"s\"\nx = 1\nx\n")
            .expect("parses and checks")
            .0;
        assert!(v.accepted(), "a lint never rejects: {:#?}", v.findings);
        assert!(
            v.findings
                .iter()
                .any(|f| f.severity == Severity::Warning
                    && f.message.contains("uncalled-unsafe lint")),
            "the definition-site advisory fires: {:#?}",
            v.findings
        );
    }

    #[test]
    fn uu_called_function_keeps_the_blocking_seat_judgment() {
        let v = check_source("f = (n) => n + \"s\"\nx = f(1)\nx\n")
            .expect("parses and checks")
            .0;
        assert!(!v.accepted(), "the call seat carries the real rejection");
        assert!(
            !v.findings
                .iter()
                .any(|f| f.message.contains("uncalled-unsafe lint")),
            "a referenced function is not \"uncalled\": {:#?}",
            v.findings
        );
    }

    #[test]
    fn uu_uncalled_safe_function_stays_silent() {
        let v = check_source("f = (n) => n + 1\nx = 1\nx\n")
            .expect("parses and checks")
            .0;
        assert!(v.accepted());
        assert!(
            !v.findings
                .iter()
                .any(|f| f.message.contains("uncalled-unsafe lint")),
            "{:#?}",
            v.findings
        );
    }
}

// TIER 5 — the C§16 discharge, executable face (A-SND v2). **Evidence, not proof**:
// grounding §13.5 states "property testing supplements §16; it never replaces it" —
// these batteries are the executable supplements, one per named obligation. The
// paper-proof half of each obligation stays owed on the C§16 ledger.
mod tier5_discharge {
    use super::*;
    use next::oracle::{BoundedRun, run_program_bounded};

    const FUEL: u64 = 200_000;

    /// The soundness harness's layer (1) at family breadth, and the executable face
    /// of C§16's **semantics theorem** (*every evaluated reference is bound*): every
    /// analyzer-accepted corpus program — one per green feature family — runs
    /// trap-free in the bounded oracle; an `UnboundEvaluation` trap in particular
    /// would refute the theorem's claim on the accepted subset.
    #[test]
    fn snd1_accepted_corpus_runs_trap_free_per_family() {
        let corpus: &[&str] = &[
            // zone certificate (GR-24/26): McCarthy 91 over the reals
            "m where (Number) => Number
m = (n) => n > 100 ? n - 10 : m(m(n + 11))
x = m(0.5)
x
",
            // joint lexicographic (GR-13/14): Ackermann, gcd
            "ack = (m, n) => m == 0 ? n + 1 : (n == 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)))
x = ack(2, 2)
x
",
            "gcd = (a, b) => b == 0 ? a : gcd(b, a % b)
x = gcd(48, 18)
x
",
            // mutual recursion — the multigraph walk (GR-07)
            "isEven = (n) => n <= 0 ? true : isOdd(n - 1)
isOdd = (n) => n <= 0 ? false : isEven(n - 1)
x = isEven(9)
x
",
            // modulo descent + parity lattice
            "f = (n) => n == 0 ? 0 : f(n - 2)
x = f(10)
x
",
            // factory instance at its seat (RT-09/C§12.3)
            "makeCounter = (limit) => (n) => n <= limit ? n : limit
c = makeCounter(5)
x = c(3)
x
",
            // recursive contract as runtime pattern + record-binder consumption
            // (C§9/E9; the recursive sum itself is grounding-unproven — structural
            // descent is GR-10(3), deferred — and is pinned as a reject in snd3)
            "IntList = Union(Null, {value: Number, next: IntList})\nhead = (l) => l :: { Null => 0\n {value: v, next: n} => v + 1 }\nx = head({value: 4, next: null})\nx\n",
            // pins, both flavors (RT-12/13)
            "y = 5
f = (x) => x :: { ^y => 1
 _ => 2 }
a = f(5)
b = f(7)
b
",
            // grapheme strings (E8) + exactness flagship (B2)
            "s = \"héllo\"
x = 0.1 + 0.2 == 0.3 ? 1 : 2
x
",
            // ?? vs ~ || (the false-vs-null split) and ?. one-step totals
            "r = {a: 1}
v = r?.b ?? 9
v
",
            // tuple patterns with rest (E9)
            "p = [1, 2, 3, 4]
[_, x, ...rest] = p
x
",
        ];
        for src in corpus {
            let v = check_source(src).expect("parses and checks").0;
            assert!(
                v.accepted(),
                "corpus member must be accepted: {src}
{:#?}",
                v.findings
            );
            match run_program_bounded(src, FUEL) {
                BoundedRun::Trapped(t) => panic!(
                    "an accepted program trapped ({:?}): {src}
{t:?}",
                    t.class
                ),
                BoundedRun::Diverged { .. } => {
                    panic!("an accepted (grounded) corpus member must complete: {src}")
                }
                BoundedRun::Completed { .. } => {}
            }
        }
    }

    /// §13.1 (GR-12, evidence): the certificate families terminate **throughout a
    /// sampled domain grid**, not just at one demo point — every analyzer-accepted
    /// call completes in the bounded oracle. Zone (McCarthy: below, inside, above
    /// and fractional), joint lex (Ackermann small grid; gcd including zero and
    /// coprime pairs), and modulo descent.
    #[test]
    fn snd_certificates_terminate_across_sampled_domains() {
        let mut cases: Vec<String> = Vec::new();
        for n in ["-40", "0", "0.5", "87", "99.25", "111", "205"] {
            cases.push(format!(
                "m where (Number) => Number
m = (n) => n > 100 ? n - 10 : m(m(n + 11))
x = m({n})
x
"
            ));
        }
        for (m, n) in [(0, 0), (1, 3), (2, 2), (3, 2)] {
            cases.push(format!(
                "ack = (m, n) => m == 0 ? n + 1 : (n == 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)))
x = ack({m}, {n})
x
"
            ));
        }
        for (a, b) in [(48, 18), (17, 5), (0, 4), (9, 0), (270, 192)] {
            cases.push(format!(
                "gcd = (a, b) => b == 0 ? a : gcd(b, a % b)
x = gcd({a}, {b})
x
"
            ));
        }
        for case in &cases {
            let v = check_source(case).expect("parses and checks").0;
            assert!(
                v.accepted(),
                "{case}
{:#?}",
                v.findings
            );
            assert!(
                matches!(
                    run_program_bounded(case, FUEL),
                    BoundedRun::Completed { .. }
                ),
                "a Grounded call must complete: {case}"
            );
        }
    }

    /// §13.4 / GR-23a (witness validity, evidence): a termination **refutation's
    /// witness is denotationally forced** — running the refuted call at its own
    /// written argument diverges in the bounded oracle (never completes, never
    /// traps). The drift-away and closed-orbit certificate shapes.
    #[test]
    fn snd_gr23a_refutation_witnesses_diverge() {
        for (src, call) in [
            (
                "g = (n) => n == 0 ? 0 : g(n + 1)
x = g(1)
",
                "g = (n) => n == 0 ? 0 : g(n + 1)
g(1)
x = 1
x
",
            ),
            (
                "h = (n) => n == 0 ? 0 : h(n)
x = h(3)
",
                "h = (n) => n == 0 ? 0 : h(n)
h(3)
x = 1
x
",
            ),
        ] {
            let v = check_source(src).expect("parses and checks").0;
            assert!(!v.accepted(), "the refuted call must reject: {src}");
            match run_program_bounded(call, FUEL) {
                BoundedRun::Diverged { .. } => {}
                other => panic!(
                    "the refutation witness must be denotationally forced to diverge, got {other:?}: {call}"
                ),
            }
        }
    }

    /// A-SND layer (3), under the stamped law. Principle 9 binds **all recursion
    /// uniformly — no seat exemption**: even a statement-seat call of an
    /// unproven-termination callee rejects (pinned here), so no call-seat gray
    /// class exists. The bounded oracle doubles as conservatism evidence: the
    /// rejected programs run without trapping — the rejections are honest unproven
    /// voices, not suppressed traps.
    #[test]
    fn snd3_unproven_recursion_rejects_uniformly_and_never_traps() {
        let collatz = "collatz = (n) => n == 1 ? 1 : (n % 2 == 0 ? collatz(n / 2) : collatz(3 * n + 1))\ncollatz(27)\nx = 1\nx\n";
        let sum = "IntList = Union(Null, {value: Number, next: IntList})\nsum = (l) => l :: { Null => 0\n {value: v, next: n} => v + sum(n) }\nx = sum({value: 1, next: {value: 2, next: null}})\nx\n";
        let ascending = "g = (n) => n == 0 ? 0 : g(n + 1)\ng(1)\nx = 1\nx\n";
        for (src, completes) in [(collatz, true), (sum, true), (ascending, false)] {
            let v = check_source(src).expect("parses and checks").0;
            assert!(
                !v.accepted(),
                "Principle 9 is uniform — unproven recursion rejects at every seat: {src}"
            );
            match run_program_bounded(src, FUEL) {
                BoundedRun::Trapped(t) => {
                    panic!("a conservatively-rejected program must not trap: {src}\n{t:?}")
                }
                BoundedRun::Completed { .. } => assert!(completes, "{src}"),
                BoundedRun::Diverged { .. } => assert!(!completes, "{src}"),
            }
        }
    }

    /// The one surviving gray class under the stamped law: **world-decided Effect
    /// recursion** (GR-26's SCC-world-decided certificate — Unproven + the label,
    /// compiling by the world's decision). Layer (3)'s obligation for it — may
    /// diverge, must not trap — awaits host effects in the bounded runner.
    #[test]
    #[ignore = "world-decided gray runner: the bounded oracle installs no host effects yet; expectation recorded — may diverge, must never trap"]
    fn snd3_world_decided_gray_runner() {
        unreachable!("pending bounded-runner host effects");
    }

    /// Recursive-contract discharge (evidence): analyzer-side membership
    /// (`recursive::contains`, the E9 runtime pattern route) and the oracle's own
    /// match agree on sampled values — inside, boundary, and outside the shape.
    #[test]
    fn snd_recursive_contract_membership_agrees_with_oracle() {
        for (literal, expected) in [
            ("null", "1"),
            ("{value: 1, next: null}", "1"),
            ("{value: 1, next: {value: 2, next: null}}", "1"),
            ("{value: \"s\", next: null}", "2"),
            ("{value: 1}", "2"),
            ("7", "2"),
        ] {
            let src = format!(
                "IntList = Union(Null, {{value: Number, next: IntList}})
                 f = (l) => l :: {{ IntList => 1
 _ => 2 }}
x = f({literal})
x
"
            );
            match run_program_bounded(&src, FUEL) {
                BoundedRun::Completed { value, .. } => {
                    assert_eq!(
                        value, expected,
                        "membership of {literal} must be {expected}"
                    );
                }
                other => panic!("membership probe must complete: {literal} → {other:?}"),
            }
        }
    }
}

// The RT-01…14 suite obligations (region spec §10) not already pinned at the lib
// layer (RT-05 ladder, RT-09 cache identity) or by `region_instantiation` (RT-01,
// both arities). Table-level rows assert the spec's (region, exact) facets; the
// walk facets assert selection/consumption; RT-10/RT-14 assert program behavior.
mod region_rows {
    use super::*;
    use next::analyzer::TypeEnv;
    use next::analyzer::domain::AnalysisContract;
    use next::analyzer::region::{region_table_in, region_table_multi, select, select_multi};
    use next::contract::{Contract, Kind};
    use next::interner::Interner;
    use next::oracle::harness::run_source_in;

    fn body_of(src: &str, i: &mut Interner) -> next::ast::Expr {
        let f = run_source_in(src, i).unwrap().0;
        (*f.as_closure().unwrap().lambda.body).clone()
    }

    /// RT-02 [the v0.2 selection-blocker regression guard]: a bounded-range capture
    /// row is a may-region — `check(50)` selects it **without first-match resolution**
    /// (the reject row is selected too, results joined), while `check(200)` falls
    /// outside the bound and selects the reject row alone.
    #[test]
    fn rt02_bounded_capture_never_resolves_first_match() {
        let mut i = Interner::new();
        let cenv = std::collections::HashMap::new();
        let body = body_of("cap = 0\nf = (n) => n <= cap ? 1 : 2\nf", &mut i);
        let mut caps = TypeEnv::new();
        caps.insert(
            "cap".to_string(),
            AnalysisContract::of_contract(Contract::LessEq(100.into())),
        );
        let rows = region_table_in(&body, "n", &caps, &cenv, &mut i);
        assert!(!rows[0].exact, "case (b) is never exact");
        assert_eq!(rows[0].region, Contract::LessEq(100.into()));
        let fifty = Contract::Equals(i.integer(50));
        assert_eq!(
            select(&rows, &fifty, &mut i).len(),
            2,
            "both carried, joined"
        );
        let two_hundred = Contract::Equals(i.integer(200));
        let sel = select(&rows, &two_hundred, &mut i);
        assert_eq!(sel.len(), 1, "accept's candidate is empty at 200");
    }

    /// RT-03 (W-3 totality) and RT-11 (case (c) is *opaque*, not held): a
    /// two-parameter guard with zero captures regionalizes to all-`Top` non-exact;
    /// both rows stay selected over the open domain. RT-06 (W-6 negation opacity):
    /// `!(n <= limit)` reads opaque too — never `Bottom`, both rows selected.
    #[test]
    fn rt03_06_11_sibling_parameters_are_opaque_never_bottom() {
        let mut i = Interner::new();
        for src in [
            "f = (n, limit) => n <= limit ? 1 : 2\nf",
            "f = (n, limit) => !(n <= limit) ? 1 : 2\nf",
        ] {
            let body = body_of(src, &mut i);
            let rows = region_table_multi(&body, &["n".into(), "limit".into()], &mut i)
                .expect("guard-only arms build the positional table");
            assert!(
                rows[0].regions.iter().all(|c| matches!(c, Contract::Top)),
                "opaque guard row: {rows:?}"
            );
            assert!(!rows[0].exact, "opaque is never exact");
            assert!(
                rows.iter()
                    .all(|r| r.regions.iter().all(|c| !matches!(c, Contract::Bottom))),
                "negation of opaque must not degenerate: {rows:?}"
            );
            let num = Contract::Kind(Kind::Number);
            let sel = select_multi(&rows, &[num.clone(), num], &mut i);
            assert_eq!(sel.len(), 2, "totality: both selected, results joined");
        }
    }

    /// RT-04 (W-4): a compound guard with a known and an opaque leaf narrows by the
    /// known leaf (`GT(0)`), stays non-exact, and consumes nothing — the else arm
    /// remains live over the whole domain.
    #[test]
    fn rt04_compound_guard_narrows_by_the_known_leaf() {
        let mut i = Interner::new();
        let cenv = std::collections::HashMap::new();
        let body = body_of(
            "lo = 0\nhi = 0\nf = (n) => n > lo && n < hi ? 1 : 2\nf",
            &mut i,
        );
        let mut caps = TypeEnv::new();
        caps.insert(
            "lo".to_string(),
            AnalysisContract::of_contract(Contract::Equals(i.integer(0))),
        );
        let rows = region_table_in(&body, "n", &caps, &cenv, &mut i);
        assert_eq!(rows[0].region, Contract::Greater(0.into()), "{rows:?}");
        assert!(!rows[0].exact, "an opaque leaf is present");
        let num = Contract::Kind(Kind::Number);
        assert_eq!(select(&rows, &num, &mut i).len(), 2, "else stays live");
    }

    /// RT-07: a bind pattern with a guard composes — region = pattern ∩ guard,
    /// exact = pattern-exact && guard-exact — in both directions (exact comparison
    /// guard stays exact; opaque guard drops exactness).
    #[test]
    fn rt07_row_exactness_is_pattern_and_guard() {
        let mut i = Interner::new();
        let cenv = std::collections::HashMap::new();
        let caps = TypeEnv::new();
        let body = body_of("f = (x) => x :: { k when k <= 5 => 1\n _ => 2 }\nf", &mut i);
        let rows = region_table_in(&body, "x", &caps, &cenv, &mut i);
        assert_eq!(rows[0].region, Contract::LessEq(5.into()));
        assert!(rows[0].exact, "bind-exact && comparison-exact");
        let body2 = body_of(
            "f = (x) => x :: { k when k * k <= 5 => 1\n _ => 2 }\nf",
            &mut i,
        );
        let rows2 = region_table_in(&body2, "x", &caps, &cenv, &mut i);
        assert!(matches!(rows2[0].region, Contract::Top) && !rows2[0].exact);
    }

    /// RT-12 [pin blocker regression guard]: a non-singleton pin (`^y`, `y` a
    /// sibling parameter) is `region Top, exact false` — it consumes nothing, the
    /// wildcard keeps the whole domain, and the pin did **not** consume the else arm.
    #[test]
    fn rt12_non_singleton_pin_consumes_nothing() {
        let mut i = Interner::new();
        let cenv = std::collections::HashMap::new();
        let body = body_of("f = (x, y) => x :: { ^y => 1\n _ => 2 }\nf", &mut i);
        let rows = region_table_in(&body, "x", &TypeEnv::new(), &cenv, &mut i);
        assert!(
            matches!(rows[0].region, Contract::Top) && !rows[0].exact,
            "relational, unrepresentable as unary on x: {rows:?}"
        );
        let num = Contract::Kind(Kind::Number);
        let sel = select(&rows, &num, &mut i);
        assert_eq!(sel.len(), 2, "wildcard stays selectable");
        assert_eq!(
            sel[1].region,
            Contract::Kind(Kind::Number),
            "the pin consumed nothing — `x != y` still reaches the else arm"
        );
    }

    /// RT-13: a singleton pin (`y = 5`) is the point region, exact; it consumes its
    /// point — `5` selects the pin alone, anything else the wildcard alone.
    #[test]
    fn rt13_singleton_pin_consumes_its_point() {
        let mut i = Interner::new();
        let cenv = std::collections::HashMap::new();
        let body = body_of("y = 5\nf = (x) => x :: { ^y => 1\n _ => 2 }\nf", &mut i);
        let mut caps = TypeEnv::new();
        caps.insert(
            "y".to_string(),
            AnalysisContract::of_contract(Contract::Equals(i.integer(5))),
        );
        let rows = region_table_in(&body, "x", &caps, &cenv, &mut i);
        assert!(rows[0].exact, "singleton pin is exact: {rows:?}");
        let five = i.integer(5);
        assert!(rows[0].region.contains(&five), "the point region");
        let at5 = Contract::Equals(five);
        assert_eq!(select(&rows, &at5, &mut i).len(), 1, "the pin consumes 5");
        let at7 = Contract::Equals(i.integer(7));
        let sel = select(&rows, &at7, &mut i);
        assert_eq!(sel.len(), 1, "7 reaches the wildcard alone");
    }

    /// RT-10 [per-call vs source guard], all three outcomes kept distinct: a row
    /// disjoint from one call's argument is silent non-selection; a row dead over
    /// the *declared* domain is silent too (the entry contract is not the
    /// function's domain — internal recursion lawfully arrives outside it, the
    /// recovered grid's `Strict` factorial being the normative witness); only a
    /// row whose region is consumed by *prior arms* — dead over the function's
    /// whole parameter domain — is the E9 unreachable-branch error.
    #[test]
    fn rt10_per_call_and_declared_narrowing_stay_silent() {
        let v = check_source("f = (x) => x :: { Number => 1\n String => 2 }\nr = f(5)\n")
            .expect("parses and checks")
            .0;
        assert!(
            v.accepted(),
            "non-selection is not an error: {:#?}",
            v.findings
        );

        let w = check_source(
            "f where (Number) => Number\nf = (x) => x :: { Number => 1\n String => 2 }\nr = f(5)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            w.accepted(),
            "declared-domain narrowing is not deadness: {:#?}",
            w.findings
        );
    }

    /// RT-10's error half: consumption-dead arms — a duplicate kind row, a
    /// duplicate literal row, and any row after a wildcard — reject with the
    /// unreachable-branch error at the `where` seat.
    #[test]
    fn rt10_consumption_dead_arms_error() {
        for src in [
            "f where (Number) => Number\nf = (x) => x :: { Number => 1\n Number => 2 }\nr = f(5)\n",
            "f where (Number) => Number\nf = (x) => x :: { 5 => 1\n 5 => 2\n _ => 3 }\nr = f(5)\n",
            "f where (Number) => Number\nf = (x) => x :: { _ => 1\n Number => 2 }\nr = f(5)\n",
        ] {
            let v = check_source(src).expect("parses and checks").0;
            assert!(!v.accepted(), "consumption-dead arm must reject: {src}");
            assert!(
                v.findings
                    .iter()
                    .any(|f| f.message.contains("unreachable branch")),
                "{src} → {:#?}",
                v.findings
            );
        }
    }

    /// RT-14 [witness bridge]: an arm selected only through an over-approximate
    /// candidate licenses no refutation — the trap behind an opaque guard's else
    /// arm rejects through the **Unproven** voice, never `Refuted` (no represented
    /// witness reaches it; dynamically none ever does).
    #[test]
    fn rt14_over_approximate_selection_mints_no_witness() {
        let v = check_source(
            "f where (Number) => Number\nf = (n) => n * n >= 0 ? 1 : 1 + \"s\"\nx = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(!v.accepted(), "policy blocks unproven safety at a where");
        assert!(
            v.body_safety_demands
                .iter()
                .all(|d| { !matches!(d.verdict, next::analyzer::safety::BodySafety::Refuted(_)) }),
            "no refutation without a represented witness: {:#?}",
            v.findings
        );
        assert!(
            v.body_safety_demands
                .iter()
                .any(|d| { matches!(d.verdict, next::analyzer::safety::BodySafety::Unproven(_)) }),
            "the honest third voice carries the rejection"
        );
    }

    /// RT-14's completion half, plus the E10 produce claim at the `where`: a body
    /// whose match provably falls through over the declared domain rejects (the
    /// oracle traps ExpectingSeat on the same input), and one whose coverage is
    /// merely unproven (opaque guard) rejects through the unproven voice — with
    /// the return demand never claiming a refutation witness in either case.
    #[test]
    fn rt14_where_completion_rejects_without_minting_witnesses() {
        let proven_gap = check_source(
            "f where (Number) => Number\nf = (n) => n :: { k when k >= 5 => 1 }\nx = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !proven_gap.accepted(),
            "f(3) traps ExpectingSeat in the oracle — accepting is a false accept"
        );

        let unproven_gap = check_source(
            "f where (Number) => Number\nf = (n) => n :: { k when k * k >= 0 => 1 }\nx = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !unproven_gap.accepted(),
            "coverage behind an opaque guard is not proven — the claim cannot stamp"
        );
        for v in [&proven_gap, &unproven_gap] {
            assert!(
                v.return_demands.iter().all(|d| {
                    !matches!(d.verdict, next::analyzer::refute::ClaimVerdict::Refuted(_))
                }),
                "no manufactured completion witness (RT-14)"
            );
        }
    }
}

// The guards' own path demands (T3.1): a guard is a body seat like any other —
// its operations and its strict Boolean tested seat (E10) fire for every arrival.
mod guard_demands {
    use super::*;

    /// The measured false accept this slice closed: the partition path analyzed
    /// only row results, so a guard that traps (mixed `+`) — or a non-Boolean
    /// tested seat — slipped through while the oracle traps. Both reject now.
    #[test]
    fn gd_trapping_and_non_boolean_guards_reject() {
        let v = check_source(
            "f where (Number) => Number\n\
             f = (n) => n + \"s\" == 0 ? 1 : 2\n\
             x = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(!v.accepted(), "the guard's Add traps on every arrival");

        let w = check_source(
            "g where (Number) => Number\n\
             g = (n) => n + 1 ? 1 : 2\n\
             x = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(
            !w.accepted(),
            "a tested seat demands Boolean on arrival (E10)"
        );
    }

    /// The sound converse: ordinary comparison guards keep proving — the demand
    /// machinery adds no false rejections to the day's green families.
    #[test]
    fn gd_ordinary_guards_still_prove() {
        let v = check_source(
            "Nat = Intersection(GreaterEq(0), Mod(1, 0))\n\
             countDown where (Nat) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n\
             x = countDown(5)\n",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);
    }
}

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

    /// The group-aware analyzer consumers (the ambient-group routing): a recursive
    /// contract **pattern** consumes its whole declared domain, so the wildcard arm
    /// is dead and the produced contract is exactly the first arm's — the declared
    /// `Range(1, 1)` return proves. The wrong claim stays rejected.
    #[test]
    fn rc_contract_pattern_consumes_and_kills_later_arms() {
        let v = check_source(
            "IntList = Union(Null, {value: Number, next: IntList})\n\
             f where (IntList) => Range(1, 1)\n\
             f = (l) => l :: { IntList => 1\n _ => 2 }\n\
             x = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(v.accepted(), "{:#?}", v.findings);

        let wrong = check_source(
            "IntList = Union(Null, {value: Number, next: IntList})\n\
             f where (IntList) => Range(2, 2)\n\
             f = (l) => l :: { IntList => 1\n _ => 2 }\n\
             x = 1\n",
        )
        .expect("parses and checks")
        .0;
        assert!(!wrong.accepted(), "the selected arm's 1 refutes Range(2,2)");
    }

    /// Structural exhaustiveness over the recursive union, no wildcard: `Null` and
    /// the record branch cover `IntList`, proven by the group's progress-guarded
    /// induction routed through the ambient group.
    #[test]
    fn rc_structural_match_proves_exhaustive() {
        let v = check_source(
            "IntList = Union(Null, {value: Number, next: IntList})\n\
             g where (IntList) => Number\n\
             g = (l) => l :: { Null => 0\n {value: v, next: n} => 1 }\n\
             x = 1\n",
        )
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

/// **The arithmetic slice is the *evaluated* form (A12), and it obeys §8's master
/// law.** Moving μ §8's frozen rewrites into the normalization phase put them in
/// front of the oracle and the analyzer both — which is the only way "preserve
/// demands so shape-level analysis never forgets an obligation" means anything.
/// It also made two long-standing violations reachable at value level, since a
/// rewritten body and its source now intern to one closure. Both are pinned shut
/// here: each pair is a program that must behave the *same* whether or not a
/// second, differently-spelled function sits above it.
mod arithmetic_normal_form {
    use next::oracle::{BoundedRun, run_program_bounded, run_program_value};

    fn value(src: &str) -> String {
        format!("{:?}", run_program_value(src).expect("completes"))
    }

    fn outcome(src: &str, fuel: u64) -> &'static str {
        match run_program_bounded(src, fuel) {
            BoundedRun::Completed { .. } => "completed",
            BoundedRun::Diverged { .. } => "diverged",
            BoundedRun::Trapped(_) => "trapped",
        }
    }

    /// The permitted rewrites still fire, now on the form everything reads.
    #[test]
    fn an_01_the_frozen_slice_still_identifies_spellings() {
        assert_eq!(
            value("[((a, b) => a + b) == ((a, b) => b + a)]"),
            value("[true]")
        );
        assert_eq!(value("[((x) => x + x) == ((x) => 2 * x)]"), value("[true]")); // H-05
        assert_eq!(
            value("[((x, y) => 2 * x + 3 * y) == ((x, y) => 3 * y + 2 * x)]"),
            value("[true]")
        );
        assert_eq!(
            value("[((x) => -x + x) == ((x) => x - x)]"),
            value("[true]")
        );
        // A12's bonus: reordering now precedes capture-slot assignment, so two
        // spellings over the same free names are one value. Before, the slot
        // order recorded the source order and they compared unequal.
        assert_eq!(
            value("a = 1\nb = 2\n[(() => a + b) == (() => b + a)]"),
            value("[true]")
        );
    }

    /// **Purity decides, not the operator [user, 2026-08-07].** An accepted
    /// program has no bottoms — Principle 9 rejects the hang, safety analysis
    /// rejects the trap — so in pure code nothing can observe which operand ran
    /// first, and the slice reorders and combines freely. A pure expression is
    /// pure wherever it sits; only a `@mutate`/`@effect` body fires something
    /// ordered.
    #[test]
    fn an_02_pure_operands_reorder_and_combine() {
        assert_eq!(
            value("[((p, q) => p() + q()) == ((p, q) => q() + p())]"),
            value("[true]")
        );
        assert_eq!(
            value("[((g) => g() + g()) == ((g) => 2 * g())]"),
            value("[true]")
        );
        assert_eq!(
            value("[((p, q) => p() * q()) == ((p, q) => q() * p())]"),
            value("[true]")
        );
    }

    /// And the programs that once witnessed a difference do not compile, which
    /// is *why* the pure world is free: `spin` is not proven to finish and `bad`
    /// is refuted outright.
    #[test]
    fn an_03_the_old_witnesses_are_rejected_programs() {
        let (v, _) = next::oracle::check_source(
            "spin = () => spin()\n\
             bad = () => \"a\" * 2\n\
             k = (p, q) => q() + p()\n\
             k(spin, bad)\n",
        )
        .expect("checks");
        assert!(
            !v.accepted(),
            "the witness must not compile: {:?}",
            v.findings
        );

        // Effect order, which *is* observable, is preserved.
        let act = "@effect p = () => { println(\"P\") }\n\
                   @effect q = () => { println(\"Q\") }\n\
                   @effect e = () => { q()\n p() }\n\
                   e()\n";
        let (_, io) = next::oracle::run_source(act).expect("runs");
        assert_eq!(io.output, vec!["Q".to_string(), "P".to_string()]);
    }

    /// MU-10's trio, read at the phase rather than at the shape helper.
    #[test]
    fn an_04_the_permanent_exclusions_do_not_fire() {
        assert_eq!(value("[((x) => x + 0) == ((x) => x)]"), value("[false]"));
        assert_eq!(
            value("[((f, x) => 0 * f(x)) == ((f, x) => 0)]"),
            value("[false]")
        );
        assert_eq!(value("[((x) => x - x) == ((x) => 0)]"), value("[false]"));
        assert_eq!(
            outcome(
                "loop = (x) => loop(x)\nz = (x) => 0 * loop(x)\nz(1)\n",
                3000
            ),
            "diverged"
        );
    }
}

/// **A consequence never speaks [user, 2026-08-07].** If `d` errors, then `f = d + e`
/// errors too — and so does the enclosing `+` of a failing sub-expression. Same
/// descendant relation, once across a binding and once inside one expression. The
/// statement level already suppressed the first; these rows pin the second, and pin
/// that suppression does not reach *siblings* (independent failures still all report)
/// or *Unproven* operands (whose seat Error is what rejects the program).
mod consequence_suppression {
    use next::analyzer::Severity;

    fn report(src: &str) -> Vec<String> {
        let (v, _) = next::oracle::check_source(src).expect("checks");
        v.findings
            .iter()
            .map(|f| format!("{:?}/{:?}", f.severity, f.class))
            .collect()
    }

    fn errors(src: &str) -> usize {
        let (v, _) = next::oracle::check_source(src).expect("checks");
        v.findings
            .iter()
            .filter(|f| f.severity == Severity::Error)
            .count()
    }

    /// The enclosing operation adds nothing once an operand has already failed.
    #[test]
    fn cs_01_the_enclosing_operation_goes_quiet() {
        assert_eq!(
            report("d = (1 + \"x\") + (2 * \"y\")\n"),
            vec!["Error/OperationSafety"],
            "the parent's two 'cannot prove Add safe' lines are consequences"
        );
    }

    /// Independent failures are **not** consequences — every one still reports.
    #[test]
    fn cs_02_siblings_all_report() {
        assert_eq!(errors("d = null.x + {a: 1}.b\n"), 2);
        assert_eq!(errors("d = null.x + [1, 2][5]\n"), 2);
        assert_eq!(errors("d = null.x + {a: 1}.b + [1, 2][5]\n"), 3);
    }

    /// Across a binding, unchanged: the chain reports its root once.
    #[test]
    fn cs_03_a_chain_reports_its_root_once() {
        assert_eq!(
            errors("a = 1 + \"x\"\nb = a + 1\nc = b + 1\ne = c + 1\n"),
            1
        );
    }

    /// **Only an Error suppresses.** An *Unproven* operand still earns the seat's
    /// unsuppressible Error — suppressing there would let the program compile.
    #[test]
    fn cs_04_unproven_still_rejects() {
        let src = "c = (n) => n == 1 ? 1 : (n % 2 == 0 ? c(n / 2) : c(3 * n + 1))\nc(7)\n";
        let (v, _) = next::oracle::check_source(src).expect("checks");
        assert!(!v.accepted(), "an unproven program must not compile");
        assert!(
            v.findings
                .iter()
                .any(|f| f.severity == Severity::Error
                    && f.message.contains("at this executable seat")),
            "the seat Error is what rejects it: {:?}",
            v.findings
        );
    }

    /// And a clean program is still accepted — suppression rejects nothing new.
    #[test]
    fn cs_05_a_clean_program_still_compiles() {
        let (v, _) = next::oracle::check_source("d = (n) => n == 0 ? 0 : d(n - 1)\nx = d(5) + 1\n")
            .expect("checks");
        assert!(v.accepted(), "{:?}", v.findings);
    }
}

/// **Phase GR — the grounding specimens (Grounding Specification §15).** One test per
/// specimen, IDs per the test-suite spec: `GR-01`–`GR-30`, with `GR-03A`–`GR-03D` for
/// 3a–3d and `GR-22B` for 22b. Expected verdicts are §15's table verbatim.
///
/// **The P-1 flip.** The suite spec writes "unproven → GRAY under current law (the
/// expectation flips to REJECT if P-1 stamps rejection; the flip rides the P-1 status,
/// not edits to these cases)." P-1 **is** stamped [user, 2026-08-07], so every unproven
/// row asserts rejection — and asserts it is reached *honestly*, with no `Refuted`
/// verdict minted. That second half is the point: specimens 10, 17 and 29 exist only to
/// assert the compiler does not claim a divergence proof it does not have.
///
/// Programs marked **[spec text]** are written in the specification itself. The rest are
/// constructed from §15's prose description and are noted as such.
mod grounding_specimens {
    use next::analyzer::grounding::Verdict;
    use next::oracle::check_source;

    fn verdicts(src: &str) -> Vec<Verdict> {
        let (v, _) = check_source(src).expect("parses and checks");
        v.grounding_demands
            .iter()
            .map(|g| g.verdict.clone())
            .collect()
    }

    fn accepted(src: &str) -> bool {
        check_source(src).expect("parses and checks").0.accepted()
    }

    /// §15 "proven": grounding certifies, and the program compiles.
    fn assert_proven(src: &str) {
        let vs = verdicts(src);
        assert!(
            !vs.is_empty() && vs.iter().all(|v| *v == Verdict::Grounded),
            "expected every recursion Grounded, got {vs:?} for:\n{src}"
        );
        assert!(accepted(src), "a grounded program must compile:\n{src}");
    }

    /// §15 "unproven": rejected under the stamp, and **no refutation minted**.
    fn assert_unproven(src: &str) {
        let vs = verdicts(src);
        assert!(
            !vs.iter().any(|v| matches!(v, Verdict::Refuted(_))),
            "a failed candidate must never be minted as a refutation, got {vs:?} for:\n{src}"
        );
        assert!(
            vs.contains(&Verdict::Unproven),
            "expected an honest Unproven, got {vs:?} for:\n{src}"
        );
        assert!(
            !accepted(src),
            "unproven termination rejects under P-1:\n{src}"
        );
    }

    /// §15 "refuted": a witness-bearing divergence proof, with the witness as stated.
    fn assert_refuted_with(src: &str, witness: i64) {
        let vs = verdicts(src);
        let found: Vec<_> = vs
            .iter()
            .filter_map(|v| match v {
                Verdict::Refuted(r) => Some(r.witness.clone()),
                _ => None,
            })
            .collect();
        assert!(
            found
                .iter()
                .any(|w| *w == next::rational::Rational::from(witness)),
            "expected Refuted with witness {witness}, got {vs:?} for:\n{src}"
        );
        assert!(!accepted(src), "a refuted program must not compile:\n{src}");
    }

    // ── The specimens ────────────────────────────────────────────────────────

    /// **GR-01 — Zeno.** [spec text, §3 GR-05(1)] Steps move forward every time but
    /// halve, so no positive floor is exposed. This is the case that forced the rule to
    /// read "at least a fixed amount" rather than "forward"; its proven twin is GR-19.
    #[test]
    fn gr_01_zeno_exposes_no_floor() {
        assert_unproven("f = (x, s) => x >= 100 ? 0 : f(x + s, s / 2)\nr = f(0, 50)\n");
    }

    /// **GR-02 — factorial.** Constant drift −1 to a point base on the integer grid.
    #[test]
    fn gr_02_factorial_is_proven() {
        assert_proven("factorial = (n) => n == 0 ? 1 : n * factorial(n - 1)\nr = factorial(5)\n");
    }

    /// **GR-05 — Ackermann.** Proven by a joint lexicographic certificate.
    #[test]
    fn gr_05_ackermann_is_proven() {
        assert_proven(
            "ack = (m, n) => m == 0 ? n + 1 : (n == 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)))\n\
             r = ack(2, 2)\n",
        );
    }

    /// **GR-06 — collatz.** No candidate source; basin derivation is deferred. Both
    /// starts unproven — and neither may be refuted.
    #[test]
    fn gr_06_collatz_is_unproven_at_both_starts() {
        let c = "c = (n) => n == 1 ? 1 : (n % 2 == 0 ? c(n / 2) : c(3 * n + 1))\n";
        assert_unproven(&format!("{c}r = c(64)\n"));
        assert_unproven(&format!("{c}r = c(27)\n"));
    }

    /// **GR-07 — McCarthy 91.** The negative battery's baseline.
    #[test]
    fn gr_07_mccarthy_91_is_proven() {
        assert_proven("m91 = (n) => n > 100 ? n - 10 : m91(m91(n + 11))\nr = m91(50)\n");
    }

    /// **GR-08 — oscillator.** [spec text, §3 GR-07] One cycle, +2 then −3; the composed
    /// progress is `Equals(1)`, so the round trip nets a fixed positive gain.
    #[test]
    #[ignore = "GAP (grounding, measured 2026-08-07): §15 #8 expects proven by cycle \
composition; the implementation returns Unproven. GR-07's per-cycle composed ProgressRange \
over the completed graph does not fire for this two-function +2/-3 cycle. Under stamped P-1 \
this is a FALSE REJECTION — a terminating program that will not compile."]
    fn gr_08_oscillator_proves_by_cycle_composition() {
        assert_proven("a = (n) => n <= 0 ? 0 : b(n + 2)\nb = (n) => a(n - 3)\nr = a(10)\n");
    }

    /// **GR-09 — countDown, wide domain.** Well-founded with unbounded depth: the
    /// certificate is never a bound on how deep the recursion goes.
    #[test]
    fn gr_09_countdown_proves_over_a_wide_domain() {
        assert_proven("countDown = (n) => n == 0 ? 0 : countDown(n - 1)\nr = countDown(5)\n");
    }

    /// **GR-10 — structural minting.** [spec text, §4 GR-10(1)] `f([x])` builds a new
    /// container whose element is the prior *state*, not a pooled atom, so the exact-chain
    /// license fails by provenance. Unproven — and explicitly **no refutation minted**.
    #[test]
    fn gr_10_structural_minting_mints_no_refutation() {
        assert_unproven("f = (x) => f([x])\nr = f(1)\n");
    }

    /// **GR-11 — 40↔60 alternation.** Every step improves toward *some* exit, never one
    /// fixed exit, so the multi-base rule declines. Candidate failure is not refutation.
    #[test]
    fn gr_11_alternation_has_no_fixed_exit() {
        assert_unproven(
            "f = (n) => n == 40 ? 0 : (n == 60 ? 1 : (n < 50 ? f(n + 10) : f(n - 10)))\nr = f(45)\n",
        );
    }

    /// **GR-12 — off-grid point base.** [spec text, §3 GR-05(2)] Constant drift −2 from a
    /// written `1`: the orbit 1, −1, −3 … provably misses the point base 0. Refuted, and
    /// the witness is the argument as written.
    #[test]
    fn gr_12_stepping_over_the_base_is_refuted() {
        assert_refuted_with("f = (n) => n == 0 ? 0 : f(n - 2)\nr = f(1)\n", 1);
    }

    /// **GR-19 — sumUntil, variable drift.** GR-01's twin: the step varies, but a floor
    /// of 1 *is* derivable from the call, so δ = 1 and the certificate closes.
    #[test]
    #[ignore = "GAP (safety, not grounding — measured 2026-08-07): grounding returns \
Grounded, exactly as §15 #19 expects. The program is still rejected, by \
`callee body safety cannot be proven at this executable seat`. This is the documented \
multi-parameter/mutual body-safety gap, surfaced here by a grounding specimen. FALSE \
REJECTION."]
    fn gr_19_a_derived_floor_proves_a_variable_drift() {
        assert_proven(
            "sumUntil = (n, acc) => n <= 0 ? acc : sumUntil(n - 1, acc + n)\nr = sumUntil(5, 0)\n",
        );
    }

    /// **GR-22 — `f(n − 1) + f(n)` at `f(1)`.** The shape that mandated multi-dependency
    /// composition. Numeric exact walking is not admitted in v1, so honestly unproven —
    /// following one call and not all is the named mistake.
    #[test]
    fn gr_22_multi_dependency_numeric_walking_is_unproven() {
        assert_unproven("f = (n) => n == 0 ? 0 : f(n - 1) + f(n)\nr = f(1)\n");
    }

    /// **GR-24 — varying step `f(n − step, step + 1)`.** No fixed lattice for the point
    /// base, and no admitted witness route: honestly unproven in both directions.
    #[test]
    fn gr_24_a_varying_step_is_honestly_unproven() {
        assert_unproven("f = (n, step) => n <= 0 ? 0 : f(n - step, step + 1)\nr = f(10, 1)\n");
    }

    /// **GR-25 — two-sided stop `a == b`.** The measure route contributes no conclusion.
    #[test]
    fn gr_25_a_two_sided_stop_yields_no_conclusion() {
        assert_unproven("f = (a, b) => a == b ? 0 : f(a + 1, b)\nr = f(0, 5)\n");
    }

    /// **GR-26 — Fibonacci through a nested function.** [spec text, §15 #26] The path
    /// closes on `go` alone — `fib` is outside the cycle — and both call edges (drifts −1
    /// and −2) check against the half-line base `k <= 1`, which lands structurally with no
    /// grid needed.
    #[test]
    #[ignore = "GAP (resolution, not grounding — measured 2026-08-07): grounding is never \
asked. `grounding_demands` is EMPTY and the rejection is \
`cannot prove this callee's body safe (callee not resolved to a known function)`. A \
recursive function declared inside a block (`go` within `fib`) does not resolve, so the \
termination prover never sees it. §15 #26 is the author's own walkthrough and expects \
proven. FALSE REJECTION."]
    fn gr_26_a_nested_recursive_function_is_proven() {
        assert_proven(
            "fib = (n) => { go = (k) => k <= 1 ? k : go(k - 1) + go(k - 2)\n go(n) }\nr = fib(6)\n",
        );
    }

    /// **GR-28 — composed range straddling zero.** [spec text, §3 GR-07] Edge progresses
    /// `Equals(2)` and `−s`. Over `s ⊑ GE(1)` the composed range straddles zero and proves
    /// nothing; pinned at the wide domain, where the answer is no conclusion.
    #[test]
    fn gr_28_a_straddling_cycle_proves_nothing() {
        assert_unproven(
            "a = (n, s) => n <= 0 ? 0 : b(n - 2, s)\nb = (n, s) => a(n + s, s)\nr = a(10, 3)\n",
        );
    }

    /// **GR-03B — literal without 7.** A list peeled one element per step; §15 expects
    /// proven, folding *after* grounding, in that order.
    #[test]
    #[ignore = "GAP (measured 2026-08-07): returns Unproven. The exact-chain license \
(§4 GR-09/10) does not fire for a written tuple argument peeled by slice. FALSE REJECTION."]
    fn gr_03b_a_literal_without_the_merge_value_is_proven() {
        assert_proven("f = (l) => l == [] ? 0 : (l[0] == 7 ? f(l) : f(l[1...]))\nr = f([3, 2])\n");
    }

    /// **GR-22B — the closed orbit, generalized.** [spec text, §4 GR-11] The exact-chain
    /// license holds (7 is a pooled element; drifts −1 and 0; flat varying state; pure).
    /// Required dependencies are `f([])`, which grounds and completes, then `f([7])` —
    /// the cycle. §15 expects **refuted**, witness `[7]`.
    #[test]
    #[ignore = "BLOCKED, structural (measured 2026-08-07): returns Unproven. §15 #22b \
expects Refuted with witness `[7]` — a *sequence* witness — but `Refutation.witness` is a \
`Rational` and cannot represent one. The exact-chain candidate (§4) does not fire for tuple \
states either. Two separate gaps; the witness type is the harder one."]
    fn gr_22b_a_required_dependency_cycle_is_refuted() {
        assert_refuted_with(
            "f = (l) => l == [] ? [] : f(l[1...]) ++ f(l)\nr = f([7])\n",
            7,
        );
    }

    /// **GR-29 — no false cycle refutation.** [spec text, §15 #29] The `f↔g` cycle's
    /// prefix `stall([7])` is outside the exact-chain license and unproven, so the whole
    /// candidate must contribute nothing. The row exists to assert the compiler does *not*
    /// mint a refutation from an unestablished path — and it holds.
    #[test]
    fn gr_29_an_unproven_prefix_mints_no_cycle_refutation() {
        assert_unproven(
            "stall = (l) => stall([l])\n\
             f = (l) => g(l)\n\
             g = (l) => stall(l) ++ f(l)\nr = f([7])\n",
        );
    }

    /// **GR-03A — the 7-literal, with the merge value present.** §15 expects refuted, the
    /// written argument being the witness.
    #[test]
    #[ignore = "BLOCKED, structural (measured 2026-08-07): returns Unproven; §15 #3a \
expects Refuted with witness `[3,7,2]`, a sequence witness `Refutation.witness` \
(a `Rational`) cannot hold. Same blocker as GR-22B."]
    fn gr_03a_the_seven_literal_is_refuted() {
        assert_refuted_with(
            "f = (l) => l == [] ? 0 : (l[0] == 7 ? f(l) : f(l[1...]))\nr = f([3, 7, 2])\n",
            7,
        );
    }

    /// **GR-13 — carried world value.** `loop(msg)` carries a value obtained from the
    /// world rather than re-reading it, so the region seed is stale: not world-decided,
    /// and grounding is unproven.
    #[test]
    #[ignore = "GAP (measured 2026-08-07): the program is ACCEPTED with an empty \
`grounding_demands`. §15 #13 expects grounding unproven, which under stamped P-1 must \
reject. A non-terminating program compiles."]
    fn gr_13_a_carried_world_value_is_not_world_decided() {
        assert_unproven(
            "@effect loop = (m) => { loop(m) }\n@effect main = () => { loop(1) }\nmain()\n",
        );
    }

    /// **GR-16 — decorative branch.** `bit ? loop() : loop()` seeds nothing: both arms
    /// recurse, so the universal closure is empty and no world decision is available.
    #[test]
    #[ignore = "GAP (measured 2026-08-07): ACCEPTED with empty `grounding_demands`; \
§15 #16 expects unproven, which rejects under P-1."]
    fn gr_16_a_decorative_branch_seeds_nothing() {
        assert_unproven(
            "@effect loop = (b) => { b ? loop(b) : loop(b) }\n\
             @effect main = () => { loop(true) }\nmain()\n",
        );
    }

    /// **GR-17 — the pending-write counterexample.** [spec text, §4 GR-10(4)] A mutator
    /// whose own staged write is what reaches the base. A stability-blind exact-chain walk
    /// would mint a **false closed-orbit refutation of a terminating program** — the worst
    /// verdict class. v1 excludes it from chain scope, so the answer is unproven.
    #[test]
    fn gr_17_a_pending_write_mints_no_false_refutation() {
        let src = "@state n = 0\n\
                   @mutate f = (xs) => { n := n + 1\n n == 10 ? 0 : f(xs) }\n\
                   @effect main = () => { f(1) }\nmain()\n";
        let (v, _) = check_source(src).expect("parses and checks");
        assert!(
            !v.grounding_demands
                .iter()
                .any(|g| matches!(g.verdict, Verdict::Refuted(_))),
            "a terminating program must never be refuted: {:?}",
            v.grounding_demands
        );
    }

    /// **GR-20 — split at a letter.** A nested non-recursive helper derives the segment
    /// length; §15 expects the segment facts to close by variable drift.
    #[test]
    #[ignore = "GAP (measured 2026-08-07): returns Unproven. GR-08's derived-segment read \
does not fire here. FALSE REJECTION."]
    fn gr_20_derived_segment_facts_close_by_variable_drift() {
        assert_proven("f = (s) => s == \"\" ? 0 : f(s[1...])\nr = f(\"abc\")\n");
    }

    /// **GR-23 — a multi-cycle SCC with one non-decreasing cycle.** The candidate
    /// contributes nothing; absent a §7 witness the answer is unproven, never refuted.
    #[test]
    fn gr_23_a_non_decreasing_cycle_yields_no_conclusion() {
        assert_unproven(
            "a = (n) => n <= 0 ? 0 : b(n - 1)\n\
             b = (n) => n > 100 ? 0 : (n < 50 ? a(n - 1) : b(n))\nr = a(10)\n",
        );
    }

    /// **GR-30 — effect-world countDown.** [spec text, §15 #30] Ordinary proven
    /// completion; `WorldDecided` is **not** minted, so downstream stays unconditioned.
    #[test]
    #[ignore = "GAP (measured 2026-08-07): §15 #30 expects ordinary proven completion. \
`grounding_demands` is EMPTY — an effect-world recursion *with a base case* raises no \
termination demand at all (one with no base case does). The program is still rejected, by \
body safety. Caught only because the first draft of this row asserted `all(...)` over the \
empty vector and passed vacuously."]
    fn gr_30_an_effect_countdown_proves_without_a_world_label() {
        let src = "@effect countDown = (n) => { n == 0 ? 0 : countDown(n - 1) }\n\
                   @effect main = () => { countDown(5) }\n\
                   main()\n";
        let (v, _) = check_source(src).expect("parses and checks");
        assert!(
            !v.grounding_demands.is_empty(),
            "the recursion must be adjudicated at all"
        );
        assert!(
            v.grounding_demands
                .iter()
                .all(|g| g.verdict == Verdict::Grounded),
            "expected ordinary proven completion: {:?}",
            v.grounding_demands
        );
        assert!(
            v.grounding_demands.iter().all(|g| !g.world_decided),
            "WorldDecided must not be minted here: {:?}",
            v.grounding_demands
        );
    }
}

/// **`++` joins two sequences of the same kind [user, 2026-08-07].** Strings or Tuples,
/// never mixed and never numeric. Tuple concatenation reuses the family's own smart
/// constructor — the shape `[...a, ...b]` already produces — so a `++` chain keeps exact
/// segment structure instead of collapsing to `Kind(Tuple)`.
mod concat_over_tuples {
    fn run(src: &str) -> String {
        format!("{:?}", next::oracle::run_program_bounded(src, 4000))
    }
    fn value(src: &str) -> String {
        match next::oracle::run_program_bounded(src, 4000) {
            next::oracle::BoundedRun::Completed { value, .. } => value,
            other => panic!("expected a value, got {other:?}"),
        }
    }

    #[test]
    fn ct_01_tuples_join() {
        assert_eq!(value("[1, 2] ++ [3]"), "[1, 2, 3]");
        assert_eq!(value("[] ++ [1]"), "[1]");
        assert_eq!(value("[1] ++ []"), "[1]");
        assert_eq!(value("[[1], [2]] ++ [[3]]"), "[[1], [2], [3]]");
        assert_eq!(value("\"a\" ++ \"b\""), "ab");
    }

    /// Mixed kinds have no meaning, and `++` is still never numeric.
    #[test]
    fn ct_02_mixed_and_numeric_operands_trap() {
        for src in ["\"a\" ++ [1]", "[1] ++ \"a\"", "1 ++ 2", "[1] ++ 2"] {
            assert!(
                run(src).contains("OperationSafety"),
                "{src} must trap, got {}",
                run(src)
            );
        }
    }

    /// The whole point of admitting tuples: the list recursions the grounding spec
    /// writes with `++` now run.
    #[test]
    fn ct_03_a_recursive_list_build_runs() {
        assert_eq!(
            value("f = (l) => l == [] ? [] : f(l[1...]) ++ l[0...1]\nr = f([1, 2, 3])\nr"),
            "[3, 2, 1]"
        );
    }

    /// `++` stays outside the arithmetic slice, so concatenation order is never
    /// rearranged — for tuples exactly as for Strings.
    #[test]
    fn ct_04_concatenation_order_survives_canonicalization() {
        assert_eq!(
            value("f = (l) => l ++ [9]\ng = (l) => [9] ++ l\n[f([1]), g([1])]"),
            "[[1, 9], [9, 1]]"
        );
    }
}
