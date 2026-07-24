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
use next::oracle::harness::{prelude_env, run_with_io};
use next::oracle::{Oracle, TrapClass, run_program_commits, run_program_value};
use next::parse::parse_program;
use next::rational::Rational;
use next::value::ValueRef;

// ── Shared helpers ───────────────────────────────────────────────────────────

fn eval(src: &str) -> ValueRef {
    run_program_value(src).expect("evaluated without trapping")
}

fn vtrue(src: &str) {
    assert_eq!(eval(src).as_boolean(), Some(true), "expected VALUE true: {src}");
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
    let Ok(sp) = parse_program(toks) else { return true };
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
    oracle.run_module_in(&module, &env).expect("evaluated without trapping")
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
        assert!(outer.as_tuple().unwrap()[0].ptr_eq(&inner), "shared subtree");
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
        num_eq(&eval("a = [() => b]\nb = [() => a]\na[0]()[0]()[0]()\n1"), 1);
    }

    #[test]
    #[ignore = "PENDING-§5: MU-18 (open-member observation traps unbound-evaluation, Option A) needs the group-construction-window mechanism — the §5 canonicalizer. Without windows, `a` closes at its own statement and `a == a` is reflexively true."]
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
        assert!(parse_error("a |> f <| b"), "unparenthesized |>/<| mixing is a parse error");
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
        assert_eq!(str_of(&eval("h = # _ > 0 ? \"pos\" : \"neg\"\nh(1)")), "pos");
        assert_eq!(str_of(&eval("h = # _ > 0 ? \"pos\" : \"neg\"\nh(-1)")), "neg");
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
        assert_eq!(v.as_record().map(|r| r.len()), Some(0), "x => {{}} yields an empty Record");
    }

    #[test]
    fn p19_empty_act_block() {
        // @effect f = () => { } — the 1.0.3 brace exception: an empty act Block.
        let (v, _io) = run_with_io("@effect f = () => { }\nf()").expect("runs");
        assert!(v.is_null(), "program ends in an effect statement; value null");
    }

    #[test]
    fn p20_two_statements_one_line() {
        assert!(parse_error("x = 1 y = 2"), "L1: one statement per line");
    }

    #[test]
    fn p21_two_arms_one_line() {
        assert!(parse_error("x = 1 :: { 1 => 1 2 => 2 }"), "L2: one arm per line");
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
        assert!(parse_error("x = { a: 1, a: 2 }"), "duplicate literal keys are banned");
    }

    #[test]
    fn p27_import_forms_parse() {
        assert!(!parse_error("import { area } from Geometry"), "named import parses");
        assert!(!parse_error("import Oddo.Utils"), "module import parses");
    }

    #[test]
    #[ignore = "module-system semantics staged: the headerless-export project error is not yet enforced (MOD rows)"]
    fn p27b_headerless_export_rejected() {
        assert!(rejected_any_stage("export x = 1"));
    }

    #[test]
    fn p28_value_side_act_annotation_banned() {
        assert!(parse_error("name = @effect (x) => {}"), "value-side @ does not exist");
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
        assert_eq!(str_of(&eval("3 :: { 1 | 3 => \"hit\"\n_ => \"miss\" }")), "hit");
        assert_eq!(str_of(&eval("2 :: { 1 | 3 => \"hit\"\n_ => \"miss\" }")), "miss");
    }

    #[test]
    fn d11_pin_is_equality_guard() {
        assert_eq!(str_of(&eval("target = 5\n5 :: { ^target => \"eq\"\n_ => \"ne\" }")), "eq");
        assert_eq!(str_of(&eval("target = 5\n4 :: { ^target => \"eq\"\n_ => \"ne\" }")), "ne");
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
        assert!(clamped.ptr_eq(&t), "clamp to the whole tuple = same pointer");
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
    #[ignore = "DIVERGES verdicts need a fuel-limited harness (staged); M-04 activates with it"]
    fn m04_diverging_outer_publishes_nothing() {
        // Expected: outer mutator diverges after inner completed → DIVERGES; σ
        // unchanged — never-completed publishes nothing.
        unreachable!("fuel harness pending");
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

    // ── MOD: modules (staged — imports parse; linking/worlds not built) ──────

    #[test]
    #[ignore = "module-system semantics staged: top-level world distinction for module files"]
    fn mod01_act_call_at_module_top_level_rejected() {
        unreachable!("module linking pending");
    }

    #[test]
    fn mod02_entry_top_level_is_effect_world() {
        let (_, io) = run_with_io("println(\"hi\")").expect("entry file runs effects");
        assert_eq!(io.output, vec!["hi".to_string()]);
    }

    #[test]
    #[ignore = "module-system semantics staged: cross-module store imports"]
    fn mod03_store_module_live_read() {
        unreachable!("module linking pending");
    }

    #[test]
    #[ignore = "module-system semantics staged: module aliasing"]
    fn mod04_module_alias_is_live() {
        unreachable!("module linking pending");
    }

    #[test]
    #[ignore = "module-system semantics staged: project-wide duplicate-module error"]
    fn mod05_duplicate_module_names_error() {
        unreachable!("module linking pending");
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
                (Ok(next::oracle::Outcome::Produced(x)), Ok(next::oracle::Outcome::Produced(y))) => {
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
// Phase A — Analyzer verdict suite (stubs; activates when the analyzer phase
// opens on whole programs — the expression analyzer exists, program-level
// verdicts and worlds do not yet).
// ═════════════════════════════════════════════════════════════════════════════

mod phase_a {
    #[test]
    #[ignore = "Phase A: program-level analyzer verdicts pending (expression analyzer exists; A-NEG needs the recursion arc)"]
    fn a_neg_negative_battery() {
        // Recorded verdicts (Part D§6 — the anti-regression tripwire; these must
        // never change under any future families/analysis work):
        //   factorial              → REJECT
        //   countdown−2            → REJECT
        //   broken fibonacci       → REJECT
        //   collatz                → GRAY
        //   the −4 trap            → excluded per battery record
        //   McCarthy 91            → proven, all reals
        //   Ackermann              → (per D§6 record)
        //   isEven/isOdd (both)    → (per D§6 record)
        //   non-tail mutual        → (per D§6 record)
        //   Hofstadter             → GRAY
        //   gcd                    → (per D§6 record)
        unreachable!("activates with the program-level analyzer");
    }

    #[test]
    #[ignore = "Phase A: acceptance battery pending — runtime-trace layer runnable now, contract-claim layer needs the analyzer"]
    fn a_acc_acceptance_battery() {
        // Two layers per case: the runtime trace (oracle-checkable — e.g.
        // makeLinkedList(1,2,3,4): x.next.next.next.value == 4; …next.next == null;
        // .value on that null TRAPs) and the contract claim (analyzer-phase:
        // builder, map incl. parametric, reverse incl. rev∘rev interning to input,
        // zip, level-regular tree, fold BOUNDED, filter depth-Range, cyclic mutual
        // builders incl. 3-cycles, cross-axis mutual, insert/delete, append,
        // flatMap rectangular, merge/sort depth-exact, walkers, pairUp ×3,
        // rotate (r.next⁷.top ⊑ Equals(\"y\")), UniformFamily guard arithmetic).
        unreachable!("activates with the program-level analyzer");
    }

    #[test]
    #[ignore = "Phase A: the C§16 soundness harness runs when program-level ACCEPT exists"]
    fn a_snd_soundness_harness() {
        // (1) accepted programs → oracle runs → zero traps, per trap class;
        // (2) sampled op inputs → results within claimed output contracts;
        // (3) gray programs may diverge but must not trap.
        unreachable!("activates with the program-level analyzer");
    }

    #[test]
    #[ignore = "Phase A: verdict cases pending program-level analysis (chain hint, exhaustiveness, unions at boundaries)"]
    fn a_ver_verdict_cases() {
        // a < b < c → REJECT with the chain hint · (a == b) == c legal iff c
        // Boolean · exhaustiveness over the E9 remainder · computed keys: finite
        // union ACCEPT / Kind(String) REJECT (the expression-level half is
        // implemented — analyzer::tests::computed_key_finiteness_demand) ·
        // destructuring irrefutability (implemented at expression level) ·
        // data.body on Union(Response, Failure) → REJECT until narrowed ·
        // Failure-overlap wrapper demand · act-kind admission over a union of
        // callees · the E5 discharge: Indeterminate(_/0) arm ACCEPTs the division
        // consumer.
        unreachable!("activates with the program-level analyzer");
    }

    #[test]
    #[ignore = "Phase A: lint tier pending (goes-nowhere, discarded effect result, identity slice, redundant ?./~, ||-non-Boolean, leading-minus continuation, self-prefix)"]
    fn a_lnt_lint_tier() {
        unreachable!("activates with the analyzer's lint pass");
    }

    #[test]
    #[ignore = "Phase A: RECOVER discharged — grids are in `next-phase-a-worked-examples-recovered.md` (verbatim from transcripts). Verification still needs the program-level analyzer (Part D recursion arc): factorial/countdown/where contract derivation, drift, fact-cycle pairs."]
    fn a_wrk_worked_example_grids() {
        unreachable!("blocked on the transcript grids");
    }
}
