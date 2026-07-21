//! Oracle conformance seeds (Semantics Companion §3/§6). The oracle is the truth
//! source; these are the executable checks the specs call for.

use super::*;
use crate::value::ValueData;

/// Evaluate a program, expecting a produced value.
fn eval(src: &str) -> ValueRef {
    run_program_value(src).expect("evaluated without trapping")
}

/// Evaluate a program, expecting a trap of the given class.
fn trap_class(src: &str) -> TrapClass {
    run_program_value(src).expect_err("expected a trap").class
}

fn is_true(v: &ValueRef) -> bool {
    v.as_boolean() == Some(true)
}
fn num(v: &ValueRef) -> &Rational {
    v.as_number().expect("a number")
}

// ── Exactness and arithmetic ─────────────────────────────────────────────────

#[test]
fn exactness_flagship_end_to_end() {
    // The conformance flagship, all the way through the pipeline.
    assert!(is_true(&eval("0.1 + 0.2 == 0.3")));
}

#[test]
fn exact_rational_arithmetic() {
    assert_eq!(num(&eval("1 / 3 + 1 / 3 + 1 / 3")), &Rational::from(1));
    assert_eq!(num(&eval("2 ** 10")), &Rational::from(1024));
    assert_eq!(num(&eval("7 % 3")), &Rational::from(1));
    assert_eq!(num(&eval("2 ** -2")), &Rational::from_decimal("0.25").unwrap());
}

#[test]
fn division_is_total_via_indeterminate() {
    assert_eq!(eval("1 / 0").as_indeterminate(), Some(IndetForm::DivByZero));
    assert_eq!(eval("0 / 0").as_indeterminate(), Some(IndetForm::ZeroOverZero));
    // Indeterminate propagates through arithmetic, left-most.
    assert_eq!(eval("1 / 0 + 5").as_indeterminate(), Some(IndetForm::DivByZero));
}

#[test]
fn indeterminate_is_a_value_not_a_trap_for_equality() {
    // `==` treats Indeterminate as an ordinary value; discharge by match.
    assert!(is_true(&eval("(1 / 0) == (2 / 0)")));
    // but an ordering comparison on it traps (undischarged).
    assert_eq!(trap_class("(1 / 0) < 2"), TrapClass::UndischargedIndeterminate);
}

// ── Truthiness desugarings, end-to-end ───────────────────────────────────────

#[test]
fn nullish_vs_escaped_or_on_false() {
    // The seed: `??` and `~||` differ exactly on `false`.
    // On null they agree (both take the right).
    assert_eq!(num(&eval("null ?? 7")), &Rational::from(7));
    assert_eq!(num(&eval("~null || 7")), &Rational::from(7));
    // On false they diverge: ?? keeps false; ~|| takes the right.
    assert_eq!(eval("false ?? 7").as_boolean(), Some(false));
    assert_eq!(num(&eval("~false || 7")), &Rational::from(7));
    // On a truthy value both keep it (0 is truthy: falsy = {false, null}).
    assert_eq!(num(&eval("0 ?? 7")), &Rational::from(0));
    assert_eq!(num(&eval("~0 || 7")), &Rational::from(0));
}

#[test]
fn boolean_operators() {
    assert_eq!(eval("true && false").as_boolean(), Some(false));
    assert_eq!(eval("false || true").as_boolean(), Some(true));
    assert_eq!(eval("!false").as_boolean(), Some(true));
    assert_eq!(eval("!~null").as_boolean(), Some(true)); // null is falsy
    assert_eq!(eval("!~5").as_boolean(), Some(false)); // 5 is truthy
    assert_eq!(num(&eval(r#"true ? 1 : 2"#)), &Rational::from(1));
}

#[test]
fn tested_seats_are_strict_boolean() {
    // A non-Boolean *guard* is the tested seat that traps (companion §3).
    let guard = "f = (v) => v :: { _ when v => 1 }\nf(5)";
    assert_eq!(trap_class(guard), TrapClass::TestedSeat);
    // A non-Boolean ternary condition instead desugars to a Boolean-exhaustive
    // match; at runtime it matches no arm ⇒ completes-without-value. In a value
    // position (here a binding) the demand surfaces at the expecting seat (the
    // analyzer rejects it up front). As a bare statement it would simply go
    // nowhere.
    assert_eq!(trap_class("y = 5 ? 1 : 2\ny"), TrapClass::ExpectingSeat);
}

// ── Functions, recursion, late binding ───────────────────────────────────────

#[test]
fn functions_and_direct_recursion() {
    let src = "
        factorial = (n) => n == 0 ? 1 : n * factorial(n - 1)
        factorial(5)
    ";
    assert_eq!(num(&eval(src)), &Rational::from(120));
}

#[test]
fn mutual_recursion_via_late_binding() {
    let src = "
        isEven = (n) => n == 0 ? true : isOdd(n - 1)
        isOdd  = (n) => n == 0 ? false : isEven(n - 1)
        isEven(10)
    ";
    assert!(is_true(&eval(src)));
}

#[test]
fn eager_self_reference_traps_unbound() {
    assert_eq!(trap_class("x = x + 1\nx"), TrapClass::UnboundEvaluation);
    assert_eq!(trap_class("y"), TrapClass::UnboundEvaluation);
}

#[test]
fn argument_arity_mismatch_traps() {
    // The parameter pattern is the argument tuple; wrong arity ⇒ obligation trap.
    assert_eq!(trap_class("f = (a, b) => a\nf(1)"), TrapClass::ArgumentObligation);
}

#[test]
fn hask_is_callable() {
    // (# _ + 1)(10) == 11
    assert_eq!(num(&eval("inc = # _ + 1\ninc(10)")), &Rational::from(11));
}

#[test]
fn pipe_is_application() {
    assert_eq!(num(&eval("double = (x) => x * 2\n5 |> double")), &Rational::from(10));
}

// ── Match, patterns, completion ──────────────────────────────────────────────

#[test]
fn match_selects_first_arm() {
    let src = "
        classify = (n) => n :: {
            0 => \"zero\"
            _ => \"other\"
        }
        classify(0)
    ";
    assert_eq!(eval(src).as_string_lossy().unwrap(), "zero");
}

#[test]
fn match_guard_and_binding() {
    let src = "
        sign = (n) => n :: {
            x when x > 0 => \"pos\"
            x when x < 0 => \"neg\"
            _ => \"zero\"
        }
        sign(-3)
    ";
    assert_eq!(eval(src).as_string_lossy().unwrap(), "neg");
}

#[test]
fn tuple_destructuring_pattern() {
    let src = "
        head = (t) => t :: { [h, ..._] => h }
        head([10, 20, 30])
    ";
    assert_eq!(num(&eval(src)), &Rational::from(10));
}

#[test]
fn contract_kind_pattern() {
    let src = "
        kind = (v) => v :: {
            Number => \"num\"
            String => \"str\"
            _ => \"other\"
        }
        kind(\"hi\")
    ";
    assert_eq!(eval(src).as_string_lossy().unwrap(), "str");
}

#[test]
fn indeterminate_discharge_by_pattern() {
    // Indeterminate(_/0) => fallback is an ordinary arm (E9).
    let src = "
        safe = (a, b) => (a / b) :: {
            Indeterminate => \"undefined\"
            v => v
        }
        safe(1, 0)
    ";
    assert_eq!(eval(src).as_string_lossy().unwrap(), "undefined");
}

#[test]
fn expecting_seat_demands_a_value() {
    // A match with no matching arm completes-without-value; used where a value is
    // expected, that traps at the expecting seat.
    let src = "
        f = (n) => n :: { 1 => \"one\" }
        f(2) == \"one\"
    ";
    assert_eq!(trap_class(src), TrapClass::ExpectingSeat);
}

// ── Construction and access ──────────────────────────────────────────────────

#[test]
fn tuple_and_record_construction_and_access() {
    assert_eq!(num(&eval("[1, 2, 3][0]")), &Rational::from(1));
    assert_eq!(num(&eval("[1, 2, 3][-1]")), &Rational::from(3)); // from-end
    assert_eq!(num(&eval("{ a: 1, b: 2 }.b")), &Rational::from(2));
    // spread + later-wins
    assert_eq!(num(&eval("{ ...{ a: 1 }, a: 9 }.a")), &Rational::from(9));
}

#[test]
fn clamped_slices() {
    // t[...10] on a 3-tuple = the 3 elements; empty windows yield [].
    assert_eq!(eval("[1, 2, 3][...10]").as_tuple().unwrap().len(), 3);
    assert_eq!(eval("[1, 2, 3][2...1]").as_tuple().unwrap().len(), 0);
    // t[-2...] = last two
    assert_eq!(eval("[1, 2, 3, 4][-2...]").as_tuple().unwrap().len(), 2);
}

#[test]
fn access_demands_and_totals() {
    // demand form traps on null receiver / absent field / out of bounds
    assert_eq!(trap_class("null.x"), TrapClass::NullReceiver);
    assert_eq!(trap_class("{ a: 1 }.b"), TrapClass::AbsentField);
    assert_eq!(trap_class("[1, 2][5]"), TrapClass::IndexBounds);
    // total form converts to null in one step
    assert!(eval("null?.x").is_null());
    assert!(eval("{ a: 1 }?.b").is_null());
    assert!(eval("[1, 2]?.[5]").is_null());
}

#[test]
fn operation_safety_trap_on_kind_mismatch() {
    assert_eq!(trap_class("1 + \"x\""), TrapClass::OperationSafety);
}

#[test]
fn spread_kind_trap() {
    assert_eq!(trap_class("[...5]"), TrapClass::SpreadKind);
    assert_eq!(trap_class("{ ...5 }"), TrapClass::SpreadKind);
}

#[test]
fn refuted_binding_trap() {
    // A destructuring binding whose pattern doesn't match its value (E9).
    assert_eq!(trap_class("[a, b] = [1]\na"), TrapClass::RefutedBinding);
}

#[test]
fn computed_key_trap() {
    // A computed record key that isn't a String (E5).
    assert_eq!(trap_class("{ [5]: 1 }"), TrapClass::ComputedKey);
}

// ── Strings (graphemes) and templates ────────────────────────────────────────

#[test]
fn grapheme_indexing_and_length_semantics() {
    // A family emoji is one grapheme; indexing yields a length-1 String.
    let s = "\"a\u{1F600}b\"";
    assert_eq!(eval(&format!("{s}[1]")).as_string_lossy().unwrap(), "\u{1F600}");
    // slice by graphemes
    assert_eq!(eval(&format!("{s}[0...2]")).as_string_lossy().unwrap(), "a\u{1F600}");
}

#[test]
fn template_stringifies_by_b2_rules() {
    // Number per B2 printing; String verbatim; prelude names by name.
    assert_eq!(eval("`x = ${1 / 2}`").as_string_lossy().unwrap(), "x = 0.5");
    assert_eq!(eval("`v = ${true}`").as_string_lossy().unwrap(), "v = true");
    assert_eq!(eval("`n = ${1 / 3}`").as_string_lossy().unwrap(), "n = 1/3");
}

// ── PR-01…05 — structure interpolation is total [user, 2026-07-18] ───────────

/// Evaluate a program to a String value.
fn eval_str(src: &str) -> String {
    let v = eval(src);
    let units = v.as_str_units().expect("a string");
    String::from_utf16_lossy(units)
}

/// Evaluate in a **caller-supplied** interner, so values from separate programs are
/// comparable by pointer (interning is per-interner).
fn eval_in(interner: &mut Interner, src: &str) -> ValueRef {
    use crate::desugar::Desugarer;
    use crate::lex::lex;
    use crate::parse::parse_program;

    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = Desugarer::new(interner).program(&sprogram).expect("desugar ok");
    let mut oracle = Oracle::new(interner);
    oracle.run_module(&module).expect("evaluated without trapping")
}

#[test]
fn pr01_tuple_renders_as_literal_with_b2_numbers() {
    assert_eq!(eval_str("`${[1, 1/3]}`"), "[1, 1/3]");
}

#[test]
fn pr02_record_renders_in_canonical_sorted_key_order() {
    assert_eq!(eval_str("`${{b: 2, a: 1}}`"), "{a: 1, b: 2}");
}

#[test]
fn pr03_inner_strings_are_quoted_and_escaped() {
    assert_eq!(eval_str(r#"`${["x"]}`"#), r#"["x"]"#);
    // A top-level string interpolates raw; only strings *inside* structures quote.
    assert_eq!(eval_str(r#"`${"x"}`"#), "x");
    // Escaping keeps the literal fragment round-trippable.
    assert_eq!(eval_str(r#"`${["a\"b"]}`"#), r#"["a\"b"]"#);
}

#[test]
fn pr04_functions_and_indeterminates_render_non_parseably() {
    assert_eq!(eval_str("f = x => x\n`${f}`"), "<Function>");
    // The *form* only — never the operands, so these are indistinguishable
    // (interning forbids remembering them).
    assert_eq!(eval_str("`${1/0}`"), "<Indeterminate _/0>");
    assert_eq!(eval_str("`${2/0}`"), "<Indeterminate _/0>");
    assert_eq!(eval_str("`${0/0}`"), "<Indeterminate 0/0>");
}

#[test]
fn pr05_parse_print_is_identity_on_the_literal_fragment() {
    // The harness law: rendering a literal-formed value and re-evaluating that
    // rendering yields the same value. Everything runs in ONE interner, so
    // "same value" is the pointer test (interning is per-interner).
    for src in [
        "[1, 2, 3]",
        "[1, 1/3, -2]",
        "{a: 1, b: 2}",
        "{b: 2, a: 1}",
        r#"["x", "a\"b"]"#,
        r#"[[1, 2], {k: "v"}]"#,
        "{outer: {inner: [true, false, null]}}",
        "[]",
    ] {
        let mut i = Interner::new();
        let original = eval_in(&mut i, src);
        let rendered = eval_in(&mut i, &format!("`${{{src}}}`"));
        let printed = String::from_utf16_lossy(rendered.as_str_units().expect("a string"));
        let reparsed = eval_in(&mut i, &printed);
        assert!(
            original.ptr_eq(&reparsed),
            "parse ∘ print ≠ identity for {src}: printed {printed:?}",
        );
    }
}

// ── Interning through evaluation ─────────────────────────────────────────────

#[test]
fn equal_values_are_pointer_equal_after_eval() {
    // Structural equality flips to true (B1): `[1,2] == [1,2]`.
    assert!(is_true(&eval("[1, 2] == [1, 2]")));
    assert!(is_true(&eval("{ a: 1 } == { a: 1 }")));
    // ...and differ when they should
    assert_eq!(eval("[1, 2] == [2, 1]").as_boolean(), Some(false));
}

#[test]
fn indeterminate_value_debug_shape() {
    // Sanity on the value kind itself.
    let v = eval("1 / 0");
    assert!(matches!(v.data(), ValueData::Indeterminate(_)));
}

// ── Mutator staging (B5/B7) ──────────────────────────────────────────────────

#[test]
fn state_mutation_via_mutator() {
    let src = "
        @state count = 0
        @mutate inc = () => { count := count + 1 }
        inc()
        count
    ";
    assert_eq!(num(&eval(src)), &Rational::from(1));
}

#[test]
fn read_your_writes_within_a_mutator() {
    // A later read in the same transaction sees the staged value, not σ.
    let src = "
        @state x = 0
        @mutate f = () => { x := 5\n x := x + 1 }
        f()
        x
    ";
    assert_eq!(num(&eval(src)), &Rational::from(6));
}

#[test]
fn nested_mutator_join_publishes_once() {
    // inner() joins outer's transaction; outer's later read sees inner's write;
    // publication happens once, at the outermost completion.
    let src = "
        @state x = 0
        @mutate inner = () => { x := 10 }
        @mutate outer = () => { inner()\n x := x + 1 }
        outer()
        x
    ";
    assert_eq!(num(&eval(src)), &Rational::from(11));
}

#[test]
fn equality_guard_skips_no_op_writes() {
    // Writing an equal value commits nothing (the interning-exact guard, B7/G1).
    let noop = "
        @state x = 5
        @mutate noop = () => { x := 5 }
        noop()
        x
    ";
    let (v, commits) = run_program_commits(noop).unwrap();
    assert_eq!(num(&v), &Rational::from(5));
    assert_eq!(commits, 0, "an equal write must not commit");

    // A changing write does commit exactly once.
    let change = "
        @state x = 5
        @mutate setX = () => { x := 6 }
        setX()
        x
    ";
    let (_, commits) = run_program_commits(change).unwrap();
    assert_eq!(commits, 1);
}

#[test]
fn effect_can_call_mutator() {
    let src = "
        @state x = 0
        @mutate setX = (v) => { x := v }
        @effect run = () => { setX(42) }
        run()
        x
    ";
    assert_eq!(num(&eval(src)), &Rational::from(42));
}

#[test]
fn world_admission_matrix() {
    // Pure cannot call an effect (containment asymmetry).
    let effect_from_pure = "
        @effect boom = () => { }
        f = () => boom()
        f()
    ";
    assert_eq!(trap_class(effect_from_pure), TrapClass::WorldAdmission);

    // Pure cannot call a mutator either.
    let mutator_from_pure = "
        @state x = 0
        @mutate m = () => { x := 1 }
        g = () => m()
        g()
    ";
    assert_eq!(trap_class(mutator_from_pure), TrapClass::WorldAdmission);

    // A write at the (effect-world) top level is not in a mutator ⇒ traps.
    let write_at_top = "
        @state x = 0
        x := 1
    ";
    assert_eq!(trap_class(write_at_top), TrapClass::WorldAdmission);
}

// ── Host effects, Failure, then/catch (B6 / §4) ──────────────────────────────

#[test]
fn host_effect_println_records_output() {
    let src = "
        @effect main = () => { println(\"hello\") }
        main()
    ";
    let (_v, io) = run_with_io(src).unwrap();
    assert_eq!(io.output, vec!["hello".to_string()]);
}

#[test]
fn host_effect_at_top_level() {
    // The entry-file top level is effect world; a host effect is a normal call.
    let (_v, io) = run_with_io("println(`x = ${1 / 2}`)").unwrap();
    assert_eq!(io.output, vec!["x = 0.5".to_string()]);
}

#[test]
fn host_effect_exit_records_code() {
    let (_v, io) = run_with_io("exit(2)").unwrap();
    assert_eq!(io.exit_code, Some(2));
}

#[test]
fn host_effect_not_admitted_in_pure() {
    // A pure function cannot call a host effect (containment asymmetry).
    let src = "
        f = () => { println(\"x\") }
        f()
    ";
    let trap = run_with_io(src).unwrap_err();
    assert_eq!(trap.class, TrapClass::WorldAdmission);
}

#[test]
fn failure_flows_as_plain_data() {
    // A failed host effect returns a Failure record; nothing unwinds — it is an
    // ordinary value with `path` and `reason` fields (B6).
    let (v, _io) = run_with_io("readFile(\"missing.txt\")").unwrap();
    let entries = v.as_record().expect("Failure is a record");
    let key = |k: &str| -> Vec<u16> { k.encode_utf16().collect() };
    let reason = entries.iter().find(|e| e.key == key("reason")).unwrap();
    assert_eq!(reason.value.as_string_lossy().unwrap(), "not found");
}

#[test]
fn then_catch_are_next_library_code() {
    // then/catch are ordinary NEXT functions over Match — not interpreter
    // builtins. A success flows through `then` and skips `catch`; a Failure skips
    // `then` and is recovered by `catch`.
    let src = "
        then  = (f) => (r) => r :: {
            Failure => r
            _ => f(r)
        }
        catch = (h) => (r) => r :: {
            Failure => h(r)
            _ => r
        }
        success = 5 |> then((x) => x + 1) |> catch((e) => 0)
        recovered = readFile(\"x\") |> then((c) => 1) |> catch((e) => 99)
        [success, recovered]
    ";
    let (v, _io) = run_with_io(src).unwrap();
    let t = v.as_tuple().unwrap();
    assert_eq!(t[0].as_number().unwrap(), &Rational::from(6), "success flows through then");
    assert_eq!(t[1].as_number().unwrap(), &Rational::from(99), "failure recovered by catch");
}

// ── Canonical function identity (§5, de-Bruijn half) ─────────────────────────

#[test]
fn alpha_equivalent_functions_are_equal() {
    // Same shape, different bound-variable names ⇒ equal (α-equivalence).
    assert!(is_true(&eval("((x) => x) == ((y) => y)")));
    assert!(is_true(&eval("((a, b) => a + b) == ((p, q) => p + q)")));
    // Nested lambdas too.
    assert!(is_true(&eval("((x) => (y) => x + y) == ((a) => (b) => a + b)")));
}

#[test]
fn functions_with_equal_captures_are_equal() {
    // Free variables are captured by value: same captured value ⇒ equal.
    assert!(is_true(&eval("k = 5\n((x) => x + k) == ((y) => y + k)")));
}

#[test]
fn functions_differing_in_body_or_capture_differ() {
    assert_eq!(eval("((x) => x + 1) == ((x) => x + 2)").as_boolean(), Some(false));
    // Different captured values ⇒ different functions.
    assert_eq!(eval("a = 1\nb = 2\n((x) => x + a) == ((y) => y + b)").as_boolean(), Some(false));
}

#[test]
fn function_identity_propagates_through_structures() {
    // A tuple/record holding α-equivalent functions is equal.
    assert!(is_true(&eval("[(x) => x] == [(y) => y]")));
}

#[test]
fn same_function_value_is_equal_to_itself() {
    // Reading one binding twice is the same value (incl. recursive/opaque ones).
    assert!(is_true(&eval("f = (n) => n == 0 ? 0 : f(n - 1)\nf == f")));
}

// ── μ-canonicalization: recursive value identity (algorithm B) ───────────────

#[test]
fn self_referential_values_intern_equal() {
    // FE-04 / the §7 seed: `y = [() => y]` and `z = [() => z]` are equal — their
    // rational trees coincide (bisimulation with the coinductive step).
    assert!(is_true(&eval("y = [() => y]\nz = [() => z]\ny == z")));
}

#[test]
fn mu17_mixed_aggregate_flagships() {
    // Open aggregates as group members: the cycle threads code, never data (B3).
    // The record variant `r = { f: () => r }` interns like the tuple flagship.
    assert!(is_true(&eval("r = { f: () => r }\ns = { f: () => s }\nr == s")));
    // and a record differing in a non-cyclic field is distinct
    assert_eq!(
        eval("r = { f: () => r, tag: 1 }\ns = { f: () => s, tag: 2 }\nr == s").as_boolean(),
        Some(false),
    );
}

#[test]
fn symmetric_group_collapses_to_self_loop() {
    // Law 4 at the value level: the two-slot symmetric group has the same
    // unfolding as the single self-loop, so `a == b == y`.
    let src = "
        a = [() => b]
        b = [() => a]
        y = [() => y]
        [a == y, a == b, b == y]
    ";
    let t = eval(src);
    let parts = t.as_tuple().unwrap();
    assert!(parts.iter().all(|p| p.as_boolean() == Some(true)), "a == b == y");
}

#[test]
fn mutual_recursion_equal_when_structurally_identical() {
    // Two independent isEven/isOdd groups with identical bodies are equal
    // (group bisimulation across captures).
    let src = "
        isEvenA = (n) => n == 0 ? true : isOddA(n - 1)
        isOddA  = (n) => n == 0 ? false : isEvenA(n - 1)
        isEvenB = (n) => n == 0 ? true : isOddB(n - 1)
        isOddB  = (n) => n == 0 ? false : isEvenB(n - 1)
        isEvenA == isEvenB
    ";
    assert!(is_true(&eval(src)));
}

#[test]
fn mu08_iseven_isodd_distinct_bodies_are_unequal() {
    // MU-08: distinct bodies (true vs false), two slots, no collapse.
    let src = "
        isEven = (n) => n == 0 ? true : isOdd(n - 1)
        isOdd  = (n) => n == 0 ? false : isEven(n - 1)
        isEven == isOdd
    ";
    assert_eq!(eval(src).as_boolean(), Some(false));
}

#[test]
fn mu04_location_captures_are_nominal() {
    // MU-04: same body over distinct @state locations ⇒ distinct; over the same
    // location ⇒ equal (the fork-13 split rule; locations never merge).
    let src = "
        @state p = 0
        @state q = 0
        fp  = () => p
        fq  = () => q
        fp2 = () => p
        [fp == fq, fp == fp2]
    ";
    let t = eval(src);
    let parts = t.as_tuple().unwrap();
    assert_eq!(parts[0].as_boolean(), Some(false), "distinct locations distinct");
    assert_eq!(parts[1].as_boolean(), Some(true), "same location equal");
}

#[test]
fn recursive_self_function_equal_by_shape() {
    // Two independent self-recursive functions with the same body are equal.
    let src = "
        f = (n) => n == 0 ? 0 : f(n - 1)
        g = (n) => n == 0 ? 0 : g(n - 1)
        f == g
    ";
    assert!(is_true(&eval(src)));
}

// ── The narrow arithmetic ==-slice (μ spec v0.5 §8; H-05 kept, MU-10 excluded) ─

#[test]
fn h05_the_permitted_arithmetic_rewrites() {
    // The three permitted rewrites: reordering, literal folding, like-term
    // combining (every variable survives with its demand).
    assert!(is_true(&eval("((x) => x + x) == ((x) => 2 * x)")), "x+x == 2x (H-05)");
    assert!(is_true(&eval("((x) => x + 1 + 1) == ((x) => x + 2)")), "literal fold");
    assert!(is_true(&eval("((x) => x * 2) == ((x) => 2 * x)")), "mul commutativity");
    assert!(is_true(&eval("((x, y) => x + y) == ((a, b) => b + a)")), "add commutativity");
    assert!(is_true(&eval("((x) => x + x + x) == ((x) => 3 * x)")), "like-term sum");
}

#[test]
fn mu10_excluded_rewrites_do_not_fire() {
    // These change divergence and/or operation-safety demands, so the shape-level
    // rewrites are permanently excluded and must NOT fire (μ spec §8 / MU-10).
    assert_eq!(eval("((x) => x - x) == ((x) => 0)").as_boolean(), Some(false), "cancellation");
    assert_eq!(eval("((x) => x + 0) == ((x) => x)").as_boolean(), Some(false), "identity-elim (+0)");
    assert_eq!(eval("((x) => x * 1) == ((x) => x)").as_boolean(), Some(false), "identity-elim (*1)");
    assert_eq!(eval("((x) => 0 * x) == ((x) => 0)").as_boolean(), Some(false), "annihilation");
    // No distribution (not in the enumerated slice).
    assert_eq!(
        eval("((x) => (x + 1) * 2) == ((x) => 2 * x + 2)").as_boolean(),
        Some(false),
        "distribution not applied",
    );
    // x/x is not 1 (Indeterminate at 0); x % x not simplified.
    assert_eq!(eval("((x) => x / x) == ((x) => 1)").as_boolean(), Some(false), "x/x != 1");
    assert_eq!(eval("((x) => x % x) == ((x) => 0)").as_boolean(), Some(false), "x%x != 0");
    // and genuinely different functions stay apart
    assert_eq!(eval("((x) => x) == ((x) => x + 1)").as_boolean(), Some(false));
}

#[test]
fn excluded_forms_still_obey_commutativity() {
    // Reordering is *always* allowed, even for forms whose simplification is
    // excluded: `x*0` and `0*x` are the same function, as are `x-x` and `-x+x`.
    assert!(is_true(&eval("((x) => x * 0) == ((x) => 0 * x)")));
    assert!(is_true(&eval("((x) => x * 1) == ((x) => 1 * x)")));
    assert!(is_true(&eval("((x) => -x + x) == ((x) => x - x)")));
}

#[test]
fn narrow_slice_equal_functions_compute_the_same() {
    // Soundness sanity: the functions the slice equates are extensionally equal.
    let src = "
        f = (x) => x + x
        g = (x) => 2 * x
        [f == g, f(5) == g(5), f(5)]
    ";
    let t = eval(src);
    let parts = t.as_tuple().unwrap();
    assert_eq!(parts[0].as_boolean(), Some(true));
    assert_eq!(parts[1].as_boolean(), Some(true));
    assert_eq!(parts[2].as_number().unwrap(), &Rational::from(10));
}
