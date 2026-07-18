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
    // match; at runtime it matches no arm ⇒ completes-without-value ⇒ the demand
    // surfaces at the expecting seat (the analyzer rejects it up front).
    assert_eq!(trap_class("5 ? 1 : 2"), TrapClass::ExpectingSeat);
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

#[test]
fn template_structure_interpolation_traps() {
    // Structure printing is deliberately unruled — it traps (E11).
    assert_eq!(trap_class("`v = ${[1, 2]}`"), TrapClass::UnprintableInterpolation);
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

// ── Deferred to §5: canonical function identity (see DECISIONS.md) ────────────

#[test]
#[ignore = "needs §5 canonical function identity (approximate identity is conservative until then)"]
fn structural_function_identity() {
    // Same-meaning, different-shape functions should compare equal under the
    // canonical-body key §5 provides. Today's pointer identity says false.
    assert!(is_true(&eval("((x) => x) == ((y) => y)")));
}

#[test]
#[ignore = "needs §5 canonical function identity + μ-markers (group-identity fork §7)"]
fn group_identity_seed() {
    // The §7 provisional-default pair: y and z should intern equal.
    assert!(is_true(&eval("y = [() => y]\nz = [() => z]\ny == z")));
}
