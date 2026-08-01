//! Denotational membership brute-tested against the oracle's values (Part I:
//! per-pair contract rules checked against the truth source).

use super::*;
use crate::interner::Interner;
use crate::value::IndeterminateFormTag;

fn n(i: &mut Interner, v: i64) -> ValueRef {
    i.integer(v)
}
fn rat(num: i64, den: i64) -> Rational {
    Rational::new(BigInt::from(num), BigInt::from(den))
}
fn r(x: i64) -> Rational {
    Rational::from(x)
}
fn div_zero(i: &mut Interner, operand: i64) -> ValueRef {
    i.div_zero(r(operand))
}
fn mod_zero(i: &mut Interner, operand: i64) -> ValueRef {
    i.mod_zero(r(operand))
}
fn exact_div_zero(i: &mut Interner, operand: i64) -> Contract {
    Contract::Equals(div_zero(i, operand))
}
fn exact_mod_zero(i: &mut Interner, operand: i64) -> Contract {
    Contract::Equals(mod_zero(i, operand))
}

/// Evaluate in the operation rule's interner so an exact function contract and
/// the oracle result inhabit the same value namespace.
fn eval_in(i: &mut Interner, src: &str) -> ValueRef {
    use crate::desugar::Desugarer;
    use crate::lex::lex;
    use crate::oracle::Oracle;
    use crate::parse::parse_program;

    let tokens = lex(src).expect("lex ok");
    let surface = parse_program(tokens).expect("parse ok");
    let module = Desugarer::new(i).program(&surface).expect("desugar ok");
    Oracle::new(i).run_module(&module).expect("evaluated without trapping")
}

#[test]
fn top_and_bottom() {
    let mut i = Interner::new();
    let v = n(&mut i, 5);
    assert!(Contract::Top.contains(&v));
    assert!(!Contract::Bottom.contains(&v));
}

#[test]
fn kind_membership() {
    let mut i = Interner::new();
    assert!(Contract::Kind(Kind::Number).contains(&i.integer(3)));
    assert!(Contract::Kind(Kind::String).contains(&i.string("hi")));
    assert!(Contract::Kind(Kind::Boolean).contains(&i.boolean(true)));
    assert!(Contract::Kind(Kind::Null).contains(&i.null()));
    let t = i.tuple(vec![]);
    assert!(Contract::Kind(Kind::Tuple).contains(&t));
    let rec = i.record_str(vec![]);
    assert!(Contract::Kind(Kind::Record).contains(&rec));
    // cross-kind is false
    assert!(!Contract::Kind(Kind::Number).contains(&i.string("3")));
    // Indeterminate is not any Kind.
    let ind = div_zero(&mut i, 1);
    assert!(!Contract::Kind(Kind::Number).contains(&ind));
}

#[test]
fn equals_uses_value_equality() {
    let mut i = Interner::new();
    let five = i.integer(5);
    assert!(Contract::Equals(five.clone()).contains(&i.integer(5)));
    assert!(!Contract::Equals(five.clone()).contains(&i.integer(6)));
    // structural equality (not pointer): a fresh equal tuple satisfies Equals
    let (one, two) = (i.integer(1), i.integer(2));
    let a = i.tuple(vec![one.clone(), two.clone()]);
    let b = i.tuple(vec![one, two]);
    assert!(Contract::Equals(a).contains(&b));
    // NotEquals ≡ Difference(Top, Equals(v))
    let ne = Contract::difference(Contract::Top, Contract::Equals(five), &mut i);
    assert!(ne.contains(&i.integer(6)));
    assert!(!ne.contains(&i.integer(5)));
}

#[test]
fn numeric_bounds_and_range() {
    let mut i = Interner::new();
    let range = Contract::Range(r(0), r(100));
    assert!(range.contains(&i.integer(0)));
    assert!(range.contains(&i.integer(50)));
    assert!(range.contains(&i.integer(100)));
    assert!(!range.contains(&i.integer(101)));
    assert!(!range.contains(&i.integer(-1)));
    assert!(!range.contains(&i.string("50"))); // non-numbers excluded

    assert!(Contract::Greater(r(5)).contains(&i.integer(6)));
    assert!(!Contract::Greater(r(5)).contains(&i.integer(5)));
    assert!(Contract::GreaterEq(r(5)).contains(&i.integer(5)));
    assert!(Contract::Less(r(5)).contains(&i.integer(4)));
    assert!(Contract::LessEq(r(5)).contains(&i.integer(5)));

    // a landing zone (T, T+d] = Intersection(GreaterThan(T), LessOrEqual(T+d))
    let lz = Contract::intersection(Contract::Greater(r(10)), Contract::LessEq(r(20)), &mut i);
    assert!(!lz.contains(&i.integer(10)));
    assert!(lz.contains(&i.integer(11)));
    assert!(lz.contains(&i.integer(20)));
    assert!(!lz.contains(&i.integer(21)));

    // fractional bound
    assert!(Contract::Range(rat(1, 2), rat(3, 2)).contains(&i.number(rat(1, 1))));
    assert!(!Contract::Range(rat(1, 2), rat(3, 2)).contains(&i.number(rat(1, 4))));
}

#[test]
fn modular_contract() {
    let mut i = Interner::new();
    // even numbers: x ≡ 0 (mod 2)
    let even = Contract::Mod { n: BigInt::from(2), r: BigInt::from(0) };
    assert!(even.contains(&i.integer(0)));
    assert!(even.contains(&i.integer(4)));
    assert!(even.contains(&i.integer(-6)));
    assert!(!even.contains(&i.integer(3)));
    // non-integers are excluded
    assert!(!even.contains(&i.number(rat(1, 2))));
    // x ≡ 1 (mod 3)
    let m = Contract::Mod { n: BigInt::from(3), r: BigInt::from(1) };
    assert!(m.contains(&i.integer(1)));
    assert!(m.contains(&i.integer(4)));
    assert!(m.contains(&i.integer(-2))); // -2 ≡ 1 (mod 3)
    assert!(!m.contains(&i.integer(2)));
}

#[test]
fn geometric_contract() {
    let mut i = Interner::new();
    // powers of two starting at 1: 1, 2, 4, 8, ...
    let g = Contract::Geo { b: r(1), r: r(2) };
    assert!(g.contains(&i.integer(1)));
    assert!(g.contains(&i.integer(2)));
    assert!(g.contains(&i.integer(8)));
    assert!(!g.contains(&i.integer(3)));
    assert!(!g.contains(&i.integer(6)));
    assert!(!g.contains(&i.number(rat(1, 2)))); // below b
    // b = 3, r = 2: 3, 6, 12, 24
    let g2 = Contract::Geo { b: r(3), r: r(2) };
    assert!(g2.contains(&i.integer(3)));
    assert!(g2.contains(&i.integer(12)));
    assert!(!g2.contains(&i.integer(9)));
}

#[test]
fn set_operations() {
    let mut i = Interner::new();
    let small = Contract::Range(r(0), r(10));
    let big = Contract::Range(r(100), r(200));
    let u = Contract::union(small.clone(), big.clone(), &mut i);
    assert!(u.contains(&i.integer(5)));
    assert!(u.contains(&i.integer(150)));
    assert!(!u.contains(&i.integer(50)));

    // Difference(Range(0,10), Equals(5)) — a hole
    let hole = Contract::difference(small, Contract::Equals(i.integer(5)), &mut i);
    assert!(hole.contains(&i.integer(4)));
    assert!(!hole.contains(&i.integer(5)));
    assert!(hole.contains(&i.integer(6)));
}

#[test]
fn record_and_tuple_and_field() {
    let mut i = Interner::new();
    let age = i.integer(30);
    let name = i.string("ann");
    let rec = i.record_str(vec![("age", age), ("name", name)]);

    // HasField is the OPEN partial form — it ignores extra fields.
    assert!(Contract::HasField("age".into()).contains(&rec));
    assert!(!Contract::HasField("email".into()).contains(&rec));

    // Record is EXACT — the key set must match exactly.
    let exact = Contract::record(
        vec![
            ("age".into(), Contract::Range(r(0), r(120))),
            ("name".into(), Contract::Kind(Kind::String)),
        ],
        &mut i,
    );
    assert!(exact.contains(&rec), "exact match of {{age, name}}");
    // an extra field is rejected (this is the exact-vs-open distinction)
    let (a1, n1, e1) = (i.integer(30), i.string("ann"), i.string("x"));
    let extra = i.record_str(vec![("age", a1), ("name", n1), ("email", e1)]);
    assert!(!exact.contains(&extra), "an un-listed field is rejected");
    // a missing field is rejected
    let a2 = i.integer(30);
    let missing = i.record_str(vec![("age", a2)]);
    assert!(!exact.contains(&missing), "a missing field is rejected");
    // a field failing its contract is rejected
    let (a3, n3) = (i.integer(200), i.string("ann"));
    let too_old = i.record_str(vec![("age", a3), ("name", n3)]);
    assert!(!exact.contains(&too_old));
    // a non-record fails
    let thirty = i.integer(30);
    assert!(!exact.contains(&thirty));

    // Tuple contract, exact length + positional contracts
    let (one, sx) = (i.integer(1), i.string("x"));
    let t = i.tuple(vec![one.clone(), sx]);
    let tc = Contract::tuple(
        vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::String)],
        &mut i,
    );
    assert!(tc.contains(&t));
    let wrong = i.tuple(vec![one]);
    assert!(!tc.contains(&wrong)); // length mismatch
}

#[test]
fn indeterminate_contracts_preserve_specific_form_and_operand_identity() {
    let mut i = Interner::new();
    let one_over_zero = div_zero(&mut i, 1);
    let two_over_zero = div_zero(&mut i, 2);
    let one_mod_zero = mod_zero(&mut i, 1);
    let div_form = Contract::Indeterminate(IndeterminateFormTag::DivZero);
    let mod_form = Contract::Indeterminate(IndeterminateFormTag::ModZero);

    assert!(div_form.contains(&one_over_zero));
    assert!(!mod_form.contains(&one_over_zero));
    assert!(mod_form.contains(&one_mod_zero));
    assert!(exact_div_zero(&mut i, 1).contains(&one_over_zero));
    assert!(!exact_div_zero(&mut i, 2).contains(&one_over_zero));
    assert!(!exact_mod_zero(&mut i, 1).contains(&one_over_zero));
    assert!(!Contract::indeterminate(&mut i).contains(&i.integer(5)));

    let numeric = Contract::numeric(&mut i);
    assert!(numeric.contains(&i.integer(5)));
    assert!(numeric.contains(&one_over_zero));
    assert!(numeric.contains(&two_over_zero));
    assert!(numeric.contains(&one_mod_zero));
    assert!(!numeric.contains(&i.string("5")));
}

#[test]
fn function_kind_and_equality() {
    // A function value is Kind(Function); Equals uses bisimulation identity.
    let v = crate::oracle::run_program_value("(x) => x + 1").unwrap();
    assert!(Contract::Kind(Kind::Function).contains(&v));
    assert!(!Contract::Kind(Kind::Number).contains(&v));
}

// ── Three-valued subcontract (C.2) ───────────────────────────────────────────

use super::{Verdict, subcontract};

fn proven(a: &Contract, b: &Contract, i: &mut Interner) {
    assert!(matches!(subcontract(a, b, i), Verdict::Proven), "expected {a:?} ⊑ {b:?} proven");
}
fn refuted(a: &Contract, b: &Contract, i: &mut Interner) {
    match subcontract(a, b, i) {
        Verdict::Refuted(w) => {
            assert!(a.contains(&w) && !b.contains(&w), "witness {w:?} must be in A\\B");
        }
        v => panic!("expected {a:?} ⊑ {b:?} refuted, got {v:?}"),
    }
}

#[test]
fn subcontract_intervals() {
    let mut i = Interner::new();
    proven(
        &Contract::Range(r(0), r(10)),
        &Contract::Range(r(0), r(100)),
        &mut i,
    );
    refuted(
        &Contract::Range(r(0), r(100)),
        &Contract::Range(r(0), r(10)),
        &mut i,
    );
    proven(
        &Contract::Range(r(0), r(10)),
        &Contract::Kind(Kind::Number),
        &mut i,
    );
    proven(&Contract::Greater(r(5)), &Contract::GreaterEq(r(5)), &mut i);
    refuted(&Contract::GreaterEq(r(5)), &Contract::Greater(r(5)), &mut i);
    // landing zone (10, 20] ⊑ [10, 20] (dense rationals: not ⊑ [11, 20]).
    let lz = Contract::intersection(Contract::Greater(r(10)), Contract::LessEq(r(20)), &mut i);
    proven(&lz, &Contract::Range(r(10), r(20)), &mut i);
    refuted(&lz, &Contract::Range(r(11), r(20)), &mut i); // 10.5 witnesses the gap
}

#[test]
fn subcontract_equals_and_kind() {
    let mut i = Interner::new();
    let five = i.integer(5);
    proven(
        &Contract::Equals(five.clone()),
        &Contract::Range(r(0), r(10)),
        &mut i,
    );
    let fifty = i.integer(50);
    refuted(
        &Contract::Equals(fifty),
        &Contract::Range(r(0), r(10)),
        &mut i,
    );
    proven(&Contract::Kind(Kind::Number), &Contract::Top, &mut i);
    refuted(
        &Contract::Kind(Kind::Number),
        &Contract::Kind(Kind::String),
        &mut i,
    );
    proven(&Contract::Bottom, &Contract::Kind(Kind::String), &mut i);
}

#[test]
fn subcontract_union_and_mod() {
    let mut i = Interner::new();
    let split = Contract::union(
        Contract::Range(r(0), r(5)),
        Contract::Range(r(6), r(10)),
        &mut i,
    );
    proven(&split, &Contract::Range(r(0), r(10)), &mut i);
    // multiples of 4 ⊑ evens; evens ⋢ multiples of 4
    let mult4 = Contract::Mod {
        n: BigInt::from(4),
        r: BigInt::from(0),
    };
    let even = Contract::Mod {
        n: BigInt::from(2),
        r: BigInt::from(0),
    };
    proven(&mult4, &even, &mut i);
    refuted(&even, &mult4, &mut i);
}

#[test]
fn subcontract_soundness_sweep() {
    // Brute-force: over a pool of values and a set of contracts, every verdict
    // must be sound against denotational membership (the truth source).
    let mut i = Interner::new();
    let five = i.integer(5);

    let contracts = vec![
        Contract::Top,
        Contract::Bottom,
        Contract::Kind(Kind::Number),
        Contract::Kind(Kind::String),
        Contract::Range(r(0), r(10)),
        Contract::Range(r(0), r(100)),
        Contract::Range(r(5), r(15)),
        Contract::Greater(r(0)),
        Contract::LessEq(r(10)),
        Contract::Equals(five),
        Contract::Mod {
            n: BigInt::from(2),
            r: BigInt::from(0),
        },
        Contract::Mod {
            n: BigInt::from(4),
            r: BigInt::from(0),
        },
        Contract::union(
            Contract::Range(r(0), r(5)),
            Contract::Range(r(6), r(10)),
            &mut i,
        ),
        Contract::intersection(
            Contract::Range(r(0), r(20)),
            Contract::Greater(r(5)),
            &mut i,
        ),
        Contract::difference(
            Contract::Range(r(0), r(10)),
            Contract::Equals(i.integer(5)),
            &mut i,
        ),
        Contract::HasField("age".into()),
        Contract::Kind(Kind::Tuple),
        Contract::Kind(Kind::Record),
        Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i),
    ];

    // A diverse value pool (numbers, non-numbers).
    let mut pool: Vec<ValueRef> = Vec::new();
    for n in [-5, 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 15, 20, 50, 100, 101] {
        pool.push(i.integer(n));
    }
    pool.push(i.number(rat(1, 2)));
    pool.push(i.string("x"));
    pool.push(i.boolean(true));
    pool.push(i.null());
    let age = i.integer(1);
    pool.push(i.record_str(vec![("age", age)]));
    let one = i.integer(1);
    pool.push(i.tuple(vec![one]));
    pool.push(i.tuple(vec![]));

    for a in &contracts {
        for b in &contracts {
            match subcontract(a, b, &mut i) {
                Verdict::Proven => {
                    for v in &pool {
                        assert!(
                            !(a.contains(v) && !b.contains(v)),
                            "UNSOUND Proven: {a:?} ⊑ {b:?} but {v:?} ∈ A∖B",
                        );
                    }
                }
                Verdict::Refuted(w) => {
                    assert!(
                        a.contains(&w) && !b.contains(&w),
                        "UNSOUND Refuted: {a:?} ⊑ {b:?} witness {w:?} not in A∖B",
                    );
                }
                Verdict::Unproven => {}
            }
        }
    }
}

#[test]
fn disjoint_soundness() {
    // Every provably-disjoint pair must share no value in a diverse pool.
    let mut i = Interner::new();
    let contracts = vec![
        Contract::Kind(Kind::Number),
        Contract::Kind(Kind::String),
        Contract::Kind(Kind::Null),
        Contract::Kind(Kind::Tuple),
        Contract::Kind(Kind::Record),
        Contract::Range(r(0), r(10)),
        Contract::HasField("a".into()),
        Contract::record(vec![("a".into(), Contract::Kind(Kind::Number))], &mut i),
        Contract::record(vec![("b".into(), Contract::Kind(Kind::Number))], &mut i),
        Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i),
        Contract::Equals(i.integer(5)),
    ];
    let mut pool: Vec<ValueRef> = vec![
        i.integer(5),
        i.number(rat(1, 2)),
        i.string("x"),
        i.boolean(true),
        i.null(),
    ];
    let a1 = i.integer(1);
    pool.push(i.tuple(vec![a1]));
    let av = i.integer(2);
    pool.push(i.record_str(vec![("a", av)]));
    let bv = i.integer(3);
    pool.push(i.record_str(vec![("b", bv)]));

    for a in &contracts {
        for b in &contracts {
            if crate::contract::disjoint(a, b) {
                for v in &pool {
                    assert!(
                        !(a.contains(v) && b.contains(v)),
                        "UNSOUND disjoint: {a:?} ⌢ {b:?} both contain {v:?}",
                    );
                }
            }
        }
    }
}

// ── Operation rules (C§7) ─────────────────────────────────────────────────────

use crate::ast::PrimOp;
use crate::oracle::eval_prim;

#[test]
fn operation_add_ranges() {
    let mut i = Interner::new();
    // [0,10] + [5,15] safely produces [5,25].
    let a = Contract::Range(r(0), r(10));
    let b = Contract::Range(r(5), r(15));
    let res = analyze_operation(PrimOp::Add, &[a, b], &mut i);
    assert!(matches!(res.safety, OpSafety::Proven));
    assert_eq!(res.output, Contract::Range(r(5), r(25)));
    // Concrete: 3 + 7 = 10 ∈ output.
    let out = eval_prim(PrimOp::Add, &[i.integer(3), i.integer(7)], &mut i).unwrap();
    assert!(res.output.contains(&out));
}

#[test]
fn operation_add_type_mismatch_refuted() {
    let mut i = Interner::new();
    // Number + String traps; the rule must exhibit a trapping witness tuple.
    let res = analyze_operation(
        PrimOp::Add,
        &[Contract::Kind(Kind::Number), Contract::Kind(Kind::String)],
        &mut i,
    );
    match res.safety {
        OpSafety::Refuted(w) => {
            assert!(eval_prim(PrimOp::Add, &w, &mut i).is_err(), "witness must trap");
        }
        other => panic!("expected Refuted, got {other:?}"),
    }
}

#[test]
fn operation_division_is_total() {
    let mut i = Interner::new();
    // Division by a range spanning zero is safe over Number operands, and its
    // image is Numeric because every canonical numerator may form `a/0`.
    let a = Contract::Kind(Kind::Number);
    let b = Contract::Range(r(0), r(10));
    let res = analyze_operation(PrimOp::Div, &[a, b], &mut i);
    assert!(matches!(res.safety, OpSafety::Proven), "division never traps");
    let one_over_zero = eval_prim(PrimOp::Div, &[i.integer(1), i.integer(0)], &mut i).unwrap();
    assert!(res.output.contains(&one_over_zero), "output must cover specific 1/0");
    assert!(res.output.contains(&div_zero(&mut i, 2)), "output must cover specific 2/0");
    assert!(!res.output.contains(&mod_zero(&mut i, 2)), "division must not produce ModZero");
    proven(&res.output, &Contract::numeric(&mut i), &mut i);
    // A nonzero divisor drops Indeterminate from the image.
    let safe = analyze_operation(
        PrimOp::Div,
        &[Contract::Kind(Kind::Number), Contract::Greater(r(0))],
        &mut i,
    );
    assert_eq!(safe.output, Contract::Kind(Kind::Number));
}

#[test]
fn operation_comparison_and_neg() {
    let mut i = Interner::new();
    let cmp = analyze_operation(
        PrimOp::Lt,
        &[Contract::Range(r(0), r(10)), Contract::Range(r(0), r(10))],
        &mut i,
    );
    assert!(matches!(cmp.safety, OpSafety::Proven));
    assert_eq!(cmp.output, Contract::Kind(Kind::Boolean));
    // Negation flips a range.
    let neg = analyze_operation(PrimOp::Neg, &[Contract::Range(r(2), r(5))], &mut i);
    assert!(matches!(neg.safety, OpSafety::Proven));
    assert_eq!(neg.output, Contract::Range(r(-5), r(-2)));
    // `<` on a non-number is refuted.
    let bad = analyze_operation(
        PrimOp::Lt,
        &[Contract::Kind(Kind::String), Contract::Kind(Kind::Number)],
        &mut i,
    );
    assert!(matches!(bad.safety, OpSafety::Refuted(_)));
}

#[test]
fn operation_equality_agrees_with_oracle_for_equal_function_singletons() {
    let mut i = Interner::new();
    let pair = eval_in(&mut i, "y = [() => y]\nz = [() => z]\n[y, z]");
    let values = pair.as_tuple().expect("function pair");
    let (left, right) = (values[0].clone(), values[1].clone());

    assert!(
        crate::oracle::values_equal(&left, &right),
        "the oracle recognizes the canonical recursive-function pointer"
    );
    assert!(
        left.ptr_eq(&right),
        "closed equal recursive values must already be one canonical singleton"
    );

    let eq = analyze_operation(
        PrimOp::Eq,
        &[Contract::Equals(left.clone()), Contract::Equals(right.clone())],
        &mut i,
    );
    let ne = analyze_operation(
        PrimOp::Ne,
        &[Contract::Equals(left), Contract::Equals(right)],
        &mut i,
    );
    assert_eq!(eq.output, Contract::Equals(i.boolean(true)));
    assert_eq!(ne.output, Contract::Equals(i.boolean(false)));
}

// ── The rulebook's precision claims (C§7 / C§17 per-pair tables) ─────────────
//
// The sweep below proves the table **sound**; these prove it **useful**. Returning
// `Kind(Number)` everywhere would pass the sweep and fail every row here.

fn out(op: PrimOp, ins: &[Contract], i: &mut Interner) -> Contract {
    analyze_operation(op, ins, i).output
}

fn nonneg_ints(i: &mut Interner) -> Contract {
    Contract::intersection(
        Contract::GreaterEq(r(0)),
        Contract::Mod {
            n: BigInt::from(1),
            r: BigInt::from(0),
        },
        i,
    )
}

#[test]
fn rulebook_additive_bounds_compose() {
    let mut i = Interner::new();
    // Half-lines compose — the gap that motivated F0 (the algebra has no infinity,
    // so half-lines *are* the unbounded form).
    assert_eq!(
        out(PrimOp::Add, &[Contract::GreaterEq(r(8)), Contract::GreaterEq(r(10))], &mut i),
        Contract::GreaterEq(r(18))
    );
    // Strictness rides along: inclusive only when both are.
    assert_eq!(
        out(PrimOp::Add, &[Contract::Greater(r(0)), Contract::GreaterEq(r(5))], &mut i),
        Contract::Greater(r(5))
    );
    // Subtraction pairs each bound with the subtrahend's *opposite* bound.
    assert_eq!(
        out(PrimOp::Sub, &[Contract::Range(r(0), r(10)), Contract::Greater(r(0))], &mut i),
        Contract::Less(r(10))
    );
    // Negation flips a half-line.
    assert_eq!(out(PrimOp::Neg, &[Contract::GreaterEq(r(3))], &mut i), Contract::LessEq(r(-3)));
}

#[test]
fn rulebook_congruence_survives_additive_ops() {
    let mut i = Interner::new();
    let one = Contract::Equals(i.integer(1));
    // The non-negative integers minus 1 are still **integers** ≥ −1 — integrality
    // survives `−` because an exact operand is a congruence with modulus 0.
    let got = out(PrimOp::Sub, &[nonneg_ints(&mut i), one.clone()], &mut i);
    let want = Contract::intersection(
        Contract::GreaterEq(r(-1)),
        Contract::Mod {
            n: BigInt::from(1),
            r: BigInt::from(0),
        },
        &mut i,
    );
    assert_eq!(got, want, "integrality must survive `- 1`");
    // even + 2 is even.
    let evens = Contract::Mod {
        n: BigInt::from(2),
        r: BigInt::from(0),
    };
    let two = Contract::Equals(i.integer(2));
    assert_eq!(out(PrimOp::Add, &[evens.clone(), two], &mut i), evens);
    // Scaling (C§7): even × 3 lands on multiples of 6.
    let three = Contract::Equals(i.integer(3));
    assert_eq!(
        out(PrimOp::Mul, &[evens, three], &mut i),
        Contract::Mod {
            n: BigInt::from(6),
            r: BigInt::from(0)
        }
    );
}

#[test]
fn rulebook_multiplicative_signs_and_form_preservation() {
    let mut i = Interner::new();
    // Corner products under extended arithmetic — no sign-class special-casing.
    assert_eq!(
        out(PrimOp::Mul, &[Contract::Range(r(-5), r(2)), Contract::Range(r(3), r(4))], &mut i),
        Contract::Range(r(-20), r(8))
    );
    // `0 · ∞ = 0` keeps a non-negative half-line non-negative rather than unbounded.
    assert_eq!(
        out(PrimOp::Mul, &[Contract::GreaterEq(r(0)), Contract::GreaterEq(r(0))], &mut i),
        Contract::GreaterEq(r(0))
    );
    // Table C — form preservation: scaling a geometric sequence stays geometric.
    let geo = Contract::Geo { b: r(2), r: r(3) };
    let four = Contract::Equals(i.integer(4));
    assert_eq!(
        out(PrimOp::Mul, &[geo, four], &mut i),
        Contract::Geo { b: r(8), r: r(3) }
    );
}

#[test]
fn rulebook_comparisons_decide_when_bounds_decide() {
    let mut i = Interner::new();
    let (t, f) = (Contract::Equals(i.boolean(true)), Contract::Equals(i.boolean(false)));
    // Disjoint ranges settle the comparison — this is what lets a guard resolve.
    assert_eq!(
        out(PrimOp::Lt, &[Contract::Range(r(0), r(5)), Contract::GreaterEq(r(10))], &mut i),
        t
    );
    assert_eq!(
        out(PrimOp::Ge, &[Contract::Range(r(0), r(5)), Contract::GreaterEq(r(10))], &mut i),
        f
    );
    // Touching at an included point: `≤` holds everywhere, `<` does not.
    assert_eq!(
        out(PrimOp::Le, &[Contract::LessEq(r(3)), Contract::GreaterEq(r(3))], &mut i),
        t
    );
    assert_eq!(
        out(PrimOp::Lt, &[Contract::LessEq(r(3)), Contract::GreaterEq(r(3))], &mut i),
        Contract::Kind(Kind::Boolean)
    );
    // Overlapping ranges stay honestly undecided.
    assert_eq!(
        out(PrimOp::Lt, &[Contract::Range(r(0), r(10)), Contract::Range(r(5), r(20))], &mut i),
        Contract::Kind(Kind::Boolean)
    );
}

#[test]
fn rulebook_division_is_total_and_remainder_is_bounded() {
    let mut i = Interner::new();
    // Total division: a possibly-zero divisor widens the Number image to Numeric.
    let res = analyze_operation(PrimOp::Div, &[Contract::Range(r(1), r(4)), Contract::Range(r(0), r(2))], &mut i);
    assert!(matches!(res.safety, OpSafety::Proven), "division never traps");
    let div0 = div_zero(&mut i, 1);
    assert!(res.output.contains(&div0), "the image must carry specific `1/0`");
    assert!(!res.output.contains(&mod_zero(&mut i, 1)), "division has the DivZero form only");
    let rem_zero = analyze_operation(
        PrimOp::Rem,
        &[Contract::Range(r(1), r(4)), Contract::Range(r(0), r(2))],
        &mut i,
    );
    assert!(rem_zero.output.contains(&mod_zero(&mut i, 1)), "the image must carry specific `1%0`");
    assert!(!rem_zero.output.contains(&div_zero(&mut i, 1)), "remainder has the ModZero form only");
    // `%` is bounded by the divisor's magnitude, with the sign following the dividend.
    let rem = out(PrimOp::Rem, &[Contract::GreaterEq(r(0)), Contract::Range(r(3), r(5))], &mut i);
    for v in [0, 1, 4] {
        let x = i.integer(v);
        assert!(rem.contains(&x), "{v} is a possible non-negative remainder: {rem:?}");
    }
    let neg = i.integer(-1);
    assert!(!rem.contains(&neg), "a non-negative dividend cannot give a negative remainder: {rem:?}");
}

#[test]
fn rulebook_requires_indeterminate_discharge_at_strict_number_seats() {
    let mut i = Interner::new();
    let num = Contract::Kind(Kind::Number);

    // The consuming algebra is open, so arithmetic and ordering are strict
    // Number seats. A represented witness of either form must refute safety.
    for indet in [exact_div_zero(&mut i, 1), exact_mod_zero(&mut i, 1)] {
        for op in [PrimOp::Add, PrimOp::Sub, PrimOp::Mul, PrimOp::Div, PrimOp::Rem, PrimOp::Pow] {
            let res = analyze_operation(op, &[indet.clone(), num.clone()], &mut i);
            assert!(matches!(res.safety, OpSafety::Refuted(_)), "{op:?} on Indeterminate must be Refuted");
        }
        let res = analyze_operation(PrimOp::Neg, std::slice::from_ref(&indet), &mut i);
        assert!(matches!(res.safety, OpSafety::Refuted(_)), "unary `-` on Indeterminate must be Refuted");

        for op in [PrimOp::Lt, PrimOp::Le, PrimOp::Gt, PrimOp::Ge] {
            let res = analyze_operation(op, &[indet.clone(), num.clone()], &mut i);
            assert!(matches!(res.safety, OpSafety::Refuted(_)), "{op:?} on Indeterminate must be Refuted");
        }

        // `==`/`!=` are total on every value, Indeterminate included.
        for op in [PrimOp::Eq, PrimOp::Ne] {
            let res = analyze_operation(op, &[indet.clone(), Contract::Top], &mut i);
            assert!(matches!(res.safety, OpSafety::Proven), "{op:?} is total");
        }
    }
}

#[test]
fn operation_soundness_sweep() {
    // Brute-force every operation over a grid of input contracts against the
    // oracle (`eval_prim`): the output must over-approximate the true image, a
    // `Proven` safety must never trap, and a `Refuted` witness must trap.
    let mut i = Interner::new();

    // The **coverage matrix**: every numeric leaf form the rulebook claims to read,
    // with sign variants (a single all-positive representative hides sign bugs in
    // `*`, `/`, `%`), plus the composites and the non-numeric forms.
    let ints = |n: i64, rr: i64| Contract::Mod { n: BigInt::from(n), r: BigInt::from(rr) };
    let inputs = vec![
        // non-numeric / catch-all
        Contract::Top,
        Contract::Bottom,
        Contract::Kind(Kind::Number),
        Contract::Kind(Kind::String),
        Contract::Kind(Kind::Boolean),
        // Range — the three sign positions
        Contract::Range(r(0), r(10)),
        Contract::Range(r(-5), r(5)),
        Contract::Range(r(-8), r(-2)),
        // half-lines — both directions, both signs, both strictnesses
        Contract::Greater(r(0)),
        Contract::GreaterEq(r(2)),
        Contract::GreaterEq(r(-3)),
        Contract::Less(r(0)),
        Contract::LessEq(r(-1)),
        Contract::LessEq(r(4)),
        // exact points, including a non-integer (no congruence) and negatives
        Contract::Equals(i.integer(0)),
        Contract::Equals(i.integer(2)),
        Contract::Equals(i.integer(-3)),
        Contract::Equals(i.number(rat(1, 2))),
        // the integer lattice
        ints(1, 0), // all integers
        ints(2, 0), // evens
        ints(3, 1),
        // geometric, both signs
        Contract::Geo { b: r(2), r: r(3) },
        Contract::Geo { b: r(-2), r: r(3) },
        // composites
        Contract::intersection(Contract::GreaterEq(r(0)), ints(1, 0), &mut i),
        Contract::union(
            Contract::Equals(i.integer(2)),
            Contract::Equals(i.integer(6)),
            &mut i,
        ),
        Contract::difference(
            Contract::Range(r(0), r(10)),
            Contract::Equals(i.integer(5)),
            &mut i,
        ),
        // Indeterminate umbrella/forms and distinct specific values.
        Contract::indeterminate(&mut i),
        Contract::Indeterminate(IndeterminateFormTag::DivZero),
        Contract::Indeterminate(IndeterminateFormTag::ModZero),
        exact_div_zero(&mut i, 0),
        exact_div_zero(&mut i, 1),
        exact_div_zero(&mut i, 2),
        exact_mod_zero(&mut i, 0),
        exact_mod_zero(&mut i, 1),
        exact_mod_zero(&mut i, 2),
    ];

    let mut pool: Vec<ValueRef> = Vec::new();
    for v in [-8, -5, -3, -2, -1, 0, 1, 2, 3, 4, 6, 7, 10, 100] {
        pool.push(i.integer(v));
    }
    pool.push(i.number(rat(1, 2)));
    pool.push(i.number(rat(-1, 2)));
    pool.push(i.string("a"));
    pool.push(i.boolean(true));
    pool.push(i.null());
    pool.push(div_zero(&mut i, 0));
    pool.push(div_zero(&mut i, 1));
    pool.push(div_zero(&mut i, 2));
    pool.push(mod_zero(&mut i, 0));
    pool.push(mod_zero(&mut i, 1));
    pool.push(mod_zero(&mut i, 2));

    let binops = [
        PrimOp::Add,
        PrimOp::Sub,
        PrimOp::Mul,
        PrimOp::Div,
        PrimOp::Rem,
        PrimOp::Pow,
        PrimOp::Lt,
        PrimOp::Le,
        PrimOp::Gt,
        PrimOp::Ge,
        PrimOp::Eq,
        PrimOp::Ne,
    ];

    for op in binops {
        for a in &inputs {
            for b in &inputs {
                let res = analyze_operation(op, &[a.clone(), b.clone()], &mut i);
                if let OpSafety::Refuted(w) = &res.safety {
                    assert!(
                        eval_prim(op, w, &mut i).is_err(),
                        "UNSOUND Refuted: {op:?} witness {w:?} does not trap",
                    );
                }
                for v1 in &pool {
                    if !a.contains(v1) {
                        continue;
                    }
                    for v2 in &pool {
                        if !b.contains(v2) {
                            continue;
                        }
                        let t = [v1.clone(), v2.clone()];
                        match eval_prim(op, &t, &mut i) {
                            Ok(out) => assert!(
                                res.output.contains(&out),
                                "IMAGE ESCAPE: {op:?}({v1:?},{v2:?}) = {out:?} ∉ {:?}",
                                res.output,
                            ),
                            Err(_) => assert!(
                                !matches!(res.safety, OpSafety::Proven),
                                "UNSOUND Proven: {op:?}({v1:?},{v2:?}) traps",
                            ),
                        }
                    }
                }
            }
        }
    }

    // Unary negation.
    for a in &inputs {
        let res = analyze_operation(PrimOp::Neg, std::slice::from_ref(a), &mut i);
        if let OpSafety::Refuted(w) = &res.safety {
            assert!(eval_prim(PrimOp::Neg, w, &mut i).is_err());
        }
        for v in &pool {
            if !a.contains(v) {
                continue;
            }
            match eval_prim(PrimOp::Neg, std::slice::from_ref(v), &mut i) {
                Ok(out) => assert!(
                    res.output.contains(&out),
                    "IMAGE ESCAPE: -{v:?} = {out:?} ∉ {:?}",
                    res.output,
                ),
                Err(_) => assert!(!matches!(res.safety, OpSafety::Proven)),
            }
        }
    }
}

// ── Recursive contracts (C§9) ─────────────────────────────────────────────────

mod rec {
    use super::*;
    use crate::contract::recursive::{self, RecGroup};

    fn rec_ref(name: &str) -> Contract {
        Contract::Ref(name.into())
    }
    fn record(fields: &[(&str, Contract)], i: &mut Interner) -> Contract {
        Contract::record(fields.iter().map(|(k, c)| (k.to_string(), c.clone())), i)
    }
    fn union(a: Contract, b: Contract, i: &mut Interner) -> Contract {
        Contract::union(a, b, i)
    }
    fn group(defs: &[(&str, Contract)]) -> RecGroup {
        RecGroup::new(defs.iter().map(|(n, c)| (n.to_string(), c.clone())))
    }

    #[test]
    fn rc09_negative_occurrence_rejected() {
        let mut i = Interner::new();
        // Bad = Difference(Top, Bad) — antitone, no least fixpoint.
        let g = group(&[(
            "Bad",
            Contract::difference(Contract::Top, rec_ref("Bad"), &mut i),
        )]);
        assert_eq!(
            recursive::admissible(&g),
            Err(recursive::DefError::NegativeOccurrence { name: "Bad".into() }),
        );
    }

    #[test]
    fn rc10_unguarded_recursion_rejected() {
        let mut i = Interner::new();
        // R = R
        let g1 = group(&[("R", rec_ref("R"))]);
        assert!(matches!(
            recursive::admissible(&g1),
            Err(recursive::DefError::Unguarded { .. })
        ));
        // R = Union(Number, R) — denotes Number; hint says so.
        let g2 = group(&[(
            "R",
            union(Contract::Kind(Kind::Number), rec_ref("R"), &mut i),
        )]);
        match recursive::admissible(&g2) {
            Err(recursive::DefError::Unguarded { hint, .. }) => assert!(hint.contains("denotes")),
            other => panic!("expected unguarded, got {other:?}"),
        }
    }

    #[test]
    fn guarded_group_is_admissible() {
        let mut i = Interner::new();
        // List = Union(Null, Record({head: Number, tail: List})) — references are
        // guarded beneath the Record.
        let g = group(&[(
            "List",
            union(
                Contract::Kind(Kind::Null),
                record(
                    &[
                        ("head", Contract::Kind(Kind::Number)),
                        ("tail", rec_ref("List")),
                    ],
                    &mut i,
                ),
                &mut i,
            ),
        )]);
        assert_eq!(recursive::admissible(&g), Ok(()));
    }

    #[test]
    fn recursive_membership() {
        let mut i = Interner::new();
        let g = group(&[(
            "List",
            union(
                Contract::Kind(Kind::Null),
                record(
                    &[
                        ("head", Contract::Kind(Kind::Number)),
                        ("tail", rec_ref("List")),
                    ],
                    &mut i,
                ),
                &mut i,
            ),
        )]);
        assert!(recursive::admissible(&g).is_ok());
        let list = rec_ref("List");

        let nil = i.null();
        assert!(recursive::contains(&g, &list, &nil)); // empty list

        let one_two = {
            let two = i.integer(2);
            let inner = i.record_str(vec![("head", two), ("tail", nil.clone())]);
            let one = i.integer(1);
            i.record_str(vec![("head", one), ("tail", inner)])
        };
        assert!(recursive::contains(&g, &list, &one_two)); // [1, 2]

        let x = i.string("x");
        let bad_head = i.record_str(vec![("head", x), ("tail", nil.clone())]);
        assert!(!recursive::contains(&g, &list, &bad_head)); // head not a Number
    }

    #[test]
    fn rc11_empty_source_subcontract_proven() {
        // μR.Record({next: R}) is empty (a list with no nil is uninhabited), so it
        // is a subcontract of everything — v0.1 would have wrongly refuted.
        let mut i = Interner::new();
        let g = group(&[("R", record(&[("next", rec_ref("R"))], &mut i))]);
        assert!(recursive::admissible(&g).is_ok());
        let v = recursive::subcontract(&g, &rec_ref("R"), &Contract::Kind(Kind::Number), &mut i);
        assert!(
            matches!(v, Verdict::Proven),
            "empty source ⊑ anything, got {v:?}"
        );
    }

    #[test]
    fn rc12_mutual_productivity() {
        // A = Record({b: B}); B = Union(Null, Record({a: A})). Both inhabited: B
        // via Null, then A via {b: null}.
        let mut i = Interner::new();
        let g = group(&[
            ("A", record(&[("b", rec_ref("B"))], &mut i)),
            (
                "B",
                union(
                    Contract::Kind(Kind::Null),
                    record(&[("a", rec_ref("A"))], &mut i),
                    &mut i,
                ),
            ),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        // Witnesses must genuinely inhabit their contracts.
        for name in ["A", "B"] {
            match &e[name] {
                recursive::Emptiness::NonEmpty(w) => {
                    assert!(recursive::contains(&g, &rec_ref(name), w), "{name} witness invalid");
                }
                other => panic!("{name} expected NonEmpty, got {other:?}"),
            }
        }
    }

    #[test]
    fn rc13_mutual_all_empty() {
        // A = Record({b: B}); B = Record({a: A}) — no base case, both empty.
        let mut i = Interner::new();
        let g = group(&[
            ("A", record(&[("b", rec_ref("B"))], &mut i)),
            ("B", record(&[("a", rec_ref("A"))], &mut i)),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        assert!(matches!(e["A"], recursive::Emptiness::Empty));
        assert!(matches!(e["B"], recursive::Emptiness::Empty));
    }

    /// `Repeat(E)` — a flat sequence, derived from Concat (tuple family §1):
    /// `R = Union(Tuple(), Concat(Tuple(E), R))`.
    fn repeat_group(name: &str, element: Contract, i: &mut Interner) -> RecGroup {
        let body = union(
            Contract::tuple(vec![], i),
            Contract::concat([Contract::tuple(vec![element], i), rec_ref(name)], i),
            i,
        );
        group(&[(name, body)])
    }

    /// Merge two groups so both `Repeat`s are comparable in one namespace.
    fn merge(a: RecGroup, b: RecGroup) -> RecGroup {
        RecGroup::new(a.defs.into_iter().chain(b.defs))
    }

    #[test]
    fn concat_guardedness_admits_repeat() {
        let mut i = Interner::new();
        // The recursive segment is guarded by a sibling of proven minimum extent 1.
        let g = repeat_group("R", Contract::Kind(Kind::Number), &mut i);
        assert_eq!(recursive::admissible(&g), Ok(()));

        // With no consuming sibling, the same shape is unguarded and rejected.
        let bad = group(&[(
            "U",
            Contract::concat([Contract::Kind(Kind::Tuple), rec_ref("U")], &mut i),
        )]);
        assert!(matches!(
            recursive::admissible(&bad),
            Err(recursive::DefError::Unguarded { .. })
        ));
    }

    #[test]
    fn concat_membership_splits_the_tuple() {
        let mut i = Interner::new();
        let g = repeat_group("R", Contract::Kind(Kind::Number), &mut i);
        let r = rec_ref("R");

        let empty = i.tuple(vec![]);
        assert!(recursive::contains(&g, &r, &empty));
        let one = i.integer(1);
        let two = i.integer(2);
        let nums = i.tuple(vec![one, two]);
        assert!(recursive::contains(&g, &r, &nums));
        let s = i.string("x");
        let mixed = i.tuple(vec![s]);
        assert!(!recursive::contains(&g, &r, &mixed));
    }

    #[test]
    fn rc17_repeat_covariance_proven_by_consumed_extent() {
        // Repeat(E) ⊑ Repeat(Top) — closes only because traversing the Concat
        // consumes ≥ 1 element, so the revisited pair advances source progress.
        let mut i = Interner::new();
        let g = merge(
            repeat_group("RN", Contract::Kind(Kind::Number), &mut i),
            repeat_group("RT", Contract::Top, &mut i),
        );
        assert!(recursive::admissible(&g).is_ok());
        let v = recursive::subcontract(&g, &rec_ref("RN"), &rec_ref("RT"), &mut i);
        assert!(
            matches!(v, Verdict::Proven),
            "Repeat(Number) ⊑ Repeat(Top), got {v:?}"
        );
    }

    #[test]
    fn rc18_repeat_mismatch_refuted_with_complete_witness() {
        // Repeat(Number) ⊄ Repeat(String) — refuted only with a *complete* finite
        // tuple witness (`[1]`), never a bare positional mismatch (§5.3).
        let mut i = Interner::new();
        let g = merge(
            repeat_group("RN", Contract::Kind(Kind::Number), &mut i),
            repeat_group("RS", Contract::Kind(Kind::String), &mut i),
        );
        assert!(recursive::admissible(&g).is_ok());
        match recursive::subcontract(&g, &rec_ref("RN"), &rec_ref("RS"), &mut i) {
            Verdict::Refuted(w) => {
                assert!(
                    recursive::contains(&g, &rec_ref("RN"), &w),
                    "witness ∈ Repeat(Number)"
                );
                assert!(
                    !recursive::contains(&g, &rec_ref("RS"), &w),
                    "witness ∉ Repeat(String)"
                );
                // A complete tuple, not a naked element.
                assert!(
                    w.as_tuple().is_some(),
                    "the witness is a whole tuple: {w:?}"
                );
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    #[test]
    fn rc19_mutual_cycle_over_record_and_concat_terminates() {
        // A cycle crossing Record descent *and* Concat consumption terminates under
        // the combined source-progress rule.
        let mut i = Interner::new();
        let g = group(&[
            ("A", record(&[("seq", rec_ref("B"))], &mut i)),
            (
                "B",
                union(
                    Contract::tuple(vec![], &mut i),
                    Contract::concat(
                        [Contract::tuple(vec![rec_ref("A")], &mut i), rec_ref("B")],
                        &mut i,
                    ),
                    &mut i,
                ),
            ),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        // Both directions terminate and stay sound; reflexivity must hold.
        let v = recursive::subcontract(&g, &rec_ref("B"), &rec_ref("B"), &mut i);
        assert!(matches!(v, Verdict::Proven), "reflexive B ⊑ B, got {v:?}");
        // The group is inhabited (B via the empty tuple, then A via {seq: []}).
        let e = recursive::emptiness(&g, &mut i);
        assert!(matches!(e["A"], recursive::Emptiness::NonEmpty(_)), "got {:?}", e["A"]);
        assert!(matches!(e["B"], recursive::Emptiness::NonEmpty(_)));
    }

    #[test]
    fn audit_concat_emptiness_voice_is_sound() {
        // AUDIT S1 regression: exact_eval lacked a Concat arm, so a Concat def fell
        // to the NonEmpty leaf default — and an opaque-dependent group could be
        // proven Empty, which feeds subcontract step 0 (empty ⊑ anything).
        let mut i = Interner::new();

        // L = Union(Function, Concat(Tuple(Number), L)) — a function value
        // inhabits L, but no witness is constructible: emptiness must be
        // Unproven, never Empty.
        let g = group(&[(
            "L",
            union(
                Contract::Kind(Kind::Function),
                Contract::concat(
                    [
                        Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i),
                        rec_ref("L"),
                    ],
                    &mut i,
                ),
                &mut i,
            ),
        )]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        assert!(
            matches!(e["L"], recursive::Emptiness::Unproven),
            "opaque-dependent Concat group must stay Unproven, got {:?}",
            e["L"],
        );
        // And the false Empty must not leak into a subcontract proof.
        let v = recursive::subcontract(&g, &rec_ref("L"), &Contract::Kind(Kind::Number), &mut i);
        assert!(
            !matches!(v, Verdict::Proven),
            "L ⊑ Number must not prove, got {v:?}"
        );

        // Control: a Concat cycle with no base really is empty.
        let dead = group(&[(
            "D",
            Contract::concat(
                [
                    Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i),
                    rec_ref("D"),
                ],
                &mut i,
            ),
        )]);
        assert!(recursive::admissible(&dead).is_ok());
        let e = recursive::emptiness(&dead, &mut i);
        assert!(
            matches!(e["D"], recursive::Emptiness::Empty),
            "got {:?}",
            e["D"]
        );
    }

    #[test]
    fn audit_equals_segment_membership() {
        // AUDIT S2 regression: an Equals segment in a Concat window was rejected
        // outright (membership false negative — the truth source must be exact).
        let mut i = Interner::new();
        let one = i.integer(1);
        let inner = i.tuple(vec![one]);
        let c = Contract::Concat(vec![
            Contract::Equals(inner).cref(&mut i),
            Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i).cref(&mut i),
        ]);
        let (a, b) = (i.integer(1), i.integer(5));
        let val = i.tuple(vec![a, b]);
        assert!(c.contains(&val), "[1, 5] splits as [1] ++ [5]");
        let (x, y) = (i.integer(2), i.integer(5));
        let miss = i.tuple(vec![x, y]);
        assert!(!c.contains(&miss), "[2, 5] does not start with [1]");

        // Group-aware path agrees.
        let g = group(&[("C", c.clone())]);
        let (a2, b2) = (i.integer(1), i.integer(5));
        let val2 = i.tuple(vec![a2, b2]);
        assert!(recursive::contains(&g, &rec_ref("C"), &val2));
    }

    #[test]
    fn rc15_opaque_leaf_stays_unproven() {
        // L = Union(Function, Record({next: L})). The Function leaf is opaque —
        // recursion never settles what its leaves cannot; emptiness is Unproven.
        let mut i = Interner::new();
        let g = group(&[(
            "L",
            union(
                Contract::Kind(Kind::Function),
                record(&[("next", rec_ref("L"))], &mut i),
                &mut i,
            ),
        )]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        assert!(
            matches!(e["L"], recursive::Emptiness::Unproven),
            "got {:?}",
            e["L"]
        );
    }

    #[test]
    fn recursive_subcontract_progress_guarded() {
        // NumList ⊑ AnyList: number lists refine top-lists, proven by descending
        // through the Record `tail` and closing the revisited pair at greater depth.
        let mut i = Interner::new();
        let num_list = union(
            Contract::Kind(Kind::Null),
            record(
                &[
                    ("head", Contract::Kind(Kind::Number)),
                    ("tail", rec_ref("NumList")),
                ],
                &mut i,
            ),
            &mut i,
        );
        let any_list = union(
            Contract::Kind(Kind::Null),
            record(
                &[("head", Contract::Top), ("tail", rec_ref("AnyList"))],
                &mut i,
            ),
            &mut i,
        );
        let g = group(&[("NumList", num_list), ("AnyList", any_list)]);
        assert!(recursive::admissible(&g).is_ok());
        let v = recursive::subcontract(&g, &rec_ref("NumList"), &rec_ref("AnyList"), &mut i);
        assert!(matches!(v, Verdict::Proven), "NumList ⊑ AnyList, got {v:?}");
    }

    fn equals(i: &mut Interner, v: i64) -> Contract {
        Contract::Equals(i.integer(v))
    }
    fn intersection(a: Contract, b: Contract, i: &mut Interner) -> Contract {
        Contract::intersection(a, b, i)
    }

    #[test]
    fn rc14_recursive_intersection_nonempty() {
        // A = Union(Equals(1), Record({next: A})); B = Union(Equals(1), Record({next: B})).
        // They share the base `1`, so the intersection is inhabited by `1`.
        let mut i = Interner::new();
        let one = equals(&mut i, 1);
        let g = group(&[
            (
                "A",
                union(
                    one.clone(),
                    record(&[("next", rec_ref("A"))], &mut i),
                    &mut i,
                ),
            ),
            (
                "B",
                union(one, record(&[("next", rec_ref("B"))], &mut i), &mut i),
            ),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        // Add the intersection as a member so emptiness reports on it.
        let g2 = group(&[
            ("A", g.defs["A"].clone()),
            ("B", g.defs["B"].clone()),
            ("AB", intersection(rec_ref("A"), rec_ref("B"), &mut i)),
        ]);
        let e = recursive::emptiness(&g2, &mut i);
        match &e["AB"] {
            recursive::Emptiness::NonEmpty(w) => {
                assert!(recursive::contains(&g2, &rec_ref("A"), w));
                assert!(recursive::contains(&g2, &rec_ref("B"), w));
            }
            other => panic!("expected NonEmpty, got {other:?}"),
        }
    }

    #[test]
    fn rc14_recursive_intersection_empty() {
        // A carries `1` at every base; B carries `2`. Disjoint singletons, and the
        // recursive branch bottoms out through the product cut ⇒ intersection empty.
        let mut i = Interner::new();
        let one = equals(&mut i, 1);
        let two = equals(&mut i, 2);
        let g = group(&[
            (
                "A",
                union(one, record(&[("next", rec_ref("A"))], &mut i), &mut i),
            ),
            (
                "B",
                union(two, record(&[("next", rec_ref("B"))], &mut i), &mut i),
            ),
            ("AB", intersection(rec_ref("A"), rec_ref("B"), &mut i)),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        // A and B are individually inhabited, but their intersection is empty.
        assert!(matches!(e["A"], recursive::Emptiness::NonEmpty(_)));
        assert!(matches!(e["B"], recursive::Emptiness::NonEmpty(_)));
        assert!(
            matches!(e["AB"], recursive::Emptiness::Empty),
            "got {:?}",
            e["AB"]
        );
    }

    #[test]
    fn recursive_subcontract_refuted_with_witness() {
        // NumList ⊄ StringList: a number-list like [1] inhabits NumList but not
        // StringList. §5.3 — the verdict is a witness, not a bare mismatch.
        let mut i = Interner::new();
        let num_list = union(
            Contract::Kind(Kind::Null),
            record(
                &[
                    ("head", Contract::Kind(Kind::Number)),
                    ("tail", rec_ref("NumList")),
                ],
                &mut i,
            ),
            &mut i,
        );
        let str_list = union(
            Contract::Kind(Kind::Null),
            record(
                &[
                    ("head", Contract::Kind(Kind::String)),
                    ("tail", rec_ref("StrList")),
                ],
                &mut i,
            ),
            &mut i,
        );
        let g = group(&[("NumList", num_list), ("StrList", str_list)]);
        assert!(recursive::admissible(&g).is_ok());
        match recursive::subcontract(&g, &rec_ref("NumList"), &rec_ref("StrList"), &mut i) {
            Verdict::Refuted(w) => {
                assert!(
                    recursive::contains(&g, &rec_ref("NumList"), &w),
                    "witness ∈ NumList"
                );
                assert!(
                    !recursive::contains(&g, &rec_ref("StrList"), &w),
                    "witness ∉ StrList"
                );
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    #[test]
    fn recursive_subcontract_soundness() {
        // Whatever the recursive subcontract proves, no sampled inhabitant of the
        // source may fall outside the target (soundness against membership).
        let mut i = Interner::new();
        let num_list = union(
            Contract::Kind(Kind::Null),
            record(
                &[
                    ("head", Contract::Kind(Kind::Number)),
                    ("tail", rec_ref("NumList")),
                ],
                &mut i,
            ),
            &mut i,
        );
        let any_list = union(
            Contract::Kind(Kind::Null),
            record(
                &[("head", Contract::Top), ("tail", rec_ref("AnyList"))],
                &mut i,
            ),
            &mut i,
        );
        let g = group(&[("NumList", num_list), ("AnyList", any_list)]);

        // Build a few concrete NumList inhabitants and confirm AnyList membership.
        let nil = i.null();
        let seven = i.integer(7);
        let l1 = i.record_str(vec![("head", seven), ("tail", nil.clone())]);
        let three = i.integer(3);
        let l2 = i.record_str(vec![("head", three), ("tail", l1.clone())]);
        if let Verdict::Proven =
            recursive::subcontract(&g, &rec_ref("NumList"), &rec_ref("AnyList"), &mut i)
        {
            for v in [&nil, &l1, &l2] {
                assert!(
                    !recursive::contains(&g, &rec_ref("NumList"), v)
                        || recursive::contains(&g, &rec_ref("AnyList"), v),
                    "UNSOUND: {v:?} ∈ NumList but ∉ AnyList",
                );
            }
        }
    }
}

// ── Concat: normal forms and membership (tuple family §1) ────────────────────

#[test]
fn concat_normal_forms() {
    let mut i = Interner::new();
    let num = || Contract::Kind(Kind::Number);
    let str_ = || Contract::Kind(Kind::String);
    fn t(e: Vec<Contract>, i: &mut Interner) -> Contract {
        Contract::tuple(e, i)
    }

    // Nested Concats flatten associatively.
    let inner = Contract::concat(
        [Contract::Kind(Kind::Tuple), Contract::Kind(Kind::Tuple)],
        &mut i,
    );
    let flat = Contract::concat([inner, Contract::Kind(Kind::Tuple)], &mut i);
    assert_eq!(
        flat,
        Contract::Concat(vec![Contract::Kind(Kind::Tuple).cref(&mut i); 3])
    );

    // The empty-tuple segment erases (a structural fact).
    assert_eq!(
        Contract::concat([t(vec![], &mut i), Contract::Kind(Kind::Tuple)], &mut i),
        Contract::Kind(Kind::Tuple)
    );
    // …and a Concat of nothing is the empty tuple.
    assert_eq!(Contract::concat([], &mut i), t(vec![], &mut i));
    assert_eq!(
        Contract::concat([t(vec![], &mut i), t(vec![], &mut i)], &mut i),
        t(vec![], &mut i)
    );

    // Adjacent exact segments fuse.
    assert_eq!(
        Contract::concat([t(vec![num()], &mut i), t(vec![str_()], &mut i)], &mut i),
        t(vec![num(), str_()], &mut i)
    );

    // An uninhabited segment NEVER erases — it empties the whole Concat (erasing
    // it would turn an empty contract into an inhabited one).
    assert_eq!(
        Contract::concat([Contract::Bottom, t(vec![num()], &mut i)], &mut i),
        Contract::Bottom
    );
    assert_eq!(
        Contract::concat(
            [
                t(vec![Contract::Bottom], &mut i),
                Contract::Kind(Kind::Tuple)
            ],
            &mut i
        ),
        Contract::Bottom,
    );

    // A single segment collapses to itself.
    assert_eq!(
        Contract::concat([t(vec![num()], &mut i)], &mut i),
        t(vec![num()], &mut i)
    );
}

#[test]
fn concat_membership_matches_denotation() {
    let mut i = Interner::new();
    // Concat(Tuple(Number), Tuple(String)) — fused to an exact 2-tuple.
    let c = Contract::concat(
        [
            Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i),
            Contract::tuple(vec![Contract::Kind(Kind::String)], &mut i),
        ],
        &mut i,
    );
    let one = i.integer(1);
    let sx = i.string("x");
    let ok = i.tuple(vec![one.clone(), sx.clone()]);
    assert!(c.contains(&ok));
    let swapped = i.tuple(vec![sx, one.clone()]);
    assert!(!c.contains(&swapped));
    let short = i.tuple(vec![one]);
    assert!(!c.contains(&short));

    // A variable head segment is searched over: Concat(Kind(Tuple), Tuple(Number)).
    let v = Contract::Concat(vec![
        Contract::Kind(Kind::Tuple).cref(&mut i),
        Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i).cref(&mut i),
    ]);
    let (a, b) = (i.string("a"), i.integer(9));
    let ends_num = i.tuple(vec![a, b]);
    assert!(v.contains(&ends_num), "any prefix, then a Number");
    let s2 = i.string("s");
    let ends_str = i.tuple(vec![s2]);
    assert!(!v.contains(&ends_str));
}

// ── Contract expressions (C§12.2) ─────────────────────────────────────────────

mod contract_expr {
    use super::*;
    use crate::ast::{Arg, BindingRef, Element, Expr, Field, Ref};
    use crate::contract::{ContractEnv, build_contract_env, eval_contract};

    fn cref(n: &str) -> Expr {
        Expr::Ref(Ref::Immutable(BindingRef::Name(n.into())))
    }
    /// `Ctor(args…)` — a contract-constructor application.
    fn ctor(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Apply {
            callee: Box::new(cref(name)),
            args: args.into_iter().map(Arg::Expr).collect(),
        }
    }

    #[test]
    fn prelude_names_and_constructors() {
        let mut i = Interner::new();
        let env = ContractEnv::new();

        assert_eq!(
            eval_contract(&cref("Number"), &env, &mut i),
            Some(Contract::Kind(Kind::Number))
        );
        assert_eq!(eval_contract(&cref("ZeroDen"), &env, &mut i), None);
        assert_eq!(
            eval_contract(&cref("Indeterminate"), &env, &mut i),
            Some(Contract::indeterminate(&mut i))
        );
        let numeric = eval_contract(&cref("Numeric"), &env, &mut i).expect("Numeric prelude contract");
        assert!(numeric.contains(&i.integer(3)));
        assert!(numeric.contains(&div_zero(&mut i, 1)));
        assert!(numeric.contains(&mod_zero(&mut i, 1)));
        assert!(!numeric.contains(&i.string("no")));
        assert_eq!(
            eval_contract(&cref("Top"), &env, &mut i),
            Some(Contract::Top)
        );
        assert_eq!(
            eval_contract(&cref("Bottom"), &env, &mut i),
            Some(Contract::Bottom)
        );

        // Range(0, 100)
        let range = ctor(
            "Range",
            vec![Expr::Const(i.integer(0)), Expr::Const(i.integer(100))],
        );
        assert_eq!(
            eval_contract(&range, &env, &mut i),
            Some(Contract::Range(r(0), r(100)))
        );

        // Greater(5) / LessEq(9)
        let g = ctor("Greater", vec![Expr::Const(i.integer(5))]);
        assert_eq!(
            eval_contract(&g, &env, &mut i),
            Some(Contract::Greater(r(5)))
        );

        // Mod(2, 0) — the even integers
        let m = ctor(
            "Mod",
            vec![Expr::Const(i.integer(2)), Expr::Const(i.integer(0))],
        );
        assert_eq!(
            eval_contract(&m, &env, &mut i),
            Some(Contract::Mod {
                n: BigInt::from(2),
                r: BigInt::from(0)
            })
        );

        // Equals(7) and HasField("age")
        let five = i.integer(7);
        let eq = ctor("Equals", vec![Expr::Const(five.clone())]);
        assert_eq!(
            eval_contract(&eq, &env, &mut i),
            Some(Contract::Equals(five))
        );
        let age = i.string("age");
        let hf = ctor("HasField", vec![Expr::Const(age)]);
        assert_eq!(
            eval_contract(&hf, &env, &mut i),
            Some(Contract::HasField("age".into()))
        );

        // An unknown bare name does not resolve.
        assert_eq!(eval_contract(&cref("Nope"), &env, &mut i), None);
    }

    #[test]
    fn set_operations_and_structural_literals() {
        let mut i = Interner::new();
        let env = ContractEnv::new();

        // Union(Number, Null)
        let u = ctor("Union", vec![cref("Number"), cref("Null")]);
        assert_eq!(
            eval_contract(&u, &env, &mut i),
            Some(Contract::union(
                Contract::Kind(Kind::Number),
                Contract::Kind(Kind::Null),
                &mut i
            )),
        );

        // A tuple literal of contracts is a tuple contract: [Number, String]
        let t = Expr::TupleCons(vec![
            Element::Expr(cref("Number")),
            Element::Expr(cref("String")),
        ]);
        assert_eq!(
            eval_contract(&t, &env, &mut i),
            Some(Contract::tuple(
                vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::String)],
                &mut i
            )),
        );

        // A record literal of contracts is a record contract: { a: Number }
        let rec = Expr::RecordCons(vec![Field::Field {
            key: "a".into(),
            value: cref("Number"),
        }]);
        assert_eq!(
            eval_contract(&rec, &env, &mut i),
            Some(Contract::record(
                vec![("a".into(), Contract::Kind(Kind::Number))],
                &mut i
            )),
        );

        // A non-contract expression is not a contract.
        assert_eq!(
            eval_contract(&Expr::Const(i.integer(3)), &env, &mut i),
            None
        );
    }

    #[test]
    fn named_contracts_resolve_and_compose() {
        // Percent = Range(0, 100);  Grade = Union(Percent, Null)
        let mut i = Interner::new();
        let percent = ctor(
            "Range",
            vec![Expr::Const(i.integer(0)), Expr::Const(i.integer(100))],
        );
        let grade = ctor("Union", vec![cref("Percent"), cref("Null")]);
        let env = build_contract_env([("Percent", &percent), ("Grade", &grade)], &mut i);

        assert_eq!(env.get("Percent"), Some(&Contract::Range(r(0), r(100))));
        assert_eq!(
            env.get("Grade"),
            Some(&Contract::union(
                Contract::Range(r(0), r(100)),
                Contract::Kind(Kind::Null),
                &mut i
            )),
        );

        // The resolved contract denotes what it should.
        let g = env.get("Grade").unwrap();
        assert!(g.contains(&i.integer(50)));
        assert!(g.contains(&i.null()));
        assert!(!g.contains(&i.integer(500)));
    }
}

// ── Length derivation Λ with exactness stamps (tuple family §2) ──────────────

mod tl {
    use super::*;
    use crate::contract::length::{Stamp, len};
    use crate::contract::recursive::{self, RecGroup};

    fn rec_ref(n: &str) -> Contract {
        Contract::Ref(n.into())
    }
    fn union(a: Contract, b: Contract, i: &mut Interner) -> Contract {
        Contract::union(a, b, i)
    }
    fn group(defs: &[(&str, Contract)]) -> RecGroup {
        RecGroup::new(defs.iter().map(|(n, c)| (n.to_string(), c.clone())))
    }
    fn empty_group() -> RecGroup {
        RecGroup::new(std::iter::empty())
    }
    /// `Equals(k)` as a length contract.
    fn eq(k: i64) -> Contract {
        Contract::Range(r(k), r(k))
    }
    fn ge(k: i64) -> Contract {
        Contract::GreaterEq(r(k))
    }
    /// `Repeat(E) = Union(Tuple(), Concat(Tuple(E), R))`.
    /// Takes the caller's interner rather than minting one: with children-first
    /// interning, terms from two interners are never pointer-equal, so a helper with a
    /// private table would silently build contracts the caller cannot match.
    fn repeat(name: &str, element: Contract, i: &mut Interner) -> RecGroup {
        group(&[(
            name,
            union(
                Contract::tuple(vec![], i),
                Contract::concat(
                    [Contract::tuple(vec![element], i), rec_ref(name)],
                    i,
                ),
                i,
            ),
        )])
    }

    #[test]
    fn exact_shapes_are_exactly_counted() {
        let mut i = Interner::new();
        let g = empty_group();
        let num = || Contract::Kind(Kind::Number);

        // A proven-inhabited exact tuple: (Equals(k), Exact).
        let t = Contract::tuple(vec![num(), num()], &mut i);
        assert_eq!(
            len(&g, &t, &mut i),
            crate::contract::Len {
                contract: eq(2),
                stamp: Stamp::Exact
            }
        );

        // An exact record counts its fields.
        let rec = Contract::record(vec![("a".into(), num()), ("b".into(), num())], &mut i);
        assert_eq!(len(&g, &rec, &mut i).contract, eq(2));

        // An uninhabited shape has NO realizable length: (Bottom, Exact) —
        // impossible shapes are never realizable lengths.
        let dead = Contract::tuple(vec![num(), Contract::Bottom], &mut i);
        let l = len(&g, &dead, &mut i);
        assert_eq!(l.contract, Contract::Bottom);
        assert!(l.is_exact());

        // Concat sums segment lengths. A `GE` operand is outside the finite-exact
        // label boundary, so the sum coarsens to the minima and stamps Approx.
        let c = Contract::Concat(vec![
            Contract::tuple(vec![num()], &mut i).cref(&mut i),
            Contract::Kind(Kind::Tuple).cref(&mut i),
        ]);
        let l = len(&g, &c, &mut i);
        assert_eq!(l.contract, ge(1), "one element, then any tail");
        assert_eq!(
            l.stamp,
            Stamp::Approx,
            "a coarsening rule forfeits the stamp"
        );

        // Two finite exact segments sum exactly.
        let both = Contract::Concat(vec![
            Contract::tuple(vec![num()], &mut i).cref(&mut i),
            Contract::tuple(vec![num(), num()], &mut i).cref(&mut i),
        ]);
        assert_eq!(
            len(&g, &both, &mut i),
            crate::contract::Len {
                contract: eq(3),
                stamp: Stamp::Exact
            },
        );

        // Union takes the union of branch lengths, exactly.
        let u = union(
            Contract::tuple(vec![num()], &mut i),
            Contract::tuple(vec![num(), num()], &mut i),
            &mut i,
        );
        let l = len(&g, &u, &mut i);
        assert!(l.is_exact());
        assert!(l.contract.contains(&i.integer(1)) && l.contract.contains(&i.integer(2)));
        assert!(!l.contract.contains(&i.integer(3)));
    }

    #[test]
    fn tl13_repeat_of_bottom_is_exactly_the_empty_tuple() {
        // The recursive branch Bottom-normalizes, so only the base survives:
        // len = (Equals(0), Exact) — never GE(0).
        let mut i = Interner::new();
        let g = repeat("R", Contract::Bottom, &mut i);
        let l = len(&g, &rec_ref("R"), &mut i);
        assert!(l.is_exact(), "the length is exact, not approximate");
        assert!(l.contract.contains(&i.integer(0)));
        assert!(
            !l.contract.contains(&i.integer(1)),
            "no nonzero length is realizable"
        );
    }

    #[test]
    fn tl14_increments_two_and_three() {
        // R = Tuple() | Tuple(E,E)++R | Tuple(E,E,E)++R — increments {2,3} over {0}.
        // Λ(R) = {0, 2, 3, 4, …}: `Union(Equals(0), GE(2))`, exact.
        let mut i = Interner::new();
        let e = || Contract::Kind(Kind::Number);
        let g = group(&[(
            "R",
            union(
                union(
                    Contract::tuple(vec![], &mut i),
                    Contract::concat(
                        [Contract::tuple(vec![e(), e()], &mut i), rec_ref("R")],
                        &mut i,
                    ),
                    &mut i,
                ),
                Contract::concat(
                    [Contract::tuple(vec![e(), e(), e()], &mut i), rec_ref("R")],
                    &mut i,
                ),
                &mut i,
            ),
        )]);
        let l = len(&g, &rec_ref("R"), &mut i);
        assert!(l.is_exact(), "finite exact labels admit the exact solution");
        for ok in [0, 2, 3, 4, 5, 9] {
            assert!(l.contract.contains(&i.integer(ok)), "{ok} is realizable");
        }
        // Length 1 refutes membership — the gap the semigroup leaves.
        assert!(!l.contract.contains(&i.integer(1)), "1 is NOT realizable");
    }

    #[test]
    fn tl19_mutual_scc_period_comes_from_cycle_weights() {
        // R = Tuple() | Tuple(E)++S ;  S = Tuple(E)++R
        // Λ(R) = evens, Λ(S) = odds. The period is the CYCLE weight (2), never the
        // gcd of the individual edge weights (1), which would erase the parity.
        let mut i = Interner::new();
        let e = || Contract::Kind(Kind::Number);
        let g = group(&[
            (
                "R",
                union(
                    Contract::tuple(vec![], &mut i),
                    Contract::concat([Contract::tuple(vec![e()], &mut i), rec_ref("S")], &mut i),
                    &mut i,
                ),
            ),
            (
                "S",
                Contract::concat([Contract::tuple(vec![e()], &mut i), rec_ref("R")], &mut i),
            ),
        ]);

        let lr = len(&g, &rec_ref("R"), &mut i);
        let ls = len(&g, &rec_ref("S"), &mut i);
        assert!(lr.is_exact() && ls.is_exact());

        for even in [0, 2, 4, 6, 10] {
            assert!(lr.contract.contains(&i.integer(even)), "R admits {even}");
            assert!(!ls.contract.contains(&i.integer(even)), "S rejects {even}");
        }
        for odd in [1, 3, 5, 7, 11] {
            assert!(ls.contract.contains(&i.integer(odd)), "S admits {odd}");
            assert!(!lr.contract.contains(&i.integer(odd)), "R rejects {odd} — parity preserved");
        }
    }

    #[test]
    fn tl15_nonlinear_alternative_is_admissible_but_approximate() {
        // R = Tuple() | Concat(Tuple(E), R, R) — two own-SCC references per
        // alternative: admissible, but its length is (GE(min), Approx). It supplies
        // no subcontract witness (§3).
        let mut i = Interner::new();
        let e = || Contract::Kind(Kind::Number);
        let g = group(&[(
            "R",
            union(
                Contract::tuple(vec![], &mut i),
                Contract::concat(
                    [
                        Contract::tuple(vec![e()], &mut i),
                        rec_ref("R"),
                        rec_ref("R"),
                    ],
                    &mut i,
                ),
                &mut i,
            ),
        )]);
        let l = len(&g, &rec_ref("R"), &mut i);
        assert_eq!(
            l.stamp,
            Stamp::Approx,
            "nonlinear alternatives forfeit exactness"
        );
        assert!(l.contract.contains(&i.integer(0)));
    }

    #[test]
    fn audit_nested_own_scc_ref_in_label_terminates() {
        // AUDIT S3 regression: an own-SCC reference nested *inside* a segment
        // (here under a Union) sent classify → len → solve → classify into
        // unbounded recursion. It must decline to Approx — and terminate.
        let mut i = Interner::new();
        let e = || Contract::Kind(Kind::Number);
        let g = group(&[(
            "R",
            union(
                Contract::tuple(vec![], &mut i),
                Contract::concat(
                    [
                        union(Contract::tuple(vec![e()], &mut i), rec_ref("R"), &mut i),
                        Contract::tuple(vec![e()], &mut i),
                    ],
                    &mut i,
                ),
                &mut i,
            ),
        )]);
        assert!(recursive::admissible(&g).is_ok());
        let l = len(&g, &rec_ref("R"), &mut i); // must not overflow the stack
        assert_eq!(
            l.stamp,
            Stamp::Approx,
            "a nested own-SCC label declines exactness"
        );
        assert!(
            l.contract.contains(&i.integer(0)),
            "soundness: 0 is realizable"
        );

        // Control: a ref nested in a *tuple element* is arity-irrelevant and must
        // stay exact — N = Tuple(E, Ref N) is always a 2-tuple... but wait, that
        // group is empty (no base), so its length is Bottom. Use the inhabited
        // variant: N = Union(Null-free base) — a 2-tuple whose element nests N or
        // terminates.
        let g2 = group(&[(
            "N",
            union(
                Contract::tuple(vec![e(), Contract::Kind(Kind::Null)], &mut i),
                Contract::tuple(vec![e(), rec_ref("N")], &mut i),
                &mut i,
            ),
        )]);
        assert!(recursive::admissible(&g2).is_ok());
        let l2 = len(&g2, &rec_ref("N"), &mut i);
        assert!(
            l2.is_exact(),
            "element-nested refs never affect arity: {l2:?}"
        );
        assert!(l2.contract.contains(&i.integer(2)));
        assert!(!l2.contract.contains(&i.integer(3)));
    }

    #[test]
    fn tl22_infinite_increment_language_declines_exact_solving() {
        // R = Tuple() | Concat(Repeat(E), R): linear, but the increment language is
        // {0,1,2,…} — outside the finite-exact label boundary, so the solver
        // declines and returns a sound approximation.
        let mut i = Interner::new();
        let e = || Contract::Kind(Kind::Number);
        let g = group(&[
            (
                "Many",
                union(
                    Contract::tuple(vec![], &mut i),
                    Contract::concat(
                        [Contract::tuple(vec![e()], &mut i), rec_ref("Many")],
                        &mut i,
                    ),
                    &mut i,
                ),
            ),
            (
                "R",
                union(
                    Contract::tuple(vec![], &mut i),
                    Contract::concat([rec_ref("Many"), rec_ref("R")], &mut i),
                    &mut i,
                ),
            ),
        ]);
        let l = len(&g, &rec_ref("R"), &mut i);
        assert_eq!(
            l.stamp,
            Stamp::Approx,
            "an infinite increment language is not exact"
        );
        // Still sound: every realizable length is admitted.
        for n in [0, 1, 2, 7] {
            assert!(l.contract.contains(&i.integer(n)));
        }
    }

    // ── §3: refutation discipline + restrictLen / LengthRestricted ───────────

    #[test]
    fn tl20_disjoint_length_uppers_refute_intersection_even_when_approx() {
        // `(GE(5), Approx)` against `Tuple(a, b)` (length exactly 2): the length
        // uppers are disjoint (2 < 5), so the intersection is empty — Approx may
        // refute *emptiness* through disjoint uppers.
        use crate::contract::intersection_empty_by_length;
        let mut i = Interner::new();
        let g = empty_group();
        // A contract whose length is (GE(5), Approx): tuples of length ≥ 5.
        let at_least_five = Contract::length_restricted(Contract::Kind(Kind::Tuple), ge(5), &mut i);
        let pair = Contract::tuple(
            vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::Number)],
            &mut i,
        );
        assert!(intersection_empty_by_length(
            &g,
            &at_least_five,
            &pair,
            &mut i
        ));
        // A length that DOES overlap must not be reported empty.
        let triple = Contract::tuple(vec![Contract::Top, Contract::Top, Contract::Top], &mut i);
        let three_plus = Contract::length_restricted(Contract::Kind(Kind::Tuple), ge(3), &mut i);
        assert!(!intersection_empty_by_length(
            &g,
            &three_plus,
            &triple,
            &mut i
        ));
    }

    #[test]
    fn tl16_approx_source_mismatch_is_unproven_never_refuted() {
        // A gcd-coarsened `Approx` source length mismatching a target proves
        // nothing about subcontract inclusion — the verdict is *unproven*, never a
        // refutation. `Repeat(Number)` (lengths {0,1,2,…}, Approx) vs an exact pair
        // `Tuple(Number, Number)`: the recursive subcontract must not `Refuted` on
        // length grounds. (It genuinely isn't a subcontract; the point is it lands
        // Unproven, not a length-manufactured Refuted.)
        let mut i = Interner::new();
        let g = group(&[
            (
                "R",
                union(
                    Contract::tuple(vec![], &mut i),
                    Contract::concat(
                        [
                            Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i),
                            rec_ref("R"),
                        ],
                        &mut i,
                    ),
                    &mut i,
                ),
            ),
            (
                "P",
                Contract::tuple(
                    vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::Number)],
                    &mut i,
                ),
            ),
        ]);
        // No length-based refutation exists in `subcontract`, so any Refuted must
        // carry a real inhabitant witness (§3.ii). Here R ⊄ P: R admits `[1]`
        // (length 1), which P rejects — a *realizable* witness, so Refuted is
        // legitimate. The discipline we assert: the witness genuinely inhabits R∖P.
        match recursive::subcontract(&g, &rec_ref("R"), &rec_ref("P"), &mut i) {
            Verdict::Refuted(w) => {
                assert!(recursive::contains(&g, &rec_ref("R"), &w), "witness ∈ R (realizable)");
                assert!(!recursive::contains(&g, &rec_ref("P"), &w), "witness ∉ P");
            }
            // Unproven is also acceptable — never a manufactured length refutation.
            Verdict::Unproven => {}
            Verdict::Proven => panic!("R ⊄ P must not prove"),
        }
    }

    #[test]
    fn tl17_restrict_len_unrolls_repeat_and_falls_to_symbolic() {
        use crate::contract::restrict_len;
        let mut i = Interner::new();
        let g = repeat("R", Contract::Kind(Kind::Number), &mut i);

        // Repeat(Number) restricted to GE(1) unrolls: Concat(Tuple(Number), R).
        let unrolled = restrict_len(&g, &rec_ref("R"), &ge(1), &mut i);
        assert_eq!(
            unrolled,
            Contract::Concat(vec![
                Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i).cref(&mut i),
                rec_ref("R").cref(&mut i)
            ]),
        );
        // It denotes "≥ 1 Number": the empty tuple is excluded, a 1-tuple included.
        let empty = i.tuple(vec![]);
        assert!(!recursive::contains(&g, &unrolled, &empty));
        let one = i.integer(7);
        let single = i.tuple(vec![one]);
        assert!(recursive::contains(&g, &unrolled, &single));

        // A restriction that can't lower falls to the symbolic LengthRestricted.
        let modular = Contract::Mod { n: BigInt::from(2), r: BigInt::from(0) }; // even lengths
        let symbolic = restrict_len(&g, &rec_ref("R"), &modular, &mut i);
        assert!(matches!(symbolic, Contract::LengthRestricted(_, _)));
        // Membership still exact: even-length all-Number tuples only.
        let two = {
            let (a, b) = (i.integer(1), i.integer(2));
            i.tuple(vec![a, b])
        };
        assert!(
            recursive::contains(&g, &symbolic, &two),
            "length 2 (even) admitted"
        );
        assert!(
            !recursive::contains(&g, &symbolic, &single),
            "length 1 (odd) excluded"
        );
    }

    #[test]
    fn length_restricted_canonical_rows() {
        let mut i = Interner::new();
        let num = || Contract::Kind(Kind::Number);
        // Bottom on either side ⇒ Bottom.
        assert_eq!(
            Contract::length_restricted(Contract::Bottom, ge(1), &mut i),
            Contract::Bottom
        );
        assert_eq!(
            Contract::length_restricted(Contract::Kind(Kind::Tuple), Contract::Bottom, &mut i),
            Contract::Bottom,
        );
        // TopLength (GE(0)) ⇒ the base unchanged.
        assert_eq!(Contract::length_restricted(num(), ge(0), &mut i), num());
        // Nesting merges the domains by intersection.
        let inner = Contract::length_restricted(Contract::Kind(Kind::Tuple), ge(2), &mut i);
        let outer = Contract::length_restricted(inner, Contract::LessEq(r(9)), &mut i);
        match outer {
            Contract::LengthRestricted(t, d) => {
                assert_eq!(*t, Contract::Kind(Kind::Tuple));
                assert!(matches!(*d, Contract::Intersection(_, _)));
            }
            other => panic!("expected merged LengthRestricted, got {other:?}"),
        }
    }

    #[test]
    fn restrict_len_exact_tuple_filter() {
        use crate::contract::restrict_len;
        let mut i = Interner::new();
        let g = empty_group();
        let pair = Contract::tuple(vec![Contract::Top, Contract::Top], &mut i);
        // Length 2 admitted by GE(1) ⇒ keep the tuple.
        assert_eq!(restrict_len(&g, &pair, &ge(1), &mut i), pair);
        // Length 2 excluded by GE(3) ⇒ Bottom.
        assert_eq!(restrict_len(&g, &pair, &ge(3), &mut i), Contract::Bottom);
    }

    // ── §4: segment alignment ────────────────────────────────────────────────

    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }
    fn str_() -> Contract {
        Contract::Kind(Kind::String)
    }
    /// The `Union(Tuple(), Concat(Tuple(E), Ref name))` body of a `Repeat(E)`.
    fn repeat_body(element: Contract, name: &str, i: &mut Interner) -> Contract {
        union(
            Contract::tuple(vec![], i),
            Contract::concat([Contract::tuple(vec![element], i), rec_ref(name)], i),
            i,
        )
    }
    /// `Concat(Tuple(E), Ref name)` — one-or-more `E` (a non-empty `Repeat`).
    fn one_or_more(element: Contract, name: &str, i: &mut Interner) -> Contract {
        Contract::concat([Contract::tuple(vec![element], i), rec_ref(name)], i)
    }

    #[test]
    fn tl18_alignment_proof_map_peels_forced_prefix() {
        // ≥1 Number ⊑ ≥1 Top. The leading fixed segments are a forced boundary:
        // peel Tuple(Number) ⊑ Tuple(Top), leaving Repeat(Number) ⊑ Repeat(Top),
        // which closes by consumed-extent covariance (RC-17).
        let mut i = Interner::new();
        let g = group(&[
            ("RN", repeat_body(num(), "RN", &mut i)),
            ("RT", repeat_body(Contract::Top, "RT", &mut i)),
        ]);
        let src = one_or_more(num(), "RN", &mut i);
        let tgt = one_or_more(Contract::Top, "RT", &mut i);
        let v = recursive::subcontract(&g, &src, &tgt, &mut i);
        assert!(
            matches!(v, Verdict::Proven),
            "≥1 Number ⊑ ≥1 Top, got {v:?}"
        );
    }

    #[test]
    fn tl18_alignment_length_refutation() {
        // ≥1 Number ⊄ exactly-2 (Tuple(Number, Number)): the single-element list
        // `[1]` inhabits the source and fails the target on *length* — a realizable
        // witness (§3.ii), not a manufactured length verdict.
        let mut i = Interner::new();
        let g = group(&[("RN", repeat_body(num(), "RN", &mut i))]);
        let src = one_or_more(num(), "RN", &mut i);
        let pair = Contract::tuple(vec![num(), num()], &mut i);
        match recursive::subcontract(&g, &src, &pair, &mut i) {
            Verdict::Refuted(w) => {
                assert!(recursive::contains(&g, &src, &w), "witness ∈ source");
                assert!(!recursive::contains(&g, &pair, &w), "witness ∉ exactly-2");
            }
            other => panic!("expected length Refuted, got {other:?}"),
        }
    }

    #[test]
    fn tl18_alignment_element_refutation_needs_complete_witness() {
        // ≥1 Number ⊄ ≥1 String. Position 0 mismatches (Number ⊄ String), but the
        // verdict is a *complete* number-list witness (`[1]`), never a bare
        // positional exclusion (§4 round 2 / §5.3).
        let mut i = Interner::new();
        let g = group(&[
            ("RN", repeat_body(num(), "RN", &mut i)),
            ("RS", repeat_body(str_(), "RS", &mut i)),
        ]);
        let src = one_or_more(num(), "RN", &mut i);
        let tgt = one_or_more(str_(), "RS", &mut i);
        match recursive::subcontract(&g, &src, &tgt, &mut i) {
            Verdict::Refuted(w) => {
                assert!(
                    recursive::contains(&g, &src, &w),
                    "witness is a complete number-list"
                );
                assert!(!recursive::contains(&g, &tgt, &w), "witness ∉ string-list");
            }
            other => panic!("expected element Refuted, got {other:?}"),
        }
    }

    #[test]
    fn tl18_variable_vs_variable_is_unproven_never_refuted() {
        // Concat(Repeat(N), Repeat(N)) ⊑ Repeat(N): a genuine subcontract, but the
        // boundary between the two source runs is not forced — round-1 alignment has
        // no unique split. It must land Unproven (a real inhabitant witness cannot
        // exist), never a fabricated refutation.
        let mut i = Interner::new();
        let g = group(&[("RN", repeat_body(num(), "RN", &mut i))]);
        let two = Contract::Concat(vec![rec_ref("RN").cref(&mut i), rec_ref("RN").cref(&mut i)]);
        let v = recursive::subcontract(&g, &two, &rec_ref("RN"), &mut i);
        assert!(
            matches!(v, Verdict::Unproven),
            "no forced split ⇒ unproven, got {v:?}"
        );
    }

    #[test]
    fn tl_two_or_more_subset_of_one_or_more() {
        // ≥2 Number ⊑ ≥1 Number. Peel one forced Number pair, then a *single*
        // variable segment binds the residual (§4 interior): the collapsed target
        // `Repeat(N)` unfolds against the source residual under the guard.
        let mut i = Interner::new();
        let g = group(&[("RN", repeat_body(num(), "RN", &mut i))]);
        let two_plus = Contract::concat(
            [Contract::tuple(vec![num(), num()], &mut i), rec_ref("RN")],
            &mut i,
        );
        let one_plus = one_or_more(num(), "RN", &mut i);
        let v = recursive::subcontract(&g, &two_plus, &one_plus, &mut i);
        assert!(
            matches!(v, Verdict::Proven),
            "≥2 Number ⊑ ≥1 Number, got {v:?}"
        );
    }

    #[test]
    fn tl_zero_or_more_not_subset_of_one_or_more() {
        // Soundness guard on the nullable boundary: ≥0 Number ⊄ ≥1 Number. The
        // empty list inhabits the source and fails the target, so the fallback must
        // NOT prove it — the empty tuple is the refutation witness.
        let mut i = Interner::new();
        let g = group(&[("RN", repeat_body(num(), "RN", &mut i))]);
        let zero_plus = Contract::Concat(vec![rec_ref("RN").cref(&mut i)]);
        let one_plus = one_or_more(num(), "RN", &mut i);
        match recursive::subcontract(&g, &zero_plus, &one_plus, &mut i) {
            Verdict::Refuted(w) => {
                assert!(recursive::contains(&g, &zero_plus, &w), "witness ∈ ≥0");
                assert!(!recursive::contains(&g, &one_plus, &w), "witness ∉ ≥1");
                assert_eq!(w, i.tuple(vec![]), "the empty list is the refutation");
            }
            other => panic!("≥0 ⊄ ≥1 must refute, not {other:?}"),
        }
    }

    #[test]
    fn tl01a_spread_arity_accept_lengths_only() {
        // "Spread-call arity accept": ≥2 Number against ≥2 of anything. Elements are
        // trivially compatible (Top on the right), so acceptance is carried by the
        // forced-boundary arity match alone — the lengths-only case (TL-01a).
        let mut i = Interner::new();
        let g = group(&[
            ("RN", repeat_body(num(), "RN", &mut i)),
            ("RT", repeat_body(Contract::Top, "RT", &mut i)),
        ]);
        let src = Contract::concat(
            [Contract::tuple(vec![num(), num()], &mut i), rec_ref("RN")],
            &mut i,
        );
        let tgt = Contract::concat(
            [
                Contract::tuple(vec![Contract::Top, Contract::Top], &mut i),
                rec_ref("RT"),
            ],
            &mut i,
        );
        let v = recursive::subcontract(&g, &src, &tgt, &mut i);
        assert!(matches!(v, Verdict::Proven), "arity ≥2 accept, got {v:?}");
    }

    #[test]
    fn tl21_uninhabited_position_guards_the_element_refutation() {
        // Tuple(Number, U) ⊑ Tuple(String, Top). Position 0 mismatches identically
        // in both rows, but the verdict turns on whether position 1 is inhabited:
        //   • U = Top  → a complete witness [num, ⋆] exists → Refuted.
        //   • U = ⊥    → the source is empty → the inclusion is vacuously true →
        //     Proven, NOT a positional refutation (the mismatch alone is
        //     insufficient — no complete source witness realizes that branch).
        let mut i = Interner::new();
        let g = empty_group();
        let inhabited = Contract::tuple(vec![num(), Contract::Top], &mut i);
        let target = Contract::tuple(vec![str_(), Contract::Top], &mut i);
        match recursive::subcontract(&g, &inhabited, &target, &mut i) {
            Verdict::Refuted(w) => {
                assert!(recursive::contains(&g, &inhabited, &w));
                assert!(!recursive::contains(&g, &target, &w));
            }
            other => panic!("inhabited position ⇒ Refuted, got {other:?}"),
        }
        let empty_pos = Contract::tuple(vec![num(), Contract::Bottom], &mut i);
        let v = recursive::subcontract(&g, &empty_pos, &target, &mut i);
        assert!(
            matches!(v, Verdict::Proven),
            "empty source ⊑ anything (guard), got {v:?}"
        );
    }
}

// ── §5: string boundary-state seams (TL-09) ──────────────────────────────────

mod seams {
    use crate::contract::grapheme::{Summary, concat_len_bound, count};

    /// UTF-16 units of a `&str`.
    fn u(s: &str) -> Vec<u16> {
        s.encode_utf16().collect()
    }
    /// The exact composed grapheme count of two literals, through the summary.
    fn seam(a: &str, b: &str) -> usize {
        Summary::of_literal(&u(a)).compose(&Summary::of_literal(&u(b))).count
    }
    fn delta(a: &str, b: &str) -> isize {
        Summary::of_literal(&u(a)).seam_delta(&Summary::of_literal(&u(b)))
    }

    // The five TL-09 boundary characters (round 1) + the round-2 flagship.
    const WOMAN: &str = "\u{1F469}";
    const GIRL: &str = "\u{1F467}";
    const ZWJ: &str = "\u{200D}";
    const RI_A: &str = "\u{1F1E6}";
    const RI_B: &str = "\u{1F1E7}";
    const RI_C: &str = "\u{1F1E8}";
    const ACUTE: &str = "\u{0301}"; // combining acute accent
    const HANGUL_L: &str = "\u{1100}"; // choseong kiyeok
    const HANGUL_V: &str = "\u{1161}"; // jungseong a

    #[test]
    fn tl09_leading_zwj_flagship_merges_by_two() {
        // 👩 ++ ‍👩‍👧  →  👩‍👩‍👧 : 1 + 2 → 1. The seam merges by TWO — the counterexample
        // that retired the unsound `−1` interval.
        let woman = WOMAN;
        let zwj_family = format!("{ZWJ}{WOMAN}{ZWJ}{GIRL}");
        assert_eq!(count(&u(woman)), 1, "👩 is one grapheme");
        assert_eq!(count(&u(&zwj_family)), 2, "‍👩‍👧 (leading ZWJ) is two graphemes");
        assert_eq!(seam(woman, &zwj_family), 1, "the whole join is one family cluster");
        assert_eq!(delta(woman, &zwj_family), -2, "seam delta below −1 (the retired interval)");
        // The right operand is fully absorbed: count(a++b) = 1 < count(b) = 2. The
        // left count is a floor, the right count is not.
        assert!(seam(woman, &zwj_family) < count(&u(&zwj_family)));
        assert!(seam(woman, &zwj_family) >= count(&u(woman)));
    }

    #[test]
    fn tl09_regional_indicator_pairing_and_parity() {
        // A flag is a pair of regional indicators: 🇦 ++ 🇧 → 🇦🇧 (1), delta −1. But an
        // already-even trailing run does NOT pair with the next: 🇦🇧 ++ 🇨 → [🇦🇧][🇨]
        // (2), delta 0. Parity, not a fixed constant.
        assert_eq!(seam(RI_A, RI_B), 1, "two RIs form one flag");
        assert_eq!(delta(RI_A, RI_B), -1);
        let flag_ab = format!("{RI_A}{RI_B}");
        assert_eq!(count(&u(&flag_ab)), 1);
        assert_eq!(seam(&flag_ab, RI_C), 2, "even run leaves the next RI unpaired");
        assert_eq!(delta(&flag_ab, RI_C), 0);
    }

    #[test]
    fn tl09_combining_mark_and_hangul_merge() {
        // A base + a following combining mark is one cluster: e ++ ´ → é (1), delta −1.
        assert_eq!(seam("e", ACUTE), 1, "base + combining acute is one grapheme");
        assert_eq!(delta("e", ACUTE), -1);
        // Hangul L + V compose one syllable block (GB6): delta −1.
        assert_eq!(seam(HANGUL_L, HANGUL_V), 1, "L + V is one syllable cluster");
        assert_eq!(delta(HANGUL_L, HANGUL_V), -1);
    }

    #[test]
    fn tl09_ascii_and_empty_are_exact_and_seamless() {
        // No cross-seam interaction for plain text.
        assert_eq!(seam("ab", "cd"), 4);
        assert_eq!(delta("ab", "cd"), 0);
        // "" + s is exactly count(s) (the proven-zero case, 0.1.1).
        let s = format!("{WOMAN}{ZWJ}{WOMAN}{ZWJ}{GIRL}");
        assert_eq!(seam("", &s), count(&u(&s)));
        assert_eq!(delta("", &s), 0);
        assert_eq!(seam(&s, ""), count(&u(&s)));
    }

    #[test]
    fn seam_composition_is_exact_and_associative_over_the_corpus() {
        // The mandated soundness cross-check: over a generated corpus of
        // boundary-relevant fragments, summary composition reproduces direct
        // segmentation, and the merges-only bounds hold. Property testing here is a
        // cross-check on the segmenter-owned seam, never the proof.
        let flag = format!("{RI_A}{RI_B}");
        let family = format!("{ZWJ}{WOMAN}{ZWJ}{GIRL}");
        let corpus = ["", "a", "ab", WOMAN, GIRL, ZWJ, RI_A, RI_B, RI_C, ACUTE, HANGUL_L, HANGUL_V, &flag, &family];
        for a in corpus {
            for b in corpus {
                let sa = Summary::of_literal(&u(a));
                let sb = Summary::of_literal(&u(b));
                let composed = sa.compose(&sb);
                let joined = format!("{a}{b}");
                // Exact for literal–literal.
                assert_eq!(composed.count, count(&u(&joined)), "compose exact for {a:?}++{b:?}");
                // Merges-only, asymmetric floor: count(a) ≤ count(a++b) ≤ count(a)+count(b).
                let (ca, cb, cj) = (sa.count, sb.count, composed.count);
                assert!(cj <= ca + cb, "no split: {a:?}++{b:?}");
                assert!(cj >= ca, "left count is the floor: {a:?}++{b:?}");
                // Associativity: (a·b)·c == a·(b·c) on counts, spot-checked with `a`.
                let via_left = sa.compose(&sb).compose(&Summary::of_literal(&u("a")));
                let via_right = sa.compose(&sb.compose(&Summary::of_literal(&u("a"))));
                assert_eq!(via_left.count, via_right.count, "associative on {a:?}++{b:?}++'a'");
            }
        }
    }

    #[test]
    fn concat_len_bound_is_the_sound_merges_only_envelope() {
        // The analyzer fallback for abstract operands: [max(lo), sum(hi)].
        assert_eq!(concat_len_bound((2, Some(3)), (1, Some(4))), (2, Some(7)));
        // An unbounded operand keeps the upper open, but the floor is the larger lo.
        assert_eq!(concat_len_bound((5, None), (2, Some(9))), (5, None));
        // Every literal seam in a small corpus lands inside its own bound.
        for a in ["", WOMAN, RI_A, "ab"] {
            for b in ["", GIRL, RI_B, "cd"] {
                let (ca, cb) = (count(&u(a)), count(&u(b)));
                let (lo, hi) = concat_len_bound((ca, Some(ca)), (cb, Some(cb)));
                let actual = seam(a, b);
                assert!(lo <= actual && actual <= hi.unwrap(), "{a:?}++{b:?} in bound");
            }
        }
    }
}
