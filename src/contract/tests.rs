//! Denotational membership brute-tested against the oracle's values (Part I:
//! per-pair contract rules checked against the truth source).

use super::*;
use crate::interner::Interner;

fn n(i: &mut Interner, v: i64) -> ValueRef {
    i.integer(v)
}
fn rat(num: i64, den: i64) -> Rational {
    Rational::new(BigInt::from(num), BigInt::from(den))
}
fn r(x: i64) -> Rational {
    Rational::from(x)
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
    // Indeterminate is not any Kind
    let ind = i.indeterminate(crate::value::IndetForm::DivByZero);
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
    let ne = Contract::Difference(Box::new(Contract::Top), Box::new(Contract::Equals(five)));
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
    let lz = Contract::Intersection(
        Box::new(Contract::Greater(r(10))),
        Box::new(Contract::LessEq(r(20))),
    );
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
    let u = Contract::Union(Box::new(small.clone()), Box::new(big.clone()));
    assert!(u.contains(&i.integer(5)));
    assert!(u.contains(&i.integer(150)));
    assert!(!u.contains(&i.integer(50)));

    // Difference(Range(0,10), Equals(5)) — a hole
    let hole = Contract::Difference(Box::new(small), Box::new(Contract::Equals(i.integer(5))));
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
    let exact = Contract::Record(vec![
        ("age".into(), Contract::Range(r(0), r(120))),
        ("name".into(), Contract::Kind(Kind::String)),
    ]);
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
    let tc = Contract::Tuple(vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::String)]);
    assert!(tc.contains(&t));
    let wrong = i.tuple(vec![one]);
    assert!(!tc.contains(&wrong)); // length mismatch
}

#[test]
fn indeterminate_contract() {
    use crate::value::IndetForm;
    let mut i = Interner::new();
    let div0 = i.indeterminate(IndetForm::DivByZero);
    assert!(Contract::Indeterminate(IndetForm::DivByZero).contains(&div0));
    assert!(!Contract::Indeterminate(IndetForm::ZeroOverZero).contains(&div0));
    assert!(!Contract::Indeterminate(IndetForm::DivByZero).contains(&i.integer(5)));
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
    proven(&Contract::Range(r(0), r(10)), &Contract::Range(r(0), r(100)), &mut i);
    refuted(&Contract::Range(r(0), r(100)), &Contract::Range(r(0), r(10)), &mut i);
    proven(&Contract::Range(r(0), r(10)), &Contract::Kind(Kind::Number), &mut i);
    proven(&Contract::Greater(r(5)), &Contract::GreaterEq(r(5)), &mut i);
    refuted(&Contract::GreaterEq(r(5)), &Contract::Greater(r(5)), &mut i);
    // landing zone (10, 20] ⊑ [10, 20] (dense rationals: not ⊑ [11, 20]).
    let lz = Contract::Intersection(
        Box::new(Contract::Greater(r(10))),
        Box::new(Contract::LessEq(r(20))),
    );
    proven(&lz, &Contract::Range(r(10), r(20)), &mut i);
    refuted(&lz, &Contract::Range(r(11), r(20)), &mut i); // 10.5 witnesses the gap
}

#[test]
fn subcontract_equals_and_kind() {
    let mut i = Interner::new();
    let five = i.integer(5);
    proven(&Contract::Equals(five.clone()), &Contract::Range(r(0), r(10)), &mut i);
    let fifty = i.integer(50);
    refuted(&Contract::Equals(fifty), &Contract::Range(r(0), r(10)), &mut i);
    proven(&Contract::Kind(Kind::Number), &Contract::Top, &mut i);
    refuted(&Contract::Kind(Kind::Number), &Contract::Kind(Kind::String), &mut i);
    proven(&Contract::Bottom, &Contract::Kind(Kind::String), &mut i);
}

#[test]
fn subcontract_union_and_mod() {
    let mut i = Interner::new();
    let split = Contract::Union(
        Box::new(Contract::Range(r(0), r(5))),
        Box::new(Contract::Range(r(6), r(10))),
    );
    proven(&split, &Contract::Range(r(0), r(10)), &mut i);
    // multiples of 4 ⊑ evens; evens ⋢ multiples of 4
    let mult4 = Contract::Mod { n: BigInt::from(4), r: BigInt::from(0) };
    let even = Contract::Mod { n: BigInt::from(2), r: BigInt::from(0) };
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
        Contract::Mod { n: BigInt::from(2), r: BigInt::from(0) },
        Contract::Mod { n: BigInt::from(4), r: BigInt::from(0) },
        Contract::Union(Box::new(Contract::Range(r(0), r(5))), Box::new(Contract::Range(r(6), r(10)))),
        Contract::Intersection(Box::new(Contract::Range(r(0), r(20))), Box::new(Contract::Greater(r(5)))),
        Contract::Difference(Box::new(Contract::Range(r(0), r(10))), Box::new(Contract::Equals(i.integer(5)))),
        Contract::HasField("age".into()),
        Contract::Kind(Kind::Tuple),
        Contract::Kind(Kind::Record),
        Contract::Tuple(vec![Contract::Kind(Kind::Number)]),
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
        Contract::Record(vec![("a".into(), Contract::Kind(Kind::Number))]),
        Contract::Record(vec![("b".into(), Contract::Kind(Kind::Number))]),
        Contract::Tuple(vec![Contract::Kind(Kind::Number)]),
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
    // Division by a range spanning zero is *safe* (total) but the image includes
    // Indeterminate values.
    let a = Contract::Kind(Kind::Number);
    let b = Contract::Range(r(0), r(10));
    let res = analyze_operation(PrimOp::Div, &[a, b], &mut i);
    assert!(matches!(res.safety, OpSafety::Proven), "division never traps");
    let one_over_zero = eval_prim(PrimOp::Div, &[i.integer(1), i.integer(0)], &mut i).unwrap();
    assert!(res.output.contains(&one_over_zero), "output must cover 1/0 = _/0");
    // A nonzero divisor drops the Indeterminate from the image.
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
fn operation_soundness_sweep() {
    // Brute-force every operation over a grid of input contracts against the
    // oracle (`eval_prim`): the output must over-approximate the true image, a
    // `Proven` safety must never trap, and a `Refuted` witness must trap.
    let mut i = Interner::new();

    let inputs = vec![
        Contract::Top,
        Contract::Kind(Kind::Number),
        Contract::Kind(Kind::String),
        Contract::Kind(Kind::Boolean),
        Contract::Range(r(0), r(10)),
        Contract::Range(r(-5), r(5)),
        Contract::Greater(r(0)),
        Contract::Equals(i.integer(0)),
        Contract::Indeterminate(crate::value::IndetForm::DivByZero),
    ];

    let mut pool: Vec<ValueRef> = Vec::new();
    for v in [-5, -2, 0, 1, 2, 3, 7, 10, 100] {
        pool.push(i.integer(v));
    }
    pool.push(i.number(rat(1, 2)));
    pool.push(i.string("a"));
    pool.push(i.boolean(true));
    pool.push(i.null());
    pool.push(i.indeterminate(crate::value::IndetForm::DivByZero));
    pool.push(i.indeterminate(crate::value::IndetForm::ZeroOverZero));

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
    fn record(fields: &[(&str, Contract)]) -> Contract {
        Contract::Record(fields.iter().map(|(k, c)| (k.to_string(), c.clone())).collect())
    }
    fn union(a: Contract, b: Contract) -> Contract {
        Contract::Union(Box::new(a), Box::new(b))
    }
    fn group(defs: &[(&str, Contract)]) -> RecGroup {
        RecGroup::new(defs.iter().map(|(n, c)| (n.to_string(), c.clone())))
    }

    #[test]
    fn rc09_negative_occurrence_rejected() {
        // Bad = Difference(Top, Bad) — antitone, no least fixpoint.
        let g = group(&[(
            "Bad",
            Contract::Difference(Box::new(Contract::Top), Box::new(rec_ref("Bad"))),
        )]);
        assert_eq!(
            recursive::admissible(&g),
            Err(recursive::DefError::NegativeOccurrence { name: "Bad".into() }),
        );
    }

    #[test]
    fn rc10_unguarded_recursion_rejected() {
        // R = R
        let g1 = group(&[("R", rec_ref("R"))]);
        assert!(matches!(
            recursive::admissible(&g1),
            Err(recursive::DefError::Unguarded { .. })
        ));
        // R = Union(Number, R) — denotes Number; hint says so.
        let g2 = group(&[("R", union(Contract::Kind(Kind::Number), rec_ref("R")))]);
        match recursive::admissible(&g2) {
            Err(recursive::DefError::Unguarded { hint, .. }) => assert!(hint.contains("denotes")),
            other => panic!("expected unguarded, got {other:?}"),
        }
    }

    #[test]
    fn guarded_group_is_admissible() {
        // List = Union(Null, Record({head: Number, tail: List})) — references are
        // guarded beneath the Record.
        let g = group(&[(
            "List",
            union(
                Contract::Kind(Kind::Null),
                record(&[("head", Contract::Kind(Kind::Number)), ("tail", rec_ref("List"))]),
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
                record(&[("head", Contract::Kind(Kind::Number)), ("tail", rec_ref("List"))]),
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
        let g = group(&[("R", record(&[("next", rec_ref("R"))]))]);
        assert!(recursive::admissible(&g).is_ok());
        let v = recursive::subcontract(&g, &rec_ref("R"), &Contract::Kind(Kind::Number), &mut i);
        assert!(matches!(v, Verdict::Proven), "empty source ⊑ anything, got {v:?}");
    }

    #[test]
    fn rc12_mutual_productivity() {
        // A = Record({b: B}); B = Union(Null, Record({a: A})). Both inhabited: B
        // via Null, then A via {b: null}.
        let mut i = Interner::new();
        let g = group(&[
            ("A", record(&[("b", rec_ref("B"))])),
            ("B", union(Contract::Kind(Kind::Null), record(&[("a", rec_ref("A"))]))),
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
            ("A", record(&[("b", rec_ref("B"))])),
            ("B", record(&[("a", rec_ref("A"))])),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        assert!(matches!(e["A"], recursive::Emptiness::Empty));
        assert!(matches!(e["B"], recursive::Emptiness::Empty));
    }

    /// `Repeat(E)` — a flat sequence, derived from Concat (tuple family §1):
    /// `R = Union(Tuple(), Concat(Tuple(E), R))`.
    fn repeat_group(name: &str, element: Contract) -> RecGroup {
        let body = union(
            Contract::Tuple(vec![]),
            Contract::concat([Contract::Tuple(vec![element]), rec_ref(name)]),
        );
        group(&[(name, body)])
    }

    /// Merge two groups so both `Repeat`s are comparable in one namespace.
    fn merge(a: RecGroup, b: RecGroup) -> RecGroup {
        RecGroup::new(a.defs.into_iter().chain(b.defs))
    }

    #[test]
    fn concat_guardedness_admits_repeat() {
        // The recursive segment is guarded by a sibling of proven minimum extent 1.
        let g = repeat_group("R", Contract::Kind(Kind::Number));
        assert_eq!(recursive::admissible(&g), Ok(()));

        // With no consuming sibling, the same shape is unguarded and rejected.
        let bad = group(&[("U", Contract::concat([Contract::Kind(Kind::Tuple), rec_ref("U")]))]);
        assert!(matches!(recursive::admissible(&bad), Err(recursive::DefError::Unguarded { .. })));
    }

    #[test]
    fn concat_membership_splits_the_tuple() {
        let mut i = Interner::new();
        let g = repeat_group("R", Contract::Kind(Kind::Number));
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
            repeat_group("RN", Contract::Kind(Kind::Number)),
            repeat_group("RT", Contract::Top),
        );
        assert!(recursive::admissible(&g).is_ok());
        let v = recursive::subcontract(&g, &rec_ref("RN"), &rec_ref("RT"), &mut i);
        assert!(matches!(v, Verdict::Proven), "Repeat(Number) ⊑ Repeat(Top), got {v:?}");
    }

    #[test]
    fn rc18_repeat_mismatch_refuted_with_complete_witness() {
        // Repeat(Number) ⊄ Repeat(String) — refuted only with a *complete* finite
        // tuple witness (`[1]`), never a bare positional mismatch (§5.3).
        let mut i = Interner::new();
        let g = merge(
            repeat_group("RN", Contract::Kind(Kind::Number)),
            repeat_group("RS", Contract::Kind(Kind::String)),
        );
        assert!(recursive::admissible(&g).is_ok());
        match recursive::subcontract(&g, &rec_ref("RN"), &rec_ref("RS"), &mut i) {
            Verdict::Refuted(w) => {
                assert!(recursive::contains(&g, &rec_ref("RN"), &w), "witness ∈ Repeat(Number)");
                assert!(!recursive::contains(&g, &rec_ref("RS"), &w), "witness ∉ Repeat(String)");
                // A complete tuple, not a naked element.
                assert!(w.as_tuple().is_some(), "the witness is a whole tuple: {w:?}");
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
            ("A", record(&[("seq", rec_ref("B"))])),
            ("B", union(Contract::Tuple(vec![]), Contract::concat([Contract::Tuple(vec![rec_ref("A")]), rec_ref("B")]))),
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
                Contract::concat([Contract::Tuple(vec![Contract::Kind(Kind::Number)]), rec_ref("L")]),
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
        assert!(!matches!(v, Verdict::Proven), "L ⊑ Number must not prove, got {v:?}");

        // Control: a Concat cycle with no base really is empty.
        let dead = group(&[(
            "D",
            Contract::concat([Contract::Tuple(vec![Contract::Kind(Kind::Number)]), rec_ref("D")]),
        )]);
        assert!(recursive::admissible(&dead).is_ok());
        let e = recursive::emptiness(&dead, &mut i);
        assert!(matches!(e["D"], recursive::Emptiness::Empty), "got {:?}", e["D"]);
    }

    #[test]
    fn audit_equals_segment_membership() {
        // AUDIT S2 regression: an Equals segment in a Concat window was rejected
        // outright (membership false negative — the truth source must be exact).
        let mut i = Interner::new();
        let one = i.integer(1);
        let inner = i.tuple(vec![one]);
        let c = Contract::Concat(vec![
            Contract::Equals(inner),
            Contract::Tuple(vec![Contract::Kind(Kind::Number)]),
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
            union(Contract::Kind(Kind::Function), record(&[("next", rec_ref("L"))])),
        )]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        assert!(matches!(e["L"], recursive::Emptiness::Unproven), "got {:?}", e["L"]);
    }

    #[test]
    fn recursive_subcontract_progress_guarded() {
        // NumList ⊑ AnyList: number lists refine top-lists, proven by descending
        // through the Record `tail` and closing the revisited pair at greater depth.
        let mut i = Interner::new();
        let num_list = union(
            Contract::Kind(Kind::Null),
            record(&[("head", Contract::Kind(Kind::Number)), ("tail", rec_ref("NumList"))]),
        );
        let any_list = union(
            Contract::Kind(Kind::Null),
            record(&[("head", Contract::Top), ("tail", rec_ref("AnyList"))]),
        );
        let g = group(&[("NumList", num_list), ("AnyList", any_list)]);
        assert!(recursive::admissible(&g).is_ok());
        let v = recursive::subcontract(&g, &rec_ref("NumList"), &rec_ref("AnyList"), &mut i);
        assert!(matches!(v, Verdict::Proven), "NumList ⊑ AnyList, got {v:?}");
    }

    fn equals(i: &mut Interner, v: i64) -> Contract {
        Contract::Equals(i.integer(v))
    }
    fn intersection(a: Contract, b: Contract) -> Contract {
        Contract::Intersection(Box::new(a), Box::new(b))
    }

    #[test]
    fn rc14_recursive_intersection_nonempty() {
        // A = Union(Equals(1), Record({next: A})); B = Union(Equals(1), Record({next: B})).
        // They share the base `1`, so the intersection is inhabited by `1`.
        let mut i = Interner::new();
        let one = equals(&mut i, 1);
        let g = group(&[
            ("A", union(one.clone(), record(&[("next", rec_ref("A"))]))),
            ("B", union(one, record(&[("next", rec_ref("B"))]))),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        // Add the intersection as a member so emptiness reports on it.
        let g2 = group(&[
            ("A", g.defs["A"].clone()),
            ("B", g.defs["B"].clone()),
            ("AB", intersection(rec_ref("A"), rec_ref("B"))),
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
            ("A", union(one, record(&[("next", rec_ref("A"))]))),
            ("B", union(two, record(&[("next", rec_ref("B"))]))),
            ("AB", intersection(rec_ref("A"), rec_ref("B"))),
        ]);
        assert!(recursive::admissible(&g).is_ok());
        let e = recursive::emptiness(&g, &mut i);
        // A and B are individually inhabited, but their intersection is empty.
        assert!(matches!(e["A"], recursive::Emptiness::NonEmpty(_)));
        assert!(matches!(e["B"], recursive::Emptiness::NonEmpty(_)));
        assert!(matches!(e["AB"], recursive::Emptiness::Empty), "got {:?}", e["AB"]);
    }

    #[test]
    fn recursive_subcontract_refuted_with_witness() {
        // NumList ⊄ StringList: a number-list like [1] inhabits NumList but not
        // StringList. §5.3 — the verdict is a witness, not a bare mismatch.
        let mut i = Interner::new();
        let num_list = union(
            Contract::Kind(Kind::Null),
            record(&[("head", Contract::Kind(Kind::Number)), ("tail", rec_ref("NumList"))]),
        );
        let str_list = union(
            Contract::Kind(Kind::Null),
            record(&[("head", Contract::Kind(Kind::String)), ("tail", rec_ref("StrList"))]),
        );
        let g = group(&[("NumList", num_list), ("StrList", str_list)]);
        assert!(recursive::admissible(&g).is_ok());
        match recursive::subcontract(&g, &rec_ref("NumList"), &rec_ref("StrList"), &mut i) {
            Verdict::Refuted(w) => {
                assert!(recursive::contains(&g, &rec_ref("NumList"), &w), "witness ∈ NumList");
                assert!(!recursive::contains(&g, &rec_ref("StrList"), &w), "witness ∉ StrList");
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
            record(&[("head", Contract::Kind(Kind::Number)), ("tail", rec_ref("NumList"))]),
        );
        let any_list = union(
            Contract::Kind(Kind::Null),
            record(&[("head", Contract::Top), ("tail", rec_ref("AnyList"))]),
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
    let num = || Contract::Kind(Kind::Number);
    let str_ = || Contract::Kind(Kind::String);
    let t = |e: Vec<Contract>| Contract::Tuple(e);

    // Nested Concats flatten associatively.
    let inner = Contract::concat([Contract::Kind(Kind::Tuple), Contract::Kind(Kind::Tuple)]);
    let flat = Contract::concat([inner, Contract::Kind(Kind::Tuple)]);
    assert_eq!(flat, Contract::Concat(vec![Contract::Kind(Kind::Tuple); 3]));

    // The empty-tuple segment erases (a structural fact).
    assert_eq!(Contract::concat([t(vec![]), Contract::Kind(Kind::Tuple)]), Contract::Kind(Kind::Tuple));
    // …and a Concat of nothing is the empty tuple.
    assert_eq!(Contract::concat([]), t(vec![]));
    assert_eq!(Contract::concat([t(vec![]), t(vec![])]), t(vec![]));

    // Adjacent exact segments fuse.
    assert_eq!(Contract::concat([t(vec![num()]), t(vec![str_()])]), t(vec![num(), str_()]));

    // An uninhabited segment NEVER erases — it empties the whole Concat (erasing
    // it would turn an empty contract into an inhabited one).
    assert_eq!(Contract::concat([Contract::Bottom, t(vec![num()])]), Contract::Bottom);
    assert_eq!(
        Contract::concat([t(vec![Contract::Bottom]), Contract::Kind(Kind::Tuple)]),
        Contract::Bottom,
    );

    // A single segment collapses to itself.
    assert_eq!(Contract::concat([t(vec![num()])]), t(vec![num()]));
}

#[test]
fn concat_membership_matches_denotation() {
    let mut i = Interner::new();
    // Concat(Tuple(Number), Tuple(String)) — fused to an exact 2-tuple.
    let c = Contract::concat([
        Contract::Tuple(vec![Contract::Kind(Kind::Number)]),
        Contract::Tuple(vec![Contract::Kind(Kind::String)]),
    ]);
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
        Contract::Kind(Kind::Tuple),
        Contract::Tuple(vec![Contract::Kind(Kind::Number)]),
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

        assert_eq!(eval_contract(&cref("Number"), &env), Some(Contract::Kind(Kind::Number)));
        assert_eq!(eval_contract(&cref("Top"), &env), Some(Contract::Top));
        assert_eq!(eval_contract(&cref("Bottom"), &env), Some(Contract::Bottom));

        // Range(0, 100)
        let range = ctor("Range", vec![Expr::Const(i.integer(0)), Expr::Const(i.integer(100))]);
        assert_eq!(eval_contract(&range, &env), Some(Contract::Range(r(0), r(100))));

        // Greater(5) / LessEq(9)
        let g = ctor("Greater", vec![Expr::Const(i.integer(5))]);
        assert_eq!(eval_contract(&g, &env), Some(Contract::Greater(r(5))));

        // Mod(2, 0) — the even integers
        let m = ctor("Mod", vec![Expr::Const(i.integer(2)), Expr::Const(i.integer(0))]);
        assert_eq!(eval_contract(&m, &env), Some(Contract::Mod { n: BigInt::from(2), r: BigInt::from(0) }));

        // Equals(7) and HasField("age")
        let five = i.integer(7);
        let eq = ctor("Equals", vec![Expr::Const(five.clone())]);
        assert_eq!(eval_contract(&eq, &env), Some(Contract::Equals(five)));
        let age = i.string("age");
        let hf = ctor("HasField", vec![Expr::Const(age)]);
        assert_eq!(eval_contract(&hf, &env), Some(Contract::HasField("age".into())));

        // An unknown bare name does not resolve.
        assert_eq!(eval_contract(&cref("Nope"), &env), None);
    }

    #[test]
    fn set_operations_and_structural_literals() {
        let mut i = Interner::new();
        let env = ContractEnv::new();

        // Union(Number, Null)
        let u = ctor("Union", vec![cref("Number"), cref("Null")]);
        assert_eq!(
            eval_contract(&u, &env),
            Some(Contract::Union(
                Box::new(Contract::Kind(Kind::Number)),
                Box::new(Contract::Kind(Kind::Null)),
            )),
        );

        // A tuple literal of contracts is a tuple contract: [Number, String]
        let t = Expr::TupleCons(vec![Element::Expr(cref("Number")), Element::Expr(cref("String"))]);
        assert_eq!(
            eval_contract(&t, &env),
            Some(Contract::Tuple(vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::String)])),
        );

        // A record literal of contracts is a record contract: { a: Number }
        let rec = Expr::RecordCons(vec![Field::Field { key: "a".into(), value: cref("Number") }]);
        assert_eq!(
            eval_contract(&rec, &env),
            Some(Contract::Record(vec![("a".into(), Contract::Kind(Kind::Number))])),
        );

        // A non-contract expression is not a contract.
        assert_eq!(eval_contract(&Expr::Const(i.integer(3)), &env), None);
    }

    #[test]
    fn named_contracts_resolve_and_compose() {
        // Percent = Range(0, 100);  Grade = Union(Percent, Null)
        let mut i = Interner::new();
        let percent = ctor("Range", vec![Expr::Const(i.integer(0)), Expr::Const(i.integer(100))]);
        let grade = ctor("Union", vec![cref("Percent"), cref("Null")]);
        let env = build_contract_env([("Percent", &percent), ("Grade", &grade)]);

        assert_eq!(env.get("Percent"), Some(&Contract::Range(r(0), r(100))));
        assert_eq!(
            env.get("Grade"),
            Some(&Contract::Union(
                Box::new(Contract::Range(r(0), r(100))),
                Box::new(Contract::Kind(Kind::Null)),
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
    use crate::contract::recursive::RecGroup;

    fn rec_ref(n: &str) -> Contract {
        Contract::Ref(n.into())
    }
    fn union(a: Contract, b: Contract) -> Contract {
        Contract::Union(Box::new(a), Box::new(b))
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
    fn repeat(name: &str, element: Contract) -> RecGroup {
        group(&[(
            name,
            union(
                Contract::Tuple(vec![]),
                Contract::concat([Contract::Tuple(vec![element]), rec_ref(name)]),
            ),
        )])
    }

    #[test]
    fn exact_shapes_are_exactly_counted() {
        let mut i = Interner::new();
        let g = empty_group();
        let num = || Contract::Kind(Kind::Number);

        // A proven-inhabited exact tuple: (Equals(k), Exact).
        let t = Contract::Tuple(vec![num(), num()]);
        assert_eq!(len(&g, &t, &mut i), crate::contract::Len { contract: eq(2), stamp: Stamp::Exact });

        // An exact record counts its fields.
        let rec = Contract::Record(vec![("a".into(), num()), ("b".into(), num())]);
        assert_eq!(len(&g, &rec, &mut i).contract, eq(2));

        // An uninhabited shape has NO realizable length: (Bottom, Exact) —
        // impossible shapes are never realizable lengths.
        let dead = Contract::Tuple(vec![num(), Contract::Bottom]);
        let l = len(&g, &dead, &mut i);
        assert_eq!(l.contract, Contract::Bottom);
        assert!(l.is_exact());

        // Concat sums segment lengths. A `GE` operand is outside the finite-exact
        // label boundary, so the sum coarsens to the minima and stamps Approx.
        let c = Contract::Concat(vec![
            Contract::Tuple(vec![num()]),
            Contract::Kind(Kind::Tuple),
        ]);
        let l = len(&g, &c, &mut i);
        assert_eq!(l.contract, ge(1), "one element, then any tail");
        assert_eq!(l.stamp, Stamp::Approx, "a coarsening rule forfeits the stamp");

        // Two finite exact segments sum exactly.
        let both = Contract::Concat(vec![
            Contract::Tuple(vec![num()]),
            Contract::Tuple(vec![num(), num()]),
        ]);
        assert_eq!(
            len(&g, &both, &mut i),
            crate::contract::Len { contract: eq(3), stamp: Stamp::Exact },
        );

        // Union takes the union of branch lengths, exactly.
        let u = union(Contract::Tuple(vec![num()]), Contract::Tuple(vec![num(), num()]));
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
        let g = repeat("R", Contract::Bottom);
        let l = len(&g, &rec_ref("R"), &mut i);
        assert!(l.is_exact(), "the length is exact, not approximate");
        assert!(l.contract.contains(&i.integer(0)));
        assert!(!l.contract.contains(&i.integer(1)), "no nonzero length is realizable");
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
                    Contract::Tuple(vec![]),
                    Contract::concat([Contract::Tuple(vec![e(), e()]), rec_ref("R")]),
                ),
                Contract::concat([Contract::Tuple(vec![e(), e(), e()]), rec_ref("R")]),
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
                    Contract::Tuple(vec![]),
                    Contract::concat([Contract::Tuple(vec![e()]), rec_ref("S")]),
                ),
            ),
            ("S", Contract::concat([Contract::Tuple(vec![e()]), rec_ref("R")])),
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
                Contract::Tuple(vec![]),
                Contract::concat([Contract::Tuple(vec![e()]), rec_ref("R"), rec_ref("R")]),
            ),
        )]);
        let l = len(&g, &rec_ref("R"), &mut i);
        assert_eq!(l.stamp, Stamp::Approx, "nonlinear alternatives forfeit exactness");
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
                Contract::Tuple(vec![]),
                Contract::concat([
                    union(Contract::Tuple(vec![e()]), rec_ref("R")),
                    Contract::Tuple(vec![e()]),
                ]),
            ),
        )]);
        assert!(recursive::admissible(&g).is_ok());
        let l = len(&g, &rec_ref("R"), &mut i); // must not overflow the stack
        assert_eq!(l.stamp, Stamp::Approx, "a nested own-SCC label declines exactness");
        assert!(l.contract.contains(&i.integer(0)), "soundness: 0 is realizable");

        // Control: a ref nested in a *tuple element* is arity-irrelevant and must
        // stay exact — N = Tuple(E, Ref N) is always a 2-tuple... but wait, that
        // group is empty (no base), so its length is Bottom. Use the inhabited
        // variant: N = Union(Null-free base) — a 2-tuple whose element nests N or
        // terminates.
        let g2 = group(&[(
            "N",
            union(
                Contract::Tuple(vec![e(), Contract::Kind(Kind::Null)]),
                Contract::Tuple(vec![e(), rec_ref("N")]),
            ),
        )]);
        assert!(recursive::admissible(&g2).is_ok());
        let l2 = len(&g2, &rec_ref("N"), &mut i);
        assert!(l2.is_exact(), "element-nested refs never affect arity: {l2:?}");
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
                    Contract::Tuple(vec![]),
                    Contract::concat([Contract::Tuple(vec![e()]), rec_ref("Many")]),
                ),
            ),
            (
                "R",
                union(
                    Contract::Tuple(vec![]),
                    Contract::concat([rec_ref("Many"), rec_ref("R")]),
                ),
            ),
        ]);
        let l = len(&g, &rec_ref("R"), &mut i);
        assert_eq!(l.stamp, Stamp::Approx, "an infinite increment language is not exact");
        // Still sound: every realizable length is admitted.
        for n in [0, 1, 2, 7] {
            assert!(l.contract.contains(&i.integer(n)));
        }
    }
}
