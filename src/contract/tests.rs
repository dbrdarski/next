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
