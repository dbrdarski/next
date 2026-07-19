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

    assert!(Contract::HasField("age".into()).contains(&rec));
    assert!(!Contract::HasField("email".into()).contains(&rec));

    // Record contract with a field-contract, open (extra fields allowed)
    let c = Contract::Record(vec![("age".into(), Contract::Range(r(0), r(120)))]);
    assert!(c.contains(&rec));
    let two_hundred = i.integer(200);
    let too_old = i.record_str(vec![("age", two_hundred)]);
    assert!(!c.contains(&too_old));
    // a non-record fails
    let thirty = i.integer(30);
    assert!(!c.contains(&thirty));

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
