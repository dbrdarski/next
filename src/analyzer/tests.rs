//! Analyzer conformance: the §6 trap↔error concordance, brute-tested against the
//! oracle (the truth source). Closed expressions give an *exact* concordance
//! (`oracle traps ⇔ analyzer errors`, classes agree); open expressions test the
//! soundness direction (`accepted ⇒ oracle never traps` over sampled inputs).

use super::*;
use crate::ast::{AccessForm, BindingRef, Element, Expr, Field, PrimOp, Ref, TemplatePart};
use crate::oracle::eval_expr;
use crate::rational::Rational;

fn afield(target: Expr, field: &str, total: bool) -> Expr {
    Expr::Access { target: Box::new(target), form: AccessForm::Field(field.into()), total }
}
fn aindex(target: Expr, idx: Expr, total: bool) -> Expr {
    Expr::Access { target: Box::new(target), form: AccessForm::Index(Box::new(idx)), total }
}

fn konst(v: ValueRef) -> Expr {
    Expr::Const(v)
}
fn prim(op: PrimOp, args: Vec<Expr>) -> Expr {
    Expr::PrimOp { op, args }
}
fn name(n: &str) -> Expr {
    Expr::Ref(Ref::Immutable(BindingRef::Name(n.into())))
}

fn empty() -> TypeEnv {
    TypeEnv::new()
}

#[test]
fn constant_folding_produces_exact_contract() {
    let mut i = Interner::new();
    // (1 + 2) * 4 == 12
    let e = prim(
        PrimOp::Mul,
        vec![
            prim(PrimOp::Add, vec![konst(i.integer(1)), konst(i.integer(2))]),
            konst(i.integer(4)),
        ],
    );
    let a = analyze(&e, &empty(), &mut i);
    assert!(a.accepted());
    assert_eq!(a.contract, Contract::Equals(i.integer(12)));
}

#[test]
fn closed_type_error_is_operation_safety() {
    let mut i = Interner::new();
    // 1 + "x" traps operation-safety.
    let hello = i.string("x");
    let e = prim(PrimOp::Add, vec![konst(i.integer(1)), konst(hello)]);
    let a = analyze(&e, &empty(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::OperationSafety);
    assert_eq!(a.findings[0].severity, Severity::Error);
}

#[test]
fn division_is_total_but_comparison_forces_the_indeterminate() {
    let mut i = Interner::new();
    // 1 / 0 alone is safe (produces Indeterminate).
    let div = prim(PrimOp::Div, vec![konst(i.integer(1)), konst(i.integer(0))]);
    assert!(analyze(&div, &empty(), &mut i).accepted());

    // (1 / 0) < 2 traps undischarged-Indeterminate.
    let cmp = prim(PrimOp::Lt, vec![div.clone(), konst(i.integer(2))]);
    let a = analyze(&cmp, &empty(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::UndischargedIndeterminate);
}

#[test]
fn zero_to_negative_power_traps() {
    let mut i = Interner::new();
    // 0 ^ -1 traps; but (2+3) ^ -1 is safe (base folds to a nonzero 5).
    let bad = prim(PrimOp::Pow, vec![konst(i.integer(0)), konst(i.integer(-1))]);
    assert!(!analyze(&bad, &empty(), &mut i).accepted());

    let five = prim(PrimOp::Add, vec![konst(i.integer(2)), konst(i.integer(3))]);
    let ok = prim(PrimOp::Pow, vec![five, konst(i.integer(-1))]);
    let a = analyze(&ok, &empty(), &mut i);
    assert!(a.accepted(), "5^-1 = 1/5 must not be flagged, got {:?}", a.findings);
    assert_eq!(a.contract, Contract::Equals(i.number(Rational::new(1.into(), 5.into()))));
}

#[test]
fn unbound_reference_is_flagged() {
    let mut i = Interner::new();
    let a = analyze(&name("nope"), &empty(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::UnboundEvaluation);
}

/// Build a spread of closed expressions covering the pure fragment and every
/// arithmetic/ordering shape, including the trap-inducing ones.
#[allow(clippy::vec_init_then_push)] // sequential build with interleaved bindings
fn closed_corpus(i: &mut Interner) -> Vec<Expr> {
    let n = |i: &mut Interner, v: i64| konst(i.integer(v));
    let s = |i: &mut Interner, t: &str| konst(i.string(t));
    let b = |i: &mut Interner, v: bool| konst(i.boolean(v));

    let mut c = Vec::new();
    // Well-typed arithmetic.
    c.push(prim(PrimOp::Add, vec![n(i, 3), n(i, 4)]));
    c.push(prim(PrimOp::Sub, vec![n(i, 3), n(i, 10)]));
    c.push(prim(PrimOp::Mul, vec![n(i, -2), n(i, 6)]));
    c.push(prim(PrimOp::Div, vec![n(i, 7), n(i, 2)]));
    c.push(prim(PrimOp::Rem, vec![n(i, 7), n(i, 3)]));
    c.push(prim(PrimOp::Pow, vec![n(i, 2), n(i, 5)]));
    c.push(prim(PrimOp::Neg, vec![n(i, 9)]));
    // String concatenation.
    let (l, r) = (s(i, "a"), s(i, "b"));
    c.push(prim(PrimOp::Add, vec![l, r]));
    // Comparisons and equality.
    c.push(prim(PrimOp::Lt, vec![n(i, 1), n(i, 2)]));
    c.push(prim(PrimOp::Ge, vec![n(i, 5), n(i, 5)]));
    let (x, y) = (n(i, 1), s(i, "z"));
    c.push(prim(PrimOp::Eq, vec![x, y])); // cross-kind == is fine (false)
    // Totality: division by zero, alone (safe) and forced (trap).
    c.push(prim(PrimOp::Div, vec![n(i, 1), n(i, 0)]));
    c.push(prim(PrimOp::Div, vec![n(i, 0), n(i, 0)]));
    let dz = prim(PrimOp::Div, vec![n(i, 1), n(i, 0)]);
    c.push(prim(PrimOp::Lt, vec![dz.clone(), n(i, 2)])); // trap: undischarged Indeterminate
    let dz2 = prim(PrimOp::Div, vec![n(i, 1), n(i, 0)]);
    c.push(prim(PrimOp::Add, vec![dz2, n(i, 2)])); // safe: Indeterminate propagates
    // Type errors.
    let (p, q) = (n(i, 1), s(i, "x"));
    c.push(prim(PrimOp::Add, vec![p, q])); // trap
    let bt = b(i, true);
    c.push(prim(PrimOp::Mul, vec![bt, n(i, 3)])); // trap
    let st = s(i, "s");
    c.push(prim(PrimOp::Lt, vec![st, n(i, 3)])); // trap
    // 0 ^ negative.
    c.push(prim(PrimOp::Pow, vec![n(i, 0), n(i, -2)])); // trap
    // Non-integer exponent.
    let half = konst(i.number(Rational::new(1.into(), 2.into())));
    c.push(prim(PrimOp::Pow, vec![n(i, 4), half])); // trap
    // Nesting and constructors.
    c.push(prim(PrimOp::Add, vec![prim(PrimOp::Mul, vec![n(i, 2), n(i, 3)]), n(i, 4)]));
    let (t1, t2) = (n(i, 1), prim(PrimOp::Add, vec![n(i, 2), s(i, "!")])); // trap inside tuple
    c.push(Expr::TupleCons(vec![Element::Expr(t1), Element::Expr(t2)]));
    let good = prim(PrimOp::Add, vec![n(i, 1), n(i, 2)]);
    c.push(Expr::RecordCons(vec![Field::Field { key: "k".into(), value: good }]));
    // Templates: a printable interpolation, and a structure interpolation (trap).
    let printable = prim(PrimOp::Add, vec![n(i, 1), n(i, 2)]);
    c.push(Expr::Template(vec![
        TemplatePart::Segment("v=".into()),
        TemplatePart::Interp(printable),
    ]));
    let structure = Expr::TupleCons(vec![Element::Expr(n(i, 1)), Element::Expr(n(i, 2))]);
    c.push(Expr::Template(vec![TemplatePart::Interp(structure)])); // trap: unprintable

    // Access (E6), closed → exact fold against the oracle.
    let field_v = i.integer(7);
    let rec = konst(i.record_str(vec![("a", field_v)]));
    c.push(afield(rec.clone(), "a", false)); // present → 7
    c.push(afield(rec.clone(), "b", false)); // trap: absent-field
    c.push(afield(rec.clone(), "b", true)); // ?. → null (safe)
    c.push(afield(konst(i.null()), "a", false)); // trap: null-receiver
    c.push(afield(konst(i.null()), "a", true)); // ?. → null (safe)
    let ten = i.integer(10);
    let twenty = i.integer(20);
    let tup = konst(i.tuple(vec![ten, twenty]));
    c.push(aindex(tup.clone(), n(i, 0), false)); // in bounds → 10
    c.push(aindex(tup.clone(), n(i, 5), false)); // trap: index-bounds
    c.push(aindex(tup.clone(), n(i, 5), true)); // ?. → null (safe)
    c.push(aindex(tup, n(i, -1), false)); // from-end → 20 (safe)
    c
}

#[test]
fn closed_expression_concordance() {
    // For every closed expression: the oracle traps ⇔ the analyzer errors, and
    // when both, the class agrees. This is the §6 concordance, exact.
    let mut i = Interner::new();
    let corpus = closed_corpus(&mut i);
    for e in &corpus {
        let analysis = analyze(e, &empty(), &mut i);
        let oracle = eval_expr(e, &mut i);
        match oracle {
            Err(trap) => {
                assert!(!analysis.accepted(), "oracle traps but analyzer accepts: {e:?}");
                let err = analysis
                    .findings
                    .iter()
                    .find(|f| f.severity == Severity::Error)
                    .expect("an error finding");
                assert_eq!(err.class, trap.class, "class mismatch for {e:?}");
            }
            Ok(_) => assert!(
                analysis.accepted(),
                "oracle produces a value but analyzer rejects {e:?}: {:?}",
                analysis.findings,
            ),
        }
    }
}

#[test]
fn template_structure_interpolation_is_rejected() {
    let mut i = Interner::new();
    // `{ (1, 2) }` interpolates a tuple → E11 trap-until-ruled, an error.
    let tuple = Expr::TupleCons(vec![Element::Expr(konst(i.integer(1)))]);
    let t = Expr::Template(vec![TemplatePart::Interp(tuple)]);
    let a = analyze(&t, &empty(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::UnprintableInterpolation);
    assert_eq!(a.findings[0].severity, Severity::Error);
}

#[test]
fn template_unknown_interpolation_warns_not_rejects() {
    let mut i = Interner::new();
    // An unconstrained `x` might or might not be printable → warning, still accepted.
    let mut env = TypeEnv::new();
    env.insert("x".into(), Contract::Top);
    let t = Expr::Template(vec![TemplatePart::Interp(name("x"))]);
    let a = analyze(&t, &env, &mut i);
    assert!(a.accepted(), "unknown printability is a warning, not a rejection");
    assert_eq!(a.findings[0].severity, Severity::Warning);
    assert_eq!(a.findings[0].class, TrapClass::UnprintableInterpolation);
}

#[test]
fn open_field_access_reasoning() {
    let mut i = Interner::new();
    let mut env = TypeEnv::new();
    env.insert(
        "r".into(),
        Contract::Record(vec![("a".into(), Contract::Kind(Kind::Number))]),
    );

    // r.a where r : Record({a: Number}) — accepted, output is Number.
    let a = analyze(&afield(name("r"), "a", false), &env, &mut i);
    assert!(a.accepted());
    assert_eq!(a.contract, Contract::Kind(Kind::Number));

    // r.b (absent from an exact record) — rejected, absent-field.
    let a = analyze(&afield(name("r"), "b", false), &env, &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::AbsentField);

    // null.a — rejected, null-receiver.
    let mut nenv = TypeEnv::new();
    nenv.insert("r".into(), Contract::Kind(Kind::Null));
    let a = analyze(&afield(name("r"), "a", false), &nenv, &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::NullReceiver);

    // r?.b on an unknown receiver — total form never traps.
    let mut tenv = TypeEnv::new();
    tenv.insert("r".into(), Contract::Top);
    let a = analyze(&afield(name("r"), "b", true), &tenv, &mut i);
    assert!(a.accepted() && a.findings.is_empty());

    // r.b on an unknown receiver (demand form) — a warning, not a rejection.
    let a = analyze(&afield(name("r"), "b", false), &tenv, &mut i);
    assert!(a.accepted());
    assert_eq!(a.findings[0].severity, Severity::Warning);
}

#[test]
fn open_expression_soundness() {
    // With a variable ranging over a contract, an *accepted* expression must never
    // trap for any concrete value the contract admits (soundness direction of §6).
    let mut i = Interner::new();

    // Cases: (expr over `x`, contract for x, sample values for x).
    let checks: Vec<(Expr, Contract, Vec<ValueRef>)> = vec![
        // x + 1 with x : Number — accepted, never traps.
        (
            prim(PrimOp::Add, vec![name("x"), konst(i.integer(1))]),
            Contract::Kind(crate::contract::Kind::Number),
            vec![i.integer(0), i.integer(-4), i.number(Rational::new(1.into(), 2.into()))],
        ),
        // x < 10 with x : [0,5] — accepted, never traps.
        (
            prim(PrimOp::Lt, vec![name("x"), konst(i.integer(10))]),
            Contract::Range(Rational::from(0), Rational::from(5)),
            vec![i.integer(0), i.integer(3), i.integer(5)],
        ),
        // x / 2 with x : Number — total, accepted.
        (
            prim(PrimOp::Div, vec![name("x"), konst(i.integer(2))]),
            Contract::Kind(crate::contract::Kind::Number),
            vec![i.integer(9), i.integer(0)],
        ),
    ];

    for (expr, contract, values) in &checks {
        let mut env = TypeEnv::new();
        env.insert("x".into(), contract.clone());
        let analysis = analyze(expr, &env, &mut i);
        if analysis.accepted() {
            for v in values {
                let concrete = substitute(expr, v);
                assert!(
                    eval_expr(&concrete, &mut i).is_ok(),
                    "UNSOUND: accepted {expr:?} traps on x = {v:?}",
                );
            }
        }
    }
}

/// Replace every `Ref(x)` occurrence with a constant — a tiny substitution so the
/// oracle can evaluate an open expression at a concrete value.
fn substitute(expr: &Expr, v: &ValueRef) -> Expr {
    match expr {
        Expr::Ref(Ref::Immutable(BindingRef::Name(_))) => Expr::Const(v.clone()),
        Expr::PrimOp { op, args } => Expr::PrimOp {
            op: *op,
            args: args.iter().map(|a| substitute(a, v)).collect(),
        },
        other => other.clone(),
    }
}
