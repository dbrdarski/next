//! Analyzer conformance: the §6 trap↔error concordance, brute-tested against the
//! oracle (the truth source). Closed expressions give an *exact* concordance
//! (`oracle traps ⇔ analyzer errors`, classes agree); open expressions test the
//! soundness direction (`accepted ⇒ oracle never traps` over sampled inputs).

use super::*;
use crate::ast::{
    AccessForm, ActKind, Arg, Arm, Bind, BindTarget, BindingRef, Element, Expr, Field, Lambda,
    Match, MatchItem, Pat, PatElem, PrimOp, Ref, TemplatePart,
};
use crate::oracle::{Outcome, eval_expr};
use crate::rational::Rational;

/// Evaluate a lambda expression to a concrete closure value.
fn closure(i: &mut Interner, params: Pat, body: Expr, act_kind: ActKind) -> ValueRef {
    let lam = Expr::Lambda(Lambda { params, body: Box::new(body), act_kind });
    match eval_expr(&lam, i) {
        Ok(Outcome::Produced(v)) => v,
        other => panic!("lambda did not produce a closure: {other:?}"),
    }
}
/// A one-parameter pattern `(x)` over the argument tuple.
fn one_param(name: &str) -> Pat {
    Pat::Tuple(vec![PatElem::Pat(Pat::Bind(name.into()))])
}
fn apply(callee: Expr, args: Vec<Expr>) -> Expr {
    Expr::Apply { callee: Box::new(callee), args: args.into_iter().map(Arg::Expr).collect() }
}

fn matchx(scrut: Option<Expr>, items: Vec<MatchItem>) -> Expr {
    Expr::Match(Match { scrutinee: scrut.map(Box::new), items })
}
fn arm(pattern: Option<Pat>, guard: Option<Expr>, result: Expr) -> MatchItem {
    MatchItem::Arm(Arm { pattern, guard, result })
}

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

    // Match (E9/E10), closed → exact against the oracle.
    let five = i.integer(5);
    c.push(matchx(Some(n(i, 5)), vec![arm(Some(Pat::Const(five)), None, n(i, 10))])); // → 10
    c.push(matchx(Some(n(i, 5)), vec![arm(Some(Pat::Wild), Some(n(i, 3)), n(i, 10))])); // tested-seat trap
    let one = i.integer(1);
    let nonexhaustive = matchx(Some(n(i, 5)), vec![arm(Some(Pat::Const(one)), None, n(i, 10))]);
    c.push(prim(PrimOp::Add, vec![nonexhaustive, n(i, 1)])); // expecting-seat trap
    let pair = Pat::Tuple(vec![
        PatElem::Pat(Pat::Bind("a".into())),
        PatElem::Pat(Pat::Bind("b".into())),
    ]);
    c.push(matchx(
        None,
        vec![MatchItem::Bind(Bind { target: BindTarget::Pattern(pair), value: n(i, 5), exported: false }), MatchItem::Stmt(name("a"))],
    )); // refuted-binding trap

    // Apply (C§7/B5), closed → exact against the oracle.
    let id = konst(closure(i, one_param("x"), name("x"), ActKind::Pure));
    c.push(apply(id.clone(), vec![n(i, 7)])); // → 7
    c.push(apply(id.clone(), vec![n(i, 1), n(i, 2)])); // argument-obligation (arity)
    c.push(apply(n(i, 5), vec![n(i, 1)])); // operation-safety: callee not a function
    let eff = konst(closure(i, one_param("x"), name("x"), ActKind::Effect));
    c.push(apply(eff, vec![n(i, 1)])); // world-admission: Effect call in pure world
    // Spread of a non-Tuple (open path — has a spread).
    c.push(Expr::Apply {
        callee: Box::new(id),
        args: vec![Arg::Spread(n(i, 5))],
    }); // spread-kind
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
fn match_tested_seat_guard() {
    let mut i = Interner::new();
    // match 5 { _ if 3 => 10 } — a non-Boolean guard is a tested-seat trap.
    let m = matchx(
        Some(konst(i.integer(5))),
        vec![arm(Some(Pat::Wild), Some(konst(i.integer(3))), konst(i.integer(10)))],
    );
    let a = analyze(&m, &empty(), &mut i);
    assert!(a.findings.iter().any(|f| f.class == TrapClass::TestedSeat && f.severity == Severity::Error));
}

#[test]
fn match_refuted_destructuring_binding() {
    let mut i = Interner::new();
    // match { [a, b] = 5; a } — destructuring a Number as a pair never matches.
    let pat = Pat::Tuple(vec![
        PatElem::Pat(Pat::Bind("a".into())),
        PatElem::Pat(Pat::Bind("b".into())),
    ]);
    let m = matchx(
        None,
        vec![
            MatchItem::Bind(Bind { target: BindTarget::Pattern(pat), value: konst(i.integer(5)), exported: false }),
            MatchItem::Stmt(name("a")),
        ],
    );
    let a = analyze(&m, &empty(), &mut i);
    assert!(a.findings.iter().any(|f| f.class == TrapClass::RefutedBinding && f.severity == Severity::Error));
}

#[test]
fn match_exhaustiveness_and_expecting_seat() {
    let mut i = Interner::new();
    // (match 5 { 1 => 10 }) + 1 — the match may fall through (non-exhaustive), so a
    // demanding seat is an expecting-seat trap.
    let one = i.integer(1);
    let nonexhaustive = matchx(
        Some(konst(i.integer(5))),
        vec![arm(Some(Pat::Const(one)), None, konst(i.integer(10)))],
    );
    let e = prim(PrimOp::Add, vec![nonexhaustive, konst(i.integer(1))]);
    let a = analyze(&e, &empty(), &mut i);
    assert!(!a.accepted());
    assert!(a.findings.iter().any(|f| f.class == TrapClass::ExpectingSeat));

    // (match 5 { _ => 10 }) + 1 — exhaustive, always produces; accepted.
    let exhaustive = matchx(
        Some(konst(i.integer(5))),
        vec![arm(Some(Pat::Wild), None, konst(i.integer(10)))],
    );
    let ok = prim(PrimOp::Add, vec![exhaustive, konst(i.integer(1))]);
    let a = analyze(&ok, &empty(), &mut i);
    assert!(a.accepted(), "exhaustive match must not trip expecting-seat: {:?}", a.findings);
}

#[test]
fn match_arm_narrows_scrutinee() {
    let mut i = Interner::new();
    // match x { [a, b] => a + b }  with x : Tuple([Number, Number]).
    // The pattern narrows the elements to Number, so `a + b` is proven safe.
    let mut env = TypeEnv::new();
    env.insert(
        "x".into(),
        Contract::Tuple(vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::Number)]),
    );
    let pat = Pat::Tuple(vec![
        PatElem::Pat(Pat::Bind("a".into())),
        PatElem::Pat(Pat::Bind("b".into())),
    ]);
    let body = prim(PrimOp::Add, vec![name("a"), name("b")]);
    let m = matchx(Some(name("x")), vec![arm(Some(pat), None, body)]);
    let a = analyze(&m, &env, &mut i);
    assert!(a.accepted() && a.findings.is_empty(), "narrowing should prove a+b safe: {:?}", a.findings);
}

#[test]
fn apply_known_callee_argument_obligation() {
    let mut i = Interner::new();
    // A one-parameter pure function, with an open (Number) argument.
    let f = closure(&mut i, one_param("x"), name("x"), ActKind::Pure);
    let mut env = TypeEnv::new();
    env.insert("f".into(), Contract::Equals(f));
    env.insert("n".into(), Contract::Kind(Kind::Number));

    // f(n) — one argument, matches the one parameter → accepted.
    let ok = apply(name("f"), vec![name("n")]);
    let a = analyze(&ok, &env, &mut i);
    assert!(a.accepted(), "f(n) should be accepted: {:?}", a.findings);

    // f(n, n) — two arguments against one parameter → argument-obligation.
    let bad = apply(name("f"), vec![name("n"), name("n")]);
    let a = analyze(&bad, &env, &mut i);
    assert!(!a.accepted());
    assert!(a.findings.iter().any(|f| f.class == TrapClass::ArgumentObligation));
}

#[test]
fn apply_non_function_callee_rejected() {
    let mut i = Interner::new();
    let mut env = TypeEnv::new();
    env.insert("x".into(), Contract::Kind(Kind::Number)); // definitely not a function
    let a = analyze(&apply(name("x"), vec![]), &env, &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::OperationSafety);
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
