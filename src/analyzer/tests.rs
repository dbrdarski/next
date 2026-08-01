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

/// An empty named-contract environment.
fn nc() -> ContractEnv {
    ContractEnv::new()
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
    let a = analyze(&e, &empty(), &nc(), &mut i);
    assert!(a.accepted());
    assert_eq!(a.contract, Contract::Equals(i.integer(12)));
}

#[test]
fn closed_type_error_is_operation_safety() {
    let mut i = Interner::new();
    // 1 + "x" traps operation-safety.
    let hello = i.string("x");
    let e = prim(PrimOp::Add, vec![konst(i.integer(1)), konst(hello)]);
    let a = analyze(&e, &empty(), &nc(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::OperationSafety);
    assert_eq!(a.findings[0].severity, Severity::Error);
}

#[test]
fn division_is_total_but_comparison_forces_indeterminate_discharge() {
    let mut i = Interner::new();
    // 1 / 0 alone is safe (produces a specific Indeterminate value).
    let div = prim(PrimOp::Div, vec![konst(i.integer(1)), konst(i.integer(0))]);
    assert!(analyze(&div, &empty(), &nc(), &mut i).accepted());

    // (1 / 0) < 2 traps at the strict Number seat.
    let cmp = prim(PrimOp::Lt, vec![div.clone(), konst(i.integer(2))]);
    let a = analyze(&cmp, &empty(), &nc(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::UndischargedIndeterminate);
}

#[test]
fn numeric_is_an_umbrella_while_arithmetic_still_demands_number() {
    let mut i = Interner::new();
    let mut numbers = empty();
    numbers.insert("x".into(), Contract::Kind(Kind::Number));
    numbers.insert("y".into(), Contract::Kind(Kind::Number));

    let div = prim(PrimOp::Div, vec![name("x"), name("y")]);
    let result = analyze(&div, &numbers, &nc(), &mut i);
    assert!(result.accepted(), "Number / Number is total: {:?}", result.findings);
    let numeric = Contract::numeric(&mut i);
    assert!(matches!(subcontract(&result.contract, &numeric, &mut i), Verdict::Proven));
    let div_zero = i.div_zero(Rational::from(1));
    let mod_zero = i.mod_zero(Rational::from(1));
    assert!(result.contract.contains(&div_zero));
    assert!(!result.contract.contains(&mod_zero));

    let mut indeterminate = empty();
    indeterminate.insert("z".into(), Contract::indeterminate(&mut i));
    let consume = prim(PrimOp::Add, vec![name("z"), konst(i.integer(1))]);
    let rejected = analyze(&consume, &indeterminate, &nc(), &mut i);
    assert!(!rejected.accepted());
    assert_eq!(rejected.findings[0].class, TrapClass::UndischargedIndeterminate);
}

#[test]
fn zero_to_negative_power_traps() {
    let mut i = Interner::new();
    // 0 ^ -1 traps; but (2+3) ^ -1 is safe (base folds to a nonzero 5).
    let bad = prim(PrimOp::Pow, vec![konst(i.integer(0)), konst(i.integer(-1))]);
    assert!(!analyze(&bad, &empty(), &nc(), &mut i).accepted());

    let five = prim(PrimOp::Add, vec![konst(i.integer(2)), konst(i.integer(3))]);
    let ok = prim(PrimOp::Pow, vec![five, konst(i.integer(-1))]);
    let a = analyze(&ok, &empty(), &nc(), &mut i);
    assert!(a.accepted(), "5^-1 = 1/5 must not be flagged, got {:?}", a.findings);
    assert_eq!(a.contract, Contract::Equals(i.number(Rational::new(1.into(), 5.into()))));
}

#[test]
fn unbound_reference_is_flagged() {
    let mut i = Interner::new();
    let a = analyze(&name("nope"), &empty(), &nc(), &mut i);
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
    c.push(prim(PrimOp::Lt, vec![dz.clone(), n(i, 2)])); // trap: Indeterminate needs discharge
    let dz2 = prim(PrimOp::Div, vec![n(i, 1), n(i, 0)]);
    c.push(prim(PrimOp::Add, vec![dz2, n(i, 2)])); // trap: Indeterminate needs discharge
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

    // AUDIT S4 rows — constructor spreads and computed keys (previously unchecked).
    c.push(Expr::TupleCons(vec![Element::Spread(n(i, 5))])); // spread-kind: [...5]
    let one_v = i.integer(1);
    let one_tuple = konst(i.tuple(vec![one_v]));
    c.push(Expr::TupleCons(vec![Element::Expr(n(i, 9)), Element::Spread(one_tuple.clone())])); // [9, ...[1]] — fine
    c.push(Expr::RecordCons(vec![Field::Spread(one_tuple)])); // spread-kind: {...[1]}
    let a_v = i.integer(1);
    let rec_ok = konst(i.record_str(vec![("a", a_v)]));
    c.push(Expr::RecordCons(vec![Field::Spread(rec_ok)])); // {...{a:1}} — fine
    c.push(Expr::RecordCons(vec![Field::Computed { key: n(i, 5), value: n(i, 1) }])); // computed-key: {[5]: v}
    let key_k = konst(i.string("k"));
    c.push(Expr::RecordCons(vec![Field::Computed { key: key_k, value: n(i, 1) }])); // {["k"]: v} — fine
    c
}

#[test]
fn closed_expression_concordance() {
    // For every closed expression: the oracle traps ⇔ the analyzer errors, and
    // when both, the class agrees. This is the §6 concordance, exact.
    let mut i = Interner::new();
    let corpus = closed_corpus(&mut i);
    for e in &corpus {
        let analysis = analyze(e, &empty(), &nc(), &mut i);
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
fn template_interpolation_is_total_never_rejected() {
    // Structure interpolation is total [user, 2026-07-18]: every value renders, so
    // no interpolation carries a printability demand and none can be rejected.
    let mut i = Interner::new();

    // A tuple interpolation — previously a rejection, now simply a String.
    let tuple = Expr::TupleCons(vec![Element::Expr(konst(i.integer(1)))]);
    let t = Expr::Template(vec![TemplatePart::Interp(tuple)]);
    let a = analyze(&t, &empty(), &nc(), &mut i);
    assert!(a.accepted() && a.findings.is_empty(), "got {:?}", a.findings);
    assert_eq!(a.contract, Contract::Kind(Kind::String));

    // An unconstrained receiver likewise carries no finding.
    let mut env = TypeEnv::new();
    env.insert("x".into(), Contract::Top);
    let t = Expr::Template(vec![TemplatePart::Interp(name("x"))]);
    let a = analyze(&t, &env, &nc(), &mut i);
    assert!(a.accepted() && a.findings.is_empty(), "got {:?}", a.findings);

    // Real findings inside an interpolation still surface (it is an expecting seat).
    let bad = prim(PrimOp::Add, vec![konst(i.integer(1)), konst(i.string("x"))]);
    let t = Expr::Template(vec![TemplatePart::Interp(bad)]);
    let a = analyze(&t, &empty(), &nc(), &mut i);
    assert!(!a.accepted(), "a trapping subexpression must still be reported");
    assert_eq!(a.findings[0].class, TrapClass::OperationSafety);
}

#[test]
fn open_field_access_reasoning() {
    let mut i = Interner::new();
    let mut env = TypeEnv::new();
    env.insert(
        "r".into(),
        Contract::record(vec![("a".into(), Contract::Kind(Kind::Number))], &mut i),
    );

    // r.a where r : Record({a: Number}) — accepted, output is Number.
    let a = analyze(&afield(name("r"), "a", false), &env, &nc(), &mut i);
    assert!(a.accepted());
    assert_eq!(a.contract, Contract::Kind(Kind::Number));

    // r.b (absent from an exact record) — rejected, absent-field.
    let a = analyze(&afield(name("r"), "b", false), &env, &nc(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::AbsentField);

    // null.a — rejected, null-receiver.
    let mut nenv = TypeEnv::new();
    nenv.insert("r".into(), Contract::Kind(Kind::Null));
    let a = analyze(&afield(name("r"), "a", false), &nenv, &nc(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::NullReceiver);

    // r?.b on an unknown receiver — total form never traps.
    let mut tenv = TypeEnv::new();
    tenv.insert("r".into(), Contract::Top);
    let a = analyze(&afield(name("r"), "b", true), &tenv, &nc(), &mut i);
    assert!(a.accepted() && a.findings.is_empty());

    // r.b on an unknown receiver (demand form) — **safety-unproven BLOCKS**
    // (late-resolution §5; ruled 2026-07-31). `b` cannot be proven present, and an
    // unproven safety demand is a compile error, un-suppressibly. The previous
    // "a warning, not a rejection" was the superseded wording.
    let a = analyze(&afield(name("r"), "b", false), &tenv, &nc(), &mut i);
    assert!(!a.accepted(), "safety-unproven blocks");
    assert_eq!(a.findings[0].severity, Severity::Error);
}

#[test]
fn match_tested_seat_guard() {
    let mut i = Interner::new();
    // match 5 { _ if 3 => 10 } — a non-Boolean guard is a tested-seat trap.
    let m = matchx(
        Some(konst(i.integer(5))),
        vec![arm(Some(Pat::Wild), Some(konst(i.integer(3))), konst(i.integer(10)))],
    );
    let a = analyze(&m, &empty(), &nc(), &mut i);
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
    let a = analyze(&m, &empty(), &nc(), &mut i);
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
    let a = analyze(&e, &empty(), &nc(), &mut i);
    assert!(!a.accepted());
    assert!(a.findings.iter().any(|f| f.class == TrapClass::ExpectingSeat));

    // (match 5 { _ => 10 }) + 1 — exhaustive, always produces; accepted.
    let exhaustive = matchx(
        Some(konst(i.integer(5))),
        vec![arm(Some(Pat::Wild), None, konst(i.integer(10)))],
    );
    let ok = prim(PrimOp::Add, vec![exhaustive, konst(i.integer(1))]);
    let a = analyze(&ok, &empty(), &nc(), &mut i);
    assert!(a.accepted(), "exhaustive match must not trip expecting-seat: {:?}", a.findings);
}

#[test]
fn a_partial_callee_at_an_expecting_seat_is_an_error() {
    // g's body `n :: { 0 => 1 }` may fall through (over Number, n = 1 is uncovered — a
    // proven-reachable fall-through), so binding g(x) at the `+` operand seat is an
    // expecting-seat ERROR (the completion threaded from the callee, closing the gap
    // where only mutators were flagged).
    let mut i = Interner::new();
    let g = crate::oracle::run_source("g = (n) => n :: { 0 => 1 }\ng")
        .unwrap()
        .0;
    let mut env = empty();
    env.insert("g".into(), Contract::Equals(g));
    env.insert("x".into(), Contract::Kind(Kind::Number));
    let e = prim(
        PrimOp::Add,
        vec![apply(name("g"), vec![name("x")]), konst(i.integer(1))],
    );
    let a = analyze(&e, &env, &nc(), &mut i);
    assert!(
        !a.accepted(),
        "a proven fall-through at an expecting seat is an error: {:?}",
        a.findings
    );
    assert!(
        a.findings
            .iter()
            .any(|f| f.class == TrapClass::ExpectingSeat && f.severity == Severity::Error),
        "expecting-seat error present: {:?}",
        a.findings
    );
}

#[test]
fn a_guarded_fall_through_is_a_warning_not_an_error() {
    // `n :: { when b => 1 }` — a guard, not a pattern, decides, and guards consume
    // nothing, so the remainder over-approximates: the fall-through is *possible* but
    // not *proven*. The three-voice verdict at an expecting seat is a WARNING, not an
    // error (the precision the tri-state buys over the old may_complete → error).
    let mut i = Interner::new();
    let m = matchx(
        Some(name("n")),
        vec![arm(None, Some(name("b")), konst(i.integer(1)))],
    );
    let e = prim(PrimOp::Add, vec![m, konst(i.integer(1))]);
    let mut env = empty();
    env.insert("n".into(), Contract::Kind(Kind::Number));
    env.insert("b".into(), Contract::Kind(Kind::Boolean));
    let a = analyze(&e, &env, &nc(), &mut i);
    assert!(
        a.accepted(),
        "a guarded (unproven) fall-through must not be an error: {:?}",
        a.findings
    );
    assert!(
        a.findings
            .iter()
            .any(|f| f.class == TrapClass::ExpectingSeat && f.severity == Severity::Warning),
        "but it warns: {:?}",
        a.findings
    );
}

#[test]
fn match_arm_narrows_scrutinee() {
    let mut i = Interner::new();
    // match x { [a, b] => a + b }  with x : Tuple([Number, Number]).
    // The pattern narrows the elements to Number, so `a + b` is proven safe.
    let mut env = TypeEnv::new();
    env.insert(
        "x".into(),
        Contract::tuple(
            vec![Contract::Kind(Kind::Number), Contract::Kind(Kind::Number)],
            &mut i,
        ),
    );
    let pat = Pat::Tuple(vec![
        PatElem::Pat(Pat::Bind("a".into())),
        PatElem::Pat(Pat::Bind("b".into())),
    ]);
    let body = prim(PrimOp::Add, vec![name("a"), name("b")]);
    let m = matchx(Some(name("x")), vec![arm(Some(pat), None, body)]);
    let a = analyze(&m, &env, &nc(), &mut i);
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
    let a = analyze(&ok, &env, &nc(), &mut i);
    assert!(a.accepted(), "f(n) should be accepted: {:?}", a.findings);

    // f(n, n) — two arguments against one parameter → argument-obligation.
    let bad = apply(name("f"), vec![name("n"), name("n")]);
    let a = analyze(&bad, &env, &nc(), &mut i);
    assert!(!a.accepted());
    assert!(a.findings.iter().any(|f| f.class == TrapClass::ArgumentObligation));
}

#[test]
fn apply_non_function_callee_rejected() {
    let mut i = Interner::new();
    let mut env = TypeEnv::new();
    env.insert("x".into(), Contract::Kind(Kind::Number)); // definitely not a function
    let a = analyze(&apply(name("x"), vec![]), &env, &nc(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::OperationSafety);
}

// ── Named (user) contracts reaching source patterns (C§12.2 / E9) ─────────────

/// `Percent = Range(0, 100)` as a source-level contract binding.
fn percent_env(i: &mut Interner) -> ContractEnv {
    let range = Expr::Apply {
        callee: Box::new(name("Range")),
        args: vec![
            Arg::Expr(konst(i.integer(0))),
            Arg::Expr(konst(i.integer(100))),
        ],
    };
    crate::contract::build_contract_env([("Percent", &range)], i)
}

fn contract_pat(n: &str) -> Pat {
    Pat::Contract(Ref::Immutable(BindingRef::Name(n.into())))
}

#[test]
fn user_contract_pattern_narrows() {
    let mut i = Interner::new();
    let cenv = percent_env(&mut i);
    let mut env = TypeEnv::new();
    env.insert("x".into(), Contract::Kind(Kind::Number));

    // match x { Percent => 1 }  with x : Number.
    let m = matchx(Some(name("x")), vec![arm(Some(contract_pat("Percent")), None, konst(i.integer(1)))]);

    // Resolved: a Number need not be a Percent, so the match is NOT exhaustive.
    let a = analyze(&m, &env, &cenv, &mut i);
    assert!(a.may_complete(), "Percent must narrow — Number is not covered by Range(0,100)");

    // Unresolved (empty contract env): the pattern widens to Top and covers
    // everything — the discriminating control for the test above.
    let a = analyze(&m, &env, &nc(), &mut i);
    assert!(!a.may_complete(), "an unresolved contract name widens to Top");
}

#[test]
fn user_contract_binding_can_be_refuted() {
    let mut i = Interner::new();
    let cenv = percent_env(&mut i);

    // match { Percent = 500 } — 500 is disjoint from Range(0, 100).
    let m = matchx(
        None,
        vec![MatchItem::Bind(Bind {
            target: BindTarget::Pattern(contract_pat("Percent")),
            value: konst(i.integer(500)),
            exported: false,
        })],
    );

    let a = analyze(&m, &empty(), &cenv, &mut i);
    assert!(
        a.findings.iter().any(|f| f.class == TrapClass::RefutedBinding && f.severity == Severity::Error),
        "500 ∉ Percent must refute the binding: {:?}",
        a.findings,
    );

    // Control: without the contract env the name is Top, so nothing is refuted.
    let a = analyze(&m, &empty(), &nc(), &mut i);
    assert!(a.accepted());
}

#[test]
fn computed_key_finiteness_demand() {
    // A-VER: computed keys demand a proven-finite string set (E5, fork 12 = R) —
    // a finite union accepts, `Kind(String)` REJECTs.
    let mut i = Interner::new();
    let mut env = TypeEnv::new();
    env.insert("k".into(), Contract::Kind(Kind::String));
    let open_key = Expr::RecordCons(vec![Field::Computed {
        key: name("k"),
        value: konst(i.integer(1)),
    }]);
    let a = analyze(&open_key, &env, &nc(), &mut i);
    assert!(!a.accepted(), "Kind(String) computed key must REJECT (finite-set demand)");
    assert_eq!(a.findings[0].class, TrapClass::ComputedKey);

    // A finite union of string singletons accepts.
    let ka = i.string("a");
    let kb = i.string("b");
    let mut fenv = TypeEnv::new();
    fenv.insert(
        "k".into(),
        Contract::union(Contract::Equals(ka), Contract::Equals(kb), &mut i),
    );
    let finite = Expr::RecordCons(vec![Field::Computed {
        key: name("k"),
        value: konst(i.integer(1)),
    }]);
    let a = analyze(&finite, &fenv, &nc(), &mut i);
    assert!(
        a.accepted(),
        "a finite string set is admitted: {:?}",
        a.findings
    );
}

#[test]
fn tuple_spread_produces_concat_shape() {
    // The tuple family's constructor: [1, ...t] with t : Tuple([Number]) fuses to
    // the exact 2-tuple Tuple([Equals(1), Number]) — no more Top for spreads.
    let mut i = Interner::new();
    let mut env = TypeEnv::new();
    env.insert(
        "t".into(),
        Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i),
    );
    let e = Expr::TupleCons(vec![
        Element::Expr(konst(i.integer(1))),
        Element::Spread(name("t")),
    ]);
    let a = analyze(&e, &env, &nc(), &mut i);
    assert!(a.accepted(), "{:?}", a.findings);
    assert_eq!(
        a.contract,
        Contract::tuple(
            vec![Contract::Equals(i.integer(1)), Contract::Kind(Kind::Number)],
            &mut i
        ),
    );

    // An unknown-shape spread survives as a Concat with a Kind(Tuple) tail.
    let mut wide = TypeEnv::new();
    wide.insert("t".into(), Contract::Kind(Kind::Tuple));
    let e = Expr::TupleCons(vec![
        Element::Expr(konst(i.integer(1))),
        Element::Spread(name("t")),
    ]);
    let a = analyze(&e, &wide, &nc(), &mut i);
    assert!(a.accepted());
    assert_eq!(
        a.contract,
        Contract::Concat(vec![
            Contract::tuple(vec![Contract::Equals(i.integer(1))], &mut i).cref(&mut i),
            Contract::Kind(Kind::Tuple).cref(&mut i)
        ]),
    );
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
        let analysis = analyze(expr, &env, &nc(), &mut i);
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

// ── AnalysisContract abstract domain (§2, application/induction v0.8.1) ────────

mod domain {
    use super::{ActKind, closure, name, one_param};
    use crate::analyzer::domain::{
        AnalysisContract, Instance, InstanceMetadata, gamma_contains, intersect_a,
        prove_subcontract_a, realizes,
    };
    use crate::ast::{Expr, Lambda};
    use crate::contract::{Contract, Kind, Verdict};
    use crate::interner::Interner;
    use crate::rational::Rational;
    use crate::value::ValueRef;
    use num_bigint::BigInt;

    fn shape_of(v: &ValueRef) -> Lambda {
        v.as_fn().expect("a function").shape().clone()
    }
    /// A non-capturing identity closure `x => x`, and its canonical shape.
    fn id_shape(i: &mut Interner) -> Lambda {
        shape_of(&closure(i, one_param("x"), name("x"), ActKind::Pure))
    }
    fn eq(i: &mut Interner, k: i64) -> Contract {
        Contract::Equals(i.integer(k))
    }
    fn range(a: i64, b: i64) -> Contract {
        let r = |k: i64| Rational::from_integer(BigInt::from(k));
        Contract::Range(r(a), r(b))
    }
    /// A single-capture instance of `shape` whose capture is a plain contract.
    fn inst(shape: &Lambda, cap: Contract) -> Instance {
        Instance { shape: shape.clone(), env: vec![AnalysisContract::of_contract(cap)] }
    }
    fn known(insts: Vec<Instance>) -> AnalysisContract {
        AnalysisContract::leaf(Contract::Kind(Kind::Function), InstanceMetadata::Known(insts))
    }
    fn unknown_fn() -> AnalysisContract {
        AnalysisContract::of_contract(Contract::Kind(Kind::Function))
    }
    fn proven(v: Verdict) -> bool {
        matches!(v, Verdict::Proven)
    }

    #[test]
    fn metadata_join_and_normalization() {
        let mut i = Interner::new();
        let s = id_shape(&mut i);
        let a = inst(&s, eq(&mut i, 1));
        let b = inst(&s, range(1, 5));
        // Known ∪ Known = union (dedup); anything ∪ Unknown = Unknown.
        let j = InstanceMetadata::join(&InstanceMetadata::Known(vec![a.clone()]), &InstanceMetadata::Known(vec![b.clone()]));
        assert_eq!(j, InstanceMetadata::Known(vec![a.clone(), b.clone()]));
        assert_eq!(
            InstanceMetadata::join(&InstanceMetadata::Known(vec![a.clone()]), &InstanceMetadata::Unknown),
            InstanceMetadata::Unknown,
        );
        // Normalization to the one canonical bottom.
        assert!(AnalysisContract::leaf(Contract::Bottom, InstanceMetadata::Unknown).is_bottom());
        assert!(known(vec![]).is_bottom(), "function-only + Known(∅) ⇒ bottom");
        // A non-function contract with Known(∅) is NOT empty — metadata is vacuous.
        let num_empty = AnalysisContract::leaf(Contract::Kind(Kind::Number), InstanceMetadata::Known(vec![]));
        assert!(!num_empty.is_bottom());
    }

    #[test]
    fn ap27_instance_coverage() {
        let mut i = Interner::new();
        let s = id_shape(&mut i);
        let eq1 = inst(&s, eq(&mut i, 1));
        let r15 = inst(&s, range(1, 5));
        // instance(shape, Equals(1)) ⊑ instance(shape, Range(1,5)) despite distinct keys.
        assert!(proven(prove_subcontract_a(&known(vec![eq1.clone()]), &known(vec![r15.clone()]), &mut i)));
        // Known(S) ⊑ Unknown proven; Unknown ⊑ Known(T) unproven.
        assert!(proven(prove_subcontract_a(&known(vec![eq1.clone()]), &unknown_fn(), &mut i)));
        assert!(!proven(prove_subcontract_a(&unknown_fn(), &known(vec![r15.clone()]), &mut i)));
        // Known(∅) ⊑ X proven (bottom source, vacuous coverage).
        assert!(proven(prove_subcontract_a(&AnalysisContract::bottom(), &known(vec![r15.clone()]), &mut i)));
        // The reverse fails: Range(1,5) is not covered by Equals(1).
        assert!(!proven(prove_subcontract_a(&known(vec![r15]), &known(vec![eq1]), &mut i)));
    }

    #[test]
    fn ap28_semantic_meet_is_the_tighter_instance() {
        let mut i = Interner::new();
        let s = id_shape(&mut i);
        let eq1 = inst(&s, eq(&mut i, 1));
        let r15 = inst(&s, range(1, 5));
        // Known({Eq(1)}) ∩ Known({Range(1,5)}) = Known({Eq(1)}) — coverage normalization,
        // never Bottom (AP-28).
        let meet = intersect_a(&known(vec![eq1.clone()]), &known(vec![r15]), &mut i);
        assert!(!meet.is_bottom());
        match &meet {
            AnalysisContract::Leaf { metadata, .. } => {
                assert_eq!(*metadata, InstanceMetadata::Known(vec![eq1]));
            }
            other => panic!("expected a Leaf meet, got {other:?}"),
        }
        // Disjoint shapes have an empty meet — a sound Bottom by disjointness.
        let z = konst_zero(&mut i);
        let s2 = shape_of(&closure(&mut i, one_param("x"), z, ActKind::Pure));
        let other = inst(&s2, eq(&mut i, 1));
        let s_eq1 = inst(&s, eq(&mut i, 1));
        let disjoint = intersect_a(&known(vec![s_eq1]), &known(vec![other]), &mut i);
        assert!(disjoint.is_bottom(), "different shapes ⇒ γ-disjoint ⇒ bottom");
    }
    fn konst_zero(i: &mut Interner) -> Expr {
        Expr::Const(i.integer(0))
    }

    #[test]
    fn gamma_realizes_shape_and_governs_functions() {
        let mut i = Interner::new();
        let idv = closure(&mut i, one_param("x"), name("x"), ActKind::Pure);
        let z = konst_zero(&mut i);
        let zerov = closure(&mut i, one_param("x"), z, ActKind::Pure);
        let id_inst = Instance { shape: shape_of(&idv), env: vec![] };
        // realizes: the identity closure realizes its own (capture-free) instance.
        assert!(realizes(&idv, &id_inst, &mut i));
        assert!(!realizes(&zerov, &id_inst, &mut i), "a different shape does not realize");
        // γ over Known(S): the id closure is in, the zero closure is out.
        let ac = AnalysisContract::leaf(Contract::Kind(Kind::Function), InstanceMetadata::Known(vec![id_inst]));
        assert!(gamma_contains(&ac, &idv, &mut i));
        assert!(!gamma_contains(&ac, &zerov, &mut i));
        // Unknown admits every function; non-functions are governed by the contract alone.
        assert!(gamma_contains(&unknown_fn(), &zerov, &mut i));
        let five = i.integer(5);
        let num = AnalysisContract::leaf(Contract::Kind(Kind::Number), InstanceMetadata::Known(vec![]));
        assert!(gamma_contains(&num, &five, &mut i), "metadata is vacuous for a non-function");
    }

    #[test]
    fn correlated_alternatives_do_not_synthesize_cross_pairs() {
        // The review's core case: `[f, 5] | [g, "hi"]` keeps f⟷5 and g⟷"hi"
        // correlated. γ holds the two represented pairs but NOT a synthesized
        // cross-pair — function metadata survives structurally through the tuple, and
        // the alternatives are never positionally flattened.
        let mut i = Interner::new();
        let f = closure(&mut i, one_param("x"), name("x"), ActKind::Pure);
        let z = konst_zero(&mut i);
        let g = closure(&mut i, one_param("x"), z, ActKind::Pure);
        let f_inst = Instance { shape: shape_of(&f), env: vec![] };
        let g_inst = Instance { shape: shape_of(&g), env: vec![] };
        let five = i.integer(5);
        let hi = i.string("hi");
        let fn_leaf = |inst: Instance| {
            AnalysisContract::leaf(Contract::Kind(Kind::Function), InstanceMetadata::Known(vec![inst]))
        };
        let val_leaf = |v: ValueRef| AnalysisContract::leaf(Contract::Equals(v), InstanceMetadata::Unknown);
        let alt1 = AnalysisContract::tuple(vec![fn_leaf(f_inst), val_leaf(five.clone())]);
        let alt2 = AnalysisContract::tuple(vec![fn_leaf(g_inst), val_leaf(hi.clone())]);
        let operand = AnalysisContract::alt(vec![alt1, alt2]);
        // The two represented pairs are in γ.
        let pair1 = i.tuple(vec![f.clone(), five.clone()]);
        let pair2 = i.tuple(vec![g.clone(), hi.clone()]);
        assert!(gamma_contains(&operand, &pair1, &mut i));
        assert!(gamma_contains(&operand, &pair2, &mut i));
        // The synthesized cross-pairs are NOT — correlation survives.
        let cross1 = i.tuple(vec![f.clone(), hi]);
        let cross2 = i.tuple(vec![g.clone(), five]);
        assert!(!gamma_contains(&operand, &cross1, &mut i), "[f, \"hi\"] is not represented");
        assert!(!gamma_contains(&operand, &cross2, &mut i), "[g, 5] is not represented");
    }
}

// ── Application transfer rule §1 — the outcome algebra (v0.8.1, 8.1b) ──────────

mod application {
    use super::{ActKind, closure, name, one_param};
    use crate::analyzer::application::{
        ApplicationOutcome, ApplicationWitness, CompletionWithoutValue as C, SeatVerdict,
        admit_callee, analyze_application, join, join_all, live_alternatives, pure_world_admits,
        seat_demand,
    };
    use crate::analyzer::domain::{AnalysisContract, Instance, InstanceMetadata};
    use crate::ast::Lambda;
    use crate::contract::{Contract, Kind, Verdict};
    use crate::interner::Interner;
    use crate::value::ValueRef;

    fn shape(i: &mut Interner, act: ActKind) -> Lambda {
        closure(i, one_param("x"), name("x"), act).as_fn().unwrap().shape().clone()
    }
    fn inst(shape: Lambda) -> Instance {
        Instance { shape, env: vec![] }
    }
    fn out(produced: Contract, completion: C, mnc: bool) -> ApplicationOutcome {
        ApplicationOutcome { produced: AnalysisContract::of_contract(produced), completion, may_not_complete: mnc }
    }
    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }
    fn proven(v: &Verdict) -> bool {
        matches!(v, Verdict::Proven)
    }
    /// A nominal represented-execution witness for the algebra tests.
    fn dummy_witness(i: &mut Interner) -> ApplicationWitness {
        let f = closure(i, one_param("x"), name("x"), ActKind::Pure);
        let a = i.integer(0);
        ApplicationWitness { callee: f, arguments: vec![a] }
    }

    #[test]
    fn ap23_completion_tri_state_at_the_seat() {
        let mut i = Interner::new();
        let w = dummy_witness(&mut i);
        let absent = out(num(), C::ProvenAbsent, false);
        let present = out(num(), C::ProvenPresent(w.clone()), false);
        let unproven = out(num(), C::UnprovenPossible, false);
        // Expecting seat: absent proven, present refuted-with-witness, unproven unproven.
        assert!(matches!(seat_demand(&absent, true), SeatVerdict::Proven));
        match seat_demand(&present, true) {
            SeatVerdict::Refuted(got) => assert_eq!(got.callee, w.callee),
            other => panic!("expected Refuted(witness), got {other:?}"),
        }
        assert!(matches!(seat_demand(&unproven, true), SeatVerdict::Unproven));
        // Statement seat accepts all three.
        for o in [&absent, &present, &unproven] {
            assert!(matches!(seat_demand(o, false), SeatVerdict::Proven));
        }
    }

    #[test]
    fn ap18_fall_through_only_callee_binds_at_expecting_seat() {
        // produced = Bottom, a witnessed fall-through: binding it (expecting seat) is
        // the violation; the statement seat accepts.
        let mut i = Interner::new();
        let w = dummy_witness(&mut i);
        let o = ApplicationOutcome {
            produced: AnalysisContract::bottom(),
            completion: C::ProvenPresent(w),
            may_not_complete: false,
        };
        assert!(matches!(seat_demand(&o, true), SeatVerdict::Refuted(_)));
        assert!(matches!(seat_demand(&o, false), SeatVerdict::Proven));
    }

    #[test]
    fn outcome_join_is_componentwise_and_evidence_preserving() {
        let mut i = Interner::new();
        let w = dummy_witness(&mut i);
        // may_not_complete by or; produced by union; completion evidence-preserving.
        let a = out(num(), C::UnprovenPossible, false);
        let b = out(Contract::Kind(Kind::String), C::ProvenPresent(w), true);
        let j = join(a, b);
        assert!(j.may_not_complete, "or of the flags");
        assert!(matches!(&j.completion, C::ProvenPresent(_)), "ProvenPresent dominates");
        assert!(matches!(j.produced, AnalysisContract::Alt(_)), "produced by correlated union");
        // UnprovenPossible beats ProvenAbsent; the empty join is the Known(∅) identity.
        let mixed = join(out(num(), C::UnprovenPossible, false), out(num(), C::ProvenAbsent, false));
        assert!(matches!(mixed.completion, C::UnprovenPossible));
        let empty = join_all(std::iter::empty());
        assert!(empty.produced.is_bottom());
        assert!(matches!(empty.completion, C::ProvenAbsent));
        assert!(!empty.may_not_complete);
    }

    #[test]
    fn ap15_ap21_act_kind_admission_over_metadata() {
        let mut i = Interner::new();
        let pure = inst(shape(&mut i, ActKind::Pure));
        let eff = inst(shape(&mut i, ActKind::Effect));
        // All-pure Known(S) admitted in the pure world.
        let known_pure = InstanceMetadata::Known(vec![pure.clone()]);
        assert!(proven(&admit_callee(&known_pure, pure_world_admits)));
        // An effect member is inadmissible — unproven (no witness at the algebra layer).
        let known_eff = InstanceMetadata::Known(vec![eff]);
        assert!(matches!(admit_callee(&known_eff, pure_world_admits), Verdict::Unproven));
        // Known(∅) passes vacuously (AP-21); Unknown is unproven (AP-15).
        assert!(proven(&admit_callee(&InstanceMetadata::Known(vec![]), pure_world_admits)));
        assert!(matches!(admit_callee(&InstanceMetadata::Unknown, pure_world_admits), Verdict::Unproven));
        // A proven-empty member is dropped, so it does not block admission.
        let dead = Instance { shape: pure.shape.clone(), env: vec![AnalysisContract::bottom()] };
        let known_dead = InstanceMetadata::Known(vec![dead]);
        assert!(proven(&admit_callee(&known_dead, pure_world_admits)));
    }

    #[test]
    fn may_not_complete_feeds_no_seat_verdict() {
        // may_not_complete = true rides alongside a ProvenAbsent completion and does
        // not turn the expecting-seat demand into a violation.
        let o = out(num(), C::ProvenAbsent, true);
        assert!(matches!(seat_demand(&o, true), SeatVerdict::Proven));
    }

    // ── The joint operand driver: AP-24 / AP-29 (correlation discipline) ─────────

    /// A callee leaf carrying a single known instance of `shape`.
    fn callee_leaf(shape: Lambda) -> AnalysisContract {
        AnalysisContract::leaf(Contract::Kind(Kind::Function), InstanceMetadata::Known(vec![inst(shape)]))
    }
    /// A value leaf `Equals(v)`.
    fn val_leaf(v: ValueRef) -> AnalysisContract {
        AnalysisContract::leaf(Contract::Equals(v), InstanceMetadata::Unknown)
    }
    fn callee_shape(ac: &AnalysisContract) -> Option<Lambda> {
        match ac {
            AnalysisContract::Leaf { metadata: InstanceMetadata::Known(s), .. } if s.len() == 1 => {
                Some(s[0].shape.clone())
            }
            _ => None,
        }
    }
    fn arg_value(ac: &AnalysisContract) -> Option<ValueRef> {
        match ac {
            AnalysisContract::Leaf { contract: Contract::Equals(v), .. } => Some(v.clone()),
            _ => None,
        }
    }

    #[test]
    fn ap24_ap29_correlated_vs_projected_application() {
        // numFn (`x => x`) is used as "accepts Numbers"; strFn (`x => 0`) as "accepts
        // Strings". The operand is [numFn, 5] | [strFn, "hi"].
        let mut i = Interner::new();
        let numfn = closure(&mut i, one_param("x"), name("x"), ActKind::Pure);
        let z = zero_body(&mut i);
        let strfn = closure(&mut i, one_param("x"), z, ActKind::Pure);
        let num_shape = numfn.as_fn().unwrap().shape().clone();
        let str_shape = strfn.as_fn().unwrap().shape().clone();
        let five = i.integer(5);
        let hi = i.string("hi");

        // `accepts`: numFn takes a numeric arg, strFn a string arg (interner-free).
        let (ns, ss) = (num_shape.clone(), str_shape.clone());
        let (nfv, sfv) = (numfn.clone(), strfn.clone());
        let accepts = move |callee: &AnalysisContract, args: &[AnalysisContract]| -> SeatVerdict {
            let (Some(shape), Some(av)) = (callee_shape(callee), args.first().and_then(arg_value)) else {
                return SeatVerdict::Unproven;
            };
            let ok = if shape == ns {
                av.as_number().is_some()
            } else if shape == ss {
                av.as_str_units().is_some()
            } else {
                false
            };
            if ok {
                SeatVerdict::Proven
            } else {
                let callee_val = if shape == ns { nfv.clone() } else { sfv.clone() };
                SeatVerdict::Refuted(ApplicationWitness { callee: callee_val, arguments: vec![av] })
            }
        };

        // AP-24: the correlated operand proves — each callee accepts its own arg, and
        // the cross-pairs are never formed.
        let correlated = AnalysisContract::alt(vec![
            AnalysisContract::tuple(vec![callee_leaf(num_shape.clone()), val_leaf(five.clone())]),
            AnalysisContract::tuple(vec![callee_leaf(str_shape.clone()), val_leaf(hi.clone())]),
        ]);
        let (a, correlated_flag) = live_alternatives(&correlated);
        assert_eq!(a.len(), 2, "two live correlated alternatives");
        assert!(correlated_flag);
        assert!(
            matches!(analyze_application(&correlated, pure_world_admits, &accepts), SeatVerdict::Proven),
            "correlated application proves; no synthesized cross-pair",
        );

        // AP-29: the projected operand [numFn|strFn, 5|"hi"] expands to the four
        // cross-pairs; (numFn,"hi") and (strFn,5) fail, but a synthesized cross-pair
        // failure must be UNPROVEN, never refuted.
        let projected = AnalysisContract::tuple(vec![
            AnalysisContract::alt(vec![callee_leaf(num_shape.clone()), callee_leaf(str_shape.clone())]),
            AnalysisContract::alt(vec![val_leaf(five), val_leaf(hi)]),
        ]);
        let (pa, projected_flag) = live_alternatives(&projected);
        assert_eq!(pa.len(), 4, "four projected cross-pairs");
        assert!(!projected_flag, "projected form is uncorrelated");
        assert!(
            matches!(analyze_application(&projected, pure_world_admits, &accepts), SeatVerdict::Unproven),
            "a cross-pair failure degrades to unproven, never refuted (AP-29)",
        );
    }

    // The structural-witness hardening (review §7) — NOT normative AP-30. Real AP-30
    // is the completion/fall-through version: a row inhabited only by a projected
    // cross-pair `(e₁,a₂) ∈ (E×A)∖R_alt` must contribute `UnprovenPossible`, flipping
    // to `ProvenPresent` only on a proved `R_alt ∩ row` inhabitant — that needs the
    // row-selection / outcome-contribution machinery of the induction tail.
    #[test]
    fn refutation_carries_a_represented_application_witness() {
        // A genuinely-failing CORRELATED alternative refutes with a structural
        // witness — the callee applied to the argument, not a bare token.
        let mut i = Interner::new();
        let numfn = closure(&mut i, one_param("x"), name("x"), ActKind::Pure);
        let num_shape = numfn.as_fn().unwrap().shape().clone();
        let hi = i.string("hi");
        let ns = num_shape.clone();
        let nfv = numfn.clone();
        let accepts = move |callee: &AnalysisContract, args: &[AnalysisContract]| -> SeatVerdict {
            let (Some(shape), Some(av)) = (callee_shape(callee), args.first().and_then(arg_value)) else {
                return SeatVerdict::Unproven;
            };
            if shape == ns && av.as_number().is_some() {
                SeatVerdict::Proven
            } else {
                SeatVerdict::Refuted(ApplicationWitness { callee: nfv.clone(), arguments: vec![av] })
            }
        };
        // [numFn, "hi"] — a single correlated alternative that genuinely rejects.
        let operand = AnalysisContract::tuple(vec![callee_leaf(num_shape), val_leaf(hi.clone())]);
        match analyze_application(&operand, pure_world_admits, &accepts) {
            SeatVerdict::Refuted(w) => {
                assert_eq!(w.callee, numfn, "witness carries the represented callee");
                assert_eq!(w.arguments, vec![hi], "and the represented argument");
            }
            other => panic!("expected a witnessed refutation, got {other:?}"),
        }
    }

    fn zero_body(i: &mut Interner) -> crate::ast::Expr {
        crate::ast::Expr::Const(i.integer(0))
    }
}

// ── Instance-chain inventory §4a (v0.8.1, 8.1c) ───────────────────────────────

mod inventory {
    use super::{ActKind, closure, konst, name, one_param};
    use crate::analyzer::domain::Instance;
    use crate::analyzer::inventory::build_inventory;
    use crate::ast::Expr;
    use crate::interner::Interner;

    /// A capture-free instance with the shape of `x => <body>`.
    fn mk(i: &mut Interner, body: Expr) -> Instance {
        let shape = closure(i, one_param("x"), body, ActKind::Pure).as_fn().unwrap().shape().clone();
        Instance { shape, env: vec![] }
    }

    #[test]
    fn ap16_mutual_recursion_hits_the_shape_cutoff() {
        // Two shapes A, B calling each other. Seeded at A: A admits B (fresh shape),
        // then B's call back to A is a shape-repeat on the path [A, B] — cut. Finite
        // inventory {A, B}; no runaway despite the cycle.
        let mut i = Interner::new();
        let a = mk(&mut i, name("x"));
        let z = konst(i.integer(0));
        let b = mk(&mut i, z);
        let (sa, sb) = (a.shape.clone(), b.shape.clone());
        let (a2, b2) = (a.clone(), b.clone());
        let trans = move |inst: &Instance| {
            if inst.shape == sa {
                vec![b2.clone()]
            } else if inst.shape == sb {
                vec![a2.clone()]
            } else {
                vec![]
            }
        };
        let inv = build_inventory(vec![a.clone()], trans);
        assert_eq!(inv.len(), 2, "exactly A and B admitted");
        assert!(inv.contains(&a) && inv.contains(&b));
    }

    #[test]
    fn self_recursion_admits_only_the_root() {
        // A calls itself: the target shape is already active on [A] — cut on the
        // first transition. Inventory {A}.
        let mut i = Interner::new();
        let a = mk(&mut i, name("x"));
        let sa = a.shape.clone();
        let a2 = a.clone();
        let trans = move |inst: &Instance| if inst.shape == sa { vec![a2.clone()] } else { vec![] };
        let inv = build_inventory(vec![a.clone()], trans);
        assert_eq!(inv.len(), 1);
        assert!(inv.contains(&a));
    }

    #[test]
    fn nonrecursive_diamond_dedups_the_join() {
        // A → {B, C}; B → D; C → D. No shape repeats, so all four admit; D is reached
        // twice but appears once (projection dedup).
        let mut i = Interner::new();
        let a = mk(&mut i, name("x"));
        let b0 = konst(i.integer(0));
        let b = mk(&mut i, b0);
        let c0 = konst(i.integer(1));
        let c = mk(&mut i, c0);
        let d0 = konst(i.integer(2));
        let d = mk(&mut i, d0);
        let (sa, sb, sc) = (a.shape.clone(), b.shape.clone(), c.shape.clone());
        let (b2, c2, d2) = (b.clone(), c.clone(), d.clone());
        let trans = move |inst: &Instance| {
            if inst.shape == sa {
                vec![b2.clone(), c2.clone()]
            } else if inst.shape == sb || inst.shape == sc {
                vec![d2.clone()]
            } else {
                vec![]
            }
        };
        let inv = build_inventory(vec![a.clone()], trans);
        assert_eq!(inv.len(), 4, "A, B, C, D each once");
        for x in [&a, &b, &c, &d] {
            assert!(inv.contains(x));
        }
    }

    #[test]
    fn membership_is_independent_of_transition_order() {
        // The inventory is a set: reversing the transition enumeration yields the same
        // membership (the returned Vec order may differ, and callers must not depend
        // on it).
        let mut i = Interner::new();
        let a = mk(&mut i, name("x"));
        let b0 = konst(i.integer(0));
        let b = mk(&mut i, b0);
        let c0 = konst(i.integer(1));
        let c = mk(&mut i, c0);
        let sa = a.shape.clone();
        let (b2, c2) = (b.clone(), c.clone());
        // A → {B, C}; forward and reversed target enumeration.
        let fwd = {
            let (b2, c2, sa) = (b2.clone(), c2.clone(), sa.clone());
            move |inst: &Instance| {
                if inst.shape == sa {
                    vec![b2.clone(), c2.clone()]
                } else {
                    vec![]
                }
            }
        };
        let rev = move |inst: &Instance| {
            if inst.shape == sa {
                vec![c2.clone(), b2.clone()] // reversed
            } else {
                vec![]
            }
        };
        let mut one = build_inventory(vec![a.clone()], fwd);
        let mut two = build_inventory(vec![a.clone()], rev);
        // Compare as sets: same membership regardless of order.
        let key = |v: &mut Vec<Instance>| {
            v.sort_by_key(|x| format!("{:?}", x.shape));
        };
        key(&mut one);
        key(&mut two);
        assert_eq!(one, two, "inventory membership is order-independent");
        assert_eq!(one.len(), 3);
    }

    #[test]
    fn membership_is_independent_of_root_order() {
        // Two independent roots reaching a shared shape: reversing the *root* order
        // yields the same inventory membership.
        let mut i = Interner::new();
        let a = mk(&mut i, name("x"));
        let b0 = konst(i.integer(0));
        let b = mk(&mut i, b0);
        let c0 = konst(i.integer(1));
        let c = mk(&mut i, c0);
        let (sa, sb, cc) = (a.shape.clone(), b.shape.clone(), c.clone());
        let trans = move |inst: &Instance| {
            if inst.shape == sa || inst.shape == sb {
                vec![cc.clone()]
            } else {
                vec![]
            }
        };
        let mut fwd = build_inventory(vec![a.clone(), b.clone()], &trans);
        let mut rev = build_inventory(vec![b.clone(), a.clone()], &trans);
        let key = |v: &mut Vec<Instance>| v.sort_by_key(|x| format!("{:?}", x.shape));
        key(&mut fwd);
        key(&mut rev);
        assert_eq!(fwd, rev, "inventory membership is independent of root order");
        assert_eq!(fwd.len(), 3, "A, B, C admitted");
    }
}

// ── μ-aware body walk / call graph (v0.8.1 induction tail, step 1) ─────────────

mod bodywalk {
    use crate::analyzer::bodywalk::{callee_targets, reachable_closures};
    use crate::oracle::run_source;
    use crate::value::ValueRef;

    /// Run a program and return its final value (a closure, for these tests).
    fn run(src: &str) -> ValueRef {
        run_source(src).expect("program runs").0
    }

    #[test]
    fn self_recursion_is_a_self_edge() {
        // `f` is captured (a free variable in its own body); the shared env late-binds
        // it to the closure, so the call graph resolves the self-edge.
        let f = run("f = (n) => n == 0 ? 0 : f(n - 1)\nf");
        let targets = callee_targets(&f);
        assert_eq!(targets.len(), 1, "one call target");
        assert!(targets.contains(&f), "the target is f itself");
        // The reachable set is finite: the self-edge closes as a shape repeat.
        let reach = reachable_closures(f.clone());
        assert_eq!(reach.len(), 1, "only f is admitted");
        assert!(reach.contains(&f));
    }

    #[test]
    fn mutual_recursion_crosses_and_is_finite() {
        let even = run(
            "even = (n) => n == 0 ? true : odd(n - 1)\n\
             odd = (n) => n == 0 ? false : even(n - 1)\n\
             even",
        );
        let odd = {
            let t = callee_targets(&even);
            assert_eq!(t.len(), 1, "even calls one function");
            t[0].clone()
        };
        assert_ne!(odd, even, "even and odd are distinct closures");
        // odd calls back to even.
        let back = callee_targets(&odd);
        assert_eq!(back.len(), 1);
        assert!(back.contains(&even), "odd calls even");
        // The reachable set is {even, odd} — the cycle closes on the shape repeat.
        let reach = reachable_closures(even.clone());
        assert_eq!(reach.len(), 2, "even and odd admitted, no runaway");
        assert!(reach.contains(&even) && reach.contains(&odd));
    }

    #[test]
    fn a_leaf_function_has_no_edges() {
        // No application in the body → no call-graph successors; reachable = {self}.
        let id = run("id = (x) => x\nid");
        assert!(callee_targets(&id).is_empty());
        assert_eq!(reachable_closures(id.clone()).len(), 1);
    }

    #[test]
    fn nonrecursive_helper_is_reached_but_bounded() {
        // g calls h (a captured helper); h calls nothing. Reachable = {g, h}.
        let g = run(
            "h = (x) => x + 1\n\
             g = (n) => h(n)\n\
             g",
        );
        let targets = callee_targets(&g);
        assert_eq!(targets.len(), 1, "g calls h");
        let reach = reachable_closures(g);
        assert_eq!(reach.len(), 2, "g and h");
    }
}

// ── Input obligation §1 step 3 — accepted-domain derivation (induction tail) ───

mod obligation {
    use super::{ActKind, closure, konst, name};
    use crate::analyzer::application::SeatVerdict;
    use crate::analyzer::obligation::{accepted_domain, input_obligation};
    use crate::ast::{BindingRef, Pat, PatElem, Ref};
    use crate::contract::{Contract, ContractEnv, Kind};
    use crate::interner::Interner;
    use crate::value::ValueRef;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    fn eq(v: ValueRef) -> Contract {
        Contract::Equals(v)
    }
    fn two_params() -> Pat {
        Pat::Tuple(vec![
            PatElem::Pat(Pat::Bind("a".into())),
            PatElem::Pat(Pat::Bind("b".into())),
        ])
    }
    fn const_param(v: ValueRef) -> Pat {
        Pat::Tuple(vec![PatElem::Pat(Pat::Const(v))])
    }
    fn contract_param(nm: &str) -> Pat {
        Pat::Tuple(vec![PatElem::Pat(Pat::Contract(Ref::Immutable(
            BindingRef::Name(nm.into()),
        )))])
    }
    fn rest_param() -> Pat {
        Pat::Tuple(vec![
            PatElem::Pat(Pat::Bind("a".into())),
            PatElem::Rest(Some("rest".into())),
        ])
    }
    fn proven(v: &SeatVerdict) -> bool {
        matches!(v, SeatVerdict::Proven)
    }

    #[test]
    fn arity_obligation_proves_and_refutes_with_a_witness() {
        let mut i = Interner::new();
        let f = closure(&mut i, two_params(), name("a"), ActKind::Pure);
        let (a1, a2) = (i.integer(1), i.integer(2));
        // f(1, 2): arity matches → proven.
        assert!(proven(&input_obligation(
            &f,
            &[eq(a1.clone()), eq(a2)],
            &cenv(),
            &mut i
        )));
        // f(1): wrong arity → refuted, with a represented (callee, args) witness.
        match input_obligation(&f, &[eq(a1)], &cenv(), &mut i) {
            SeatVerdict::Refuted(w) => {
                assert_eq!(w.callee, f, "witness carries the callee");
                assert_eq!(w.arguments.len(), 1, "and the rejecting argument tuple");
            }
            other => panic!("arity mismatch must refute, got {other:?}"),
        }
    }

    #[test]
    fn contract_param_domain_governs_the_argument() {
        let mut i = Interner::new();
        let one = i.integer(1);
        let f = closure(&mut i, contract_param("Number"), konst(one), ActKind::Pure);
        // Sanity: the derived domain is a single-Number tuple.
        assert_eq!(
            accepted_domain(&f, &cenv(), &mut i),
            Some(Contract::tuple(vec![Contract::Kind(Kind::Number)], &mut i))
        );
        let five = i.integer(5);
        let hi = i.string("hi");
        assert!(
            proven(&input_obligation(&f, &[eq(five)], &cenv(), &mut i)),
            "5 : Number accepted"
        );
        match input_obligation(&f, &[eq(hi.clone())], &cenv(), &mut i) {
            SeatVerdict::Refuted(w) => {
                assert_eq!(w.arguments, vec![hi], "\"hi\" rejected, witnessed")
            }
            other => panic!("String arg must refute a Number param, got {other:?}"),
        }
        // A Top argument neither proves nor refutes.
        assert!(matches!(
            input_obligation(&f, &[Contract::Top], &cenv(), &mut i),
            SeatVerdict::Unproven
        ));
    }

    #[test]
    fn const_param_accepts_only_its_value() {
        let mut i = Interner::new();
        let zero = i.integer(0);
        let one = i.integer(1);
        let f = closure(&mut i, const_param(zero.clone()), konst(one), ActKind::Pure);
        assert!(
            proven(&input_obligation(&f, &[eq(zero)], &cenv(), &mut i)),
            "0 accepted"
        );
        let five = i.integer(5);
        assert!(
            matches!(
                input_obligation(&f, &[eq(five)], &cenv(), &mut i),
                SeatVerdict::Refuted(_)
            ),
            "5 rejected"
        );
    }

    #[test]
    fn rest_param_domain_is_deferred_not_unsound() {
        // A rest parameter's sound domain is length-precise (§4 restrictLen), owed.
        // Until then accepted_domain declines it, so the obligation is Unproven — never
        // the unsound over-approximation that would bless f() against `(a, ...rest)`.
        let mut i = Interner::new();
        let f = closure(&mut i, rest_param(), name("a"), ActKind::Pure);
        assert_eq!(accepted_domain(&f, &cenv(), &mut i), None);
        assert!(matches!(
            input_obligation(&f, &[], &cenv(), &mut i),
            SeatVerdict::Unproven
        ));
    }
}

// ── Outcome contribution §1 steps 4-5 — per-instance body summary (tail) ───────

mod outcome {
    use super::{ActKind, arm, closure, konst, matchx, name, one_param};
    use crate::analyzer::application::CompletionWithoutValue as C;
    use crate::analyzer::outcome::summarize_instance;
    use crate::ast::Pat;
    use crate::contract::{Contract, ContractEnv, Kind, Verdict, subcontract};
    use crate::interner::Interner;
    use crate::oracle::run_source;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }

    #[test]
    fn identity_body_produces_the_narrowed_parameter() {
        let mut i = Interner::new();
        let f = closure(&mut i, one_param("n"), name("n"), ActKind::Pure);
        let o = summarize_instance(&f, &[num()], &cenv(), &mut i).unwrap();
        assert_eq!(
            o.produced.erase(&mut i),
            num(),
            "(n) => n applied to Number produces Number"
        );
        assert!(
            matches!(o.completion, C::ProvenAbsent),
            "always produces — no fall-through"
        );
    }

    #[test]
    fn constant_body_produces_the_constant() {
        let mut i = Interner::new();
        let five = i.integer(5);
        let f = closure(&mut i, one_param("n"), konst(five.clone()), ActKind::Pure);
        let o = summarize_instance(&f, &[num()], &cenv(), &mut i).unwrap();
        assert_eq!(o.produced.erase(&mut i), Contract::Equals(five));
        assert!(matches!(o.completion, C::ProvenAbsent));
    }

    #[test]
    fn a_partial_match_body_may_fall_through() {
        // (n) => n :: { 0 => 1 } — over a Number the single arm is non-exhaustive, so
        // the body may complete without a value: UnprovenPossible.
        let mut i = Interner::new();
        let (zero, one) = (i.integer(0), i.integer(1));
        let body = matchx(
            Some(name("n")),
            vec![arm(Some(Pat::Const(zero)), None, konst(one.clone()))],
        );
        let f = closure(&mut i, one_param("n"), body, ActKind::Pure);
        let o = summarize_instance(&f, &[num()], &cenv(), &mut i).unwrap();
        assert_eq!(
            o.produced.erase(&mut i),
            Contract::Equals(one),
            "the matching arm produces 1"
        );
        assert!(
            matches!(o.completion, C::UnprovenPossible),
            "may fall through"
        );
    }

    #[test]
    fn recursion_is_coarse_and_terminating() {
        // A self-recursive body summarized over an abstract (non-singleton) argument:
        // the recursive call does not constant-fold, so it returns Top and the summary
        // terminates rather than re-entering the body. Sound but coarse (produced Top);
        // the §6 induction sharpens it.
        let f = run_source("f = (n) => n == 0 ? 0 : f(n - 1)\nf").unwrap().0;
        let mut i = Interner::new();
        let o = summarize_instance(&f, &[num()], &cenv(), &mut i).expect("summarizes");
        assert!(!o.produced.is_bottom(), "a real result contract");
        // The recursive branch coarsened to Top, so the produced contract admits
        // everything (Top ⊑ produced) — sound, and the summary terminated.
        let erased = o.produced.erase(&mut i);
        assert!(
            matches!(
                subcontract(&Contract::Top, &erased, &mut i),
                Verdict::Proven
            ),
            "coarse: {erased:?}"
        );
        assert!(
            matches!(o.completion, C::ProvenAbsent),
            "the total ternary never falls through"
        );
    }
}

// ── Return induction §6 — the joint vector pass (induction tail) ──────────────

mod induction {
    use crate::analyzer::bodywalk::callee_targets;
    use crate::analyzer::induction::{Candidate, Claim, joint_vector_pass};
    use crate::contract::{Contract, ContractEnv, Kind};
    use crate::interner::Interner;
    use crate::oracle::run_source;
    use crate::value::ValueRef;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }
    fn boolean() -> Contract {
        Contract::Kind(Kind::Boolean)
    }
    fn cand(callee: ValueRef, contract: Contract) -> Candidate {
        Candidate {
            callee,
            args: vec![Contract::Kind(Kind::Number)],
            claim: Claim::Return(contract),
            cutoff: false,
        }
    }

    #[test]
    fn factorial_returns_number_by_induction() {
        // Under the hypothesis `f : Number`, the recursive `f(n-1)` returns Number, so
        // `n * f(n-1)` is Number and the body produces ⊑ Number — the induction closes.
        let f = run_source("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf")
            .unwrap()
            .0;
        let mut i = Interner::new();
        assert!(
            joint_vector_pass(&[cand(f, num())], &cenv(), &mut i),
            "f returns Number"
        );
    }

    #[test]
    fn a_false_return_claim_is_rejected() {
        // Claiming `f : String` fails: under that hypothesis the body `n * f(n-1)` is a
        // type error and does not produce a String.
        let f = run_source("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf")
            .unwrap()
            .0;
        let mut i = Interner::new();
        assert!(!joint_vector_pass(
            &[cand(f, Contract::Kind(Kind::String))],
            &cenv(),
            &mut i
        ));
    }

    #[test]
    fn mutual_recursion_closes_jointly() {
        // even/odd both return Boolean — provable only with BOTH hypotheses installed
        // (each body calls the other).
        let even = run_source(
            "even = (n) => n == 0 ? true : odd(n - 1)\n\
             odd = (n) => n == 0 ? false : even(n - 1)\n\
             even",
        )
        .unwrap()
        .0;
        let odd = callee_targets(&even)[0].clone();
        let mut i = Interner::new();
        let members = [cand(even.clone(), boolean()), cand(odd.clone(), boolean())];
        assert!(
            joint_vector_pass(&members, &cenv(), &mut i),
            "even/odd jointly return Boolean"
        );

        // Vector failure: a wrong claim on one member fails the whole component.
        let bad = [cand(even, boolean()), cand(odd, num())];
        assert!(
            !joint_vector_pass(&bad, &cenv(), &mut i),
            "one wrong claim ⇒ component unproven"
        );
    }
}

// ── Multi-SCC driver §6/§13.2a — reverse-topological hypothesis carrying (tail) ─

mod driver {
    use crate::analyzer::bodywalk::callee_targets;
    use crate::analyzer::induction::{Candidate, Claim, joint_vector_pass, prove_facts};
    use crate::contract::{Contract, ContractEnv, Kind};
    use crate::interner::Interner;
    use crate::oracle::run_source;
    use crate::value::ValueRef;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }
    fn boolean() -> Contract {
        Contract::Kind(Kind::Boolean)
    }
    fn cand(callee: ValueRef, contract: Contract) -> Candidate {
        Candidate { callee, args: vec![Contract::Kind(Kind::Number)], claim: Claim::Return(contract), cutoff: false }
    }

    /// `quad` calls `double`; `double` is a leaf. Returns `(double, quad)`.
    fn double_quad() -> (ValueRef, ValueRef) {
        let quad = run_source("double = (n) => n * 2\nquad = (n) => double(n) + double(n)\nquad").unwrap().0;
        let double = callee_targets(&quad)[0].clone();
        (double, quad)
    }

    #[test]
    fn a_dependent_and_its_nonrecursive_dependency_both_prove() {
        let (double, quad) = double_quad();
        let mut i = Interner::new();

        // `double` is non-recursive, so its body summary resolves `double(n) → Number`
        // directly (Archive8 unification); `quad`'s body `double(n) + double(n)` is thus
        // Number, and quad proves — no reverse-topo hypothesis-carrying needed for a
        // non-recursive dependency (that path is exercised by the mutual even/odd test).
        assert!(
            joint_vector_pass(&[cand(quad.clone(), num())], &cenv(), &mut i),
            "quad : Number via direct double"
        );

        // The multi-SCC driver still proves the whole set.
        let r = prove_facts(
            vec![cand(double, num()), cand(quad, num())],
            &cenv(),
            &mut i,
        );
        assert_eq!(r.proven.len(), 2, "double AND quad proven");
        assert!(r.unproven.is_empty());
    }

    #[test]
    fn the_driver_is_independent_of_candidate_list_order() {
        let (double, quad) = double_quad();
        let mut i = Interner::new();
        let fwd = prove_facts(
            vec![cand(double.clone(), num()), cand(quad.clone(), num())],
            &cenv(),
            &mut i,
        );
        let rev = prove_facts(
            vec![cand(quad, num()), cand(double, num())],
            &cenv(),
            &mut i,
        );
        assert_eq!(fwd.proven.len(), 2);
        assert_eq!(
            rev.proven.len(),
            2,
            "reversing the candidate list changes nothing — SCC order is graph-intrinsic"
        );
    }

    #[test]
    fn a_vector_failure_leaves_only_its_component_unproven() {
        // `double : Number` is independent and provable; claiming `quad : String` fails.
        // The failure must not poison `double` — and `double`'s fact is still used to
        // reduce `quad`'s body (which is why `quad` fails against String, not Top).
        let (double, quad) = double_quad();
        let mut i = Interner::new();
        let r = prove_facts(
            vec![
                cand(double.clone(), num()),
                cand(quad, Contract::Kind(Kind::String)),
            ],
            &cenv(),
            &mut i,
        );
        assert_eq!(r.proven.len(), 1, "double still proven");
        assert!(r.proven.iter().any(|c| c.callee == double));
        assert_eq!(r.unproven.len(), 1, "only quad : String is unproven");
    }

    #[test]
    fn a_mutual_nest_is_one_component_in_the_driver() {
        // even/odd form one SCC (each calls the other); the driver proves them jointly
        // as a single component — no reverse-topo split, one vector pass.
        let even = run_source(
            "even = (n) => n == 0 ? true : odd(n - 1)\n\
             odd = (n) => n == 0 ? false : even(n - 1)\n\
             even",
        )
        .unwrap()
        .0;
        let odd = callee_targets(&even)[0].clone();
        let mut i = Interner::new();
        let r = prove_facts(
            vec![cand(even, boolean()), cand(odd, boolean())],
            &cenv(),
            &mut i,
        );
        assert_eq!(
            r.proven.len(),
            2,
            "even and odd proven together as one component"
        );
        assert!(r.unproven.is_empty());
    }
}

// ── Return-fact inference §6 — autonomous claim proposal + the driver (tail) ────

mod inference {
    use crate::analyzer::induction::infer_return_fact;
    use crate::contract::{Contract, ContractEnv, Kind, Verdict, subcontract};
    use crate::interner::Interner;
    use crate::oracle::run_source;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }
    /// Contract equivalence: mutual subcontract (so `Union(Number, Number)` counts as
    /// `Number`, the proposal's un-normalized shape).
    fn equiv(a: &Contract, b: &Contract, i: &mut Interner) -> bool {
        matches!(subcontract(a, b, i), Verdict::Proven) && matches!(subcontract(b, a, i), Verdict::Proven)
    }

    #[test]
    fn infers_factorial_returns_number_over_its_domain() {
        // No supplied claim: the base `1` generalizes to Number, and the induction
        // proves `n * f(n-1)`'s return under it. Over the **untyped (Top) accepted
        // domain**, the successful arithmetic paths still produce Number; non-Number
        // inputs are rejected by the separate safety fact rather than becoming return
        // alternatives. The inferred return is therefore tighter than Top.
        let f = run_source("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf")
            .unwrap()
            .0;
        let mut i = Interner::new();
        let fact =
            infer_return_fact(&f, None, &cenv(), &mut i).expect("a return fact is inferred");
        assert!(
            matches!(subcontract(&num(), &fact, &mut i), Verdict::Proven),
            "Number ⊑ inferred {fact:?}"
        );
        let hi = i.string("hi");
        assert!(
            !fact.contains(&hi),
            "the fact admits no String — tighter than Top: {fact:?}"
        );
    }

    #[test]
    fn infers_even_and_odd_return_boolean() {
        // Mutual: each base (`true` / `false`) generalizes to Boolean; the recursive
        // tail call drops out of the base union under the Bottom pin, so the proposal
        // is Boolean (not Top), and the joint pass proves it.
        let even = run_source(
            "even = (n) => n == 0 ? true : odd(n - 1)\n\
             odd = (n) => n == 0 ? false : even(n - 1)\n\
             even",
        )
        .unwrap()
        .0;
        let mut i = Interner::new();
        let fact = infer_return_fact(&even, None, &cenv(), &mut i)
            .expect("even's return is inferred");
        assert!(
            equiv(&fact, &Contract::Kind(Kind::Boolean), &mut i),
            "even returns Boolean, got {fact:?}"
        );
    }

    #[test]
    fn identity_recursion_infers_a_sound_overapproximation() {
        // `f = (n) => n == 0 ? 0 : f(n-1)` truly returns 0, but the Kind-generalized
        // claim is Number — a sound over-approximation (Equals(0) ⊑ Number).
        let f = run_source("f = (n) => n == 0 ? 0 : f(n - 1)\nf").unwrap().0;
        let mut i = Interner::new();
        let fact =
            infer_return_fact(&f, None, &cenv(), &mut i).expect("a return fact is inferred");
        let zero = Contract::Equals(i.integer(0));
        assert!(
            matches!(subcontract(&zero, &fact, &mut i), Verdict::Proven),
            "0 ⊑ inferred return {fact:?}"
        );
        assert!(equiv(&fact, &num(), &mut i), "and it generalizes to Number");
    }

    #[test]
    fn a_baseless_recursion_yields_no_fact() {
        // `loop = (n) => loop(n)` has no base — the proposal is Bottom, rejected, so no
        // fact is asserted (→ coarse Top at a call site, never an overclaim).
        let f = run_source("loop = (n) => loop(n)\nloop").unwrap().0;
        let mut i = Interner::new();
        assert!(
            infer_return_fact(&f, None, &cenv(), &mut i).is_none(),
            "no fact for a baseless recursion"
        );
    }
}

// ── analyze_apply rewiring — a recursive call site infers its return (tail) ─────

mod apply_wiring {
    use super::{analyze, apply, arm, empty, konst, matchx, name, nc};
    use crate::contract::{Contract, Kind, Verdict, subcontract};
    use crate::interner::Interner;
    use crate::oracle::run_source;

    fn equiv(a: &Contract, b: &Contract, i: &mut Interner) -> bool {
        matches!(subcontract(a, b, i), Verdict::Proven) && matches!(subcontract(b, a, i), Verdict::Proven)
    }

    #[test]
    fn a_recursive_call_infers_its_return_over_the_argument() {
        // `f(x)` with `x : Number` — `analyze_apply` now infers f's return over the
        // call-site argument, giving pure Number rather than Top.
        let mut i = Interner::new();
        let f = run_source("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf").unwrap().0;
        let mut env = empty();
        env.insert("f".into(), Contract::Equals(f));
        env.insert("x".into(), Contract::Kind(Kind::Number));

        let call = apply(name("f"), vec![name("x")]);
        let a = analyze(&call, &env, &nc(), &mut i);
        assert!(a.accepted(), "the call is accepted: {:?}", a.findings);
        assert!(equiv(&a.contract, &Contract::Kind(Kind::Number), &mut i), "f(x) : Number, got {:?}", a.contract);
    }

    #[test]
    fn an_inferred_boolean_return_satisfies_a_tested_seat() {
        // `even(x) ? 1 : 2` — even(x) is inferred Boolean, so the guard's tested seat is
        // satisfied with **no** finding (a coarse Top would raise a tested-seat warning).
        let mut i = Interner::new();
        let even = run_source(
            "even = (n) => n == 0 ? true : odd(n - 1)\n\
             odd = (n) => n == 0 ? false : even(n - 1)\n\
             even",
        )
        .unwrap()
        .0;
        let mut env = empty();
        env.insert("even".into(), Contract::Equals(even));
        env.insert("x".into(), Contract::Kind(Kind::Number));

        let guard = apply(name("even"), vec![name("x")]);
        let m = matchx(None, vec![arm(None, Some(guard), konst(i.integer(1))), arm(None, None, konst(i.integer(2)))]);
        let a = analyze(&m, &env, &nc(), &mut i);
        assert!(a.findings.is_empty(), "even(x) : Boolean satisfies the guard with no finding: {:?}", a.findings);
    }

    #[test]
    fn an_unconstrained_argument_stays_sound() {
        // `f(x)` with `x : Top` — no call-site constraint. The successful return
        // over-approximation still admits Number; body safety is a separate judgment.
        let mut i = Interner::new();
        let f = run_source("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf").unwrap().0;
        let mut env = empty();
        env.insert("f".into(), Contract::Equals(f));
        env.insert("x".into(), Contract::Top);

        let call = apply(name("f"), vec![name("x")]);
        let a = analyze(&call, &env, &nc(), &mut i);
        assert!(matches!(subcontract(&Contract::Kind(Kind::Number), &a.contract, &mut i), Verdict::Proven), "Number ⊑ {:?}", a.contract);
    }
}

// ── Realized-witness refutation §6 — the permanent third voice (tail) ──────────

mod refute {
    use crate::analyzer::refute::{ClaimVerdict, check_return_claim, realized_refutation};
    use crate::ast::{Arg, Expr};
    use crate::contract::{Contract, ContractEnv, Kind};
    use crate::interner::Interner;
    use crate::oracle::{BoundedOutcome, eval_expr_bounded, run_source_in};
    use crate::rational::Rational;
    use crate::value::ValueRef;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }
    fn string() -> Contract {
        Contract::Kind(Kind::String)
    }
    /// factorial, built **in `i`** — evaluating it needs the same interner (interned
    /// `==` is pointer identity, so a cross-interner `n == 0` would never fire).
    fn factorial(i: &mut Interner) -> ValueRef {
        run_source_in("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf", i).unwrap().0
    }
    fn call(callee: ValueRef, arg: ValueRef) -> Expr {
        Expr::Apply { callee: Box::new(Expr::Const(callee)), args: vec![Arg::Expr(Expr::Const(arg))] }
    }

    #[test]
    fn realized_refutation_disproves_a_wrong_return_claim() {
        // f does not return String: f(0) = 1 (a Number) ∉ String — a represented witness.
        let mut i = Interner::new();
        let f = factorial(&mut i);
        let w = realized_refutation(&f, &[num()], &string(), &mut i).expect("String claim is refuted");
        assert!(!string().contains(&w.produced), "the witness value is genuinely not a String");
        assert_eq!(w.arguments.len(), 1, "a represented single-argument tuple");
    }

    #[test]
    fn a_true_claim_has_no_realized_witness_and_terminates() {
        // f DOES return Number over Number. The [Number] sample includes -1, on which f
        // diverges — the call-depth bound skips it (OutOfFuel), so the search both finds
        // no witness AND terminates (divergence-safety).
        let mut i = Interner::new();
        let f = factorial(&mut i);
        assert!(realized_refutation(&f, &[num()], &num(), &mut i).is_none());
    }

    #[test]
    fn check_return_claim_is_three_voiced() {
        let mut i = Interner::new();
        let f = factorial(&mut i);
        // Proven by induction; refuted by a realized witness (permanent); and true but
        // neither provable (n could be negative → n·positive not provably positive) nor
        // disprovable (no *completing* input yields a non-positive) → Unproven.
        assert!(matches!(
            check_return_claim(&f, &[num()], &num(), &cenv(), &mut i),
            ClaimVerdict::Proven
        ));
        assert!(matches!(
            check_return_claim(&f, &[num()], &string(), &cenv(), &mut i),
            ClaimVerdict::Refuted(_)
        ));
        let positive = Contract::Greater(Rational::from(0));
        assert!(matches!(
            check_return_claim(&f, &[num()], &positive, &cenv(), &mut i),
            ClaimVerdict::Unproven
        ));
    }

    #[test]
    fn the_depth_bound_cuts_off_divergence() {
        // A baseless recursion never completes → OutOfFuel (the call-depth bound), not a
        // hang; a terminating call completes within the bound.
        let mut i = Interner::new();
        let loop_fn = run_source_in("loop = (n) => loop(n)\nloop", &mut i).unwrap().0;
        let zero = i.integer(0);
        assert!(matches!(eval_expr_bounded(&call(loop_fn, zero), 5_000, &mut i), BoundedOutcome::OutOfFuel));
        let f = factorial(&mut i);
        let five = i.integer(5);
        assert!(matches!(eval_expr_bounded(&call(f, five), 200_000, &mut i), BoundedOutcome::Produced(_)));
    }
}

// ── Fact identity — instance + domain keyed hypotheses (Archive4 review §5) ─────

mod fact_identity {
    use crate::analyzer::bodywalk::callee_targets;
    use crate::analyzer::induction::infer_return_fact;
    use crate::contract::{Contract, ContractEnv, Kind, Verdict, subcontract};
    use crate::interner::Interner;
    use crate::oracle::run_source_in;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    fn is_num(c: &Contract, i: &mut Interner) -> bool {
        matches!(
            subcontract(c, &Contract::Kind(Kind::Number), i),
            Verdict::Proven
        )
    }

    #[test]
    fn same_shape_different_captures_are_not_aliased() {
        // `make(1)` and `make("s")` are one shape, different captures. A candidate/return
        // fact must stay attached to the concrete instance, not the shape.
        let mut i = Interner::new();
        let h = run_source_in(
            "make = (v) => () => v\n\
             a = make(1)\n\
             b = make(\"s\")\n\
             h = (c, d) => c ? 0 : (d ? a() : b())\n\
             h",
            &mut i,
        )
        .unwrap()
        .0;
        let targets = callee_targets(&h);
        assert_eq!(targets.len(), 2, "h calls two closures");
        assert_ne!(
            targets[0], targets[1],
            "a and b are distinct values despite one shape"
        );

        // Each closure keeps its own return fact — one Number, one String.
        let facts: Vec<Contract> = targets
            .iter()
            .filter_map(|c| infer_return_fact(c, None, &cenv(), &mut i))
            .collect();
        assert_eq!(facts.len(), 2, "both closures infer a fact: {facts:?}");
        let a_num = is_num(&facts[0], &mut i);
        let b_num = is_num(&facts[1], &mut i);
        assert!(
            a_num ^ b_num,
            "exactly one is Number, one is String — not aliased: {facts:?}"
        );

        // The adversarial payoff: with shape-only keying, `a()`/`b()` would share a fact
        // and `h : Number` could falsely close — but `h(false,false) → "s"`. The instance
        // key rejects the false Number.
        let h_fact = infer_return_fact(&h, None, &cenv(), &mut i);
        assert!(
            !matches!(&h_fact, Some(f) if is_num(f, &mut i)),
            "h must not falsely infer a Number return: {h_fact:?}"
        );
    }

    #[test]
    fn a_hypothesis_applies_only_within_its_input_domain() {
        // Lock the domain-indexed lookup law *directly* (Archive5 §4) — no execution,
        // recursion, or oracle. A fact `f : [Number] → Boolean` is consumable exactly
        // when the call's argument domain is `⊑ [Number]`.
        use crate::analyzer::induction::{Claim, Hypothesis, hypothesis_for, with_hypotheses};
        let mut i = Interner::new();
        let f = run_source_in("f = (n) => n\nf", &mut i).unwrap().0;
        let hyp = Hypothesis { callee: f.clone(), input: vec![Contract::Kind(Kind::Number)], claim: Claim::Return(Contract::Kind(Kind::Boolean)) };
        let one = Contract::Equals(i.integer(1));
        with_hypotheses(vec![hyp], || {
            let boolean = Some(Contract::Kind(Kind::Boolean));
            assert_eq!(hypothesis_for(&f, &[Contract::Kind(Kind::Number)], &mut i), boolean, "[Number] ⊑ [Number]");
            assert_eq!(hypothesis_for(&f, std::slice::from_ref(&one), &mut i), boolean, "[Equals(1)] ⊑ [Number]");
            assert_eq!(hypothesis_for(&f, &[Contract::Kind(Kind::String)], &mut i), None, "[String] ⊄ [Number]");
            assert_eq!(hypothesis_for(&f, &[Contract::Top], &mut i), None, "[Top] ⊄ [Number]");
        });
    }

    // The domain-rejection law (v0.8.1's `call input ⊆ fact input domain`) is locked
    // *directly* by `a_hypothesis_applies_only_within_its_input_domain` above — the even/odd
    // mutual path no longer exercises it, since `infer_inner` now propagates a consistent
    // domain to same-arity partners (so no out-of-domain lookup is generated). The direct
    // unit test is exactly what the review asked for in place of that indirect coverage.
}

// ── Interprocedural body safety — replaces the closed-call oracle fold (Archive6) ──

mod body_safety {
    use super::{Analysis, analyze, apply, empty, konst, name, nc};
    use crate::contract::{Contract, Kind};
    use crate::interner::Interner;
    use crate::oracle::run_source_in;

    /// Run `src` (whose last statement is the entry function), bind it to `callee` and
    /// each `(name, contract)` argument, and analyze `callee(arg names…)`.
    fn analyze_call(src: &str, callee: &str, args: &[(&str, Contract)]) -> Analysis {
        let mut i = Interner::new();
        let f = run_source_in(src, &mut i).unwrap().0;
        let mut env = empty();
        env.insert(callee.into(), Contract::Equals(f));
        let mut arg_exprs = Vec::new();
        for (nm, c) in args {
            env.insert((*nm).into(), c.clone());
            arg_exprs.push(name(nm));
        }
        analyze(&apply(name(callee), arg_exprs), &env, &nc(), &mut i)
    }
    fn num() -> Contract {
        Contract::Kind(Kind::Number)
    }

    #[test]
    fn direct_body_trap_is_rejected() {
        let a = analyze_call("bad = () => 1 + \"x\"\nbad", "bad", &[]);
        assert!(!a.accepted(), "the callee body traps (1 + \"x\"): {:?}", a.findings);
    }

    #[test]
    fn transitive_body_trap_is_rejected() {
        // bad calls helper, whose body traps — the dependency component settles first,
        // and its refutation must reach bad's call site.
        let a = analyze_call("helper = () => 1 + \"x\"\nbad = () => helper()\nbad", "bad", &[]);
        assert!(!a.accepted(), "a transitive body trap must be surfaced: {:?}", a.findings);
    }

    #[test]
    fn a_safe_transitive_call_is_accepted() {
        let a = analyze_call("helper = (x) => x + 1\nf = (x) => helper(x)\nf", "f", &[("n", num())]);
        assert!(a.accepted(), "no trap anywhere: {:?}", a.findings);
    }

    #[test]
    fn a_recursive_safe_body_terminates_without_false_findings() {
        // factorial: safety, completion, and return all close over the covering Number
        // fact, so the recursive operand is safe and analysis terminates.
        let a = analyze_call("f = (n) => n == 0 ? 1 : n * f(n - 1)\nf", "f", &[("n", num())]);
        assert!(a.accepted(), "factorial accepted: {:?}", a.findings);
        assert!(a.findings.is_empty(), "no false findings from the coarsened recursion: {:?}", a.findings);
    }

    #[test]
    fn a_recursive_body_with_a_local_trap_is_rejected() {
        let a = analyze_call("f = (n) => n == 0 ? (1 + \"x\") : f(n - 1)\nf", "f", &[("n", num())]);
        assert!(!a.accepted(), "the local trap must be surfaced: {:?}", a.findings);
    }

    #[test]
    fn a_trap_in_a_mutual_partner_reaches_the_caller() {
        let a = analyze_call(
            "f = (n) => n == 0 ? 0 : g(n - 1)\n\
             g = (n) => n == 0 ? (1 + \"x\") : f(n - 1)\n\
             f",
            "f",
            &[("n", num())],
        );
        assert!(!a.accepted(), "g's trap must reach f's call site: {:?}", a.findings);
    }

    #[test]
    fn diverging_recursion_terminates_without_execution() {
        // The architectural proof: `loop()` would diverge if executed, but body safety
        // analyzes the body once and never runs it — so this test *terminating* is the
        // evidence the oracle-execution coupling is gone. No trap (divergence ≠ trap).
        let a = analyze_call("loop = () => loop()\nloop", "loop", &[]);
        assert!(a.accepted(), "divergence is not a trap: {:?}", a.findings);
    }

    // ── Archive7 §11 — the actual-call-edge adversarial cases ─────────────────────

    #[test]
    fn a_parameter_callee_trap_is_rejected() {
        // §11.1: `bad` is passed as a PARAMETER (not a capture), so a syntactic
        // reachable-closure walk misses it. The actual-edge walk resolves `f = bad` from
        // the argument value and surfaces bad's body trap.
        let mut i = Interner::new();
        let bad = run_source_in("bad = () => 1 + \"x\"\nbad", &mut i).unwrap().0;
        let invoke = run_source_in("invoke = (f) => f()\ninvoke", &mut i).unwrap().0;
        let mut env = empty();
        env.insert("invoke".into(), Contract::Equals(invoke));
        let a = analyze(&apply(name("invoke"), vec![konst(bad)]), &env, &nc(), &mut i);
        assert!(!a.accepted(), "invoke(bad) must be rejected — bad() traps: {:?}", a.findings);
    }

    #[test]
    fn a_callee_is_checked_over_its_actual_edge_domain() {
        // §11.2/§11.4: root(Number) calls helper("x"). helper must be analyzed over the
        // actual [String] edge — where `"x" + 1` traps — NOT over root's Number domain.
        let a = analyze_call("helper = (x) => x + 1\nroot = (n) => helper(\"x\")\nroot", "root", &[("n", num())]);
        assert!(!a.accepted(), "helper(\"x\") traps over its actual String domain: {:?}", a.findings);
    }

    #[test]
    fn a_narrowed_dead_branch_is_not_a_false_trap() {
        // §11.3: helper(0) — the trapping branch is dead for x == 0, so analyzing helper
        // over [Equals(0)] must not surface the dead `1 + "x"` branch.
        let a = analyze_call(
            "helper = (x) => x == 0 ? 1 : 1 + \"x\"\nroot = () => helper(0)\nroot",
            "root",
            &[],
        );
        assert!(a.accepted(), "helper(0)'s bad branch is dead — no false trap: {:?}", a.findings);
    }

    // ── Archive8 §11 — (instance, input-domain) identity + multi-callee + return facts ─

    #[test]
    fn same_shape_different_captures_are_not_cut_off() {
        // §11.1: b = make(bad), c = make(b) share the inner Lambda shape but capture
        // different values. c() → b() → bad() traps. Keying the cutoff by *instance*
        // (not shape) must analyze b's capture-dependent body.
        let mut i = Interner::new();
        let c = run_source_in(
            "bad = () => 1 + \"x\"\nmake = (f) => () => f()\nb = make(bad)\nc = make(b)\nc",
            &mut i,
        )
        .unwrap()
        .0;
        let mut env = empty();
        env.insert("c".into(), Contract::Equals(c));
        let a = analyze(&apply(name("c"), vec![]), &env, &nc(), &mut i);
        assert!(!a.accepted(), "c() → b() → bad() traps: {:?}", a.findings);
    }

    #[test]
    fn a_recursive_call_over_a_new_domain_is_not_silently_accepted() {
        // §11.2: f(0) recurses to f("x"); over String, `x + 1` traps. The second f is a
        // repeated shape and therefore not admitted through this path; the honest graph
        // result is Unproven, which must block rather than silently accept.
        let mut i = Interner::new();
        let f = run_source_in("f = (x) => x == 0 ? f(\"x\") : x + 1\nf", &mut i).unwrap().0;
        let mut env = empty();
        env.insert("f".into(), Contract::Equals(f));
        let zero = i.integer(0);
        let a = analyze(&apply(name("f"), vec![konst(zero)]), &env, &nc(), &mut i);
        assert!(!a.accepted(), "f(0) → f(\"x\") → \"x\" + 1 traps: {:?}", a.findings);
    }

    #[test]
    fn a_multiple_callee_alternative_trap_is_rejected() {
        // §11.3: (b ? bad : good)() — the callee is Union(Equals(bad), Equals(good)); the
        // bad alternative must be inspected, not bypassed as a non-singleton callee.
        let a = analyze_call(
            "bad = () => 1 + \"x\"\ngood = () => 1\nroot = (b) => (b ? bad : good)()\nroot",
            "root",
            &[("c", Contract::Kind(Kind::Boolean))],
        );
        assert!(!a.accepted(), "the bad alternative traps: {:?}", a.findings);
    }

    #[test]
    fn a_return_dependent_safe_path_is_accepted() {
        // §11.4: always() returns true, so `always() ? 1 : 1 + "x"`'s bad branch is dead.
        // The callee's *exact* non-recursive return (Equals(true), not generalized
        // Boolean) must be preserved for the dead-arm to fire.
        let a = analyze_call(
            "always = () => true\nroot = () => always() ? 1 : 1 + \"x\"\nroot",
            "root",
            &[],
        );
        assert!(
            a.accepted(),
            "always() = true kills the bad branch: {:?}",
            a.findings
        );
    }
}

// ── Archive9 §17 — alternative totality + widened-domain refutation discipline ──

mod alternatives {
    use super::{analyze, apply, empty, konst, name, nc, prim};
    use crate::ast::PrimOp;
    use crate::contract::{Contract, Kind, Verdict, subcontract};
    use crate::interner::Interner;
    use crate::oracle::run_source_in;

    #[test]
    fn a_non_function_alternative_is_rejected() {
        // §17.2: `(b ? good : 1)()` — the `1` alternative is provably not callable, so a
        // represented execution traps. It must not vanish because a known function
        // alternative is present.
        let mut i = Interner::new();
        let root = run_source_in("good = () => 1\nroot = (b) => (b ? good : 1)()\nroot", &mut i).unwrap().0;
        let mut env = empty();
        env.insert("root".into(), Contract::Equals(root));
        env.insert("c".into(), Contract::Kind(Kind::Boolean));
        let a = analyze(&apply(name("root"), vec![name("c")]), &env, &nc(), &mut i);
        assert!(!a.accepted(), "the non-function alternative `1` traps when called: {:?}", a.findings);
    }

    #[test]
    fn an_unknown_function_alternative_is_not_sharpened_away() {
        // §17.3: callee = Equals(good) ∪ Kind(Function). The unknown alternative may
        // return anything, so the application must NOT sharpen to `good`'s exact
        // `Equals(1)` — otherwise a downstream `+ 1` would look proven safe.
        let mut i = Interner::new();
        let good = run_source_in("good = () => 1\ngood", &mut i).unwrap().0;
        let mut env = empty();
        env.insert(
            "f".into(),
            Contract::union(
                Contract::Equals(good),
                Contract::Kind(Kind::Function),
                &mut i,
            ),
        );
        let a = analyze(&apply(name("f"), vec![]), &env, &nc(), &mut i);
        let one = Contract::Equals(i.integer(1));
        assert!(
            !matches!(subcontract(&a.contract, &one, &mut i), Verdict::Proven),
            "the unknown alternative must keep the result unsharpened, got {:?}",
            a.contract
        );
        // And a downstream numeric use is not proven safe.
        let b = analyze(&prim(PrimOp::Add, vec![apply(name("f"), vec![]), konst(i.integer(1))]), &env, &nc(), &mut i);
        assert!(!b.findings.is_empty(), "the unknown callee leaves the downstream `+ 1` unproven");
    }
}

// ── Archive9 §17.1/§17.4 — widened-domain refutation + advance-bounded termination ──

mod recursive_domains {
    use super::{analyze, apply, empty, konst, name, nc};
    use crate::contract::Contract;
    use crate::interner::Interner;
    use crate::oracle::run_source_in;
    use crate::rational::Rational;

    #[test]
    #[ignore = "BLOCKER 1b: the safe exact chain f(0) -> f(1) crosses a repeated shape. Section 4a admits no new node through that path, so proving this call requires grounding section 4's exact-singleton fact-chain mechanism. The retired reaching checker accepted it by following domains forward; do not restore that mechanism."]
    fn a_widened_domain_trap_does_not_refute_the_narrower_call() {
        // §17.1: f(0) → f(1) → 1 is concretely safe. Widening `Equals(1)` to `Number`
        // would make `1 + "x"` live, but that trap has no witness represented in
        // `Equals(1)` — it must not refute the call. The exact edge is known, but §4a's
        // shape-repeat cutoff cannot admit it as another ordinary fact node; grounding's
        // exact-singleton chain is the separate proof license this test awaits.
        let mut i = Interner::new();
        let f = run_source_in(
            "f = (x) => x == 0 ? f(1) : (x == 1 ? 1 : 1 + \"x\")\nf",
            &mut i,
        )
        .unwrap()
        .0;
        let mut env = empty();
        env.insert("f".into(), Contract::Equals(f));
        let zero = i.integer(0);
        let a = analyze(&apply(name("f"), vec![konst(zero)]), &env, &nc(), &mut i);
        assert!(a.accepted(), "f(0) → f(1) → 1 is safe; the Number-only trap must not refute it: {:?}", a.findings);
    }

    #[test]
    fn a_growing_non_singleton_recursive_domain_terminates() {
        // §17.4: f(x + y, y) over Ranges generates Range(0,1) → Range(1,3) → Range(2,5)
        // → … — an unbounded chain of distinct domains. Termination must come from the
        // finite admitted basis (a computed `Range` is not in the program's literal
        // vocabulary, so the recursive edge widens into the Kind basis and stabilizes),
        // not from a fuel counter. This test *terminating* is the assertion.
        let mut i = Interner::new();
        let f = run_source_in("f = (x, y) => f(x + y, y)\nf", &mut i).unwrap().0;
        let mut env = empty();
        env.insert("f".into(), Contract::Equals(f));
        env.insert("a".into(), Contract::Range(Rational::from(0), Rational::from(1)));
        env.insert("b".into(), Contract::Range(Rational::from(1), Rational::from(2)));
        let a = analyze(&apply(name("f"), vec![name("a"), name("b")]), &env, &nc(), &mut i);
        // No claim about the verdict — only that analysis terminated by construction.
        let _ = a.accepted();
    }
}

#[test]
fn a_growing_union_recursive_domain_terminates() {
    // Archive10 §11–§12: `f = (x, b) => f(b ? x : 0, b)` grows the first argument's
    // contract structurally — Equals(0) → Union(E0,E0) → Union(Union(E0,E0),E0) → … —
    // all built from one admitted literal. Admitting unions exactly made every one a
    // distinct `(instance, domain)` key, so widening never fired and the walk overflowed
    // the stack. Atoms-only admission widens at the first union, so this terminates.
    let mut i = Interner::new();
    let f = crate::oracle::run_source_in("f = (x, b) => f(b ? x : 0, b)\nf", &mut i).unwrap().0;
    let mut env = empty();
    env.insert("f".into(), Contract::Equals(f));
    env.insert("k".into(), Contract::Equals(i.integer(0)));
    env.insert("c".into(), Contract::Kind(Kind::Boolean));
    let a = analyze(&apply(name("f"), vec![name("k"), name("c")]), &env, &nc(), &mut i);
    let _ = a.accepted(); // the assertion is that analysis terminated at all
}

// ── Region-table computation (recovery Phase 2; region-table spec v0.3) ────────

mod region {
    use super::{arm, konst, matchx, name, prim};
    use crate::analyzer::region::{region_table, select};
    use crate::ast::{Expr, Pat, PrimOp};
    use crate::contract::{Contract, ContractEnv};
    use crate::interner::Interner;
    use crate::rational::Rational;

    fn cenv() -> ContractEnv {
        ContractEnv::new()
    }
    /// A singleton argument contract `Equals(v)`.
    fn eq(i: &mut Interner, v: i64) -> Contract {
        Contract::Equals(i.integer(v))
    }

    /// `n == 0 ? 1 : n + "x"` (desugared): Match(∅, [Arm(guard n==0, 1), Arm(n+"x")]).
    fn ternary(i: &mut Interner) -> Expr {
        let (zero, one, x) = (i.integer(0), i.integer(1), i.string("x"));
        matchx(
            None,
            vec![
                arm(None, Some(prim(PrimOp::Eq, vec![name("n"), konst(zero)])), konst(one)),
                arm(None, None, prim(PrimOp::Add, vec![name("n"), konst(x)])),
            ],
        )
    }

    #[test]
    fn ternary_is_two_rows_equals0_then_top() {
        let mut i = Interner::new();
        let body = ternary(&mut i);
        let rows = region_table(&body, "n", &cenv(), &mut i);
        assert_eq!(rows.len(), 2);
        // row 0: n == 0 → Range(0,0), exact; row 1: unconditional → Top, exact.
        assert!(
            matches!(rows[0].region, Contract::Range(_, _)) && rows[0].exact,
            "row0 Equals(0) exact"
        );
        assert!(
            matches!(rows[1].region, Contract::Top) && rows[1].exact,
            "row1 Top exact"
        );
    }

    #[test]
    fn selection_walk_resolves_first_match_by_exactness() {
        let mut i = Interner::new();
        let body = ternary(&mut i);
        let rows = region_table(&body, "n", &cenv(), &mut i);
        // Over Top: both rows selected; row 1's effective region is Top ∖ Equals(0).
        let sel = select(&rows, &Contract::Top, &mut i);
        assert_eq!(sel.len(), 2, "both branches carried");
        assert!(
            matches!(sel[1].region, Contract::Difference(_, _)),
            "row1 effective = remaining"
        );
        // f(0): only row 0 (the exact match consumes; remaining becomes empty).
        let z = eq(&mut i, 0);
        let s0 = select(&rows, &z, &mut i);
        assert_eq!(s0.len(), 1, "only the 0-arm reachable");
        // f(5): only row 1 (row 0 disjoint on the point).
        let five = eq(&mut i, 5);
        let s5 = select(&rows, &five, &mut i);
        assert_eq!(s5.len(), 1, "only the else-arm reachable");
    }

    #[test]
    fn pattern_arms_regionalize_the_scrutinee() {
        // x :: { 0 => A  _ => B } — patterns on the parameter.
        let mut i = Interner::new();
        let (zero, a, b) = (i.integer(0), i.integer(10), i.integer(20));
        let body = matchx(
            Some(name("x")),
            vec![
                arm(Some(Pat::Const(zero)), None, konst(a)),
                arm(Some(Pat::Wild), None, konst(b)),
            ],
        );
        let rows = region_table(&body, "x", &cenv(), &mut i);
        assert_eq!(rows.len(), 2);
        assert!(
            matches!(rows[0].region, Contract::Equals(_)) && rows[0].exact,
            "0 pattern exact"
        );
        assert!(
            matches!(rows[1].region, Contract::Top) && rows[1].exact,
            "wildcard Top exact"
        );
    }

    #[test]
    fn an_opaque_guard_consumes_nothing() {
        // (n) => n * n <= 5 ? A : B — the tested side is not the bare parameter → case
        // (d): Top, non-exact. On a point argument BOTH arms stay selected.
        let mut i = Interner::new();
        let (five, a, b) = (i.integer(5), i.integer(1), i.integer(2));
        let guard = prim(
            PrimOp::Le,
            vec![prim(PrimOp::Mul, vec![name("n"), name("n")]), konst(five)],
        );
        let body = matchx(
            None,
            vec![arm(None, Some(guard), konst(a)), arm(None, None, konst(b))],
        );
        let rows = region_table(&body, "n", &cenv(), &mut i);
        assert!(
            matches!(rows[0].region, Contract::Top) && !rows[0].exact,
            "opaque guard: Top, non-exact"
        );
        let two = eq(&mut i, 2);
        assert_eq!(
            select(&rows, &two, &mut i).len(),
            2,
            "non-exact consumes nothing — else stays live"
        );
    }

    #[test]
    fn rt05_ladder_the_walk_derives_the_rational_regions() {
        // n :: { when n<=3 => P  when n<=7 => Q  _ => R } — rows LE(3), LE(7), Top, all
        // exact; the walk derives the half-open middle region (3.5 lands in Q).
        let mut i = Interner::new();
        let (three, seven, p, q, r) = (
            i.integer(3),
            i.integer(7),
            i.integer(1),
            i.integer(2),
            i.integer(3),
        );
        let body = matchx(
            Some(name("n")),
            vec![
                arm(
                    None,
                    Some(prim(PrimOp::Le, vec![name("n"), konst(three)])),
                    konst(p),
                ),
                arm(
                    None,
                    Some(prim(PrimOp::Le, vec![name("n"), konst(seven)])),
                    konst(q),
                ),
                arm(None, None, konst(r)),
            ],
        );
        let rows = region_table(&body, "n", &cenv(), &mut i);
        assert_eq!(rows.len(), 3);
        assert!(matches!(rows[0].region, Contract::LessEq(_)) && rows[0].exact);
        assert!(matches!(rows[1].region, Contract::LessEq(_)) && rows[1].exact);
        // n = 3.5 selects exactly the middle arm (Q).
        let half = i.number(Rational::new(7.into(), 2.into()));
        let sel = select(&rows, &Contract::Equals(half), &mut i);
        assert_eq!(sel.len(), 1, "3.5 lands in exactly one arm");
        // n = 2 → first arm; n = 9 → last arm.
        let two = eq(&mut i, 2);
        assert_eq!(select(&rows, &two, &mut i).len(), 1);
        let nine = eq(&mut i, 9);
        assert_eq!(select(&rows, &nine, &mut i).len(), 1);
    }
}
