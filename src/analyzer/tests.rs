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
fn division_is_total_but_comparison_forces_the_indeterminate() {
    let mut i = Interner::new();
    // 1 / 0 alone is safe (produces Indeterminate).
    let div = prim(PrimOp::Div, vec![konst(i.integer(1)), konst(i.integer(0))]);
    assert!(analyze(&div, &empty(), &nc(), &mut i).accepted());

    // (1 / 0) < 2 traps undischarged-Indeterminate.
    let cmp = prim(PrimOp::Lt, vec![div.clone(), konst(i.integer(2))]);
    let a = analyze(&cmp, &empty(), &nc(), &mut i);
    assert!(!a.accepted());
    assert_eq!(a.findings[0].class, TrapClass::UndischargedIndeterminate);
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
        Contract::Record(vec![("a".into(), Contract::Kind(Kind::Number))]),
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

    // r.b on an unknown receiver (demand form) — a warning, not a rejection.
    let a = analyze(&afield(name("r"), "b", false), &tenv, &nc(), &mut i);
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
    crate::contract::build_contract_env([("Percent", &range)])
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
    assert!(a.may_complete, "Percent must narrow — Number is not covered by Range(0,100)");

    // Unresolved (empty contract env): the pattern widens to Top and covers
    // everything — the discriminating control for the test above.
    let a = analyze(&m, &env, &nc(), &mut i);
    assert!(!a.may_complete, "an unresolved contract name widens to Top");
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
        Contract::Union(Box::new(Contract::Equals(ka)), Box::new(Contract::Equals(kb))),
    );
    let finite = Expr::RecordCons(vec![Field::Computed {
        key: name("k"),
        value: konst(i.integer(1)),
    }]);
    let a = analyze(&finite, &fenv, &nc(), &mut i);
    assert!(a.accepted(), "a finite string set is admitted: {:?}", a.findings);
}

#[test]
fn tuple_spread_produces_concat_shape() {
    // The tuple family's constructor: [1, ...t] with t : Tuple([Number]) fuses to
    // the exact 2-tuple Tuple([Equals(1), Number]) — no more Top for spreads.
    let mut i = Interner::new();
    let mut env = TypeEnv::new();
    env.insert("t".into(), Contract::Tuple(vec![Contract::Kind(Kind::Number)]));
    let e = Expr::TupleCons(vec![
        Element::Expr(konst(i.integer(1))),
        Element::Spread(name("t")),
    ]);
    let a = analyze(&e, &env, &nc(), &mut i);
    assert!(a.accepted(), "{:?}", a.findings);
    assert_eq!(
        a.contract,
        Contract::Tuple(vec![Contract::Equals(i.integer(1)), Contract::Kind(Kind::Number)]),
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
            Contract::Tuple(vec![Contract::Equals(i.integer(1))]),
            Contract::Kind(Kind::Tuple),
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
