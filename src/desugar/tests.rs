//! Desugar-equivalence seeds — kernel AST spec §4 catalog rows + conformance
//! seeds (the `?? vs ~||` false distinction, interning).

use super::*;
use crate::lex::lex;
use crate::parse::{parse_expression, parse_program};
use crate::value::ValueData;

fn lower_with(interner: &mut Interner, src: &str) -> Expr {
    let sexpr = parse_expression(lex(src).unwrap()).unwrap();
    Desugarer::new(interner).expr(&sexpr).unwrap()
}

fn lower(src: &str) -> Expr {
    let mut interner = Interner::new();
    lower_with(&mut interner, src)
}

fn lower_program(src: &str) -> Module {
    let mut interner = Interner::new();
    let prog = parse_program(lex(src).unwrap()).unwrap();
    Desugarer::new(&mut interner).program(&prog).unwrap()
}

/// Extract a `Match`'s items, or panic.
fn match_items(e: &Expr) -> &[MatchItem] {
    match e {
        Expr::Match(m) => &m.items,
        other => panic!("expected Match, got {other:?}"),
    }
}

// ── Desugar-equivalence rows (§4) ────────────────────────────────────────────

#[test]
fn pipes_are_application() {
    // x |> f  ≡  f <| x  ≡  f(x)  — Apply(f, [x]), nothing else.
    let mut i = Interner::new();
    let forward = lower_with(&mut i, "x |> f");
    let backward = lower_with(&mut i, "f <| x");
    let call = lower_with(&mut i, "f(x)");
    assert_eq!(forward, call);
    assert_eq!(backward, call);
}

#[test]
fn pipe_chain_matches_nested_calls() {
    // a |> f |> g  ≡  g(f(a))
    let mut i = Interner::new();
    assert_eq!(lower_with(&mut i, "a |> f |> g"), lower_with(&mut i, "g(f(a))"));
}

#[test]
fn conjunction_desugars_to_match() {
    // a && b  ⇒  a ? b : false  ⇒  Match(a, [true => b, false => false])
    let items = match_items(&lower("a && b")).to_vec();
    assert_eq!(items.len(), 2);
    // First arm: pattern true, result Ref(b). Second: pattern false, result Const(false).
    if let MatchItem::Arm(arm0) = &items[0] {
        assert!(matches!(arm0.result, Expr::Ref(_)));
    } else {
        panic!("expected arm");
    }
}

#[test]
fn disjunction_desugars_to_match() {
    // a || b  ⇒  a ? true : b
    let e = lower("a || b");
    assert_eq!(match_items(&e).len(), 2);
}

#[test]
fn ternary_desugars_to_bool_match() {
    let e = lower(r#"c ? "t" : "e""#);
    let items = match_items(&e);
    assert_eq!(items.len(), 2);
}

#[test]
fn not_desugars_to_match() {
    // !x  ⇒  Match(x, [true => false, false => true])
    assert_eq!(match_items(&lower("!x")).len(), 2);
}

#[test]
fn double_negation_loosen_is_falsy_test() {
    // !~x  ⇒  falsy-set match emitting Booleans: [false => true, null => true, _ => false]
    let e = lower("!~x");
    let items = match_items(&e);
    assert_eq!(items.len(), 3);
    assert!(matches!(items[2], MatchItem::Arm(Arm { pattern: Some(Pat::Wild), .. })));
}

#[test]
fn nullish_vs_escaped_or_differ_on_false() {
    // The flagship distinction: `a ?? b` tests only null (2 arms); `~a || b`
    // tests false AND null (3 arms) — they differ exactly on `false`.
    let nullish = lower("a ?? b");
    let escaped = lower("~a || b");
    assert_eq!(match_items(&nullish).len(), 2, "?? tests null only");
    assert_eq!(match_items(&escaped).len(), 3, "~|| tests false and null");
    assert_ne!(nullish, escaped);

    // `??` first arm matches null; `~||` first arm matches false.
    let null_v = Interner::new().null();
    if let MatchItem::Arm(a) = &match_items(&nullish)[0] {
        // pattern is Const(null)
        assert!(matches!(&a.pattern, Some(Pat::Const(v)) if v.data() == null_v.data()));
    }
}

#[test]
fn escaped_and_propagates_falsy() {
    // ~a && b  ⇒  Match(a, [false => false, null => null, v => b])
    let e = lower("~a && b");
    assert_eq!(match_items(&e).len(), 3);
}

// ── Arrows, hasks, blocks ────────────────────────────────────────────────────

#[test]
fn arrow_is_a_pure_lambda_over_the_argument_tuple() {
    // x => x  ⇒  Lambda(Tuple([Bind x]), Ref x, pure)
    match lower("x => x") {
        Expr::Lambda(l) => {
            assert_eq!(l.act_kind, ActKind::Pure);
            assert_eq!(l.params, Pat::Tuple(vec![PatElem::Pat(Pat::Bind("x".into()))]));
            assert!(matches!(*l.body, Expr::Ref(_)));
        }
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn arrow_two_params() {
    match lower("(a, b) => a") {
        Expr::Lambda(l) => assert_eq!(
            l.params,
            Pat::Tuple(vec![
                PatElem::Pat(Pat::Bind("a".into())),
                PatElem::Pat(Pat::Bind("b".into())),
            ])
        ),
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn hask_anon_hole() {
    // # _ + 1  ⇒  Lambda(Tuple([Bind %h]), PrimOp(Add, [Ref %h, Const 1]))
    match lower("# _ + 1") {
        Expr::Lambda(l) => {
            assert!(matches!(l.params, Pat::Tuple(ref v) if v.len() == 1));
            assert!(matches!(*l.body, Expr::PrimOp { op: PrimOp::Add, .. }));
        }
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn hask_two_anon_holes_in_order() {
    // # f(_, _)  ⇒  two params
    match lower("# f(_, _)") {
        Expr::Lambda(l) => assert!(matches!(l.params, Pat::Tuple(ref v) if v.len() == 2)),
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn hask_indexed_holes_reuse() {
    // # _1 + _1  ⇒  one param (repeats reuse)
    match lower("# _1 + _1") {
        Expr::Lambda(l) => assert!(matches!(l.params, Pat::Tuple(ref v) if v.len() == 1)),
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn hask_rest_hole_as_one_tuple() {
    // #([..._1])  ⇒  Lambda(Tuple([Rest]), TupleCons([Spread(Ref)]))
    match lower("#([..._1])") {
        Expr::Lambda(l) => {
            assert_eq!(l.params, Pat::Tuple(vec![PatElem::Rest(Some("%hrest0".into()))]));
            match *l.body {
                Expr::TupleCons(ref elems) => {
                    assert!(matches!(elems[0], Element::Spread(Expr::Ref(_))));
                }
                ref other => panic!("expected tuple cons, got {other:?}"),
            }
        }
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn nested_hask_opens_fresh_scope() {
    // # f(# _ + 1, _)  — inner _ belongs to the inner hask; outer has one param.
    match lower("# f(# _ + 1, _)") {
        Expr::Lambda(outer) => {
            assert!(matches!(outer.params, Pat::Tuple(ref v) if v.len() == 1));
        }
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn block_body_is_scrutinee_less_match() {
    // n => { => n }  ⇒  Lambda body Match(None, [Arm(None, None, Ref n)])
    match lower("n => { => n }") {
        Expr::Lambda(l) => match *l.body {
            Expr::Match(ref m) => {
                assert!(m.scrutinee.is_none());
                assert!(matches!(m.items[0], MatchItem::Arm(Arm { pattern: None, guard: None, .. })));
            }
            ref other => panic!("expected match body, got {other:?}"),
        },
        other => panic!("expected lambda, got {other:?}"),
    }
}

// ── Match arms: alternation and pins ─────────────────────────────────────────

#[test]
fn alternation_expands_to_multiple_arms() {
    // 1 | 2 | 3 => "s" expands to three arms with the same result.
    let e = lower("v :: {\n 1 | 2 | 3 => \"s\"\n _ => \"o\"\n }");
    let items = match_items(&e);
    // three expanded arms + the wildcard arm = 4
    assert_eq!(items.len(), 4);
}

#[test]
fn pin_becomes_equality_guard() {
    // ^target => "hit"  ⇒  Arm(Bind %pin, guard %pin == target)
    let e = lower("v :: {\n ^target => \"hit\"\n _ => \"o\"\n }");
    if let MatchItem::Arm(arm) = &match_items(&e)[0] {
        assert!(matches!(arm.pattern, Some(Pat::Bind(_))));
        assert!(matches!(arm.guard, Some(Expr::PrimOp { op: PrimOp::Eq, .. })));
    } else {
        panic!("expected arm");
    }
}

// ── Mutation (§4) ────────────────────────────────────────────────────────────

#[test]
fn simple_assign_is_write() {
    // Inside a mutator body: x := 5  ⇒  Write(Name x, Const 5)
    let m = lower_program("@mutate setX = (v) => { x := 5 }");
    let body = mutate_body(&m);
    assert!(matches!(
        body,
        MatchItem::Stmt(Expr::Write { slot: SlotRef::Name(n), .. }) if n == "x"
    ));
}

#[test]
fn compound_assign_reads_then_writes() {
    // count +:= 1  ⇒  Write(Name count, PrimOp(Add, [Ref count, Const 1]))
    let m = lower_program("@mutate inc = () => { count +:= 1 }");
    match mutate_body(&m) {
        MatchItem::Stmt(Expr::Write { slot: SlotRef::Name(n), value }) => {
            assert_eq!(n, "count");
            assert!(matches!(**value, Expr::PrimOp { op: PrimOp::Add, .. }));
        }
        other => panic!("expected write, got {other:?}"),
    }
}

#[test]
fn field_path_assign_is_functional_update() {
    // a.b := v  ⇒  Write(Name a, { ...a, b: v })
    let m = lower_program("@mutate f = () => { a.b := v }");
    match mutate_body(&m) {
        MatchItem::Stmt(Expr::Write { slot: SlotRef::Name(n), value }) => {
            assert_eq!(n, "a");
            match &**value {
                Expr::RecordCons(fields) => {
                    assert!(matches!(fields[0], Field::Spread(_)));
                    assert!(matches!(&fields[1], Field::Field { key, .. } if key == "b"));
                }
                other => panic!("expected record update, got {other:?}"),
            }
        }
        other => panic!("expected write, got {other:?}"),
    }
}

/// Pull the single statement out of a one-`@mutate` module's body.
fn mutate_body(m: &Module) -> &MatchItem {
    match &m.items[0] {
        Item::ActBind(ab) => match &*ab.lambda.body {
            Expr::Match(inner) => &inner.items[0],
            other => panic!("expected block body, got {other:?}"),
        },
        other => panic!("expected act bind, got {other:?}"),
    }
}

// ── Top-level declarations ───────────────────────────────────────────────────

#[test]
fn state_and_mutable_become_slot_decls() {
    let m = lower_program("@state count = 0\n@mutable temp = 1");
    assert!(matches!(&m.items[0], Item::SlotDecl(s) if s.reactive && s.name == "count"));
    assert!(matches!(&m.items[1], Item::SlotDecl(s) if !s.reactive && s.name == "temp"));
}

#[test]
fn effect_becomes_act_bind() {
    let m = lower_program("@effect log = (msg) => { }");
    match &m.items[0] {
        Item::ActBind(ab) => {
            assert_eq!(ab.kind, ActKind::Effect);
            assert_eq!(ab.lambda.act_kind, ActKind::Effect);
        }
        other => panic!("expected act bind, got {other:?}"),
    }
}

#[test]
fn reactive_layer_is_fenced() {
    let mut interner = Interner::new();
    let prog = parse_program(lex("@computed total = 0").unwrap()).unwrap();
    assert!(Desugarer::new(&mut interner).program(&prog).is_err());
}

// ── Interning through desugar ────────────────────────────────────────────────

#[test]
fn constants_intern_across_desugar() {
    // Equal literals in one interner produce the same interned ValueRef.
    let mut i = Interner::new();
    let a = lower_with(&mut i, "0.5");
    let b = lower_with(&mut i, "1 / 2 == 0.5"); // contains 0.5
    let (Expr::Const(va), _) = (&a, &b) else { panic!() };
    // Find the 0.5 const inside b's PrimOp tree and check pointer identity.
    fn find_half(e: &Expr) -> Option<&crate::value::ValueRef> {
        match e {
            Expr::Const(v) => {
                matches!(v.data(), ValueData::Number(n) if n == &crate::rational::Rational::from_decimal("0.5").unwrap())
                    .then_some(v)
            }
            Expr::PrimOp { args, .. } => args.iter().find_map(find_half),
            _ => None,
        }
    }
    let vb = find_half(&b).expect("0.5 present in b");
    assert!(va.ptr_eq(vb), "equal constants share one interned pointer");
}

#[test]
fn equal_programs_lower_equal() {
    // Structural equality of kernel forms (same interner ⇒ shared consts).
    let mut i = Interner::new();
    assert_eq!(lower_with(&mut i, "f(g(a))"), lower_with(&mut i, "a |> g |> f"));
}
