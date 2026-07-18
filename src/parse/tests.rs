//! Surface parser conformance seeds — E2 worked parses + grammar §10.

use super::surface::*;
use super::*;
use crate::lex::lex;
use crate::rational::Rational;

fn expr(src: &str) -> SExpr {
    parse_expression(lex(src).expect("lex ok")).expect("parse ok")
}

fn program(src: &str) -> SProgram {
    parse_program(lex(src).expect("lex ok")).expect("parse ok")
}

fn parse_err(src: &str) -> bool {
    match lex(src) {
        Ok(toks) => parse_program(toks).is_err(),
        Err(_) => false, // a lex error is not a parse error
    }
}

// Small builders to keep expected trees readable.
fn n(i: i64) -> SExpr {
    SExpr::Number(Rational::from(i))
}
fn id(s: &str) -> SExpr {
    SExpr::Ident(s.to_string())
}
fn b(op: BinOp, l: SExpr, r: SExpr) -> SExpr {
    SExpr::Binary { op, left: Box::new(l), right: Box::new(r) }
}
fn u(op: UnOp, e: SExpr) -> SExpr {
    SExpr::Unary { op, operand: Box::new(e) }
}
fn pipe(dir: PipeDir, l: SExpr, r: SExpr) -> SExpr {
    SExpr::Pipe { dir, left: Box::new(l), right: Box::new(r) }
}

#[test]
fn pipes_left_associate_forward() {
    // a |> f |> g  ≡  g(f(a))  →  Pipe(Pipe(a,f),g)
    assert_eq!(
        expr("a |> f |> g"),
        pipe(PipeDir::Forward, pipe(PipeDir::Forward, id("a"), id("f")), id("g"))
    );
}

#[test]
fn pipes_right_associate_backward() {
    // f <| g <| x  ≡  f(g(x))  →  Pipe(f, Pipe(g, x))
    assert_eq!(
        expr("f <| g <| x"),
        pipe(PipeDir::Backward, id("f"), pipe(PipeDir::Backward, id("g"), id("x")))
    );
}

#[test]
fn mixed_pipes_are_a_parse_error() {
    assert!(parse_err("a |> f <| b"), "unparenthesized pipe mixing must error");
    // Parenthesized mixing is fine.
    assert!(!parse_err("(a |> f) <| b"));
}

#[test]
fn defaulting_tier_shares_precedence() {
    // a ?? b || c  ≡  (a ?? b) || c
    assert_eq!(
        expr("a ?? b || c"),
        b(BinOp::Or, b(BinOp::NullOr, id("a"), id("b")), id("c"))
    );
}

#[test]
fn unary_prefixes_stack() {
    // !~x  ≡  !(~x)
    assert_eq!(expr("!~x"), u(UnOp::Not, u(UnOp::Loosen, id("x"))));
    // ~count || fallback  →  (~count) || fallback
    assert_eq!(
        expr("~count || fallback"),
        b(BinOp::Or, u(UnOp::Loosen, id("count")), id("fallback"))
    );
}

#[test]
fn power_binds_tighter_than_unary_minus() {
    // -x ** 2  ≡  -(x ** 2)
    assert_eq!(expr("-x ** 2"), u(UnOp::Neg, b(BinOp::Pow, id("x"), n(2))));
    // 2 ** -3  legal (right operand admits unary)
    assert_eq!(expr("2 ** -3"), b(BinOp::Pow, n(2), u(UnOp::Neg, n(3))));
}

#[test]
fn comparison_chain_parses_left_assoc() {
    // a < b < c parses as (a < b) < c — self-refutes at the contract level, not here.
    assert_eq!(expr("a < b < c"), b(BinOp::Lt, b(BinOp::Lt, id("a"), id("b")), id("c")));
}

#[test]
fn access_chain_totals_are_per_hop() {
    // u?.name.first — first hop total (?.), second plain (.)
    let inner = SExpr::Access {
        target: Box::new(id("u")),
        form: SAccessForm::Field("name".into()),
        total: true,
    };
    let outer = SExpr::Access {
        target: Box::new(inner),
        form: SAccessForm::Field("first".into()),
        total: false,
    };
    assert_eq!(expr("u?.name.first"), outer);
}

#[test]
fn from_end_slice() {
    // t[-2...] — last two, clamped
    let slice = SExpr::Access {
        target: Box::new(id("t")),
        form: SAccessForm::Slice { lo: Some(Box::new(u(UnOp::Neg, n(2)))), hi: None },
        total: false,
    };
    assert_eq!(expr("t[-2...]"), slice);
}

#[test]
fn arrow_forms() {
    // x => x — single bare param
    assert_eq!(
        expr("x => x"),
        SExpr::Arrow(SArrow {
            params: vec![SParam::Ident("x".into())],
            body: Box::new(SArrowBody::Expr(id("x"))),
        })
    );
    // (a, b) => a — parenthesized param list
    match expr("(a, b) => a") {
        SExpr::Arrow(a) => assert_eq!(a.params.len(), 2),
        other => panic!("expected arrow, got {other:?}"),
    }
}

#[test]
fn empty_braces_after_arrow_is_empty_record() {
    // x => {} returns the empty record (§8 brace rule)
    assert_eq!(
        expr("x => {}"),
        SExpr::Arrow(SArrow {
            params: vec![SParam::Ident("x".into())],
            body: Box::new(SArrowBody::Expr(SExpr::Record(vec![]))),
        })
    );
}

#[test]
fn arrow_block_body_with_arms() {
    // n => { x = n \n => x } — a block body (binding + unconditional exit)
    match expr("n => { x = n\n => x }") {
        SExpr::Arrow(a) => match *a.body {
            SArrowBody::Block(stmts) => {
                assert!(matches!(stmts[0], SStmt::Binding(_)));
                assert!(matches!(stmts[1], SStmt::ElseArm { .. }));
            }
            other => panic!("expected block body, got {other:?}"),
        },
        other => panic!("expected arrow, got {other:?}"),
    }
}

#[test]
fn hask_binds_whole_ternary() {
    // # _ > 0 ? "pos" : "neg" — the hask body is the whole ternary
    match expr(r#"# _ > 0 ? "pos" : "neg""#) {
        SExpr::Hask(body) => assert!(matches!(*body, SExpr::Ternary { .. })),
        other => panic!("expected hask, got {other:?}"),
    }
}

#[test]
fn grouped_hask_primary_and_rest_hole() {
    // #([..._1]) — grouped hask; rest values as one tuple
    match expr("#([..._1])") {
        SExpr::Hask(inner) => match *inner {
            SExpr::Grouping(g) => match *g {
                SExpr::Tuple(elems) => {
                    assert_eq!(elems, vec![SElem::Spread(SExpr::Hole(Hole::Indexed(1)))]);
                }
                other => panic!("expected tuple, got {other:?}"),
            },
            other => panic!("expected grouping, got {other:?}"),
        },
        other => panic!("expected hask, got {other:?}"),
    }
}

#[test]
fn immediate_hask_invocation_needs_grouping() {
    // (# f(_))(x) — grouped hask, then called
    match expr("(# f(_))(x)") {
        SExpr::Call { callee, args } => {
            assert!(matches!(*callee, SExpr::Grouping(_)));
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected call, got {other:?}"),
    }
}

#[test]
fn match_left_of_pipe_and_arms() {
    // a |> b :: { ... }  ≡  (a |> b) :: { ... }
    match expr("a |> b :: {\n 0 => \"z\"\n _ => \"o\"\n }") {
        SExpr::Match { scrutinee, arms } => {
            assert!(matches!(*scrutinee, SExpr::Pipe { dir: PipeDir::Forward, .. }));
            assert_eq!(arms.len(), 2);
            assert_eq!(arms[0].pattern, Some(SPattern::Number(Rational::from(0))));
            assert_eq!(arms[1].pattern, Some(SPattern::Wild));
        }
        other => panic!("expected match, got {other:?}"),
    }
}

#[test]
fn guarded_arm() {
    // pattern + guard
    match expr("v :: {\n x when x > 0 => x\n _ => 0\n }") {
        SExpr::Match { arms, .. } => {
            assert_eq!(arms[0].pattern, Some(SPattern::Bind("x".into())));
            assert!(arms[0].guard.is_some());
        }
        other => panic!("expected match, got {other:?}"),
    }
}

#[test]
fn template_interpolation_parses_inner_expression() {
    match expr("`hi ${name}`") {
        SExpr::Template(parts) => {
            assert_eq!(parts.len(), 2);
            assert!(matches!(&parts[0], STemplatePart::Str(_)));
            assert_eq!(parts[1], STemplatePart::Interp(id("name")));
        }
        other => panic!("expected template, got {other:?}"),
    }
}

// ── Statements ───────────────────────────────────────────────────────────────

#[test]
fn binding_statement() {
    let prog = program("double = x => x * 2");
    assert_eq!(prog.statements.len(), 1);
    match &prog.statements[0] {
        SStmt::Binding(bnd) => {
            assert_eq!(bnd.target, SBindTarget::Name("double".into()));
            assert!(matches!(bnd.value, SExpr::Arrow(_)));
        }
        other => panic!("expected binding, got {other:?}"),
    }
}

#[test]
fn destructuring_binding() {
    let prog = program("[name, age] = pair");
    match &prog.statements[0] {
        SStmt::Binding(bnd) => match &bnd.target {
            SBindTarget::Tuple(elems) => assert_eq!(elems.len(), 2),
            other => panic!("expected tuple target, got {other:?}"),
        },
        other => panic!("expected binding, got {other:?}"),
    }
}

#[test]
fn mutation_statement() {
    let prog = program("count +:= 1");
    match &prog.statements[0] {
        SStmt::Mutation { path, op, .. } => {
            assert_eq!(path.root, "count");
            assert_eq!(*op, MutOp::Add);
        }
        other => panic!("expected mutation, got {other:?}"),
    }
    // Path mutation with a field segment.
    match &program("a.b.c := v").statements[0] {
        SStmt::Mutation { path, op, .. } => {
            assert_eq!(path.segments.len(), 2);
            assert_eq!(*op, MutOp::Assign);
        }
        other => panic!("expected mutation, got {other:?}"),
    }
}

#[test]
fn two_statements_separate_greedily() {
    let prog = program("x = 1\ny = 2");
    assert_eq!(prog.statements.len(), 2);
}

#[test]
fn import_and_module_header() {
    let prog = program("module App.Main\nimport { a, b } from Foo.Bar");
    assert_eq!(prog.header, Some(vec!["App".into(), "Main".into()]));
    match &prog.statements[0] {
        SStmt::Import { names, module } => {
            assert_eq!(names.as_deref(), Some(["a".to_string(), "b".to_string()].as_slice()));
            assert_eq!(module, &vec!["Foo".to_string(), "Bar".to_string()]);
        }
        other => panic!("expected import, got {other:?}"),
    }
    // bare import
    match &program("import Foo.Bar").statements[0] {
        SStmt::Import { names, module } => {
            assert!(names.is_none());
            assert_eq!(module, &vec!["Foo".to_string(), "Bar".to_string()]);
        }
        other => panic!("expected import, got {other:?}"),
    }
}

#[test]
fn export_marks_binding() {
    match &program("export Percent = Range(0, 100)").statements[0] {
        SStmt::Binding(bnd) => {
            assert!(bnd.exported);
            assert_eq!(bnd.target, SBindTarget::Name("Percent".into()));
        }
        other => panic!("expected exported binding, got {other:?}"),
    }
}

#[test]
fn at_effect_declaration_has_block_body() {
    // The @-arrow body is always a Block (§8 [1.0.3]); empty here.
    match &program("@effect log = (m) => { }").statements[0] {
        SStmt::At(SAt::Binding { op, binding }) => {
            assert_eq!(op, "effect");
            match &binding.value {
                SExpr::Arrow(a) => assert!(matches!(*a.body, SArrowBody::Block(_))),
                other => panic!("expected arrow, got {other:?}"),
            }
        }
        other => panic!("expected @effect, got {other:?}"),
    }
}

#[test]
fn at_mutate_with_writes() {
    match &program("@mutate setX = (v) => { x := v }").statements[0] {
        SStmt::At(SAt::Binding { op, binding }) => {
            assert_eq!(op, "mutate");
            match &binding.value {
                SExpr::Arrow(a) => match &*a.body {
                    SArrowBody::Block(stmts) => {
                        assert!(matches!(stmts[0], SStmt::Mutation { .. }));
                    }
                    other => panic!("expected block, got {other:?}"),
                },
                other => panic!("expected arrow, got {other:?}"),
            }
        }
        other => panic!("expected @mutate, got {other:?}"),
    }
}

#[test]
fn where_signature_statement() {
    match &program("double where (Number) => Number").statements[0] {
        SStmt::Where { name, inputs, ret } => {
            assert_eq!(name, "double");
            assert_eq!(inputs, &vec![id("Number")]);
            assert_eq!(ret, &id("Number"));
        }
        other => panic!("expected where, got {other:?}"),
    }
}

#[test]
fn alternation_and_pin_patterns() {
    // p1 | p2 alternation, and ^name pin
    match expr("v :: {\n 1 | 2 | 3 => \"small\"\n ^target => \"hit\"\n _ => \"other\"\n }") {
        SExpr::Match { arms, .. } => {
            assert!(matches!(arms[0].pattern, Some(SPattern::Alt(_))));
            assert_eq!(arms[1].pattern, Some(SPattern::Pin("target".into())));
        }
        other => panic!("expected match, got {other:?}"),
    }
}

#[test]
fn contract_pattern_by_capitalization() {
    match expr("v :: {\n Number => \"num\"\n _ => \"other\"\n }") {
        SExpr::Match { arms, .. } => {
            assert_eq!(arms[0].pattern, Some(SPattern::Contract("Number".into())));
        }
        other => panic!("expected match, got {other:?}"),
    }
}
