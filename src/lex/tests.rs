//! Lexer conformance seeds (Grammar Specification v0.1, §10 + E2 worked parses).

use super::*;
use crate::rational::Rational;

/// Lex to token kinds, dropping the trailing `Eof`.
fn kinds(src: &str) -> Vec<TokenKind> {
    let mut toks = lex(src).expect("lex ok");
    assert_eq!(toks.pop().map(|t| t.kind), Some(TokenKind::Eof));
    toks.into_iter().map(|t| t.kind).collect()
}

fn num(s: &str) -> TokenKind {
    TokenKind::Number(Rational::from_decimal(s).unwrap())
}

fn int(n: i64) -> TokenKind {
    TokenKind::Number(Rational::from(n))
}

fn ident(s: &str) -> TokenKind {
    TokenKind::Ident(s.to_string())
}

fn s(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

#[test]
fn slice_lexing_t2() {
    // `1...3` lexes cleanly as `1` `...` `3` (the trailing-dot ban is load-bearing).
    use TokenKind::*;
    assert_eq!(kinds("1...3"), vec![int(1), DotDotDot, int(3)]);
    // `t[-2...]` — last two, clamped
    assert_eq!(
        kinds("t[-2...]"),
        vec![ident("t"), LBracket, Minus, int(2), DotDotDot, RBracket]
    );
}

#[test]
fn question_dot_digit_lookahead_t1() {
    // `a ?.5 : b` lexes `?` `.5` (T1: `?.` not formed before a digit).
    use TokenKind::*;
    assert_eq!(kinds("a ?.5 : b"), vec![ident("a"), Question, num("0.5"), Colon, ident("b")]);
    // Ordinary `a?.b` is a single `?.`.
    assert_eq!(kinds("a?.b"), vec![ident("a"), QuestionDot, ident("b")]);
}

#[test]
fn member_access_vs_leading_dot_number() {
    use TokenKind::*;
    // After a postfix-target token, `.` is member access, not a number.
    assert_eq!(kinds("a.b"), vec![ident("a"), Dot, ident("b")]);
    // In operator position, `.5` is a number.
    assert_eq!(kinds("x + .5"), vec![ident("x"), Plus, num("0.5")]);
}

#[test]
fn numeric_bans() {
    assert!(lex("5.").is_err(), "dangling trailing-dot must error");
    assert!(lex("5. + 1").is_err(), "trailing-dot before an operator must error");
    assert!(lex("017").is_err(), "legacy octal must error");
    assert!(lex("123n").is_err(), "BigInt suffix must error");
}

#[test]
fn number_then_member_access_is_not_trailing_dot() {
    // `5.foo` is `5` `.` `foo` (member access), not a trailing-dot error — the
    // ban targets a dangling dot, and numbers having no fields is an analyzer
    // concern, not the lexer's.
    use TokenKind::*;
    assert_eq!(kinds("5.foo"), vec![int(5), Dot, ident("foo")]);
}

#[test]
fn numeric_forms() {
    assert_eq!(kinds("0xff"), vec![int(255)]);
    assert_eq!(kinds("0o17"), vec![int(15)]);
    assert_eq!(kinds("0b1010"), vec![int(10)]);
    assert_eq!(kinds("1_000"), vec![int(1000)]);
    assert_eq!(kinds("0.1"), vec![num("0.1")]);
    assert_eq!(kinds("1e3"), vec![int(1000)]);
    assert_eq!(kinds("5.0"), vec![int(5)]); // 5.0 ≡ 5 as an exact rational
    assert_eq!(kinds("0"), vec![int(0)]);
}

#[test]
fn maximal_munch_operators() {
    use TokenKind::*;
    assert_eq!(kinds("**:="), vec![StarStarEq]);
    assert_eq!(kinds("??:="), vec![QuestionQuestionEq]);
    assert_eq!(kinds("+:="), vec![PlusEq]);
    assert_eq!(kinds(":="), vec![ColonEq]);
    assert_eq!(kinds("=>"), vec![FatArrow]);
    assert_eq!(kinds("::"), vec![ColonColon]);
    assert_eq!(kinds("<|"), vec![LtPipe]);
    assert_eq!(kinds("|>"), vec![PipeGt]);
    assert_eq!(kinds("<="), vec![Le]);
    assert_eq!(kinds("**"), vec![StarStar]);
    // `<|` must not swallow into `<`; a lone `<` stays `<`.
    assert_eq!(kinds("a < b"), vec![ident("a"), Lt, ident("b")]);
}

#[test]
fn unary_stack_and_power() {
    use TokenKind::*;
    // `!~x` lexes as two prefixes; `-x ** 2` is Minus x StarStar 2 (parser groups).
    assert_eq!(kinds("!~x"), vec![Bang, Tilde, ident("x")]);
    assert_eq!(kinds("-x ** 2"), vec![Minus, ident("x"), StarStar, int(2)]);
    assert_eq!(kinds("2 ** -3"), vec![int(2), StarStar, Minus, int(3)]);
}

#[test]
fn holes_and_pattern_glyphs() {
    use TokenKind::*;
    assert_eq!(kinds("_"), vec![Underscore]);
    assert_eq!(kinds("_1"), vec![IndexedHole(1)]);
    assert_eq!(kinds("^_2"), vec![Caret, IndexedHole(2)]);
    // `#([..._1])` — rest values as one tuple
    assert_eq!(
        kinds("#([..._1])"),
        vec![Hash, LParen, LBracket, DotDotDot, IndexedHole(1), RBracket, RParen]
    );
}

#[test]
fn strings_with_escapes() {
    // Escapes resolve to UTF-16 at lex time.
    assert_eq!(kinds(r#""a\nb""#), vec![TokenKind::Str(s("a\nb"))]);
    assert_eq!(kinds(r#""tab\tend""#), vec![TokenKind::Str(s("tab\tend"))]);
    assert_eq!(kinds(r#""quote\"in""#), vec![TokenKind::Str(s("quote\"in"))]);
    assert_eq!(kinds(r#""\u{1F600}""#), vec![TokenKind::Str(s("😀"))]);
    assert!(lex("\"line\nbreak\"").is_err(), "raw newline in string must error");
}

#[test]
fn template_with_interpolation() {
    // `hi ${x} there` → segment, interpolation (a token sub-stream), segment.
    let toks = lex("`hi ${x} there`").unwrap();
    let TokenKind::Template(elems) = &toks[0].kind else {
        panic!("expected template, got {:?}", toks[0].kind);
    };
    assert_eq!(elems.len(), 3);
    assert_eq!(elems[0], TemplateElem::Str(s("hi ")));
    match &elems[1] {
        TemplateElem::Interp(inner) => assert_eq!(inner, &vec![Token::new(ident("x"), 1)]),
        other => panic!("expected interpolation, got {other:?}"),
    }
    assert_eq!(elems[2], TemplateElem::Str(s(" there")));
}

#[test]
fn template_brace_depth_aware_interpolation() {
    // A record literal inside an interpolation: the inner `}` must not close it.
    let toks = lex("`v=${ {a: 1} }`").unwrap();
    let TokenKind::Template(elems) = &toks[0].kind else {
        panic!("expected template");
    };
    // segment "v=" then one interpolation carrying `{ a : 1 }`.
    assert_eq!(elems[0], TemplateElem::Str(s("v=")));
    match &elems[1] {
        TemplateElem::Interp(inner) => {
            let ks: Vec<TokenKind> = inner.iter().map(|t| t.kind.clone()).collect();
            use TokenKind::*;
            assert_eq!(ks, vec![LBrace, ident("a"), Colon, int(1), RBrace]);
        }
        other => panic!("expected interpolation, got {other:?}"),
    }
}

#[test]
fn comments_skipped_and_lines_tracked() {
    // Line comments, block comments, and line numbers for L1/L2.
    let toks = lex("a // comment\n/* block */ b").unwrap();
    let pairs: Vec<(TokenKind, u32)> = toks.iter().map(|t| (t.kind.clone(), t.line)).collect();
    assert_eq!(pairs[0], (ident("a"), 1));
    assert_eq!(pairs[1], (ident("b"), 2));
    assert_eq!(pairs[2].0, TokenKind::Eof);
}

#[test]
fn worked_parse_token_shapes() {
    use TokenKind::*;
    // `a |> f |> g`
    assert_eq!(
        kinds("a |> f |> g"),
        vec![ident("a"), PipeGt, ident("f"), PipeGt, ident("g")]
    );
    // `~count || fallback`
    assert_eq!(
        kinds("~count || fallback"),
        vec![Tilde, ident("count"), PipePipe, ident("fallback")]
    );
    // `u?.name.first`
    assert_eq!(
        kinds("u?.name.first"),
        vec![ident("u"), QuestionDot, ident("name"), Dot, ident("first")]
    );
}
