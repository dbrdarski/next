//! Tokens — the lexer's output (Grammar Specification v0.1, §1).
//!
//! Literals are resolved during lexing (§4 of the desugar catalog: "string
//! escapes, numeric forms resolved at lexing; kernel sees interned values"), so
//! `Number` already carries an exact [`Rational`] and `Str` already carries
//! UTF-16 code units. Every token records its source line so the parser can
//! enforce the two line-sensitivity rules L1/L2 (§1.1).

use crate::rational::Rational;

/// A lexed token with its source line (1-based).
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub line: u32,
}

impl Token {
    pub fn new(kind: TokenKind, line: u32) -> Token {
        Token { kind, line }
    }
}

/// One element of a template literal: a literal segment (resolved UTF-16) or an
/// interpolation whose inner expression is captured as a pre-lexed token stream
/// (the parser parses it as an `Expression`).
#[derive(Clone, Debug, PartialEq)]
pub enum TemplateElem {
    Str(Vec<u16>),
    Interp(Vec<Token>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    // ── Literals and names ───────────────────────────────────────────────────
    /// A numeric literal, already resolved to an exact rational (§1.4).
    Number(Rational),
    /// A string literal with escapes resolved to UTF-16 (§1.5).
    Str(Vec<u16>),
    /// A template literal; segments and interpolations interleaved (§1.5).
    Template(Vec<TemplateElem>),
    /// An identifier. Contextual keywords (`module`, `import`, `export`, `from`,
    /// `when`, `where`) and the prelude names `true`/`false`/`null` are ordinary
    /// identifiers here — the parser decides their role by seat (§1.3).
    Ident(String),
    /// The plain hole / wildcard `_` (role decided by position — §1.3, §8).
    Underscore,
    /// An indexed hole `_n`, `n ≥ 1` (hask scope — §1.3).
    IndexedHole(u32),

    // ── Grouping and punctuation ─────────────────────────────────────────────
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Dot,
    DotDotDot,

    // ── Operators (§1.6) ─────────────────────────────────────────────────────
    FatArrow,          // =>
    ColonColon,        // ::
    PipeGt,            // |>
    LtPipe,            // <|
    Hash,              // #
    Question,          // ?
    Colon,             // :
    QuestionDot,       // ?.
    QuestionQuestion,  // ??
    PipePipe,          // ||
    AmpAmp,            // &&
    EqEq,              // ==
    BangEq,            // !=
    Lt,                // <
    Le,                // <=
    Gt,                // >
    Ge,                // >=
    Plus,              // +
    Minus,             // -
    Star,              // *
    Slash,             // /
    Percent,           // %
    StarStar,          // **
    Bang,              // !
    Tilde,             // ~
    Eq,                // =
    At,                // @
    Caret,             // ^
    Pipe,              // |  (pattern alternation only)

    // ── Mutation compound assignment (statement-level, §2.4) ─────────────────
    ColonEq,           // :=
    PlusEq,            // +:=
    MinusEq,           // -:=
    StarEq,            // *:=
    SlashEq,           // /:=
    PercentEq,         // %:=
    StarStarEq,        // **:=
    AmpAmpEq,          // &&:=
    PipePipeEq,        // ||:=
    QuestionQuestionEq,// ??:=

    /// End of input.
    Eof,
}

impl TokenKind {
    /// Whether a token can end a postfix target — used for the leading-dot
    /// number disambiguation (`a.5` ≠ `a` `.5`; but `? .5` is a number). See
    /// the lexer's `.`/`?` handling and grammar T1.
    pub fn ends_postfix_target(&self) -> bool {
        matches!(
            self,
            TokenKind::Ident(_)
                | TokenKind::Number(_)
                | TokenKind::Str(_)
                | TokenKind::Template(_)
                | TokenKind::Underscore
                | TokenKind::IndexedHole(_)
                | TokenKind::RParen
                | TokenKind::RBracket
                | TokenKind::RBrace
        )
    }
}
