//! The lexer (Grammar Specification v0.1, §1).
//!
//! Produces a flat [`Token`] stream with per-token line numbers. Whitespace and
//! line breaks are skipped (there are **no newline tokens** — §1.1); the parser
//! reconstructs L1/L2 from recorded lines. Numeric and string literals are
//! resolved here (§4 desugar catalog); templates keep their interpolations as
//! pre-lexed sub-streams.

use num_bigint::BigInt;
use num_traits::Num;

use super::token::{TemplateElem, Token, TokenKind};
use crate::rational::Rational;

/// A lexical error with the offending source line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    pub message: String,
    pub line: u32,
}

/// Lex a complete source string into tokens, terminated by [`TokenKind::Eof`].
pub fn lex(src: &str) -> Result<Vec<Token>, LexError> {
    let mut lexer = Lexer::new(src);
    let mut tokens = lexer.run(StopAt::Eof)?;
    tokens.push(Token::new(TokenKind::Eof, lexer.line));
    Ok(tokens)
}

/// Where a token-producing loop stops.
enum StopAt {
    /// Consume until end of input.
    Eof,
    /// Consume until the `}` that closes a template interpolation (brace-depth
    /// 0). The closing brace is consumed but not emitted.
    InterpClose,
}

struct Lexer {
    src: Vec<char>,
    pos: usize,
    line: u32,
    /// The last significant token kind emitted — drives leading-dot number
    /// disambiguation (grammar T1).
    prev: Option<TokenKind>,
}

impl Lexer {
    fn new(src: &str) -> Lexer {
        Lexer { src: src.chars().collect(), pos: 0, line: 1, prev: None }
    }

    // ── Character cursor ─────────────────────────────────────────────────────

    fn peek(&self) -> Option<char> {
        self.src.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.src.get(self.pos + offset).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if let Some(c) = c {
            self.pos += 1;
            if c == '\n' {
                self.line += 1;
            }
        }
        c
    }

    /// If the upcoming characters equal `s`, consume them and return true.
    fn eat(&mut self, s: &str) -> bool {
        let chars: Vec<char> = s.chars().collect();
        if self.src[self.pos..].starts_with(chars.as_slice()) {
            for _ in 0..chars.len() {
                self.bump();
            }
            true
        } else {
            false
        }
    }

    fn err<T>(&self, message: impl Into<String>) -> Result<T, LexError> {
        Err(LexError { message: message.into(), line: self.line })
    }

    // ── Driver ───────────────────────────────────────────────────────────────

    fn run(&mut self, stop: StopAt) -> Result<Vec<Token>, LexError> {
        let mut tokens = Vec::new();
        let mut brace_depth = 0u32;
        loop {
            self.skip_trivia();
            match self.peek() {
                None => match stop {
                    StopAt::Eof => break,
                    StopAt::InterpClose => {
                        return self.err("unterminated template interpolation");
                    }
                },
                Some('}') if matches!(stop, StopAt::InterpClose) && brace_depth == 0 => {
                    self.bump(); // consume the interpolation-closing brace
                    break;
                }
                Some(_) => {
                    let tok = self.next_token()?;
                    match tok.kind {
                        TokenKind::LBrace => brace_depth += 1,
                        TokenKind::RBrace => brace_depth = brace_depth.saturating_sub(1),
                        _ => {}
                    }
                    self.prev = Some(tok.kind.clone());
                    tokens.push(tok);
                }
            }
        }
        Ok(tokens)
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => {
                    self.bump();
                }
                Some('/') if self.peek_at(1) == Some('/') => {
                    // Line comment (incl. `///` doc comments) to end of line.
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                Some('/') if self.peek_at(1) == Some('*') => {
                    // Block comment, non-nesting.
                    self.bump();
                    self.bump();
                    while let Some(c) = self.peek() {
                        if c == '*' && self.peek_at(1) == Some('/') {
                            self.bump();
                            self.bump();
                            break;
                        }
                        self.bump();
                    }
                }
                _ => break,
            }
        }
    }

    // ── One token ────────────────────────────────────────────────────────────

    fn next_token(&mut self) -> Result<Token, LexError> {
        let line = self.line;
        let c = self.peek().expect("next_token called at EOF");

        // Literals and names that don't begin with an operator char.
        if c == '"' {
            return Ok(Token::new(self.lex_string()?, line));
        }
        if c == '`' {
            return Ok(Token::new(self.lex_template()?, line));
        }
        if c == '_' {
            return Ok(Token::new(self.lex_hole(), line));
        }
        if c.is_ascii_digit() {
            return Ok(Token::new(TokenKind::Number(self.lex_number()?), line));
        }
        if is_ident_start(c) {
            return Ok(Token::new(self.lex_ident(), line));
        }

        // Operators and punctuation — maximal munch.
        let kind = self.lex_operator()?;
        Ok(Token::new(kind, line))
    }

    fn lex_operator(&mut self) -> Result<TokenKind, LexError> {
        use TokenKind::*;

        // Order matters: try longer forms first.
        if self.eat("...") {
            return Ok(DotDotDot); // T2: `...` always wins over `.` sequences
        }
        if self.eat("=>") {
            return Ok(FatArrow);
        }
        if self.eat("==") {
            return Ok(EqEq);
        }
        if self.eat("!=") {
            return Ok(BangEq);
        }
        if self.eat("<|") {
            return Ok(LtPipe);
        }
        if self.eat("<=") {
            return Ok(Le);
        }
        if self.eat(">=") {
            return Ok(Ge);
        }
        if self.eat("::") {
            return Ok(ColonColon);
        }
        if self.eat(":=") {
            return Ok(ColonEq);
        }
        // Compound mutation ops (T3: single tokens). Longest first.
        if self.eat("**:=") {
            return Ok(StarStarEq);
        }
        if self.eat("&&:=") {
            return Ok(AmpAmpEq);
        }
        if self.eat("||:=") {
            return Ok(PipePipeEq);
        }
        if self.eat("??:=") {
            return Ok(QuestionQuestionEq);
        }
        if self.eat("+:=") {
            return Ok(PlusEq);
        }
        if self.eat("-:=") {
            return Ok(MinusEq);
        }
        if self.eat("*:=") {
            return Ok(StarEq);
        }
        if self.eat("/:=") {
            return Ok(SlashEq);
        }
        if self.eat("%:=") {
            return Ok(PercentEq);
        }
        if self.eat("**") {
            return Ok(StarStar);
        }
        if self.eat("&&") {
            return Ok(AmpAmp);
        }
        if self.eat("||") {
            return Ok(PipePipe);
        }
        if self.eat("|>") {
            return Ok(PipeGt);
        }
        if self.eat("??") {
            return Ok(QuestionQuestion);
        }

        // `?.` with the T1 digit lookahead: not formed before a decimal digit.
        if self.peek() == Some('?') && self.peek_at(1) == Some('.') {
            if self.peek_at(2).is_some_and(|c| c.is_ascii_digit()) {
                self.bump(); // just `?`; the `.5` becomes a leading-dot number
                return Ok(Question);
            }
            self.bump();
            self.bump();
            return Ok(QuestionDot);
        }

        // `.` — leading-dot number vs member access. (`...` already handled.)
        if self.peek() == Some('.') {
            let next_is_digit = self.peek_at(1).is_some_and(|c| c.is_ascii_digit());
            let after_postfix = self.prev.as_ref().is_some_and(|k| k.ends_postfix_target());
            if next_is_digit && !after_postfix {
                return Ok(TokenKind::Number(self.lex_number()?));
            }
            self.bump();
            return Ok(Dot);
        }

        // Single-character tokens.
        let c = self.bump().unwrap();
        let kind = match c {
            '(' => LParen,
            ')' => RParen,
            '[' => LBracket,
            ']' => RBracket,
            '{' => LBrace,
            '}' => RBrace,
            ',' => Comma,
            '#' => Hash,
            '?' => Question,
            ':' => Colon,
            '<' => Lt,
            '>' => Gt,
            '+' => Plus,
            '-' => Minus,
            '*' => Star,
            '/' => Slash,
            '%' => Percent,
            '!' => Bang,
            '~' => Tilde,
            '=' => Eq,
            '@' => At,
            '^' => Caret,
            '|' => Pipe,
            '&' => return self.err("`&` is not an operator (bitwise family discarded); did you mean `&&`?"),
            '$' => return self.err("`$` is only valid inside template interpolation"),
            other => return self.err(format!("unexpected character `{other}`")),
        };
        Ok(kind)
    }

    // ── Holes and identifiers ────────────────────────────────────────────────

    fn lex_hole(&mut self) -> TokenKind {
        self.bump(); // `_`
        let mut digits = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                digits.push(c);
                self.bump();
            } else {
                break;
            }
        }
        if digits.is_empty() {
            TokenKind::Underscore
        } else {
            // `_0` is not a valid indexed hole (indices are n ≥ 1); parse and let
            // it be `_` + no — grammar says `_n` for n ≥ 1. Treat `_0` as index 0
            // here and let the analyzer reject; but keep it simple: n ≥ 1 only.
            TokenKind::IndexedHole(digits.parse().unwrap_or(0))
        }
    }

    fn lex_ident(&mut self) -> TokenKind {
        let mut name = String::new();
        while let Some(c) = self.peek() {
            if is_ident_continue(c) {
                name.push(c);
                self.bump();
            } else {
                break;
            }
        }
        TokenKind::Ident(name)
    }

    // ── Numeric literals (§1.4) ──────────────────────────────────────────────

    fn lex_number(&mut self) -> Result<Rational, LexError> {
        let start_line = self.line;

        // Base prefixes: 0x / 0o / 0b.
        if self.peek() == Some('0') {
            if let Some(radix_char) = self.peek_at(1) {
                let radix = match radix_char {
                    'x' | 'X' => Some(16),
                    'o' | 'O' => Some(8),
                    'b' | 'B' => Some(2),
                    _ => None,
                };
                if let Some(radix) = radix {
                    self.bump();
                    self.bump();
                    let digits = self.take_digits_with_separators(radix);
                    if digits.is_empty() {
                        return self.err("missing digits after base prefix");
                    }
                    let n = BigInt::from_str_radix(&digits, radix)
                        .map_err(|_| LexError {
                            message: format!("invalid base-{radix} literal"),
                            line: start_line,
                        })?;
                    self.reject_bigint_suffix()?;
                    return Ok(Rational::from_integer(n));
                }
            }
            // Legacy octal / leading zeros: `0` followed by a decimal digit.
            if self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
                return self.err("legacy octal / leading-zero literals are not allowed");
            }
        }

        // Decimal: [int] [. frac] [e exp]. The int part may be empty for the
        // leading-dot form (`.5`).
        let int_part = self.take_digits_with_separators(10);

        let mut frac_part = String::new();
        if self.peek() == Some('.') {
            // Only consume `.` as a fraction point when a digit follows; this
            // keeps `1...3` (T2) and `5.foo` from being misread, and lets `5.`
            // surface as the banned trailing-dot form.
            match self.peek_at(1) {
                Some(d) if d.is_ascii_digit() => {
                    self.bump(); // `.`
                    frac_part = self.take_digits_with_separators(10);
                }
                // `..`/`...` — leave for the operator lexer (T2).
                Some('.') => {}
                // `5.foo` — member access; stop and let `.` become a `Dot`.
                Some(c) if is_ident_start(c) => {}
                // A dangling dot (`5.` before whitespace/operator/EOF) is the
                // banned trailing-dot numeral.
                _ => {
                    return self.err("trailing-dot numerals are not allowed; write `5` or `5.0`");
                }
            }
        }

        if int_part.is_empty() && frac_part.is_empty() {
            return self.err("malformed numeric literal");
        }

        // Exponent.
        let mut exp = String::new();
        if matches!(self.peek(), Some('e' | 'E')) {
            self.bump();
            if matches!(self.peek(), Some('+' | '-')) {
                exp.push(self.bump().unwrap());
            }
            let exp_digits = self.take_digits_with_separators(10);
            if exp_digits.is_empty() {
                return self.err("missing exponent digits");
            }
            exp.push_str(&exp_digits);
        }

        self.reject_bigint_suffix()?;

        // Assemble a canonical decimal string and reuse the B2-aware parser.
        let mut lexeme = String::new();
        if int_part.is_empty() {
            lexeme.push('0');
        } else {
            lexeme.push_str(&int_part);
        }
        if !frac_part.is_empty() {
            lexeme.push('.');
            lexeme.push_str(&frac_part);
        }
        if !exp.is_empty() {
            lexeme.push('e');
            lexeme.push_str(&exp);
        }
        Rational::from_decimal(&lexeme).ok_or(LexError {
            message: format!("invalid numeric literal `{lexeme}`"),
            line: start_line,
        })
    }

    /// Consume digits valid in `radix`, allowing token-internal `_` separators
    /// (never leading/trailing enforcement here — a lint concern). Returns the
    /// digits with separators stripped.
    fn take_digits_with_separators(&mut self, radix: u32) -> String {
        let mut out = String::new();
        while let Some(c) = self.peek() {
            if c == '_' {
                self.bump();
            } else if c.is_digit(radix) {
                out.push(c);
                self.bump();
            } else {
                break;
            }
        }
        out
    }

    fn reject_bigint_suffix(&mut self) -> Result<(), LexError> {
        if self.peek() == Some('n') {
            return self.err("BigInt `n` suffix is not supported (numbers are exact rationals)");
        }
        Ok(())
    }

    // ── String literals (§1.5) ───────────────────────────────────────────────

    fn lex_string(&mut self) -> Result<TokenKind, LexError> {
        self.bump(); // opening `"`
        let mut units: Vec<u16> = Vec::new();
        loop {
            match self.peek() {
                None => return self.err("unterminated string literal"),
                Some('"') => {
                    self.bump();
                    return Ok(TokenKind::Str(units));
                }
                Some('\n') => {
                    return self.err("a string literal may not span lines (use a template)");
                }
                Some('\\') => {
                    self.bump();
                    self.lex_escape(&mut units)?;
                }
                Some(c) => {
                    self.bump();
                    push_utf16(&mut units, c);
                }
            }
        }
    }

    // ── Template literals (§1.5) ─────────────────────────────────────────────

    fn lex_template(&mut self) -> Result<TokenKind, LexError> {
        self.bump(); // opening backtick
        let mut elems: Vec<TemplateElem> = Vec::new();
        let mut seg: Vec<u16> = Vec::new();
        loop {
            match self.peek() {
                None => return self.err("unterminated template literal"),
                Some('`') => {
                    self.bump();
                    if !seg.is_empty() {
                        elems.push(TemplateElem::Str(seg));
                    }
                    return Ok(TokenKind::Template(elems));
                }
                Some('\\') => {
                    self.bump();
                    // Template escapes include \` and \${ in addition to the set.
                    if self.peek() == Some('`') {
                        self.bump();
                        push_utf16(&mut seg, '`');
                    } else if self.peek() == Some('$') {
                        self.bump();
                        push_utf16(&mut seg, '$');
                    } else {
                        self.lex_escape(&mut seg)?;
                    }
                }
                Some('$') if self.peek_at(1) == Some('{') => {
                    self.bump(); // `$`
                    self.bump(); // `{`
                    if !seg.is_empty() {
                        elems.push(TemplateElem::Str(std::mem::take(&mut seg)));
                    }
                    let interp = self.run(StopAt::InterpClose)?;
                    elems.push(TemplateElem::Interp(interp));
                }
                Some(c) => {
                    self.bump();
                    push_utf16(&mut seg, c);
                }
            }
        }
    }

    /// Handle one escape sequence (the backslash is already consumed), pushing
    /// the resulting UTF-16 units. Shared by strings and templates.
    fn lex_escape(&mut self, out: &mut Vec<u16>) -> Result<(), LexError> {
        let c = match self.bump() {
            None => return self.err("unterminated escape sequence"),
            Some(c) => c,
        };
        match c {
            'n' => out.push(b'\n' as u16),
            't' => out.push(b'\t' as u16),
            'r' => out.push(b'\r' as u16),
            '0' => out.push(0),
            'b' => out.push(0x08),
            'f' => out.push(0x0C),
            'v' => out.push(0x0B),
            '\\' => out.push('\\' as u16),
            '"' => out.push('"' as u16),
            '\'' => out.push('\'' as u16),
            'x' => {
                let hi = self.hex_digits(2)?;
                out.push(hi as u16);
            }
            'u' => {
                if self.peek() == Some('{') {
                    self.bump();
                    let mut hex = String::new();
                    while let Some(ch) = self.peek() {
                        if ch == '}' {
                            break;
                        }
                        hex.push(ch);
                        self.bump();
                    }
                    if self.peek() != Some('}') {
                        return self.err("unterminated `\\u{...}` escape");
                    }
                    self.bump(); // `}`
                    let cp = u32::from_str_radix(&hex, 16)
                        .map_err(|_| LexError { message: "invalid `\\u{...}` escape".into(), line: self.line })?;
                    let ch = char::from_u32(cp)
                        .ok_or(LexError { message: "invalid Unicode scalar in escape".into(), line: self.line })?;
                    push_utf16(out, ch); // astral → surrogate pair
                } else {
                    // \uXXXX — a single UTF-16 code unit (may be a surrogate half).
                    let unit = self.hex_digits(4)?;
                    out.push(unit as u16);
                }
            }
            other => return self.err(format!("unknown escape `\\{other}`")),
        }
        Ok(())
    }

    fn hex_digits(&mut self, n: usize) -> Result<u32, LexError> {
        let mut value = 0u32;
        for _ in 0..n {
            let c = self.peek().ok_or(LexError {
                message: "unterminated hex escape".into(),
                line: self.line,
            })?;
            let d = c.to_digit(16).ok_or(LexError {
                message: format!("invalid hex digit `{c}` in escape"),
                line: self.line,
            })?;
            value = value * 16 + d;
            self.bump();
        }
        Ok(value)
    }
}

fn push_utf16(out: &mut Vec<u16>, c: char) {
    let mut buf = [0u16; 2];
    out.extend_from_slice(c.encode_utf16(&mut buf));
}

// Identifier classes (§1.3): Unicode identifier characters, `_`- and `$`-free.
// `_` and `$` are excluded so holes and interpolation sigils never collide. This
// uses std's Unicode-aware `is_alphabetic`/`is_alphanumeric` as an approximation
// of XID_Start/XID_Continue — see DECISIONS.md.
fn is_ident_start(c: char) -> bool {
    c != '_' && c != '$' && c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c != '_' && c != '$' && c.is_alphanumeric()
}
