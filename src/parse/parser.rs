//! The surface parser (Grammar Specification v0.1, §§2–5).
//!
//! Recursive descent over the precedence ladder (§3). Produces the surface AST;
//! desugaring to the kernel form is a separate pass (2c). Statement separation is
//! by natural greedy termination — the parser consumes an expression as far as
//! the grammar allows (the documented greedy-continuation behavior, §1.1), then
//! the next statement begins. Strict L1/L2 line *enforcement* is deferred to a
//! later diagnostic pass (see DECISIONS.md); token lines are preserved for it.

use super::surface::*;
use super::token_kw;
use crate::lex::{Token, TokenKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub line: u32,
}

/// Parse a token stream (as produced by [`crate::lex::lex`]) into a program.
pub fn parse_program(tokens: Vec<Token>) -> Result<SProgram, ParseError> {
    let mut p = Parser::new(tokens);
    let program = p.program()?;
    p.expect(TokenKind::Eof)?;
    Ok(program)
}

/// Parse a token stream as a single expression (for interpolations and tests).
pub fn parse_expression(tokens: Vec<Token>) -> Result<SExpr, ParseError> {
    let mut p = Parser::new(tokens);
    let e = p.expr()?;
    p.expect(TokenKind::Eof)?;
    Ok(e)
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    /// When set, the next arrow body's `{` is forced to a Block (the §8 [1.0.3]
    /// exception for `@`-declaration arrows: act bodies are statement sequences).
    force_at_block: bool,
}

impl Parser {
    fn new(toks: Vec<Token>) -> Parser {
        Parser { toks, pos: 0, force_at_block: false }
    }

    // ── Cursor ───────────────────────────────────────────────────────────────

    fn kind(&self) -> &TokenKind {
        self.toks.get(self.pos).map(|t| &t.kind).unwrap_or(&TokenKind::Eof)
    }

    fn kind_at(&self, n: usize) -> &TokenKind {
        self.toks.get(self.pos + n).map(|t| &t.kind).unwrap_or(&TokenKind::Eof)
    }

    fn line(&self) -> u32 {
        self.toks.get(self.pos).map(|t| t.line).unwrap_or_else(|| {
            self.toks.last().map(|t| t.line).unwrap_or(1)
        })
    }

    fn advance(&mut self) -> TokenKind {
        let k = self.kind().clone();
        if self.pos < self.toks.len() {
            self.pos += 1;
        }
        k
    }

    fn at(&self, k: &TokenKind) -> bool {
        self.kind() == k
    }

    /// Whether the current token sits on the same source line as the previous
    /// one — used to keep a line-leading `[`/`(` from attaching as a postfix.
    fn adjacent_to_prev(&self) -> bool {
        match (self.pos.checked_sub(1).and_then(|i| self.toks.get(i)), self.toks.get(self.pos)) {
            (Some(prev), Some(cur)) => prev.line == cur.line,
            _ => true,
        }
    }

    fn eat(&mut self, k: &TokenKind) -> bool {
        if self.at(k) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, k: TokenKind) -> Result<(), ParseError> {
        if self.at(&k) {
            self.advance();
            Ok(())
        } else {
            Err(self.err(format!("expected {k:?}, found {:?}", self.kind())))
        }
    }

    fn err(&self, message: impl Into<String>) -> ParseError {
        ParseError { message: message.into(), line: self.line() }
    }

    fn ident(&mut self) -> Result<String, ParseError> {
        match self.kind().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(name)
            }
            other => Err(self.err(format!("expected identifier, found {other:?}"))),
        }
    }

    fn at_ident_kw(&self, kw: &str) -> bool {
        matches!(self.kind(), TokenKind::Ident(n) if n == kw)
    }

    fn ident_at_is_kw(&self, n: usize, kw: &str) -> bool {
        matches!(self.kind_at(n), TokenKind::Ident(name) if name == kw)
    }

    // ── Program and statements (§2) ──────────────────────────────────────────

    fn program(&mut self) -> Result<SProgram, ParseError> {
        let header = if self.at_ident_kw(token_kw::MODULE) {
            self.advance();
            Some(self.dotted_name()?)
        } else {
            None
        };
        let mut statements = Vec::new();
        while !self.at(&TokenKind::Eof) {
            statements.push(self.statement()?);
        }
        Ok(SProgram { header, statements })
    }

    fn dotted_name(&mut self) -> Result<Vec<String>, ParseError> {
        let mut parts = vec![self.ident()?];
        while self.eat(&TokenKind::Dot) {
            parts.push(self.ident()?);
        }
        Ok(parts)
    }

    fn statement(&mut self) -> Result<SStmt, ParseError> {
        // Contextual statement heads.
        if self.at_ident_kw(token_kw::IMPORT) && self.import_ahead() {
            return self.import_statement();
        }
        if self.at_ident_kw(token_kw::EXPORT) {
            self.advance();
            return self.exported_statement();
        }
        if self.at(&TokenKind::At) {
            return Ok(SStmt::At(self.at_declaration()?));
        }
        if self.at_ident_kw(token_kw::WHEN) {
            self.advance();
            let guard = self.match_expr()?; // below the arrow tier (see `arm`)
            self.expect(TokenKind::FatArrow)?;
            let result = self.expr()?;
            return Ok(SStmt::WhenArm { guard, result });
        }
        if self.at(&TokenKind::FatArrow) {
            self.advance();
            let result = self.expr()?;
            return Ok(SStmt::ElseArm { result });
        }
        // `name where (...) => ret`.
        if matches!(self.kind(), TokenKind::Ident(_)) && self.ident_at_is_kw(1, token_kw::WHERE) {
            return self.where_statement();
        }

        // Binding / mutation / expression, disambiguated by the statement-only
        // operators `=` (binding) and `:=`/compounds (mutation), which never
        // occur in the expression grammar.
        let save = self.pos;
        if let Some(binding) = self.try_binding(false)? {
            return Ok(SStmt::Binding(binding));
        }
        self.pos = save;
        if let Some(mutation) = self.try_mutation()? {
            return Ok(mutation);
        }
        self.pos = save;
        Ok(SStmt::Expr(self.expr()?))
    }

    /// After `export`: a binding or an `@`-declaration, marked exported.
    fn exported_statement(&mut self) -> Result<SStmt, ParseError> {
        if self.at(&TokenKind::At) {
            let at = self.at_declaration()?;
            let at = match at {
                SAt::Binding { op, mut binding } => {
                    binding.exported = true;
                    SAt::Binding { op, binding }
                }
                other => other,
            };
            return Ok(SStmt::At(at));
        }
        match self.try_binding(true)? {
            Some(binding) => Ok(SStmt::Binding(binding)),
            None => Err(self.err("`export` must be followed by a binding")),
        }
    }

    fn import_ahead(&self) -> bool {
        // Commit `import` as a keyword only when a `{` or a name follows (so a
        // variable literally named `import` can still be bound/used elsewhere).
        matches!(self.kind_at(1), TokenKind::LBrace | TokenKind::Ident(_))
    }

    fn import_statement(&mut self) -> Result<SStmt, ParseError> {
        self.advance(); // `import`
        if self.eat(&TokenKind::LBrace) {
            let mut names = vec![self.ident()?];
            while self.eat(&TokenKind::Comma) {
                if self.at(&TokenKind::RBrace) {
                    break; // trailing comma
                }
                names.push(self.ident()?);
            }
            self.expect(TokenKind::RBrace)?;
            if !self.at_ident_kw(token_kw::FROM) {
                return Err(self.err("expected `from` after import list"));
            }
            self.advance();
            let module = self.dotted_name()?;
            Ok(SStmt::Import { names: Some(names), module })
        } else {
            let module = self.dotted_name()?;
            Ok(SStmt::Import { names: None, module })
        }
    }

    fn where_statement(&mut self) -> Result<SStmt, ParseError> {
        let name = self.ident()?;
        self.advance(); // `where`
        self.expect(TokenKind::LParen)?;
        let mut inputs = Vec::new();
        if !self.at(&TokenKind::RParen) {
            inputs.push(self.expr()?);
            while self.eat(&TokenKind::Comma) {
                if self.at(&TokenKind::RParen) {
                    break;
                }
                inputs.push(self.expr()?);
            }
        }
        self.expect(TokenKind::RParen)?;
        self.expect(TokenKind::FatArrow)?;
        let ret = self.expr()?;
        Ok(SStmt::Where { name, inputs, ret })
    }

    /// Try to parse a binding `BindTarget "=" Expression`. Restores nothing on
    /// failure (caller resets `pos`).
    fn try_binding(&mut self, exported: bool) -> Result<Option<SBinding>, ParseError> {
        let Some(target) = self.try_bind_target() else {
            return Ok(None);
        };
        if !self.eat(&TokenKind::Eq) {
            return Ok(None);
        }
        let value = self.expr()?;
        Ok(Some(SBinding { target, value, exported }))
    }

    fn try_bind_target(&mut self) -> Option<SBindTarget> {
        match self.kind().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Some(SBindTarget::Name(name))
            }
            TokenKind::LBracket => {
                let elems = self.tuple_pattern_elems().ok()?;
                Some(SBindTarget::Tuple(elems))
            }
            TokenKind::LBrace => {
                let (fields, exact) = self.record_pattern_fields().ok()?;
                Some(SBindTarget::Record(fields, exact))
            }
            _ => None,
        }
    }

    fn try_mutation(&mut self) -> Result<Option<SStmt>, ParseError> {
        if !matches!(self.kind(), TokenKind::Ident(_)) {
            return Ok(None);
        }
        let root = self.ident()?;
        let mut segments = Vec::new();
        loop {
            if self.eat(&TokenKind::Dot) {
                segments.push(SPathSeg::Field(self.ident()?));
            } else if self.eat(&TokenKind::LBracket) {
                let seg = self.index_or_slice_path()?;
                self.expect(TokenKind::RBracket)?;
                segments.push(seg);
            } else {
                break;
            }
        }
        let op = match self.kind() {
            TokenKind::ColonEq => MutOp::Assign,
            TokenKind::PlusEq => MutOp::Add,
            TokenKind::MinusEq => MutOp::Sub,
            TokenKind::StarEq => MutOp::Mul,
            TokenKind::SlashEq => MutOp::Div,
            TokenKind::PercentEq => MutOp::Rem,
            TokenKind::StarStarEq => MutOp::Pow,
            TokenKind::AmpAmpEq => MutOp::And,
            TokenKind::PipePipeEq => MutOp::Or,
            TokenKind::QuestionQuestionEq => MutOp::Null,
            _ => return Ok(None),
        };
        self.advance();
        let value = self.expr()?;
        Ok(Some(SStmt::Mutation { path: SPath { root, segments }, op, value }))
    }

    fn index_or_slice_path(&mut self) -> Result<SPathSeg, ParseError> {
        if self.eat(&TokenKind::DotDotDot) {
            let hi = if self.at(&TokenKind::RBracket) { None } else { Some(self.expr()?) };
            return Ok(SPathSeg::Slice { lo: None, hi });
        }
        let first = self.expr()?;
        if self.eat(&TokenKind::DotDotDot) {
            let hi = if self.at(&TokenKind::RBracket) { None } else { Some(self.expr()?) };
            Ok(SPathSeg::Slice { lo: Some(first), hi })
        } else {
            Ok(SPathSeg::Index(first))
        }
    }

    // ── `@` declarations (§2.5) ──────────────────────────────────────────────

    fn at_declaration(&mut self) -> Result<SAt, ParseError> {
        self.expect(TokenKind::At)?;
        let op = self.ident()?;
        self.force_at_block = true;
        let result = if self.looks_like_arrow() {
            let arrow = self.expr()?;
            Ok(SAt::Anon { op, arrow })
        } else {
            let name = self.ident()?;
            let target = SBindTarget::Name(name);
            self.expect(TokenKind::Eq)?;
            let value = self.expr()?;
            Ok(SAt::Binding { op, binding: SBinding { target, value, exported: false } })
        };
        self.force_at_block = false;
        result
    }

    // ── Expression ladder (§3) ───────────────────────────────────────────────

    fn expr(&mut self) -> Result<SExpr, ParseError> {
        self.arrow_expr()
    }

    fn arrow_expr(&mut self) -> Result<SExpr, ParseError> {
        if self.looks_like_arrow() {
            let params = self.params()?;
            self.expect(TokenKind::FatArrow)?;
            let body = self.arrow_body()?;
            return Ok(SExpr::Arrow(SArrow { params, body: Box::new(body) }));
        }
        self.match_expr()
    }

    /// Lookahead for `Params =>`: a bare `IDENT =>`, or a `(...)` whose matching
    /// `)` is immediately followed by `=>`. The `=>` must sit on the **same line**
    /// as its params — a `=>` starting a fresh line is a block-body arm exit, not
    /// an arrow (this is where L2 disambiguates the greedy hazard).
    fn looks_like_arrow(&self) -> bool {
        match self.kind() {
            TokenKind::Ident(_) => self.fat_arrow_same_line(self.pos, self.pos + 1),
            TokenKind::LParen => match self.matching_close(self.pos) {
                Some(close) => self.fat_arrow_same_line(close, close + 1),
                None => false,
            },
            _ => false,
        }
    }

    /// True iff the token at `arrow_idx` is `=>` on the same source line as the
    /// token at `params_end_idx`.
    fn fat_arrow_same_line(&self, params_end_idx: usize, arrow_idx: usize) -> bool {
        match (self.toks.get(params_end_idx), self.toks.get(arrow_idx)) {
            (Some(end), Some(arrow)) => {
                arrow.kind == TokenKind::FatArrow && arrow.line == end.line
            }
            _ => false,
        }
    }

    /// Index of the bracket that closes the one at `open` (any bracket kind).
    fn matching_close(&self, open: usize) -> Option<usize> {
        let mut depth = 0i32;
        let mut i = open;
        while i < self.toks.len() {
            match self.toks[i].kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i);
                    }
                }
                TokenKind::Eof => break,
                _ => {}
            }
            i += 1;
        }
        None
    }

    fn params(&mut self) -> Result<Vec<SParam>, ParseError> {
        if let TokenKind::Ident(name) = self.kind().clone() {
            self.advance();
            return Ok(vec![SParam::Ident(name)]);
        }
        self.expect(TokenKind::LParen)?;
        let mut params = Vec::new();
        if !self.at(&TokenKind::RParen) {
            params.push(self.param()?);
            while self.eat(&TokenKind::Comma) {
                if self.at(&TokenKind::RParen) {
                    break;
                }
                params.push(self.param()?);
            }
        }
        self.expect(TokenKind::RParen)?;
        Ok(params)
    }

    fn param(&mut self) -> Result<SParam, ParseError> {
        match self.kind().clone() {
            TokenKind::DotDotDot => {
                self.advance();
                Ok(SParam::Rest(self.ident()?))
            }
            TokenKind::LBracket => Ok(SParam::Tuple(self.tuple_pattern_elems()?)),
            TokenKind::LBrace => {
                let (fields, exact) = self.record_pattern_fields()?;
                Ok(SParam::Record(fields, exact))
            }
            TokenKind::Ident(name) => {
                self.advance();
                Ok(SParam::Ident(name))
            }
            other => Err(self.err(format!("expected parameter, found {other:?}"))),
        }
    }

    fn arrow_body(&mut self) -> Result<SArrowBody, ParseError> {
        if self.at(&TokenKind::LBrace) {
            let force_block = self.force_at_block;
            self.force_at_block = false;
            if force_block || !self.brace_is_record() {
                return Ok(SArrowBody::Block(self.block()?));
            }
            return Ok(SArrowBody::Expr(self.record_literal()?));
        }
        Ok(SArrowBody::Expr(self.expr()?))
    }

    fn match_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut node = self.pipe_expr()?;
        while self.eat(&TokenKind::ColonColon) {
            self.expect(TokenKind::LBrace)?;
            let arms = self.arm_block()?;
            node = SExpr::Match { scrutinee: Box::new(node), arms };
        }
        Ok(node)
    }

    fn arm_block(&mut self) -> Result<Vec<SArm>, ParseError> {
        let mut arms = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at(&TokenKind::Eof) {
            arms.push(self.arm()?);
        }
        self.expect(TokenKind::RBrace)?;
        Ok(arms)
    }

    fn arm(&mut self) -> Result<SArm, ParseError> {
        // `[pattern] [when guard] => result`.
        let pattern = if self.at(&TokenKind::FatArrow) || self.at_ident_kw(token_kw::WHEN) {
            None
        } else {
            Some(self.pattern()?)
        };
        let guard = if self.at_ident_kw(token_kw::WHEN) {
            self.advance();
            // Parse below the arrow tier so the arm's own `=>` is not swallowed
            // as an arrow body (a guard is a Boolean test, never a bare arrow).
            Some(self.match_expr()?)
        } else {
            None
        };
        self.expect(TokenKind::FatArrow)?;
        let result = self.expr()?;
        Ok(SArm { pattern, guard, result })
    }

    fn pipe_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut operands = vec![self.hask_expr()?];
        let mut dir: Option<PipeDir> = None;
        loop {
            let d = match self.kind() {
                TokenKind::PipeGt => Some(PipeDir::Forward),
                TokenKind::LtPipe => Some(PipeDir::Backward),
                _ => None,
            };
            let Some(d) = d else { break };
            match dir {
                None => dir = Some(d),
                Some(prev) if prev != d => {
                    return Err(self.err(
                        "unparenthesized `|>` and `<|` mixing is not allowed; add parentheses",
                    ));
                }
                _ => {}
            }
            self.advance();
            operands.push(self.hask_expr()?);
        }
        Ok(match dir {
            None => operands.pop().unwrap(),
            Some(PipeDir::Forward) => {
                let mut it = operands.into_iter();
                let mut acc = it.next().unwrap();
                for right in it {
                    acc = SExpr::Pipe {
                        dir: PipeDir::Forward,
                        left: Box::new(acc),
                        right: Box::new(right),
                    };
                }
                acc
            }
            Some(PipeDir::Backward) => {
                let mut acc = operands.pop().unwrap();
                while let Some(left) = operands.pop() {
                    acc = SExpr::Pipe {
                        dir: PipeDir::Backward,
                        left: Box::new(left),
                        right: Box::new(acc),
                    };
                }
                acc
            }
        })
    }

    fn hask_expr(&mut self) -> Result<SExpr, ParseError> {
        if self.at(&TokenKind::Hash) {
            self.advance();
            let body = self.ternary_expr()?;
            return Ok(SExpr::Hask(Box::new(body)));
        }
        self.ternary_expr()
    }

    fn ternary_expr(&mut self) -> Result<SExpr, ParseError> {
        let cond = self.null_or_expr()?;
        if self.eat(&TokenKind::Question) {
            let then = self.ternary_expr()?;
            self.expect(TokenKind::Colon)?;
            let els = self.ternary_expr()?;
            return Ok(SExpr::Ternary {
                cond: Box::new(cond),
                then: Box::new(then),
                els: Box::new(els),
            });
        }
        Ok(cond)
    }

    fn null_or_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut left = self.and_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::QuestionQuestion => BinOp::NullOr,
                TokenKind::PipePipe => BinOp::Or,
                _ => break,
            };
            self.advance();
            let right = self.and_expr()?;
            left = binary(op, left, right);
        }
        Ok(left)
    }

    fn and_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut left = self.eq_expr()?;
        while self.at(&TokenKind::AmpAmp) {
            self.advance();
            let right = self.eq_expr()?;
            left = binary(BinOp::And, left, right);
        }
        Ok(left)
    }

    fn eq_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut left = self.rel_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::EqEq => BinOp::Eq,
                TokenKind::BangEq => BinOp::Ne,
                _ => break,
            };
            self.advance();
            let right = self.rel_expr()?;
            left = binary(op, left, right);
        }
        Ok(left)
    }

    fn rel_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut left = self.add_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Le => BinOp::Le,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::Ge => BinOp::Ge,
                _ => break,
            };
            self.advance();
            let right = self.add_expr()?;
            left = binary(op, left, right);
        }
        Ok(left)
    }

    fn add_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut left = self.mul_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::Plus => BinOp::Add,
                TokenKind::Minus => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let right = self.mul_expr()?;
            left = binary(op, left, right);
        }
        Ok(left)
    }

    fn mul_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut left = self.unary_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::Star => BinOp::Mul,
                TokenKind::Slash => BinOp::Div,
                TokenKind::Percent => BinOp::Rem,
                _ => break,
            };
            self.advance();
            let right = self.unary_expr()?;
            left = binary(op, left, right);
        }
        Ok(left)
    }

    fn unary_expr(&mut self) -> Result<SExpr, ParseError> {
        let op = match self.kind() {
            TokenKind::Minus => Some(UnOp::Neg),
            TokenKind::Bang => Some(UnOp::Not),
            TokenKind::Tilde => Some(UnOp::Loosen),
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            let operand = self.unary_expr()?;
            return Ok(SExpr::Unary { op, operand: Box::new(operand) });
        }
        self.power_expr()
    }

    fn power_expr(&mut self) -> Result<SExpr, ParseError> {
        let base = self.postfix_expr()?;
        if self.eat(&TokenKind::StarStar) {
            let exp = self.unary_expr()?; // right operand admits unary; right-assoc
            return Ok(binary(BinOp::Pow, base, exp));
        }
        Ok(base)
    }

    fn postfix_expr(&mut self) -> Result<SExpr, ParseError> {
        let mut node = self.primary()?;
        loop {
            match self.kind() {
                TokenKind::Dot => {
                    self.advance();
                    let field = self.ident()?;
                    node = SExpr::Access {
                        target: Box::new(node),
                        form: SAccessForm::Field(field),
                        total: false,
                    };
                }
                TokenKind::QuestionDot => {
                    self.advance();
                    if self.eat(&TokenKind::LBracket) {
                        let form = self.index_or_slice()?;
                        self.expect(TokenKind::RBracket)?;
                        node = SExpr::Access { target: Box::new(node), form, total: true };
                    } else {
                        let field = self.ident()?;
                        node = SExpr::Access {
                            target: Box::new(node),
                            form: SAccessForm::Field(field),
                            total: true,
                        };
                    }
                }
                // Index and call only attach when the bracket is on the same line
                // as the target: a `[`/`(` opening a fresh line begins a new
                // statement (the greedy-continuation hazard, §1.1). Leading `.` /
                // `?.` are unambiguous and may continue across lines.
                TokenKind::LBracket if self.adjacent_to_prev() => {
                    self.advance();
                    let form = self.index_or_slice()?;
                    self.expect(TokenKind::RBracket)?;
                    node = SExpr::Access { target: Box::new(node), form, total: false };
                }
                TokenKind::LParen if self.adjacent_to_prev() => {
                    self.advance();
                    let args = self.arg_list()?;
                    self.expect(TokenKind::RParen)?;
                    node = SExpr::Call { callee: Box::new(node), args };
                }
                _ => break,
            }
        }
        Ok(node)
    }

    fn index_or_slice(&mut self) -> Result<SAccessForm, ParseError> {
        if self.eat(&TokenKind::DotDotDot) {
            let hi = if self.at(&TokenKind::RBracket) { None } else { Some(Box::new(self.expr()?)) };
            return Ok(SAccessForm::Slice { lo: None, hi });
        }
        let first = self.expr()?;
        if self.eat(&TokenKind::DotDotDot) {
            let hi = if self.at(&TokenKind::RBracket) { None } else { Some(Box::new(self.expr()?)) };
            Ok(SAccessForm::Slice { lo: Some(Box::new(first)), hi })
        } else {
            Ok(SAccessForm::Index(Box::new(first)))
        }
    }

    fn arg_list(&mut self) -> Result<Vec<SArg>, ParseError> {
        let mut args = Vec::new();
        if !self.at(&TokenKind::RParen) {
            args.push(self.arg()?);
            while self.eat(&TokenKind::Comma) {
                if self.at(&TokenKind::RParen) {
                    break;
                }
                args.push(self.arg()?);
            }
        }
        Ok(args)
    }

    fn arg(&mut self) -> Result<SArg, ParseError> {
        if self.eat(&TokenKind::DotDotDot) {
            Ok(SArg::Spread(self.expr()?))
        } else {
            Ok(SArg::Expr(self.expr()?))
        }
    }

    fn primary(&mut self) -> Result<SExpr, ParseError> {
        match self.kind().clone() {
            TokenKind::Number(n) => {
                self.advance();
                Ok(SExpr::Number(n))
            }
            TokenKind::Str(units) => {
                self.advance();
                Ok(SExpr::Str(units))
            }
            TokenKind::Template(parts) => {
                self.advance();
                Ok(SExpr::Template(self.template_parts(parts)?))
            }
            TokenKind::Ident(name) => {
                self.advance();
                Ok(SExpr::Ident(name))
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(SExpr::Hole(Hole::Anon))
            }
            TokenKind::IndexedHole(n) => {
                self.advance();
                Ok(SExpr::Hole(Hole::Indexed(n)))
            }
            TokenKind::Hash => {
                // A grouped hask primary `#( Expression )` — the only `#` form
                // legal below the loose-prefix tier (§3 Primary).
                self.advance();
                if !self.at(&TokenKind::LParen) {
                    return Err(self.err("a bare hask `#` is not allowed here; group it as `#(...)`"));
                }
                self.advance();
                let inner = self.expr()?;
                self.expect(TokenKind::RParen)?;
                Ok(SExpr::Hask(Box::new(SExpr::Grouping(Box::new(inner)))))
            }
            TokenKind::LParen => {
                self.advance();
                let inner = self.expr()?;
                self.expect(TokenKind::RParen)?;
                Ok(SExpr::Grouping(Box::new(inner)))
            }
            TokenKind::LBracket => self.tuple_literal(),
            TokenKind::LBrace => self.record_literal(),
            other => Err(self.err(format!("expected an expression, found {other:?}"))),
        }
    }

    fn template_parts(&mut self, parts: Vec<crate::lex::TemplateElem>) -> Result<Vec<STemplatePart>, ParseError> {
        let mut out = Vec::new();
        for part in parts {
            match part {
                crate::lex::TemplateElem::Str(u) => out.push(STemplatePart::Str(u)),
                crate::lex::TemplateElem::Interp(toks) => {
                    let mut inner = toks;
                    inner.push(Token::new(TokenKind::Eof, self.line()));
                    out.push(STemplatePart::Interp(parse_expression(inner)?));
                }
            }
        }
        Ok(out)
    }

    fn tuple_literal(&mut self) -> Result<SExpr, ParseError> {
        self.expect(TokenKind::LBracket)?;
        let mut elems = Vec::new();
        if !self.at(&TokenKind::RBracket) {
            elems.push(self.element()?);
            while self.eat(&TokenKind::Comma) {
                if self.at(&TokenKind::RBracket) {
                    break;
                }
                elems.push(self.element()?);
            }
        }
        self.expect(TokenKind::RBracket)?;
        Ok(SExpr::Tuple(elems))
    }

    fn element(&mut self) -> Result<SElem, ParseError> {
        if self.eat(&TokenKind::DotDotDot) {
            Ok(SElem::Spread(self.expr()?))
        } else {
            Ok(SElem::Expr(self.expr()?))
        }
    }

    /// `{` opens a record when the first token is `}`, `IDENT :`, `IDENT` then
    /// `,`/`}` (shorthand), `[` (computed key), or `...` (§8). Assumes the
    /// current token is `{`.
    fn brace_is_record(&self) -> bool {
        match self.kind_at(1) {
            TokenKind::RBrace => true,
            TokenKind::LBracket | TokenKind::DotDotDot => true,
            TokenKind::Ident(_) => matches!(
                self.kind_at(2),
                TokenKind::Colon | TokenKind::Comma | TokenKind::RBrace
            ),
            _ => false,
        }
    }

    fn record_literal(&mut self) -> Result<SExpr, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut fields = Vec::new();
        if !self.at(&TokenKind::RBrace) {
            fields.push(self.record_field()?);
            while self.eat(&TokenKind::Comma) {
                if self.at(&TokenKind::RBrace) {
                    break;
                }
                fields.push(self.record_field()?);
            }
        }
        self.expect(TokenKind::RBrace)?;
        Ok(SExpr::Record(fields))
    }

    fn record_field(&mut self) -> Result<SField, ParseError> {
        if self.eat(&TokenKind::DotDotDot) {
            return Ok(SField::Spread(self.expr()?));
        }
        if self.eat(&TokenKind::LBracket) {
            let key = self.expr()?;
            self.expect(TokenKind::RBracket)?;
            self.expect(TokenKind::Colon)?;
            let value = self.expr()?;
            return Ok(SField::Computed(key, value));
        }
        let name = self.ident()?;
        if self.eat(&TokenKind::Colon) {
            let value = self.expr()?;
            Ok(SField::KeyValue(name, value))
        } else {
            Ok(SField::Shorthand(name))
        }
    }

    fn block(&mut self) -> Result<Vec<SStmt>, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut stmts = Vec::new();
        while !self.at(&TokenKind::RBrace) && !self.at(&TokenKind::Eof) {
            stmts.push(self.statement()?);
        }
        self.expect(TokenKind::RBrace)?;
        Ok(stmts)
    }

    // ── Patterns (§4) ────────────────────────────────────────────────────────

    fn pattern(&mut self) -> Result<SPattern, ParseError> {
        let first = self.pattern_seq()?;
        if !self.at(&TokenKind::Pipe) {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(&TokenKind::Pipe) {
            alts.push(self.pattern_seq()?);
        }
        Ok(SPattern::Alt(alts))
    }

    fn pattern_seq(&mut self) -> Result<SPattern, ParseError> {
        match self.kind().clone() {
            TokenKind::Minus => {
                self.advance();
                match self.kind().clone() {
                    TokenKind::Number(n) => {
                        self.advance();
                        Ok(SPattern::Number(-n))
                    }
                    other => Err(self.err(format!("expected a number after `-` in pattern, found {other:?}"))),
                }
            }
            TokenKind::Number(n) => {
                self.advance();
                Ok(SPattern::Number(n))
            }
            TokenKind::Str(units) => {
                self.advance();
                Ok(SPattern::Str(units))
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(SPattern::Wild)
            }
            TokenKind::Caret => {
                self.advance();
                match self.kind().clone() {
                    TokenKind::Ident(name) => {
                        self.advance();
                        Ok(SPattern::Pin(name))
                    }
                    TokenKind::Underscore => {
                        self.advance();
                        Ok(SPattern::PinHole(Hole::Anon))
                    }
                    TokenKind::IndexedHole(n) => {
                        self.advance();
                        Ok(SPattern::PinHole(Hole::Indexed(n)))
                    }
                    other => Err(self.err(format!("expected name or hole after `^`, found {other:?}"))),
                }
            }
            TokenKind::Ident(name) => {
                self.advance();
                Ok(classify_ident_pattern(name))
            }
            TokenKind::LBracket => Ok(SPattern::Tuple(self.tuple_pattern_elems()?)),
            TokenKind::LBrace => {
                let (fields, exact) = self.record_pattern_fields()?;
                Ok(SPattern::Record(fields, exact))
            }
            other => Err(self.err(format!("expected a pattern, found {other:?}"))),
        }
    }

    fn tuple_pattern_elems(&mut self) -> Result<Vec<SPatElem>, ParseError> {
        self.expect(TokenKind::LBracket)?;
        let mut elems = Vec::new();
        if !self.at(&TokenKind::RBracket) {
            elems.push(self.pat_elem()?);
            while self.eat(&TokenKind::Comma) {
                if self.at(&TokenKind::RBracket) {
                    break;
                }
                elems.push(self.pat_elem()?);
            }
        }
        self.expect(TokenKind::RBracket)?;
        Ok(elems)
    }

    fn pat_elem(&mut self) -> Result<SPatElem, ParseError> {
        if self.eat(&TokenKind::DotDotDot) {
            Ok(SPatElem::Rest(self.rest_binder()?))
        } else {
            Ok(SPatElem::Pat(self.pattern()?))
        }
    }

    fn record_pattern_fields(&mut self) -> Result<(Vec<SPatField>, bool), ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut exact = true;
        if !self.at(&TokenKind::RBrace) {
            loop {
                if self.eat(&TokenKind::DotDotDot) {
                    fields.push(SPatField::Rest(self.rest_binder()?));
                    exact = false;
                } else {
                    let key = self.ident()?;
                    let pat = if self.eat(&TokenKind::Colon) { Some(self.pattern()?) } else { None };
                    fields.push(SPatField::Field(key, pat));
                }
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
                if self.at(&TokenKind::RBrace) {
                    break;
                }
            }
        }
        self.expect(TokenKind::RBrace)?;
        Ok((fields, exact))
    }

    /// A rest binder after `...`: `_` (ignore) or an identifier (capture).
    fn rest_binder(&mut self) -> Result<Option<String>, ParseError> {
        match self.kind().clone() {
            TokenKind::Underscore => {
                self.advance();
                Ok(None)
            }
            TokenKind::Ident(name) => {
                self.advance();
                Ok(Some(name))
            }
            other => Err(self.err(format!("expected `_` or a name after `...`, found {other:?}"))),
        }
    }
}

fn binary(op: BinOp, left: SExpr, right: SExpr) -> SExpr {
    SExpr::Binary { op, left: Box::new(left), right: Box::new(right) }
}

/// Classify an identifier appearing in pattern position (§4, §8): the prelude
/// constants are literals, a capitalized name is a contract, otherwise a binding.
fn classify_ident_pattern(name: String) -> SPattern {
    match name.as_str() {
        "true" | "false" | "null" => SPattern::Prelude(name),
        _ if name.chars().next().is_some_and(|c| c.is_uppercase()) => SPattern::Contract(name),
        _ => SPattern::Bind(name),
    }
}
