//! Desugaring: surface AST → kernel AST (Kernel AST Specification v0.1, §4).
//!
//! The catalog is **closed and normative** — every surface form not already a
//! kernel node lowers here, before identity/contract analysis. Constants are
//! interned as they are produced. The output is kernel AST in its
//! *pre-canonicalization* form: `Ref`s and `Write` slots still carry surface
//! names (resolving names to positional/location markers is §5/analyzer work).
//!
//! Rows implemented per §4 and E10; the deferred corners (nested pins, index/
//! slice mutation, mixed hask holes, the reactive fence) return a clear
//! `DesugarError` rather than guessing — see DECISIONS.md.

use crate::ast::*;
use crate::interner::Interner;
use crate::parse::surface::*;

mod hask;
#[cfg(test)]
mod tests;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DesugarError {
    pub message: String,
}

fn err<T>(message: impl Into<String>) -> Result<T, DesugarError> {
    Err(DesugarError { message: message.into() })
}

/// Lowers surface syntax to kernel AST, interning constants through `interner`.
pub struct Desugarer<'a> {
    interner: &'a mut Interner,
    gensym: u32,
    /// Active hask scopes (innermost last). A `#` pushes one; holes inside
    /// register against the top scope (a nested `#` opens a fresh scope — E4).
    hask_stack: Vec<hask::HaskScope>,
}

impl<'a> Desugarer<'a> {
    pub fn new(interner: &'a mut Interner) -> Desugarer<'a> {
        Desugarer { interner, gensym: 0, hask_stack: Vec::new() }
    }

    /// A fresh synthetic binding name. Uses a `%` prefix, which no surface
    /// identifier can contain (identifiers are `_`/`$`-free alphanumerics), so
    /// generated names never collide with user names.
    fn fresh(&mut self, tag: &str) -> String {
        let n = self.gensym;
        self.gensym += 1;
        format!("%{tag}{n}")
    }

    // ── Constants ────────────────────────────────────────────────────────────

    fn c_bool(&mut self, b: bool) -> Expr {
        Expr::Const(self.interner.boolean(b))
    }
    fn c_null(&mut self) -> Expr {
        Expr::Const(self.interner.null())
    }

    fn name_ref(name: &str) -> Expr {
        Expr::Ref(Ref::Immutable(BindingRef::Name(name.to_string())))
    }

    // ── Program / module ─────────────────────────────────────────────────────

    pub fn program(&mut self, p: &SProgram) -> Result<Module, DesugarError> {
        let mut items = Vec::new();
        for stmt in &p.statements {
            items.extend(self.top_item(stmt)?);
        }
        Ok(Module { name: p.header.as_ref().map(|parts| parts.join(".")), items })
    }

    fn top_item(&mut self, stmt: &SStmt) -> Result<Vec<Item>, DesugarError> {
        Ok(match stmt {
            SStmt::Binding(b) => vec![Item::Bind(self.binding(b)?)],
            SStmt::Import { names, module } => vec![Item::Import(Import {
                names: names.clone(),
                module: module.join("."),
            })],
            SStmt::Where { name, inputs, ret } => {
                vec![Item::Where(self.where_clause(name, inputs, ret)?)]
            }
            SStmt::At(at) => vec![self.at_item(at)?],
            SStmt::Mutation { path, op, value } => {
                vec![Item::Stmt(self.mutation(path, *op, value)?)]
            }
            SStmt::Expr(e) => vec![Item::Stmt(self.expr(e)?)],
            SStmt::WhenArm { .. } | SStmt::ElseArm { .. } => {
                return err("arm exits (`=>` / `when`) are only legal inside a block body");
            }
        })
    }

    fn binding(&mut self, b: &SBinding) -> Result<Bind, DesugarError> {
        Ok(Bind {
            target: self.bind_target(&b.target)?,
            value: self.expr(&b.value)?,
            exported: b.exported,
        })
    }

    fn bind_target(&mut self, t: &SBindTarget) -> Result<BindTarget, DesugarError> {
        Ok(match t {
            SBindTarget::Name(n) => BindTarget::Name(n.clone()),
            SBindTarget::Tuple(elems) => BindTarget::Pattern(Pat::Tuple(self.pat_elems(elems)?)),
            SBindTarget::Record(fields, exact) => {
                BindTarget::Pattern(Pat::Record { fields: self.pat_fields(fields)?, exact: *exact })
            }
        })
    }

    fn where_clause(
        &mut self,
        name: &str,
        inputs: &[SExpr],
        ret: &SExpr,
    ) -> Result<Where, DesugarError> {
        // A multi-element contract list is a contract over the argument tuple.
        let input_contract = match inputs {
            [single] => self.expr(single)?,
            many => {
                let elems = many
                    .iter()
                    .map(|e| Ok(Element::Expr(self.expr(e)?)))
                    .collect::<Result<_, DesugarError>>()?;
                Expr::TupleCons(elems)
            }
        };
        Ok(Where {
            name: name.to_string(),
            input_contract,
            return_contract: self.expr(ret)?,
        })
    }

    fn at_item(&mut self, at: &SAt) -> Result<Item, DesugarError> {
        match at {
            SAt::Binding { op, binding } => match op.as_str() {
                "state" | "mutable" => {
                    let name = match &binding.target {
                        SBindTarget::Name(n) => n.clone(),
                        _ => return err("@state/@mutable require a simple name target"),
                    };
                    Ok(Item::SlotDecl(SlotDecl {
                        reactive: op == "state",
                        name,
                        init: self.expr(&binding.value)?,
                        exported: binding.exported,
                    }))
                }
                "mutate" | "effect" => {
                    let name = match &binding.target {
                        SBindTarget::Name(n) => n.clone(),
                        _ => return err("@mutate/@effect require a simple name target"),
                    };
                    let kind = if op == "mutate" { ActKind::Mutator } else { ActKind::Effect };
                    let mut lambda = self.expect_lambda(&binding.value)?;
                    lambda.act_kind = kind;
                    Ok(Item::ActBind(ActBind { kind, name, lambda, exported: binding.exported }))
                }
                "computed" | "reactive" => {
                    err("@computed/@reactive are the fenced reactive layer (G1); not implemented")
                }
                other => err(format!("unknown privileged operation `@{other}`")),
            },
            SAt::Anon { op, .. } => {
                err(format!("anonymous `@{op}` declarations are the fenced reactive layer (G1)"))
            }
        }
    }

    fn expect_lambda(&mut self, e: &SExpr) -> Result<Lambda, DesugarError> {
        match self.expr(e)? {
            Expr::Lambda(l) => Ok(l),
            _ => err("expected an arrow function on the right of this `@`-declaration"),
        }
    }

    // ── Expressions ──────────────────────────────────────────────────────────

    pub fn expr(&mut self, e: &SExpr) -> Result<Expr, DesugarError> {
        Ok(match e {
            SExpr::Number(n) => Expr::Const(self.interner.number(n.clone())),
            SExpr::Str(u) => Expr::Const(self.interner.string_units(u.clone())),
            SExpr::Template(parts) => Expr::Template(self.template(parts)?),
            SExpr::Ident(name) => match name.as_str() {
                "true" => self.c_bool(true),
                "false" => self.c_bool(false),
                "null" => self.c_null(),
                _ => Self::name_ref(name),
            },
            SExpr::Hole(h) => {
                let name = self.register_hole(h)?;
                Self::name_ref(&name)
            }
            SExpr::Grouping(inner) => self.expr(inner)?,
            SExpr::Tuple(elems) => Expr::TupleCons(self.elements(elems)?),
            SExpr::Record(fields) => Expr::RecordCons(self.fields(fields)?),
            SExpr::Block(stmts) => Expr::Match(self.block_match(stmts)?),
            SExpr::Arrow(a) => Expr::Lambda(self.arrow(a)?),
            SExpr::Hask(body) => self.hask(body)?,
            SExpr::Match { scrutinee, arms } => {
                let scrut = self.expr(scrutinee)?;
                let mut items = Vec::new();
                for arm in arms {
                    for a in self.arm(arm)? {
                        items.push(MatchItem::Arm(a));
                    }
                }
                Expr::Match(Match { scrutinee: Some(Box::new(scrut)), items })
            }
            SExpr::Pipe { dir, left, right } => self.pipe(*dir, left, right)?,
            SExpr::Ternary { cond, then, els } => {
                // c ? t : e  ⇒  Match(c, [true => t, false => e]).
                let scrut = self.expr(cond)?;
                let t = self.expr(then)?;
                let f = self.expr(els)?;
                self.bool_match(scrut, t, f)
            }
            SExpr::Binary { op, left, right } => self.binary(*op, left, right)?,
            SExpr::Unary { op, operand } => self.unary(*op, operand)?,
            SExpr::Access { target, form, total } => Expr::Access {
                target: Box::new(self.expr(target)?),
                form: self.access_form(form)?,
                total: *total,
            },
            SExpr::Call { callee, args } => Expr::Apply {
                callee: Box::new(self.expr(callee)?),
                args: self.args(args)?,
            },
        })
    }

    fn template(&mut self, parts: &[STemplatePart]) -> Result<Vec<TemplatePart>, DesugarError> {
        parts
            .iter()
            .map(|p| {
                Ok(match p {
                    STemplatePart::Str(u) => TemplatePart::Segment(String::from_utf16_lossy(u)),
                    STemplatePart::Interp(e) => TemplatePart::Interp(self.expr(e)?),
                })
            })
            .collect()
    }

    fn elements(&mut self, elems: &[SElem]) -> Result<Vec<Element>, DesugarError> {
        elems
            .iter()
            .map(|el| {
                Ok(match el {
                    SElem::Expr(e) => Element::Expr(self.expr(e)?),
                    // `...<hole>` inside a hask is a rest hole (`..._` / `..._n`).
                    SElem::Spread(SExpr::Hole(h)) if !self.hask_stack.is_empty() => {
                        Element::Spread(Self::name_ref(&self.register_rest_hole(h)?))
                    }
                    SElem::Spread(e) => Element::Spread(self.expr(e)?),
                })
            })
            .collect()
    }

    fn fields(&mut self, fields: &[SField]) -> Result<Vec<Field>, DesugarError> {
        fields
            .iter()
            .map(|f| {
                Ok(match f {
                    SField::Shorthand(name) => {
                        Field::Field { key: name.clone(), value: Self::name_ref(name) }
                    }
                    SField::KeyValue(k, v) => Field::Field { key: k.clone(), value: self.expr(v)? },
                    SField::Computed(k, v) => {
                        Field::Computed { key: self.expr(k)?, value: self.expr(v)? }
                    }
                    SField::Spread(e) => Field::Spread(self.expr(e)?),
                })
            })
            .collect()
    }

    fn args(&mut self, args: &[SArg]) -> Result<Vec<Arg>, DesugarError> {
        args.iter()
            .map(|a| {
                Ok(match a {
                    SArg::Expr(e) => Arg::Expr(self.expr(e)?),
                    SArg::Spread(SExpr::Hole(h)) if !self.hask_stack.is_empty() => {
                        Arg::Spread(Self::name_ref(&self.register_rest_hole(h)?))
                    }
                    SArg::Spread(e) => Arg::Spread(self.expr(e)?),
                })
            })
            .collect()
    }

    fn access_form(&mut self, form: &SAccessForm) -> Result<AccessForm, DesugarError> {
        Ok(match form {
            SAccessForm::Field(name) => AccessForm::Field(name.clone()),
            SAccessForm::Index(e) => AccessForm::Index(Box::new(self.expr(e)?)),
            SAccessForm::Slice { lo, hi } => AccessForm::Slice {
                lo: self.opt_expr(lo)?,
                hi: self.opt_expr(hi)?,
            },
        })
    }

    fn opt_expr(&mut self, e: &Option<Box<SExpr>>) -> Result<Option<Box<Expr>>, DesugarError> {
        Ok(match e {
            Some(inner) => Some(Box::new(self.expr(inner)?)),
            None => None,
        })
    }

    fn pipe(&mut self, dir: PipeDir, left: &SExpr, right: &SExpr) -> Result<Expr, DesugarError> {
        // x |> f  ≡  f <| x  ≡  Apply(f, [x]) — application, nothing else (E2).
        let (callee, arg) = match dir {
            PipeDir::Forward => (right, left),
            PipeDir::Backward => (left, right),
        };
        Ok(Expr::Apply {
            callee: Box::new(self.expr(callee)?),
            args: vec![Arg::Expr(self.expr(arg)?)],
        })
    }

    fn binary(&mut self, op: BinOp, left: &SExpr, right: &SExpr) -> Result<Expr, DesugarError> {
        // Escaped-selection forms: `~a || b`, `~a && b` (E10 / §4).
        if let SExpr::Unary { op: UnOp::Loosen, operand } = left {
            match op {
                BinOp::Or => return self.escaped_or(operand, right),
                BinOp::And => return self.escaped_and(operand, right),
                _ => {}
            }
        }
        match op {
            BinOp::And => {
                // a && b  ⇒  a ? b : false
                let a = self.expr(left)?;
                let b = self.expr(right)?;
                let f = self.c_bool(false);
                Ok(self.bool_match(a, b, f))
            }
            BinOp::Or => {
                // a || b  ⇒  a ? true : b
                let a = self.expr(left)?;
                let t = self.c_bool(true);
                let b = self.expr(right)?;
                Ok(self.bool_match(a, t, b))
            }
            BinOp::NullOr => {
                // a ?? b  ⇒  Match(a, [null => b, v => v]); scrutinee once.
                let a = self.expr(left)?;
                let b = self.expr(right)?;
                let v = self.fresh("nn");
                let null_pat = Pat::Const(self.interner.null());
                Ok(Expr::Match(Match {
                    scrutinee: Some(Box::new(a)),
                    items: vec![
                        MatchItem::Arm(Arm { pattern: Some(null_pat), guard: None, result: b }),
                        MatchItem::Arm(Arm {
                            pattern: Some(Pat::Bind(v.clone())),
                            guard: None,
                            result: Self::name_ref(&v),
                        }),
                    ],
                }))
            }
            _ => {
                let prim = match op {
                    BinOp::Eq => PrimOp::Eq,
                    BinOp::Ne => PrimOp::Ne,
                    BinOp::Lt => PrimOp::Lt,
                    BinOp::Le => PrimOp::Le,
                    BinOp::Gt => PrimOp::Gt,
                    BinOp::Ge => PrimOp::Ge,
                    BinOp::Add => PrimOp::Add,
                    BinOp::Sub => PrimOp::Sub,
                    BinOp::Mul => PrimOp::Mul,
                    BinOp::Div => PrimOp::Div,
                    BinOp::Rem => PrimOp::Rem,
                    BinOp::Pow => PrimOp::Pow,
                    BinOp::And | BinOp::Or | BinOp::NullOr => unreachable!(),
                };
                Ok(Expr::PrimOp {
                    op: prim,
                    args: vec![self.expr(left)?, self.expr(right)?],
                })
            }
        }
    }

    fn unary(&mut self, op: UnOp, operand: &SExpr) -> Result<Expr, DesugarError> {
        match op {
            UnOp::Neg => Ok(Expr::PrimOp { op: PrimOp::Neg, args: vec![self.expr(operand)?] }),
            UnOp::Not => {
                // `!~x` is the falsiness test emitting Booleans (E10 / §4).
                if let SExpr::Unary { op: UnOp::Loosen, operand: inner } = operand {
                    let a = self.expr(inner)?;
                    let (t, f) = (self.c_bool(true), self.c_bool(false));
                    // is-falsy: false/null => true, else false
                    return Ok(self.falsy_set_match(a, t, f));
                }
                // !x  ⇒  Match(x, [true => false, false => true])
                let x = self.expr(operand)?;
                let f = self.c_bool(false);
                let t = self.c_bool(true);
                Ok(self.bool_match(x, f, t))
            }
            UnOp::Loosen => {
                // A bare `~a` in a value/tested seat: the truthiness test itself
                // (E10 — the classification as a value happens via glyphs; here we
                // emit the strict-Boolean test the seat demands).
                let a = self.expr(operand)?;
                let (t, f) = (self.c_bool(true), self.c_bool(false));
                Ok(self.falsy_set_match(a, f, t)) // falsy => f(false), truthy => t(true)
            }
        }
    }

    /// `~a || b` (E10): a itself when truthy, else b.
    fn escaped_or(&mut self, a: &SExpr, b: &SExpr) -> Result<Expr, DesugarError> {
        let scrut = self.expr(a)?;
        let b1 = self.expr(b)?;
        let b2 = b1.clone();
        let v = self.fresh("esc");
        let (false_p, null_p) = (self.interner.boolean(false), self.interner.null());
        Ok(Expr::Match(Match {
            scrutinee: Some(Box::new(scrut)),
            items: vec![
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(false_p)), guard: None, result: b1 }),
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(null_p)), guard: None, result: b2 }),
                MatchItem::Arm(Arm {
                    pattern: Some(Pat::Bind(v.clone())),
                    guard: None,
                    result: Self::name_ref(&v),
                }),
            ],
        }))
    }

    /// `~a && b` (E10): b when a truthy, else a itself (the falsy propagates).
    fn escaped_and(&mut self, a: &SExpr, b: &SExpr) -> Result<Expr, DesugarError> {
        let scrut = self.expr(a)?;
        let b1 = self.expr(b)?;
        let (false_c, null_c) = (self.c_bool(false), self.c_null());
        let (false_p, null_p) = (self.interner.boolean(false), self.interner.null());
        let v = self.fresh("esc");
        Ok(Expr::Match(Match {
            scrutinee: Some(Box::new(scrut)),
            items: vec![
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(false_p)), guard: None, result: false_c }),
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(null_p)), guard: None, result: null_c }),
                MatchItem::Arm(Arm { pattern: Some(Pat::Bind(v)), guard: None, result: b1 }),
            ],
        }))
    }

    /// Match on a strict Boolean scrutinee: `[true => t, false => f]`.
    fn bool_match(&mut self, scrut: Expr, t: Expr, f: Expr) -> Expr {
        let (tp, fp) = (self.interner.boolean(true), self.interner.boolean(false));
        Expr::Match(Match {
            scrutinee: Some(Box::new(scrut)),
            items: vec![
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(tp)), guard: None, result: t }),
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(fp)), guard: None, result: f }),
            ],
        })
    }

    /// Match on the falsy set: `false`/`null` => `falsy`, anything else => `other`.
    fn falsy_set_match(&mut self, scrut: Expr, falsy: Expr, other: Expr) -> Expr {
        let falsy2 = falsy.clone();
        let (fp, np) = (self.interner.boolean(false), self.interner.null());
        Expr::Match(Match {
            scrutinee: Some(Box::new(scrut)),
            items: vec![
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(fp)), guard: None, result: falsy }),
                MatchItem::Arm(Arm { pattern: Some(Pat::Const(np)), guard: None, result: falsy2 }),
                MatchItem::Arm(Arm { pattern: Some(Pat::Wild), guard: None, result: other }),
            ],
        })
    }

    // ── Arrows and blocks ────────────────────────────────────────────────────

    fn arrow(&mut self, a: &SArrow) -> Result<Lambda, DesugarError> {
        let params = self.params_pattern(&a.params)?;
        let body = match &*a.body {
            SArrowBody::Expr(e) => self.expr(e)?,
            SArrowBody::Block(stmts) => Expr::Match(self.block_match(stmts)?),
        };
        Ok(Lambda { params, body: Box::new(body), act_kind: ActKind::Pure })
    }

    /// Parameters lower to a pattern over the complete argument tuple (the arity
    /// model, E3): integer arity is the exact-tuple special case.
    fn params_pattern(&mut self, params: &[SParam]) -> Result<Pat, DesugarError> {
        let mut elems = Vec::with_capacity(params.len());
        for p in params {
            elems.push(match p {
                SParam::Ident(n) => PatElem::Pat(Pat::Bind(n.clone())),
                SParam::Tuple(es) => PatElem::Pat(Pat::Tuple(self.pat_elems(es)?)),
                SParam::Record(fs, exact) => {
                    PatElem::Pat(Pat::Record { fields: self.pat_fields(fs)?, exact: *exact })
                }
                SParam::Rest(n) => PatElem::Rest(Some(n.clone())),
            });
        }
        Ok(Pat::Tuple(elems))
    }

    /// A block lowers to a `Match` with no scrutinee (E10 / §4): bindings and
    /// statements interleaved, arm exits as guarded/unguarded arms.
    fn block_match(&mut self, stmts: &[SStmt]) -> Result<Match, DesugarError> {
        let mut items = Vec::new();
        for stmt in stmts {
            match stmt {
                SStmt::Binding(b) => items.push(MatchItem::Bind(self.binding(b)?)),
                SStmt::Expr(e) => items.push(MatchItem::Stmt(self.expr(e)?)),
                SStmt::Mutation { path, op, value } => {
                    items.push(MatchItem::Stmt(self.mutation(path, *op, value)?))
                }
                SStmt::WhenArm { guard, result } => items.push(MatchItem::Arm(Arm {
                    pattern: None,
                    guard: Some(self.guard(guard)?),
                    result: self.expr(result)?,
                })),
                SStmt::ElseArm { result } => items.push(MatchItem::Arm(Arm {
                    pattern: None,
                    guard: None,
                    result: self.expr(result)?,
                })),
                SStmt::At(_) | SStmt::Import { .. } | SStmt::Where { .. } => {
                    return err("declarations are not allowed inside a block body");
                }
            }
        }
        Ok(Match { scrutinee: None, items })
    }

    // ── Match arms and patterns ──────────────────────────────────────────────

    /// One surface arm lowers to one or more kernel arms: alternation expands
    /// (§4), and a top-level pin becomes an equality guard.
    fn arm(&mut self, a: &SArm) -> Result<Vec<Arm>, DesugarError> {
        let result = self.expr(&a.result)?;
        let base_guard = match &a.guard {
            Some(g) => Some(self.guard(g)?),
            None => None,
        };

        let patterns: Vec<&SPattern> = match &a.pattern {
            Some(SPattern::Alt(alts)) => {
                // Alternation is sound because alternatives are binding-free (E9,
                // P-30): a capture in any alternative is rejected here (the spec
                // allows parse- or analyzer-phase; desugar is the earliest point
                // that sees the expanded arms).
                for alt in alts {
                    if let Some(name) = first_binding(alt) {
                        return err(format!(
                            "alternation alternatives are binding-free (E9): `{name}` binds"
                        ));
                    }
                }
                alts.iter().collect()
            }
            Some(p) => vec![p],
            None => {
                return Ok(vec![Arm { pattern: None, guard: base_guard, result }]);
            }
        };

        let mut out = Vec::with_capacity(patterns.len());
        for p in patterns {
            let (pat, guard) = self.arm_pattern(p, base_guard.clone())?;
            out.push(Arm { pattern: Some(pat), guard, result: result.clone() });
        }
        Ok(out)
    }

    /// Lower an arm pattern, folding a top-level pin `^name` into an equality
    /// guard combined with any existing guard (§4).
    fn arm_pattern(
        &mut self,
        p: &SPattern,
        base_guard: Option<Expr>,
    ) -> Result<(Pat, Option<Expr>), DesugarError> {
        match p {
            SPattern::Pin(name) => {
                // `^name` ⇒ bind a fresh temp and add an equality guard, combined
                // with any existing guard via `&&`.
                let tmp = self.fresh("pin");
                let eq = Expr::PrimOp {
                    op: PrimOp::Eq,
                    args: vec![Self::name_ref(&tmp), Self::name_ref(name)],
                };
                let guard = match base_guard {
                    Some(g) => Some(self.and_exprs(eq, g)),
                    None => Some(eq),
                };
                Ok((Pat::Bind(tmp), guard))
            }
            _ => Ok((self.pattern(p)?, base_guard)),
        }
    }

    /// Kernel-level `&&` over two already-lowered Boolean expressions.
    fn and_exprs(&mut self, a: Expr, b: Expr) -> Expr {
        let f = self.c_bool(false);
        self.bool_match(a, b, f)
    }

    /// A guard is a strict tested seat; a `~`-loosened guard becomes the
    /// truthiness test (E10). Plain guards pass through as Boolean expressions.
    fn guard(&mut self, g: &SExpr) -> Result<Expr, DesugarError> {
        if let SExpr::Unary { op: UnOp::Loosen, operand } = g {
            let a = self.expr(operand)?;
            let (t, f) = (self.c_bool(true), self.c_bool(false));
            return Ok(self.falsy_set_match(a, f, t));
        }
        self.expr(g)
    }

    fn pattern(&mut self, p: &SPattern) -> Result<Pat, DesugarError> {
        Ok(match p {
            SPattern::Number(n) => Pat::Const(self.interner.number(n.clone())),
            SPattern::Str(u) => Pat::Const(self.interner.string_units(u.clone())),
            SPattern::Prelude(name) => Pat::Const(match name.as_str() {
                "true" => self.interner.boolean(true),
                "false" => self.interner.boolean(false),
                _ => self.interner.null(),
            }),
            SPattern::Bind(n) => Pat::Bind(n.clone()),
            SPattern::Wild => Pat::Wild,
            SPattern::Contract(n) => {
                Pat::Contract(Ref::Immutable(BindingRef::Name(n.clone())))
            }
            SPattern::Tuple(elems) => Pat::Tuple(self.pat_elems(elems)?),
            SPattern::Record(fields, exact) => {
                Pat::Record { fields: self.pat_fields(fields)?, exact: *exact }
            }
            SPattern::Pin(_) | SPattern::PinHole(_) => {
                return err("pins are only supported at the top level of an arm pattern (v0.1)");
            }
            SPattern::Alt(_) => {
                return err("nested alternation is not yet lowered (v0.1)");
            }
        })
    }

    fn pat_elems(&mut self, elems: &[SPatElem]) -> Result<Vec<PatElem>, DesugarError> {
        elems
            .iter()
            .map(|e| {
                Ok(match e {
                    SPatElem::Pat(p) => PatElem::Pat(self.pattern(p)?),
                    SPatElem::Rest(name) => PatElem::Rest(name.clone()),
                })
            })
            .collect()
    }

    fn pat_fields(&mut self, fields: &[SPatField]) -> Result<Vec<PatField>, DesugarError> {
        fields
            .iter()
            .map(|f| {
                Ok(match f {
                    SPatField::Field(key, pat) => PatField::Field {
                        key: key.clone(),
                        pat: match pat {
                            Some(p) => self.pattern(p)?,
                            None => Pat::Bind(key.clone()), // shorthand `{ key }`
                        },
                    },
                    SPatField::Rest(name) => PatField::Rest(name.clone()),
                })
            })
            .collect()
    }

    // ── Mutation (§4) ────────────────────────────────────────────────────────

    fn mutation(&mut self, path: &SPath, op: MutOp, value: &SExpr) -> Result<Expr, DesugarError> {
        // The splice row (§4): `items[a...b] := r` ⇒ `Write(items,
        // [...items[...a], ...r, ...items[b...]])` — a spread-composed splice
        // (E7). An absent bound drops its side's spread (empty window).
        if let [SPathSeg::Slice { lo, hi }] = path.segments.as_slice() {
            if op != MutOp::Assign {
                return err("compound assignment on a slice is not defined; use `:=`");
            }
            let r = self.expr(value)?;
            let slice_of = |lo: Option<Box<Expr>>, hi: Option<Box<Expr>>| Expr::Access {
                target: Box::new(Self::name_ref(&path.root)),
                form: AccessForm::Slice { lo, hi },
                total: false, // slices ignore `total` — clamped-total always (E7)
            };
            let mut elems: Vec<Element> = Vec::new();
            if let Some(a) = lo {
                let a_k = Box::new(self.expr(a)?);
                elems.push(Element::Spread(slice_of(None, Some(a_k))));
            }
            elems.push(Element::Spread(r));
            if let Some(b) = hi {
                let b_k = Box::new(self.expr(b)?);
                elems.push(Element::Spread(slice_of(Some(b_k), None)));
            }
            return Ok(Expr::Write {
                slot: SlotRef::Name(path.root.clone()),
                value: Box::new(Expr::TupleCons(elems)),
            });
        }

        // Only field paths are lowered otherwise; index mutation is deferred.
        let mut fields = Vec::new();
        for seg in &path.segments {
            match seg {
                SPathSeg::Field(f) => fields.push(f.clone()),
                SPathSeg::Index(_) | SPathSeg::Slice { .. } => {
                    return err("index mutation / non-terminal slice is not yet lowered (v0.1)");
                }
            }
        }

        let rhs = self.expr(value)?;
        // The value written is `combine(op, read(path), rhs)`.
        let new_value = if op == MutOp::Assign {
            rhs
        } else {
            let read = self.read_path(&path.root, &fields);
            self.combine(op, read, rhs)?
        };

        // Functional update: rebuild the root with the nested field replaced.
        let updated = self.field_update(&path.root, &fields, new_value);
        Ok(Expr::Write { slot: SlotRef::Name(path.root.clone()), value: Box::new(updated) })
    }

    /// Read expression for a field path: `root.f1.f2…` (demand form).
    fn read_path(&self, root: &str, fields: &[String]) -> Expr {
        let mut node = Self::name_ref(root);
        for f in fields {
            node = Expr::Access {
                target: Box::new(node),
                form: AccessForm::Field(f.clone()),
                total: false,
            };
        }
        node
    }

    /// Functional record update: `root.f1.f2 := v` ⇒
    /// `{ ...root, f1: { ...root.f1, f2: v } }` (E5 spread-nesting; B5 atomic).
    fn field_update(&mut self, root: &str, fields: &[String], new_value: Expr) -> Expr {
        fn build(base: Expr, fields: &[String], new_value: Expr) -> Expr {
            match fields {
                [] => new_value,
                [f, rest @ ..] => {
                    let inner_base = Expr::Access {
                        target: Box::new(base.clone()),
                        form: AccessForm::Field(f.clone()),
                        total: false,
                    };
                    let inner = build(inner_base, rest, new_value);
                    Expr::RecordCons(vec![
                        Field::Spread(base),
                        Field::Field { key: f.clone(), value: inner },
                    ])
                }
            }
        }
        if fields.is_empty() {
            // Bare `x := v` — the written value is just `v`.
            new_value
        } else {
            build(Self::name_ref(root), fields, new_value)
        }
    }

    /// Combine a compound mutation operator with the current value: `x op:= e`.
    fn combine(&mut self, op: MutOp, read: Expr, rhs: Expr) -> Result<Expr, DesugarError> {
        Ok(match op {
            MutOp::Assign => rhs,
            MutOp::Add => prim(PrimOp::Add, read, rhs),
            MutOp::Sub => prim(PrimOp::Sub, read, rhs),
            MutOp::Mul => prim(PrimOp::Mul, read, rhs),
            MutOp::Div => prim(PrimOp::Div, read, rhs),
            MutOp::Rem => prim(PrimOp::Rem, read, rhs),
            MutOp::Pow => prim(PrimOp::Pow, read, rhs),
            MutOp::And => {
                let f = self.c_bool(false);
                self.bool_match(read, rhs, f)
            }
            MutOp::Or => {
                let t = self.c_bool(true);
                self.bool_match(read, t, rhs)
            }
            MutOp::Null => {
                let v = self.fresh("nn");
                let null_pat = Pat::Const(self.interner.null());
                Expr::Match(Match {
                    scrutinee: Some(Box::new(read)),
                    items: vec![
                        MatchItem::Arm(Arm { pattern: Some(null_pat), guard: None, result: rhs }),
                        MatchItem::Arm(Arm {
                            pattern: Some(Pat::Bind(v.clone())),
                            guard: None,
                            result: Self::name_ref(&v),
                        }),
                    ],
                })
            }
        })
    }
}

fn prim(op: PrimOp, a: Expr, b: Expr) -> Expr {
    Expr::PrimOp { op, args: vec![a, b] }
}

/// The first bound name in a surface pattern, if any — alternation alternatives
/// must be binding-free (E9). Pins compare (no binding); record-field shorthand
/// (`{x}`) and captured rests bind.
fn first_binding(p: &SPattern) -> Option<String> {
    match p {
        SPattern::Bind(name) => Some(name.clone()),
        SPattern::Tuple(elems) => elems.iter().find_map(|e| match e {
            SPatElem::Pat(inner) => first_binding(inner),
            SPatElem::Rest(Some(name)) => Some(name.clone()),
            SPatElem::Rest(None) => None,
        }),
        SPattern::Record(fields, _) => fields.iter().find_map(|f| match f {
            SPatField::Field(key, None) => Some(key.clone()), // shorthand binds
            SPatField::Field(_, Some(inner)) => first_binding(inner),
            SPatField::Rest(Some(name)) => Some(name.clone()),
            SPatField::Rest(None) => None,
        }),
        SPattern::Alt(alts) => alts.iter().find_map(first_binding),
        _ => None,
    }
}
