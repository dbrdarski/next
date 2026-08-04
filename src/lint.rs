//! The lint tier (A-LNT) — advisory findings only; a lint **never** rejects.
//!
//! Lints live where their information lives. Here: the **source-text** pass (the
//! leading-`-` continuation hazard E1 states) and the **surface** pass (`~`/`?.`
//! redundancy, the identity slice, the non-Boolean `||` right — all sugar the kernel
//! erases). The program checker owns the analysis-adjacent lints (goes-nowhere,
//! discarded fallible-effect result, self-prefix imports), where act kinds and
//! produced contracts are in hand. All are `Severity::Warning`.
//!
//! v1 scope: syntactic recognizers, one honest case each (the suite row's grain) —
//! `~` on a literal Boolean or comparison; `?.` on a record literal that spells the
//! field; a literal non-Boolean right of an **unescaped** `||`. Contract-aware
//! precision (a receiver *proven* non-null, a right operand *proven* non-Boolean)
//! rides the analyzer later; absence of a lint is always sound.

use crate::analyzer::{Finding, Severity};
use crate::oracle::TrapClass;
use crate::parse::surface::{
    BinOp, SAccessForm, SArg, SArm, SArrowBody, SAt, SElem, SExpr, SField, SPathSeg, SProgram,
    SStmt, STemplatePart, UnOp,
};

fn lint(message: impl Into<String>) -> Finding {
    Finding {
        class: TrapClass::ArgumentObligation,
        severity: Severity::Warning,
        message: message.into(),
    }
}

/// The source-text pass: a continuation line whose first token is `-` parses as
/// subtraction (E1's stated hazard) — legal, linted.
pub fn source_lints(src: &str) -> Vec<Finding> {
    let mut out = Vec::new();
    for (i, line) in src.lines().enumerate() {
        let trimmed = line.trim_start();
        if i > 0 && trimmed.starts_with('-') && !trimmed.starts_with("--") {
            out.push(lint(format!(
                "line {}: a leading `-` continues the previous expression as subtraction \
                 (leading-minus continuation)",
                i + 1
            )));
        }
    }
    out
}

/// The surface pass — sugar-level redundancies the kernel erases.
pub fn surface_lints(p: &SProgram) -> Vec<Finding> {
    let mut out = Vec::new();
    for s in &p.statements {
        stmt(s, &mut out);
    }
    out
}

fn stmt(s: &SStmt, out: &mut Vec<Finding>) {
    match s {
        SStmt::Binding(b) => expr(&b.value, out),
        SStmt::Expr(e) => expr(e, out),
        SStmt::Import { .. } | SStmt::Where { .. } => {}
        SStmt::At(SAt::Binding { binding, .. }) => expr(&binding.value, out),
        SStmt::At(SAt::Anon { arrow, .. }) => expr(arrow, out),
        SStmt::Mutation { path, value, .. } => {
            for seg in &path.segments {
                match seg {
                    SPathSeg::Field(_) => {}
                    SPathSeg::Index(e) => expr(e, out),
                    SPathSeg::Slice { lo, hi } => {
                        if let Some(e) = lo {
                            expr(e, out);
                        }
                        if let Some(e) = hi {
                            expr(e, out);
                        }
                    }
                }
            }
            expr(value, out);
        }
        SStmt::WhenArm { guard, result } => {
            expr(guard, out);
            expr(result, out);
        }
        SStmt::ElseArm { result } => expr(result, out),
    }
}

fn expr(e: &SExpr, out: &mut Vec<Finding>) {
    match e {
        SExpr::Unary {
            op: UnOp::Loosen,
            operand,
        } => {
            if boolean_shaped(operand) {
                out.push(lint(
                    "`~` loosens a seat its operand already satisfies — the operand is \
                     Boolean (redundant `~`)",
                ));
            }
            expr(operand, out);
        }
        SExpr::Binary { op, left, right }
            if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                && (comparison(left) || comparison(right)) =>
        {
            // E2: comparison chains self-refute (a Boolean lands in a relational
            // operand — the rejection is the operand demand's); this is the owed hint.
            out.push(lint(
                "a comparison chains into a comparison — did you mean `a < b && b < c`? (comparison-chain hint)",
            ));
            expr(left, out);
            expr(right, out);
        }
        SExpr::Binary {
            op: BinOp::Or,
            left,
            right,
        } => {
            let escaped = matches!(
                &**left,
                SExpr::Unary {
                    op: UnOp::Loosen,
                    ..
                }
            );
            if !escaped && non_boolean_literal(right) {
                out.push(lint(
                    "a non-Boolean right of an unescaped `||` — legal, but only `false` \
                     selects it (non-Boolean `||` right)",
                ));
            }
            expr(left, out);
            expr(right, out);
        }
        SExpr::Access {
            target,
            form: SAccessForm::Slice { lo: None, hi: None },
            ..
        } => {
            out.push(lint(
                "`t[...]` is the identity slice — it returns `t` itself, same pointer",
            ));
            expr(target, out);
        }
        SExpr::Access {
            target,
            form: SAccessForm::Field(field),
            total: true,
        } => {
            if let SExpr::Record(fields) = &**target
                && fields.iter().any(|f| match f {
                    SField::Shorthand(k) | SField::KeyValue(k, _) => k == field,
                    SField::Computed(..) | SField::Spread(_) => false,
                })
            {
                out.push(lint(format!(
                    "`?.` on a record that spells `{field}` — permission granted where none \
                     is needed (redundant `?.`)"
                )));
            }
            expr(target, out);
        }
        SExpr::Number(_) | SExpr::Str(_) | SExpr::Ident(_) | SExpr::Hole(_) => {}
        SExpr::Template(parts) => {
            for p in parts {
                if let STemplatePart::Interp(x) = p {
                    expr(x, out);
                }
            }
        }
        SExpr::Tuple(els) => {
            for el in els {
                let (SElem::Expr(x) | SElem::Spread(x)) = el;
                expr(x, out);
            }
        }
        SExpr::Record(fields) => {
            for f in fields {
                match f {
                    SField::Shorthand(_) => {}
                    SField::KeyValue(_, v) | SField::Spread(v) => expr(v, out),
                    SField::Computed(k, v) => {
                        expr(k, out);
                        expr(v, out);
                    }
                }
            }
        }
        SExpr::Block(stmts) => {
            for s in stmts {
                stmt(s, out);
            }
        }
        SExpr::Grouping(x) | SExpr::Hask(x) => expr(x, out),
        SExpr::Arrow(a) => match &*a.body {
            SArrowBody::Expr(x) => expr(x, out),
            SArrowBody::Block(stmts) => {
                for s in stmts {
                    stmt(s, out);
                }
            }
        },
        SExpr::Match { scrutinee, arms } => {
            expr(scrutinee, out);
            for SArm { guard, result, .. } in arms {
                if let Some(g) = guard {
                    expr(g, out);
                }
                expr(result, out);
            }
        }
        SExpr::Pipe { left, right, .. } => {
            expr(left, out);
            expr(right, out);
        }
        SExpr::Ternary { cond, then, els } => {
            expr(cond, out);
            expr(then, out);
            expr(els, out);
        }
        SExpr::Binary { left, right, .. } => {
            expr(left, out);
            expr(right, out);
        }
        SExpr::Unary { operand, .. } => expr(operand, out),
        SExpr::Access { target, form, .. } => {
            expr(target, out);
            match form {
                SAccessForm::Field(_) => {}
                SAccessForm::Index(x) => expr(x, out),
                SAccessForm::Slice { lo, hi } => {
                    if let Some(x) = lo {
                        expr(x, out);
                    }
                    if let Some(x) = hi {
                        expr(x, out);
                    }
                }
            }
        }
        SExpr::Call { callee, args } => {
            expr(callee, out);
            for a in args {
                let (SArg::Expr(x) | SArg::Spread(x)) = a;
                expr(x, out);
            }
        }
    }
}

/// Syntactically Boolean: the literals, a comparison/equality/logic result, or `!`.
fn boolean_shaped(e: &SExpr) -> bool {
    match e {
        SExpr::Ident(n) => n == "true" || n == "false",
        SExpr::Unary { op: UnOp::Not, .. } => true,
        SExpr::Binary { op, .. } => matches!(
            op,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::And
        ),
        SExpr::Grouping(x) => boolean_shaped(x),
        _ => false,
    }
}

/// A comparison node (through grouping) — the chain hint's operand test.
fn comparison(e: &SExpr) -> bool {
    match e {
        SExpr::Binary { op, .. } => matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge),
        SExpr::Grouping(x) => comparison(x),
        _ => false,
    }
}

/// Syntactically non-Boolean: a literal number/string/tuple/record/template.
fn non_boolean_literal(e: &SExpr) -> bool {
    matches!(
        e,
        SExpr::Number(_) | SExpr::Str(_) | SExpr::Template(_) | SExpr::Tuple(_) | SExpr::Record(_)
    )
}
