//! Normalization — the equal-under-rules rewriting of kernel AST (Kernel AST
//! Specification v0.1, §5).
//!
//! `normalize` rewrites a kernel form to a canonical, **evaluation-preserving**
//! one: the harness enforces `eval ∘ normalize = eval` and idempotence against
//! the oracle (Part I). The heavy §5 canonicalization (de-Bruijn free-variable
//! ordering, μ-binder canonicalization) is deferred with the rest of §5 — see
//! DECISIONS.md — so the active rules are the structural, name-free ones the
//! catalog names:
//!
//! - **Template segment folding** (§4): merge adjacent literal segments.
//! - **Literal template → constant**: a template with no interpolations is the
//!   string it denotes (its interpolation stringification is B2's rule, but with
//!   no interpolations it is a plain literal).
//!
//! Everything else is a structure-preserving recursive map, so new rules bolt on
//! in one place.

use crate::ast::*;
use crate::interner::Interner;

#[cfg(test)]
mod tests;

/// Normalize a whole module.
pub fn normalize_module(module: &Module, interner: &mut Interner) -> Module {
    Module {
        name: module.name.clone(),
        items: module.items.iter().map(|i| normalize_item(i, interner)).collect(),
    }
}

fn normalize_item(item: &Item, interner: &mut Interner) -> Item {
    match item {
        Item::Bind(b) => Item::Bind(normalize_bind(b, interner)),
        Item::SlotDecl(s) => Item::SlotDecl(SlotDecl {
            reactive: s.reactive,
            name: s.name.clone(),
            init: normalize_expr(&s.init, interner),
            exported: s.exported,
        }),
        Item::ActBind(a) => Item::ActBind(ActBind {
            kind: a.kind,
            name: a.name.clone(),
            lambda: normalize_lambda(&a.lambda, interner),
            exported: a.exported,
        }),
        Item::Where(w) => Item::Where(Where {
            name: w.name.clone(),
            input_contract: normalize_expr(&w.input_contract, interner),
            return_contract: normalize_expr(&w.return_contract, interner),
        }),
        Item::Import(i) => Item::Import(i.clone()),
        Item::Stmt(e) => Item::Stmt(normalize_expr(e, interner)),
    }
}

fn normalize_bind(b: &Bind, interner: &mut Interner) -> Bind {
    Bind { target: b.target.clone(), value: normalize_expr(&b.value, interner), exported: b.exported }
}

fn normalize_lambda(l: &Lambda, interner: &mut Interner) -> Lambda {
    Lambda {
        params: l.params.clone(),
        body: Box::new(normalize_expr(&l.body, interner)),
        act_kind: l.act_kind,
    }
}

/// Normalize an expression: recurse into children, then apply the local rules.
pub fn normalize_expr(e: &Expr, interner: &mut Interner) -> Expr {
    match e {
        Expr::Const(_) | Expr::Ref(_) => e.clone(),
        Expr::Lambda(l) => Expr::Lambda(normalize_lambda(l, interner)),
        Expr::Apply { callee, args } => Expr::Apply {
            callee: Box::new(normalize_expr(callee, interner)),
            args: args.iter().map(|a| normalize_arg(a, interner)).collect(),
        },
        Expr::PrimOp { op, args } => Expr::PrimOp {
            op: *op,
            args: args.iter().map(|a| normalize_expr(a, interner)).collect(),
        },
        Expr::Match(m) => Expr::Match(normalize_match(m, interner)),
        Expr::TupleCons(elems) => {
            Expr::TupleCons(elems.iter().map(|el| normalize_element(el, interner)).collect())
        }
        Expr::RecordCons(fields) => {
            Expr::RecordCons(fields.iter().map(|f| normalize_field(f, interner)).collect())
        }
        Expr::Access { target, form, total } => Expr::Access {
            target: Box::new(normalize_expr(target, interner)),
            form: normalize_access_form(form, interner),
            total: *total,
        },
        Expr::Write { slot, value } => Expr::Write {
            slot: slot.clone(),
            value: Box::new(normalize_expr(value, interner)),
        },
        Expr::Template(parts) => normalize_template(parts, interner),
    }
}

fn normalize_arg(a: &Arg, interner: &mut Interner) -> Arg {
    match a {
        Arg::Expr(e) => Arg::Expr(normalize_expr(e, interner)),
        Arg::Spread(e) => Arg::Spread(normalize_expr(e, interner)),
    }
}

fn normalize_element(el: &Element, interner: &mut Interner) -> Element {
    match el {
        Element::Expr(e) => Element::Expr(normalize_expr(e, interner)),
        Element::Spread(e) => Element::Spread(normalize_expr(e, interner)),
    }
}

fn normalize_field(f: &Field, interner: &mut Interner) -> Field {
    match f {
        Field::Field { key, value } => {
            Field::Field { key: key.clone(), value: normalize_expr(value, interner) }
        }
        Field::Computed { key, value } => Field::Computed {
            key: normalize_expr(key, interner),
            value: normalize_expr(value, interner),
        },
        Field::Spread(e) => Field::Spread(normalize_expr(e, interner)),
    }
}

fn normalize_access_form(form: &AccessForm, interner: &mut Interner) -> AccessForm {
    match form {
        AccessForm::Field(name) => AccessForm::Field(name.clone()),
        AccessForm::Index(e) => AccessForm::Index(Box::new(normalize_expr(e, interner))),
        AccessForm::Slice { lo, hi } => AccessForm::Slice {
            lo: lo.as_ref().map(|e| Box::new(normalize_expr(e, interner))),
            hi: hi.as_ref().map(|e| Box::new(normalize_expr(e, interner))),
        },
    }
}

fn normalize_match(m: &Match, interner: &mut Interner) -> Match {
    Match {
        scrutinee: m.scrutinee.as_ref().map(|e| Box::new(normalize_expr(e, interner))),
        items: m.items.iter().map(|i| normalize_match_item(i, interner)).collect(),
    }
}

fn normalize_match_item(item: &MatchItem, interner: &mut Interner) -> MatchItem {
    match item {
        MatchItem::Bind(b) => MatchItem::Bind(normalize_bind(b, interner)),
        MatchItem::Stmt(e) => MatchItem::Stmt(normalize_expr(e, interner)),
        MatchItem::Arm(arm) => MatchItem::Arm(Arm {
            pattern: arm.pattern.clone(),
            guard: arm.guard.as_ref().map(|g| normalize_expr(g, interner)),
            result: normalize_expr(&arm.result, interner),
        }),
    }
}

/// Template rules (§4): fold adjacent literal segments; a template with no
/// interpolations is the constant string it denotes.
fn normalize_template(parts: &[TemplatePart], interner: &mut Interner) -> Expr {
    let normalized: Vec<TemplatePart> = parts
        .iter()
        .map(|p| match p {
            TemplatePart::Segment(s) => TemplatePart::Segment(s.clone()),
            TemplatePart::Interp(e) => TemplatePart::Interp(normalize_expr(e, interner)),
        })
        .collect();
    let folded = fold_segments(normalized);

    if folded.iter().all(|p| matches!(p, TemplatePart::Segment(_))) {
        let mut text = String::new();
        for p in &folded {
            if let TemplatePart::Segment(s) = p {
                text.push_str(s);
            }
        }
        return Expr::Const(interner.string(&text));
    }
    Expr::Template(folded)
}

/// Merge consecutive `Segment` parts into one.
fn fold_segments(parts: Vec<TemplatePart>) -> Vec<TemplatePart> {
    let mut out: Vec<TemplatePart> = Vec::with_capacity(parts.len());
    for p in parts {
        if let (Some(TemplatePart::Segment(prev)), TemplatePart::Segment(s)) = (out.last_mut(), &p) {
            prev.push_str(s);
        } else {
            out.push(p);
        }
    }
    out
}
