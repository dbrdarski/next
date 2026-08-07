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
//! - **The arithmetic slice** ([`arith`]): μ §8's frozen `==`-set — commutative
//!   reordering, literal constant folding, and like-term combining.
//!
//! Everything else is a structure-preserving recursive map, so new rules bolt on
//! in one place.
//!
//! ## Why the arithmetic slice lives *here*
//!
//! §8's master law demands the frozen set preserve "demand[s] so shape-level
//! analysis never forgets an obligation" — which only means anything if analysis
//! reads the normalized form. The phase runs inside `lower_program`, so the one
//! rewriting is what the oracle evaluates, what the analyzer contracts over, and
//! (re-run after α-conversion, since renaming changes the ordering keys) what
//! decides function-shape identity. One rule, one law, one harness.

use crate::ast::*;
use crate::interner::Interner;

mod arith;
#[cfg(test)]
mod tests;

/// Normalize a whole module.
pub fn normalize_module(module: &Module, interner: &mut Interner) -> Module {
    Module {
        name: module.name.clone(),
        items: module
            .items
            .iter()
            .map(|i| normalize_item(i, interner))
            .collect(),
    }
}

/// Module items sit in the **pure** world: an ordinary binding, a slot
/// initializer, a `where` contract. Only an act *declaration* leaves it, and it
/// does so through its own lambda's `act_kind`.
fn normalize_item(item: &Item, interner: &mut Interner) -> Item {
    let act = false;
    match item {
        Item::Bind(b) => Item::Bind(normalize_bind(b, interner, act)),
        Item::SlotDecl(s) => Item::SlotDecl(SlotDecl {
            reactive: s.reactive,
            name: s.name.clone(),
            init: normalize_in(&s.init, interner, act),
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
            input_contract: normalize_in(&w.input_contract, interner, act),
            return_contract: normalize_in(&w.return_contract, interner, act),
        }),
        Item::Import(i) => Item::Import(i.clone()),
        Item::Stmt(e) => Item::Stmt(normalize_in(e, interner, act)),
    }
}

fn normalize_bind(b: &Bind, interner: &mut Interner, act: bool) -> Bind {
    Bind {
        target: b.target.clone(),
        value: normalize_in(&b.value, interner, act),
        exported: b.exported,
    }
}

/// Normalize a lambda. Public to the crate because shape canonicalization must
/// re-run the phase **after** α-conversion: renaming rewrites the very `Ref`s the
/// ordering keys are built from, so the pre-α order is not the canonical one.
///
/// The body's world is the lambda's **own** `act_kind`, never the surrounding
/// one — that is where a `@effect`/`@mutate` body starts, and where an ordinary
/// arrow returns to pure.
pub(crate) fn normalize_lambda(l: &Lambda, interner: &mut Interner) -> Lambda {
    Lambda {
        params: l.params.clone(),
        body: Box::new(normalize_in(&l.body, interner, in_act(l.act_kind))),
        act_kind: l.act_kind,
    }
}

fn in_act(kind: ActKind) -> bool {
    !matches!(kind, ActKind::Pure)
}

/// Normalize an expression in the **pure** world — the default everywhere an act
/// body has not been entered, module bindings and slot initializers included.
/// `x = a + b` is a pure expression whether or not a lambda encloses it; having
/// no enclosing lambda is not missing information, it is the ordinary case.
pub fn normalize_expr(e: &Expr, interner: &mut Interner) -> Expr {
    normalize_in(e, interner, false)
}

fn normalize_in(e: &Expr, interner: &mut Interner, act: bool) -> Expr {
    let rebuilt = normalize_children(e, interner, act);
    arith::rewrite(&rebuilt, interner, act)
}

/// The structure-preserving map over children, plus the template rules.
fn normalize_children(e: &Expr, interner: &mut Interner, act: bool) -> Expr {
    match e {
        Expr::Const(_) | Expr::Ref(_) => e.clone(),
        Expr::Lambda(l) => Expr::Lambda(normalize_lambda(l, interner)),
        Expr::Apply { callee, args } => Expr::Apply {
            callee: Box::new(normalize_in(callee, interner, act)),
            args: args
                .iter()
                .map(|a| normalize_arg(a, interner, act))
                .collect(),
        },
        Expr::PrimOp { op, args } => Expr::PrimOp {
            op: *op,
            args: args
                .iter()
                .map(|a| normalize_in(a, interner, act))
                .collect(),
        },
        Expr::Match(m) => Expr::Match(normalize_match(m, interner, act)),
        Expr::TupleCons(elems) => Expr::TupleCons(
            elems
                .iter()
                .map(|el| normalize_element(el, interner, act))
                .collect(),
        ),
        Expr::RecordCons(fields) => Expr::RecordCons(
            fields
                .iter()
                .map(|f| normalize_field(f, interner, act))
                .collect(),
        ),
        Expr::Access {
            target,
            form,
            total,
        } => Expr::Access {
            target: Box::new(normalize_in(target, interner, act)),
            form: normalize_access_form(form, interner, act),
            total: *total,
        },
        Expr::Write { slot, value } => Expr::Write {
            slot: slot.clone(),
            value: Box::new(normalize_in(value, interner, act)),
        },
        Expr::Template(parts) => normalize_template(parts, interner, act),
    }
}

fn normalize_arg(a: &Arg, interner: &mut Interner, act: bool) -> Arg {
    match a {
        Arg::Expr(e) => Arg::Expr(normalize_in(e, interner, act)),
        Arg::Spread(e) => Arg::Spread(normalize_in(e, interner, act)),
    }
}

fn normalize_element(el: &Element, interner: &mut Interner, act: bool) -> Element {
    match el {
        Element::Expr(e) => Element::Expr(normalize_in(e, interner, act)),
        Element::Spread(e) => Element::Spread(normalize_in(e, interner, act)),
    }
}

fn normalize_field(f: &Field, interner: &mut Interner, act: bool) -> Field {
    match f {
        Field::Field { key, value } => Field::Field {
            key: key.clone(),
            value: normalize_in(value, interner, act),
        },
        Field::Computed { key, value } => Field::Computed {
            key: normalize_in(key, interner, act),
            value: normalize_in(value, interner, act),
        },
        Field::Spread(e) => Field::Spread(normalize_in(e, interner, act)),
    }
}

fn normalize_access_form(form: &AccessForm, interner: &mut Interner, act: bool) -> AccessForm {
    match form {
        AccessForm::Field(name) => AccessForm::Field(name.clone()),
        AccessForm::Index(e) => AccessForm::Index(Box::new(normalize_in(e, interner, act))),
        AccessForm::Slice { lo, hi } => AccessForm::Slice {
            lo: lo
                .as_ref()
                .map(|e| Box::new(normalize_in(e, interner, act))),
            hi: hi
                .as_ref()
                .map(|e| Box::new(normalize_in(e, interner, act))),
        },
    }
}

fn normalize_match(m: &Match, interner: &mut Interner, act: bool) -> Match {
    Match {
        scrutinee: m
            .scrutinee
            .as_ref()
            .map(|e| Box::new(normalize_in(e, interner, act))),
        items: m
            .items
            .iter()
            .map(|i| normalize_match_item(i, interner, act))
            .collect(),
    }
}

fn normalize_match_item(item: &MatchItem, interner: &mut Interner, act: bool) -> MatchItem {
    match item {
        MatchItem::Bind(b) => MatchItem::Bind(normalize_bind(b, interner, act)),
        MatchItem::Stmt(e) => MatchItem::Stmt(normalize_in(e, interner, act)),
        MatchItem::Arm(arm) => MatchItem::Arm(Arm {
            pattern: arm.pattern.clone(),
            guard: arm.guard.as_ref().map(|g| normalize_in(g, interner, act)),
            result: normalize_in(&arm.result, interner, act),
        }),
    }
}

/// Template rules (§4): fold adjacent literal segments; a template with no
/// interpolations is the constant string it denotes.
fn normalize_template(parts: &[TemplatePart], interner: &mut Interner, act: bool) -> Expr {
    let normalized: Vec<TemplatePart> = parts
        .iter()
        .map(|p| match p {
            TemplatePart::Segment(s) => TemplatePart::Segment(s.clone()),
            TemplatePart::Interp(e) => TemplatePart::Interp(normalize_in(e, interner, act)),
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
        if let (Some(TemplatePart::Segment(prev)), TemplatePart::Segment(s)) = (out.last_mut(), &p)
        {
            prev.push_str(s);
        } else {
            out.push(p);
        }
    }
    out
}
