//! The **μ-aware call graph** — the induction tail, step 1.
//!
//! Recursion lives in the **captures**, not the code: a recursive or mutual callee
//! `f` in a body is a free variable, canonicalized to a capture slot `@capᵢ` whose
//! original name is `free_vars[i]`; the closure's **shared** environment late-binds
//! it to the target closure (a plain `Binding::Value`, not a slot — slots are only
//! for `@:` mutables). So the call graph is read directly off a closure **value**:
//! walk its shape body for applications and resolve each capture-slot callee to the
//! captured function value. The §4a shape-repeat cutoff ([`build_inventory_by`]) then
//! bounds the reachable set — a recursive edge simply closes as a shape repeat, so no
//! μ-binder minimization is required.
//!
//! **Soundness of the two under-approximations.** The walk does not descend into
//! nested `Lambda` bodies (those are distinct instances) and resolves only
//! capture-slot callees — a parameter or local callee contributes no edge. Both can
//! only *drop* an edge, never add a spurious one, so the inventory may be smaller than
//! the true reachable set; the induction then treats an unreached instance as
//! `unproven`, never a false proof.

use crate::analyzer::inventory::build_inventory_by;
use crate::ast::{AccessForm, Arg, Bind, Element, Expr, Field, Lambda, Match, MatchItem, Ref, TemplatePart};
use crate::env::Binding;
use crate::value::ValueRef;

/// Canonical capture-slot prefix (mirrors `oracle::canon`).
const CAP: &str = "@cap";

/// The function values this closure may call **directly** — its call-graph
/// successors, the captured functions its body applies. Non-function captures,
/// parameters, and locals contribute no edge. Deduplicated by value equality.
pub fn callee_targets(v: &ValueRef) -> Vec<ValueRef> {
    let Some(f) = v.as_fn() else { return vec![] };
    let mut callees: Vec<Expr> = Vec::new();
    collect_callees(&f.shape().body, &mut callees);
    let mut targets: Vec<ValueRef> = Vec::new();
    for callee in &callees {
        let Some(idx) = capture_index(callee) else { continue };
        let Some(orig) = f.free_vars().get(idx) else { continue };
        match f.closure().env.lookup(orig) {
            Some(Binding::Value(cv)) if cv.is_function() && !targets.contains(&cv) => targets.push(cv),
            _ => {}
        }
    }
    targets
}

/// The finite set of closures reachable from `root` under the §4a cutoff — the
/// concrete instance graph the return induction (§6) will process. Every recursive or
/// mutual cycle closes as a shape repeat, so this terminates on any program.
pub fn reachable_closures(root: ValueRef) -> Vec<ValueRef> {
    build_inventory_by(vec![root], closure_shape, callee_targets)
}

/// The program's **finite literal vocabulary** reachable from `root`: every constant
/// appearing in the reachable group's bodies (plus nested lambdas — a literal is a
/// literal wherever it sits). This is the finite, advance-known basis the analyzer
/// admits *exact* recursive domains over (§4b `GeneralizationDomains` "derived from the
/// finite program"): a demanded domain built from these values is analyzed precisely; a
/// **computed** domain outside it resolves through the Kind basis instead, which is what
/// bounds the recursive state universe.
pub fn literal_values(root: &ValueRef) -> Vec<ValueRef> {
    let mut out: Vec<ValueRef> = Vec::new();
    for f in reachable_closures(root.clone()) {
        let Some(fv) = f.as_fn() else { continue };
        collect_consts(&fv.shape().body, &mut out);
    }
    out
}

/// Collect every `Const` value in `e`, descending into nested lambdas.
fn collect_consts(e: &Expr, out: &mut Vec<ValueRef>) {
    let push = |v: &ValueRef, out: &mut Vec<ValueRef>| {
        if !out.contains(v) {
            out.push(v.clone());
        }
    };
    match e {
        Expr::Const(v) => push(v, out),
        Expr::Ref(_) => {}
        Expr::Lambda(l) => collect_consts(&l.body, out),
        Expr::Apply { callee, args } => {
            collect_consts(callee, out);
            for a in args {
                match a {
                    Arg::Expr(x) | Arg::Spread(x) => collect_consts(x, out),
                }
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                collect_consts(a, out);
            }
        }
        Expr::Match(m) => {
            if let Some(s) = &m.scrutinee {
                collect_consts(s, out);
            }
            for item in &m.items {
                match item {
                    MatchItem::Bind(Bind { value, .. }) => collect_consts(value, out),
                    MatchItem::Stmt(x) => collect_consts(x, out),
                    MatchItem::Arm(arm) => {
                        if let Some(p) = &arm.pattern {
                            collect_pattern_consts(p, out);
                        }
                        if let Some(g) = &arm.guard {
                            collect_consts(g, out);
                        }
                        collect_consts(&arm.result, out);
                    }
                }
            }
        }
        Expr::TupleCons(els) => {
            for el in els {
                match el {
                    Element::Expr(x) | Element::Spread(x) => collect_consts(x, out),
                }
            }
        }
        Expr::RecordCons(fs) => {
            for f in fs {
                match f {
                    Field::Field { value, .. } | Field::Spread(value) => collect_consts(value, out),
                    Field::Computed { key, value } => {
                        collect_consts(key, out);
                        collect_consts(value, out);
                    }
                }
            }
        }
        Expr::Access { target, form, .. } => {
            collect_consts(target, out);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(x) => collect_consts(x, out),
                AccessForm::Slice { lo, hi } => {
                    if let Some(x) = lo {
                        collect_consts(x, out);
                    }
                    if let Some(x) = hi {
                        collect_consts(x, out);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    collect_consts(x, out);
                }
            }
        }
        Expr::Write { value, .. } => collect_consts(value, out),
    }
}

/// Literal values bound into patterns (`0 => …`) are part of the vocabulary too.
fn collect_pattern_consts(p: &crate::ast::Pat, out: &mut Vec<ValueRef>) {
    use crate::ast::{Pat, PatElem, PatField};
    match p {
        Pat::Const(v) => {
            if !out.contains(v) {
                out.push(v.clone());
            }
        }
        Pat::Tuple(elems) => {
            for e in elems {
                if let PatElem::Pat(q) = e {
                    collect_pattern_consts(q, out);
                }
            }
        }
        Pat::Record { fields, .. } => {
            for f in fields {
                if let PatField::Field { pat, .. } = f {
                    collect_pattern_consts(pat, out);
                }
            }
        }
        Pat::Wild | Pat::Bind(_) | Pat::Contract(_) => {}
    }
}

/// The shape (canonical `Lambda`) of a closure value; an empty lambda for a
/// non-function (never reached — roots and targets are functions).
fn closure_shape(v: &ValueRef) -> Lambda {
    v.as_fn().map(|f| f.shape().clone()).expect("a closure value")
}

/// If `callee` is a capture-slot reference `@capᵢ`, its index `i`.
fn capture_index(callee: &Expr) -> Option<usize> {
    let Expr::Ref(Ref::Immutable(crate::ast::BindingRef::Name(n))) = callee else { return None };
    n.strip_prefix(CAP).and_then(|d| d.parse::<usize>().ok())
}

/// Collect every application-callee expression in `e`, **without** descending into
/// nested lambdas (a distinct instance).
fn collect_callees(e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::Const(_) | Expr::Ref(_) => {}
        Expr::Lambda(_) => {} // distinct instance — not this body's edges
        Expr::Apply { callee, args } => {
            out.push((**callee).clone());
            collect_callees(callee, out);
            for a in args {
                match a {
                    Arg::Expr(x) | Arg::Spread(x) => collect_callees(x, out),
                }
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                collect_callees(a, out);
            }
        }
        Expr::Match(m) => collect_match(m, out),
        Expr::TupleCons(els) => {
            for el in els {
                match el {
                    Element::Expr(x) | Element::Spread(x) => collect_callees(x, out),
                }
            }
        }
        Expr::RecordCons(fs) => {
            for f in fs {
                match f {
                    Field::Field { value, .. } | Field::Spread(value) => collect_callees(value, out),
                    Field::Computed { key, value } => {
                        collect_callees(key, out);
                        collect_callees(value, out);
                    }
                }
            }
        }
        Expr::Access { target, form, .. } => {
            collect_callees(target, out);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(x) => collect_callees(x, out),
                AccessForm::Slice { lo, hi } => {
                    if let Some(x) = lo {
                        collect_callees(x, out);
                    }
                    if let Some(x) = hi {
                        collect_callees(x, out);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(x) = p {
                    collect_callees(x, out);
                }
            }
        }
        Expr::Write { value, .. } => collect_callees(value, out),
    }
}

fn collect_match(m: &Match, out: &mut Vec<Expr>) {
    if let Some(s) = &m.scrutinee {
        collect_callees(s, out);
    }
    for item in &m.items {
        match item {
            MatchItem::Bind(Bind { value, .. }) => collect_callees(value, out),
            MatchItem::Stmt(x) => collect_callees(x, out),
            MatchItem::Arm(arm) => {
                if let Some(g) = &arm.guard {
                    collect_callees(g, out);
                }
                collect_callees(&arm.result, out);
            }
        }
    }
}
