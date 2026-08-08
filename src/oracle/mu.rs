//! Recursive construction-window discovery.
//!
//! SCCs here only tell the evaluator when a mutually recursive set must be
//! allocated and closed together. They do not contribute function identity.
//! Identity comes from each function's canonical code applied to its immutable
//! positional capture graph; the interner closes and bisimulation-collapses that
//! graph after this temporary construction window has served its purpose.

use std::collections::{HashMap, HashSet};

use crate::ast::*;

#[cfg(test)]
mod tests;

// ── Free group references (respecting binders) ───────────────────────────────

fn free_group_refs(e: &Expr, group: &HashSet<String>) -> HashSet<String> {
    let mut found = HashSet::new();
    let mut bound: Vec<String> = Vec::new();
    collect_refs(e, group, &mut bound, &mut found);
    found
}

/// A recursive construction window over one lexical item sequence. `members`
/// are the SCC's own declarations; `end` also covers any later declaration the
/// component needs as an external capture before it can become a closed value.
#[derive(Clone, Debug)]
pub(super) struct GroupWindow {
    pub start: usize,
    pub end: usize,
    pub members: Vec<(usize, String)>,
}

/// Derive recursive construction windows from `(item index, binding name,
/// initializer)` triples. The SCC is construction scheduling only; the window
/// does not create or contribute to function identity. Its lifetime extends
/// through later declaration dependencies so closure never exposes a graph with
/// an unresolved outside capture.
pub(super) fn group_windows(bindings: &[(usize, String, Expr)]) -> Vec<GroupWindow> {
    let names: Vec<String> = bindings.iter().map(|(_, name, _)| name.clone()).collect();
    let name_set: HashSet<String> = names.iter().cloned().collect();
    let index: HashMap<String, usize> = names.iter().cloned().zip(0..).collect();
    let graph: Vec<HashSet<usize>> = bindings
        .iter()
        .map(|(_, _, initializer)| {
            free_group_refs(initializer, &name_set)
                .into_iter()
                .filter_map(|name| index.get(&name).copied())
                .collect()
        })
        .collect();

    let mut windows = Vec::new();
    for component in tarjan_scc(&graph) {
        let cyclic = component.len() > 1
            || component
                .first()
                .is_some_and(|member| graph[*member].contains(member));
        if !cyclic {
            continue;
        }

        let mut reachable: HashSet<usize> = component.iter().copied().collect();
        let mut stack = component.clone();
        while let Some(member) = stack.pop() {
            for dependency in &graph[member] {
                if reachable.insert(*dependency) {
                    stack.push(*dependency);
                }
            }
        }

        let members: Vec<(usize, String)> = component
            .iter()
            .map(|member| (bindings[*member].0, bindings[*member].1.clone()))
            .collect();
        let start = members.iter().map(|(item, _)| *item).min().unwrap();
        let end = reachable
            .iter()
            .map(|member| bindings[*member].0)
            .max()
            .unwrap();
        windows.push(GroupWindow {
            start,
            end,
            members,
        });
    }
    windows.sort_by_key(|window| (window.start, window.end));
    windows
}

fn collect_refs(
    e: &Expr,
    group: &HashSet<String>,
    bound: &mut Vec<String>,
    found: &mut HashSet<String>,
) {
    match e {
        Expr::Const(_) => {}
        Expr::Ref(Ref::Immutable(BindingRef::Name(n))) => {
            if !bound.contains(n) && group.contains(n) {
                found.insert(n.clone());
            }
        }
        Expr::Ref(_) => {}
        Expr::Lambda(l) => {
            let mark = bound.len();
            bind_pat(&l.params, bound);
            collect_refs(&l.body, group, bound, found);
            bound.truncate(mark);
        }
        Expr::Apply { callee, args } => {
            collect_refs(callee, group, bound, found);
            for a in args {
                match a {
                    Arg::Expr(e) | Arg::Spread(e) => collect_refs(e, group, bound, found),
                }
            }
        }
        Expr::PrimOp { args, .. } => {
            for a in args {
                collect_refs(a, group, bound, found);
            }
        }
        Expr::Match(m) => {
            let mark = bound.len();
            if let Some(s) = &m.scrutinee {
                collect_refs(s, group, bound, found);
            }
            for item in &m.items {
                match item {
                    MatchItem::Bind(b) => {
                        collect_refs(&b.value, group, bound, found);
                        bind_target(&b.target, bound);
                    }
                    MatchItem::Stmt(e) => collect_refs(e, group, bound, found),
                    MatchItem::Arm(arm) => {
                        let arm_mark = bound.len();
                        if let Some(p) = &arm.pattern {
                            bind_pat(p, bound);
                        }
                        if let Some(g) = &arm.guard {
                            collect_refs(g, group, bound, found);
                        }
                        collect_refs(&arm.result, group, bound, found);
                        bound.truncate(arm_mark);
                    }
                }
            }
            bound.truncate(mark);
        }
        Expr::TupleCons(elems) => {
            for el in elems {
                match el {
                    Element::Expr(e) | Element::Spread(e) => collect_refs(e, group, bound, found),
                }
            }
        }
        Expr::RecordCons(fields) => {
            for f in fields {
                match f {
                    Field::Field { value, .. } => collect_refs(value, group, bound, found),
                    Field::Computed { key, value } => {
                        collect_refs(key, group, bound, found);
                        collect_refs(value, group, bound, found);
                    }
                    Field::Spread(e) => collect_refs(e, group, bound, found),
                }
            }
        }
        Expr::Access { target, form, .. } => {
            collect_refs(target, group, bound, found);
            match form {
                AccessForm::Field(_) => {}
                AccessForm::Index(e) => collect_refs(e, group, bound, found),
                AccessForm::Slice { lo, hi } => {
                    if let Some(e) = lo {
                        collect_refs(e, group, bound, found);
                    }
                    if let Some(e) = hi {
                        collect_refs(e, group, bound, found);
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TemplatePart::Interp(e) = p {
                    collect_refs(e, group, bound, found);
                }
            }
        }
        Expr::Write { slot, value } => {
            match slot {
                SlotRef::Name(n) if !bound.contains(n) && group.contains(n) => {
                    found.insert(n.clone());
                }
                _ => {}
            }
            collect_refs(value, group, bound, found);
        }
    }
}

fn bind_pat(p: &Pat, bound: &mut Vec<String>) {
    match p {
        Pat::Bind(n) => bound.push(n.clone()),
        Pat::Tuple(elems) => {
            for e in elems {
                match e {
                    PatElem::Pat(p) => bind_pat(p, bound),
                    PatElem::Rest(Some(n)) => bound.push(n.clone()),
                    PatElem::Rest(None) => {}
                }
            }
        }
        Pat::Record { fields, .. } => {
            for f in fields {
                match f {
                    PatField::Field { pat, .. } => bind_pat(pat, bound),
                    PatField::Rest(Some(n)) => bound.push(n.clone()),
                    PatField::Rest(None) => {}
                }
            }
        }
        Pat::Const(_) | Pat::Wild | Pat::Contract(_) => {}
    }
}

fn bind_target(t: &BindTarget, bound: &mut Vec<String>) {
    match t {
        BindTarget::Name(n) => bound.push(n.clone()),
        BindTarget::Pattern(p) => bind_pat(p, bound),
    }
}

// ── Tarjan strongly-connected components ────────────────────────────────────

fn tarjan_scc(graph: &[HashSet<usize>]) -> Vec<Vec<usize>> {
    struct State<'a> {
        graph: &'a [HashSet<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn strong(s: &mut State, v: usize) {
        s.index[v] = Some(s.next);
        s.low[v] = s.next;
        s.next += 1;
        s.stack.push(v);
        s.on_stack[v] = true;
        let mut succ: Vec<usize> = s.graph[v].iter().copied().collect();
        succ.sort_unstable();
        for w in succ {
            if s.index[w].is_none() {
                strong(s, w);
                s.low[v] = s.low[v].min(s.low[w]);
            } else if s.on_stack[w] {
                s.low[v] = s.low[v].min(s.index[w].unwrap());
            }
        }
        if s.low[v] == s.index[v].unwrap() {
            let mut comp = Vec::new();
            loop {
                let w = s.stack.pop().unwrap();
                s.on_stack[w] = false;
                comp.push(w);
                if w == v {
                    break;
                }
            }
            comp.sort_unstable();
            s.out.push(comp);
        }
    }
    let n = graph.len();
    let mut s = State {
        graph,
        index: vec![None; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next: 0,
        out: Vec::new(),
    };
    for v in 0..n {
        if s.index[v].is_none() {
            strong(&mut s, v);
        }
    }
    s.out
}
