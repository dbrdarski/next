//! Algorithm A — eager code canonicalization of binding groups
//! (μ-Canonicalization Spec v0.1, §2/§3/§4A).
//!
//! This canonicalizes a set of (possibly mutually recursive) bindings into
//! **canonical code**: mutual references become positional **μ-refs**, the
//! recursion structure is grouped by strongly-connected components, and each
//! group is serialized in a canonical slot order — so the result is invariant
//! under renaming and member permutation. This is the layer-2 shape used by
//! C§13.4 cache keys and recursive contracts (C§9); it has no runtime consumer
//! yet (layer-1 `==` is algorithm B).
//!
//! Scope of this implementation (the testable core):
//! - **Law 3 / minimal group + law 1 / no vacuous binder:** only genuine SCCs
//!   (a self-loop or a ≥2 cycle) become μ-groups; acyclic members split out.
//! - **Positional μ-refs** `⟨d,i⟩` for intra-group references, de-Bruijn for
//!   λ/match-bound variables, cross-SCC references by canonical key, free names
//!   by name.
//! - **Law 5 / canonical slot order:** the slot permutation whose serialization
//!   is lexicographically least (brute-forced — groups are tiny).
//!
//! Deferred refinements (flagged): law 2 (adjacent/nested-binder merge — needs
//! nested groups) and law 4 (bisimulation collapse of truly-symmetric slots via
//! partition refinement; law 5 already gives permutation-invariance, just not
//! slot *merging*).
//!
//! No runtime consumer yet — the analyzer's cache keys (C§13.4) will use this;
//! until then it is exercised only by the MU conformance tests.
#![allow(dead_code)]

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ast::*;
use crate::value::{ValueData, ValueRef};

/// Content-based serialization of a constant value — stable across interners (so
/// canonical codes from different programs compare equal). Desugared `Const`s are
/// scalar literals; compound cases are handled recursively for completeness.
fn const_repr(v: &ValueRef) -> String {
    match v.data() {
        ValueData::Number(n) => format!("N{n}"),
        ValueData::Boolean(b) => format!("B{b}"),
        ValueData::Null => "Z".to_string(),
        ValueData::Str(u) => format!("S{:?}", String::from_utf16_lossy(u)),
        ValueData::Indeterminate(f) => format!("I{}", f.label()),
        ValueData::Tuple(items) => {
            format!("T[{}]", items.iter().map(const_repr).collect::<Vec<_>>().join(","))
        }
        ValueData::Record(fields) => format!(
            "D[{}]",
            fields
                .iter()
                .map(|e| format!("{}:{}", String::from_utf16_lossy(&e.key), const_repr(&e.value)))
                .collect::<Vec<_>>()
                .join(",")
        ),
        ValueData::Function(_) | ValueData::Native(_) => "Fn".to_string(),
    }
}

#[cfg(test)]
mod tests;

/// Canonicalize a binding group; returns each binding name → its canonical code
/// key. Intra-group cycles are μ-bound; everything else is plain canonical code.
pub(super) fn canonicalize_group(bindings: &[(String, Expr)]) -> BTreeMap<String, String> {
    let names: Vec<String> = bindings.iter().map(|(n, _)| n.clone()).collect();
    let name_set: HashSet<String> = names.iter().cloned().collect();
    let index: HashMap<String, usize> = names.iter().cloned().zip(0..).collect();
    let bodies: Vec<&Expr> = bindings.iter().map(|(_, e)| e).collect();

    // Reference graph: i → j iff body_i freely references group member j.
    let refs: Vec<HashSet<usize>> = bodies
        .iter()
        .map(|b| {
            free_group_refs(b, &name_set)
                .into_iter()
                .map(|n| index[&n])
                .collect()
        })
        .collect();

    // SCCs in reverse-topological order (a component's out-neighbours come first).
    let sccs = tarjan_scc(&refs);

    let mut keys: HashMap<usize, String> = HashMap::new();
    for scc in &sccs {
        canonicalize_scc(scc, &names, &bodies, &refs, &mut keys);
    }

    names
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), keys[&i].clone()))
        .collect()
}

/// Canonicalize one SCC, filling `keys` for its members.
fn canonicalize_scc(
    scc: &[usize],
    names: &[String],
    bodies: &[&Expr],
    refs: &[HashSet<usize>],
    keys: &mut HashMap<usize, String>,
) {
    let is_cycle = scc.len() > 1 || (scc.len() == 1 && refs[scc[0]].contains(&scc[0]));

    if !is_cycle {
        // Law 1/3: a lone acyclic binding is plain canonical code — no μ.
        let i = scc[0];
        let key = serialize_member(bodies[i], &HashMap::new(), names, keys);
        keys.insert(i, key);
        return;
    }

    // A μ-group. Choose the slot permutation (law 5) whose concatenated
    // serialization is lexicographically least.
    let members: Vec<usize> = scc.to_vec();
    let best = permutations(&members)
        .into_iter()
        .map(|perm| {
            // slot_of[member] = its slot index under this permutation.
            let slot_of: HashMap<usize, usize> =
                perm.iter().enumerate().map(|(slot, &m)| (m, slot)).collect();
            let group = perm
                .iter()
                .map(|&m| serialize_member(bodies[m], &slot_of, names, keys))
                .collect::<Vec<_>>()
                .join("|");
            (format!("mu[{}]({group})", perm.len()), slot_of)
        })
        .min_by(|(a, _), (b, _)| a.cmp(b))
        .expect("a permutation exists");

    let (group_code, slot_of) = best;
    for &m in &members {
        keys.insert(m, format!("{group_code}@{}", slot_of[&m]));
    }
}

/// Serialize one member body to canonical code. `slots` maps the *current* SCC's
/// members to μ-slots; other group members resolve to their (already-computed)
/// keys; λ/match-bound variables become de-Bruijn; free names stay named.
fn serialize_member(
    body: &Expr,
    slots: &HashMap<usize, usize>,
    names: &[String],
    keys: &HashMap<usize, String>,
) -> String {
    let name_index: HashMap<&str, usize> = names.iter().enumerate().map(|(i, n)| (n.as_str(), i)).collect();
    let mut s = Ser { slots, keys, name_index, scopes: Vec::new(), counter: 0 };
    let mut out = String::new();
    s.expr(body, &mut out);
    out
}

struct Ser<'a> {
    slots: &'a HashMap<usize, usize>,
    keys: &'a HashMap<usize, String>,
    name_index: HashMap<&'a str, usize>,
    scopes: Vec<HashMap<String, u32>>,
    counter: u32,
}

impl Ser<'_> {
    fn bind(&mut self, name: &str) {
        let n = self.counter;
        self.counter += 1;
        self.scopes.last_mut().expect("scope open").insert(name.to_string(), n);
    }
    fn bound(&self, name: &str) -> Option<u32> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    fn reference(&self, name: &str, out: &mut String) {
        if let Some(db) = self.bound(name) {
            out.push_str(&format!("b{db};"));
            return;
        }
        if let Some(&i) = self.name_index.get(name) {
            if let Some(&slot) = self.slots.get(&i) {
                out.push_str(&format!("μ⟨0,{slot}⟩;")); // intra-group μ-ref
                return;
            }
            if let Some(key) = self.keys.get(&i) {
                out.push_str(&format!("k[{key}];")); // cross-SCC canonical key
                return;
            }
        }
        out.push_str(&format!("f{name};")); // free (outside the group)
    }

    fn expr(&mut self, e: &Expr, out: &mut String) {
        match e {
            Expr::Const(v) => out.push_str(&format!("c{}", const_repr(v))),
            Expr::Ref(Ref::Immutable(BindingRef::Name(n))) => self.reference(n, out),
            Expr::Ref(r) => out.push_str(&format!("R{r:?}")),
            Expr::Lambda(l) => {
                out.push('L');
                self.scopes.push(HashMap::new());
                self.pat(&l.params, out);
                out.push(';');
                self.expr(&l.body, out);
                out.push_str(&format!("{:?}", l.act_kind));
                self.scopes.pop();
            }
            Expr::Apply { callee, args } => {
                out.push_str("A(");
                self.expr(callee, out);
                for a in args {
                    match a {
                        Arg::Expr(e) => self.expr(e, out),
                        Arg::Spread(e) => {
                            out.push('*');
                            self.expr(e, out);
                        }
                    }
                    out.push(',');
                }
                out.push(')');
            }
            Expr::PrimOp { op, args } => {
                out.push_str(&format!("P{op:?}("));
                for a in args {
                    self.expr(a, out);
                    out.push(',');
                }
                out.push(')');
            }
            Expr::Match(m) => {
                out.push_str("M(");
                if let Some(s) = &m.scrutinee {
                    self.expr(s, out);
                }
                out.push(';');
                self.scopes.push(HashMap::new());
                for item in &m.items {
                    self.match_item(item, out);
                    out.push(';');
                }
                self.scopes.pop();
                out.push(')');
            }
            Expr::TupleCons(elems) => {
                out.push_str("T(");
                for el in elems {
                    match el {
                        Element::Expr(e) => self.expr(e, out),
                        Element::Spread(e) => {
                            out.push('*');
                            self.expr(e, out);
                        }
                    }
                    out.push(',');
                }
                out.push(')');
            }
            Expr::RecordCons(fields) => {
                out.push_str("D(");
                for f in fields {
                    match f {
                        Field::Field { key, value } => {
                            out.push_str(&format!("{key}:"));
                            self.expr(value, out);
                        }
                        Field::Computed { key, value } => {
                            out.push('[');
                            self.expr(key, out);
                            out.push_str("]:");
                            self.expr(value, out);
                        }
                        Field::Spread(e) => {
                            out.push_str("...");
                            self.expr(e, out);
                        }
                    }
                    out.push(',');
                }
                out.push(')');
            }
            Expr::Access { target, form, total } => {
                out.push_str(&format!("X{total}("));
                self.expr(target, out);
                match form {
                    AccessForm::Field(n) => out.push_str(&format!(".{n}")),
                    AccessForm::Index(e) => {
                        out.push('[');
                        self.expr(e, out);
                        out.push(']');
                    }
                    AccessForm::Slice { lo, hi } => {
                        out.push('[');
                        if let Some(e) = lo {
                            self.expr(e, out);
                        }
                        out.push_str("..");
                        if let Some(e) = hi {
                            self.expr(e, out);
                        }
                        out.push(']');
                    }
                }
                out.push(')');
            }
            Expr::Template(parts) => {
                out.push_str("S(");
                for p in parts {
                    match p {
                        TemplatePart::Segment(s) => out.push_str(&format!("s{s:?}")),
                        TemplatePart::Interp(e) => self.expr(e, out),
                    }
                    out.push(',');
                }
                out.push(')');
            }
            Expr::Write { slot, value } => {
                out.push_str("W(");
                match slot {
                    SlotRef::Name(n) => self.reference(n, out),
                    SlotRef::Location(l) => out.push_str(&format!("l{};", l.0)),
                }
                self.expr(value, out);
                out.push(')');
            }
        }
    }

    fn match_item(&mut self, item: &MatchItem, out: &mut String) {
        match item {
            MatchItem::Bind(b) => {
                out.push('=');
                self.expr(&b.value, out);
                self.bind_target(&b.target, out);
            }
            MatchItem::Stmt(e) => {
                out.push('.');
                self.expr(e, out);
            }
            MatchItem::Arm(arm) => {
                out.push_str("=>");
                self.scopes.push(HashMap::new());
                if let Some(p) = &arm.pattern {
                    self.pat(p, out);
                }
                if let Some(g) = &arm.guard {
                    out.push('?');
                    self.expr(g, out);
                }
                self.expr(&arm.result, out);
                self.scopes.pop();
            }
        }
    }

    fn bind_target(&mut self, t: &BindTarget, out: &mut String) {
        match t {
            BindTarget::Name(n) => {
                self.bind(n);
                out.push_str(&format!("+b{};", self.bound(n).unwrap()));
            }
            BindTarget::Pattern(p) => self.pat(p, out),
        }
    }

    fn pat(&mut self, p: &Pat, out: &mut String) {
        match p {
            Pat::Const(v) => out.push_str(&format!("pc{}", const_repr(v))),
            Pat::Wild => out.push('_'),
            Pat::Bind(n) => {
                self.bind(n);
                out.push_str(&format!("pb{};", self.bound(n).unwrap()));
            }
            Pat::Tuple(elems) => {
                out.push_str("pt(");
                for e in elems {
                    match e {
                        PatElem::Pat(p) => self.pat(p, out),
                        PatElem::Rest(Some(n)) => {
                            self.bind(n);
                            out.push_str(&format!("...b{};", self.bound(n).unwrap()));
                        }
                        PatElem::Rest(None) => out.push_str("..._"),
                    }
                    out.push(',');
                }
                out.push(')');
            }
            Pat::Record { fields, exact } => {
                out.push_str(&format!("pr{exact}("));
                for f in fields {
                    match f {
                        PatField::Field { key, pat } => {
                            out.push_str(&format!("{key}:"));
                            self.pat(pat, out);
                        }
                        PatField::Rest(Some(n)) => {
                            self.bind(n);
                            out.push_str(&format!("...b{};", self.bound(n).unwrap()));
                        }
                        PatField::Rest(None) => out.push_str("..._"),
                    }
                    out.push(',');
                }
                out.push(')');
            }
            Pat::Contract(r) => match r {
                Ref::Immutable(BindingRef::Name(n)) => out.push_str(&format!("pk{n};")),
                other => out.push_str(&format!("pk{other:?}")),
            },
        }
    }
}

// ── Free group references (respecting binders) ───────────────────────────────

fn free_group_refs(e: &Expr, group: &HashSet<String>) -> HashSet<String> {
    let mut found = HashSet::new();
    let mut bound: Vec<String> = Vec::new();
    collect_refs(e, group, &mut bound, &mut found);
    found
}

fn collect_refs(e: &Expr, group: &HashSet<String>, bound: &mut Vec<String>, found: &mut HashSet<String>) {
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

// ── Tarjan strongly-connected components (reverse-topological order) ──────────

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

fn permutations(items: &[usize]) -> Vec<Vec<usize>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let head = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, head);
            out.push(p);
        }
    }
    out
}
