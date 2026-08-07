//! Project linking (E12) — **static whole-program resolution, one store**.
//!
//! A project is a set of sources: named modules (`module M` headers) plus exactly one
//! headerless entry file. Modules **define, never do** — their top levels are bindings
//! (MOD-01 polices act calls statically); the entry runs last in effect world. All
//! modules share one interner and one oracle store, so an exported `@state` binding
//! imported elsewhere is the *same location* — reads are live (MOD-03) and a module
//! reference aliases the namespace rather than copying anything (MOD-04).
//!
//! **Resolution is static and name-level.** `import { count } from Counter` installs
//! Counter's exported *binding* (a value, or the slot itself) under `count` before the
//! importer runs. A whole-module import (`import Counter`) makes the namespace name
//! visible; `Counter.count` — and `m.count` after the alias `m = Counter` — rewrites at
//! link time to a hidden binding spelled `"Counter.count"` (a dot keeps it out of the
//! user namespace). A module name in any other value seat is a clear error — the
//! module-in-a-value-seat corner is deliberately open in the design, and unimplemented
//! is the ruled-correct answer.
//!
//! **Scope notes (v1).** Aliases resolve through bare `m = Namespace` bindings; local
//! shadowing is honored by tracking bound names through lambdas, patterns, and match
//! items. Import cycles between named modules are a clear error (E12 resolves value
//! cycles through late-bound lambdas; cross-module construction windows are not built
//! here). Exported names come from `Name` targets only.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::{
    AccessForm, Arg, Bind, BindTarget, BindingRef, Element, Expr, Field, Item, Match, MatchItem,
    Module, Pat, PatElem, PatField, Ref, TemplatePart,
};
use crate::env::{Binding, Env, Scope};
use crate::interner::Interner;
use crate::lex::lex;
use crate::oracle::harness::{HostIo, install_host_effects, prelude_env};
use crate::oracle::{Oracle, Trap};
use crate::parse::parse_program;
use crate::value::ValueRef;

/// A static linking failure — project-wide, before anything runs.
#[derive(Debug)]
pub enum LinkError {
    /// A source failed lexing/parsing/desugaring; the message carries the stage.
    Front { source: usize, message: String },
    /// MOD-05: two files declare the same module name — one error naming both.
    DuplicateModule {
        name: String,
        first: usize,
        second: usize,
    },
    /// The project has no headerless entry file, or more than one.
    Entries(usize),
    /// An import names a module no file declares.
    UnknownModule { importer: String, module: String },
    /// An import names a binding the module does not export.
    NotExported { module: String, name: String },
    /// A module name reached a true value seat (open corner — clear error).
    ModuleInValueSeat { module: String },
    /// Named modules import each other in a cycle.
    ImportCycle,
}

impl std::fmt::Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinkError::Front { source, message } => write!(f, "source {source}: {message}"),
            LinkError::DuplicateModule {
                name,
                first,
                second,
            } => write!(
                f,
                "module `{name}` is declared by two files (source {first} and source {second}); \
                 module names are project-wide"
            ),
            LinkError::Entries(n) => {
                write!(
                    f,
                    "a project needs exactly one headerless entry file, found {n}"
                )
            }
            LinkError::UnknownModule { importer, module } => {
                write!(f, "`{importer}` imports `{module}`, which no file declares")
            }
            LinkError::NotExported { module, name } => {
                write!(f, "`{module}` does not export `{name}`")
            }
            LinkError::ModuleInValueSeat { module } => write!(
                f,
                "module `{module}` used in a value seat — modules are namespaces, not values \
                 (aliasing `m = {module}` and `m.field` access are the supported forms)"
            ),
            LinkError::ImportCycle => write!(f, "named modules import each other in a cycle"),
        }
    }
}

/// A project failure: static linking, or a runtime trap from the entry.
#[derive(Debug)]
pub enum ProjectError {
    Link(LinkError),
    Trap(Trap),
}

/// A linked, resolved, ordered project — the shared front half of running and
/// checking (E12/C§14: resolution is static and whole-program; what differs is
/// only what walks the modules afterwards).
struct Assembled {
    modules: Vec<Module>,
    order: Vec<usize>,
    entry: usize,
}

fn assemble(sources: &[&str], interner: &mut Interner) -> Result<Assembled, ProjectError> {
    let mut modules: Vec<Module> = Vec::new();
    for (i, src) in sources.iter().enumerate() {
        modules.push(front(src, i, interner).map_err(ProjectError::Link)?);
    }

    // Index named modules; find the one entry (MOD-05, entry-count).
    let mut by_name: HashMap<String, usize> = HashMap::new();
    let mut entry: Option<usize> = None;
    let mut entries = 0usize;
    for (i, m) in modules.iter().enumerate() {
        match &m.name {
            Some(name) => {
                if let Some(&first) = by_name.get(name) {
                    return Err(ProjectError::Link(LinkError::DuplicateModule {
                        name: name.clone(),
                        first,
                        second: i,
                    }));
                }
                by_name.insert(name.clone(), i);
            }
            None => {
                entries += 1;
                entry = Some(i);
            }
        }
    }
    if entries != 1 {
        return Err(ProjectError::Link(LinkError::Entries(entries)));
    }
    let entry = entry.expect("counted above");

    // Validate imports and collect the export tables.
    let exports: HashMap<String, Vec<String>> = modules
        .iter()
        .filter_map(|m| m.name.clone().map(|n| (n, exported_names(m))))
        .collect();
    for m in &modules {
        let importer = m.name.clone().unwrap_or_else(|| "the entry file".into());
        for item in &m.items {
            if let Item::Import(imp) = item {
                let Some(names) = exports.get(&imp.module) else {
                    return Err(ProjectError::Link(LinkError::UnknownModule {
                        importer,
                        module: imp.module.clone(),
                    }));
                };
                for n in imp.names.iter().flatten() {
                    if !names.contains(n) {
                        return Err(ProjectError::Link(LinkError::NotExported {
                            module: imp.module.clone(),
                            name: n.clone(),
                        }));
                    }
                }
            }
        }
    }

    // Alias resolution + namespace-access rewriting, per module.
    let modules: Vec<Module> = modules
        .into_iter()
        .map(|m| resolve(m, &exports))
        .collect::<Result<_, _>>()
        .map_err(ProjectError::Link)?;

    // Topological setup order over named-module imports.
    let order = topo_order(&modules, &by_name, entry).map_err(ProjectError::Link)?;

    Ok(Assembled {
        modules,
        order,
        entry,
    })
}

/// Link and run a project. The last source slot may be any position — the entry is
/// found by its missing header. Returns the entry's final value and captured IO.
pub fn run_project(sources: &[&str]) -> Result<(ValueRef, HostIo), ProjectError> {
    let mut interner = Interner::new();
    let Assembled {
        modules,
        order,
        entry,
    } = assemble(sources, &mut interner)?;

    // One prelude, one io, one oracle, one store — then each module in order.
    let io = Rc::new(RefCell::new(HostIo::default()));
    let base = prelude_env(&mut interner);
    install_host_effects(&mut interner, &base, &io);
    let mut oracle = Oracle::new(&mut interner);

    let mut export_bindings: HashMap<String, Vec<(String, Binding)>> = HashMap::new();
    let mut value = None;
    for idx in order {
        let module = &modules[idx];
        let scope = Scope::child(&base);
        for item in &module.items {
            if let Item::Import(imp) = item {
                install_imports(imp, &export_bindings, &scope);
            }
        }
        let v = oracle
            .run_module_in(module, &scope)
            .map_err(ProjectError::Trap)?;
        if idx == entry {
            value = Some(v);
        } else if let Some(name) = &module.name {
            let harvested = exported_names(module)
                .into_iter()
                .filter_map(|n| scope.lookup(&n).map(|b| (n, b)))
                .collect();
            export_bindings.insert(name.clone(), harvested);
        }
    }

    let captured = std::mem::take(&mut *io.borrow_mut());
    Ok((value.expect("the entry ran"), captured))
}

/// One checked module of a project: its declared name (`None` for the entry) and
/// its full program verdict.
pub struct CheckedModule {
    pub name: Option<String>,
    pub verdict: crate::analyzer::program::ProgramVerdict,
}

/// The check-mode analogue of [`run_project`]'s result: every module's verdict, in
/// setup order.
pub struct ProjectVerdict {
    pub modules: Vec<CheckedModule>,
}

impl ProjectVerdict {
    /// The project is accepted when every module's program policy accepted.
    pub fn accepted(&self) -> bool {
        self.modules.iter().all(|m| m.verdict.accepted())
    }
}

/// Link and **check** a project — E12/C§14's static whole-program resolution feeding
/// the program checker instead of the oracle. The same assembly (front ends, module
/// index, import validation, alias/namespace resolution, topological order) runs
/// once; each module is then analyzed with its imports installed: value bindings
/// harvested from the exporter's checked scope, and exported **named contracts**
/// seeded into the importer's contract environment. Nothing is evaluated.
///
/// v1 residue, named: an exported `@state`/`@mutable` slot has no check-mode scope
/// binding to harvest (the checker tracks slots in its expression environment, not
/// the value scope), so a cross-module *state* import currently surfaces as unbound
/// findings in the importer — the MOD-03 shape stays runtime-verified only.
pub fn check_project(sources: &[&str]) -> Result<ProjectVerdict, ProjectError> {
    let mut interner = Interner::new();
    let Assembled { modules, order, .. } = assemble(sources, &mut interner)?;

    // The same inert harness values check mode always starts with (String,
    // println, exit, readFile) — installed once, shared by every module scope.
    let io = Rc::new(RefCell::new(HostIo::default()));
    let base = prelude_env(&mut interner);
    install_host_effects(&mut interner, &base, &io);

    let mut export_bindings: HashMap<String, Vec<(String, Binding)>> = HashMap::new();
    let mut export_cenvs: HashMap<String, crate::contract::ContractEnv> = HashMap::new();
    let mut out = Vec::new();
    for idx in order {
        let module = &modules[idx];
        let scope = Scope::child(&base);
        let mut seed = crate::contract::ContractEnv::new();
        for item in &module.items {
            if let Item::Import(imp) = item {
                install_imports(imp, &export_bindings, &scope);
                // Whole-module contract access (`M.Percent` in a contract seat)
                // is not a named import; it stays unresolved in v1.
                if let Some(exported) = export_cenvs.get(&imp.module)
                    && let Some(names) = &imp.names
                {
                    for n in names {
                        if let Some(c) = exported.get(n) {
                            seed.insert(n.clone(), c.clone());
                        }
                    }
                }
            }
        }
        let (verdict, cenv) =
            crate::analyzer::program::analyze_program_project(module, &scope, &seed, &mut interner);
        if let Some(name) = &module.name {
            let harvested = exported_names(module)
                .into_iter()
                .filter_map(|n| scope.lookup(&n).map(|b| (n, b)))
                .collect();
            export_bindings.insert(name.clone(), harvested);
            let exported: crate::contract::ContractEnv = exported_names(module)
                .into_iter()
                .filter_map(|n| cenv.get(&n).map(|c| (n, c.clone())))
                .collect();
            export_cenvs.insert(name.clone(), exported);
        }
        out.push(CheckedModule {
            name: module.name.clone(),
            verdict,
        });
    }
    Ok(ProjectVerdict { modules: out })
}

fn front(src: &str, source: usize, interner: &mut Interner) -> Result<Module, LinkError> {
    let fail = |message: String| LinkError::Front { source, message };
    let toks = lex(src).map_err(|e| fail(format!("{e:?}")))?;
    let sp = parse_program(toks).map_err(|e| fail(format!("{e:?}")))?;
    crate::desugar::lower_program(&sp, interner).map_err(|e| fail(e.message))
}

fn exported_names(m: &Module) -> Vec<String> {
    m.items
        .iter()
        .filter_map(|item| match item {
            Item::Bind(Bind {
                target: BindTarget::Name(n),
                exported: true,
                ..
            }) => Some(n.clone()),
            Item::SlotDecl(s) if s.exported => Some(s.name.clone()),
            Item::ActBind(a) if a.exported => Some(a.name.clone()),
            _ => None,
        })
        .collect()
}

/// Install one import into the consumer's scope: named imports bind the exported
/// binding itself (a slot stays the same location — live reads); a whole-module
/// import installs every export under its mangled `"Module.name"` spelling for the
/// rewritten accesses.
fn install_imports(
    imp: &crate::ast::Import,
    export_bindings: &HashMap<String, Vec<(String, Binding)>>,
    scope: &Env,
) {
    let Some(bindings) = export_bindings.get(&imp.module) else {
        return; // validated earlier; an unrun module has nothing to install
    };
    match &imp.names {
        Some(names) => {
            for n in names {
                if let Some((_, b)) = bindings.iter().find(|(name, _)| name == n) {
                    scope.define(n, b.clone());
                }
            }
        }
        None => {
            for (n, b) in bindings {
                scope.define(&format!("{}.{n}", imp.module), b.clone());
            }
        }
    }
}

fn topo_order(
    modules: &[Module],
    by_name: &HashMap<String, usize>,
    entry: usize,
) -> Result<Vec<usize>, LinkError> {
    let deps = |i: usize| -> Vec<usize> {
        modules[i]
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Import(imp) => by_name.get(&imp.module).copied(),
                _ => None,
            })
            .collect()
    };
    let mut order = Vec::new();
    let mut state: HashMap<usize, u8> = HashMap::new(); // 1 = visiting, 2 = done
    fn visit(
        i: usize,
        deps: &dyn Fn(usize) -> Vec<usize>,
        state: &mut HashMap<usize, u8>,
        order: &mut Vec<usize>,
    ) -> Result<(), LinkError> {
        match state.get(&i) {
            Some(2) => return Ok(()),
            Some(1) => return Err(LinkError::ImportCycle),
            _ => {}
        }
        state.insert(i, 1);
        for d in deps(i) {
            visit(d, deps, state, order)?;
        }
        state.insert(i, 2);
        order.push(i);
        Ok(())
    }
    for i in 0..modules.len() {
        if i != entry {
            visit(i, &deps, &mut state, &mut order)?;
        }
    }
    visit(entry, &deps, &mut state, &mut order)?;
    Ok(order)
}

// ── Alias resolution and namespace-access rewriting ──────────────────────────

fn resolve(m: Module, exports: &HashMap<String, Vec<String>>) -> Result<Module, LinkError> {
    // Visible namespaces: whole-module imports, then bare aliases (`m = Counter`),
    // which resolve in source order and may chain.
    let mut namespaces: HashMap<String, String> = HashMap::new();
    for item in &m.items {
        if let Item::Import(imp) = item
            && imp.names.is_none()
        {
            namespaces.insert(imp.module.clone(), imp.module.clone());
        }
    }
    let mut items = Vec::new();
    for item in m.items {
        match item {
            Item::Bind(Bind {
                target: BindTarget::Name(alias),
                value: Expr::Ref(Ref::Immutable(BindingRef::Name(n))),
                exported,
            }) if namespaces.contains_key(&n) => {
                let target = namespaces[&n].clone();
                // An exported alias would re-export a namespace — out of v1 scope.
                if exported {
                    return Err(LinkError::ModuleInValueSeat { module: target });
                }
                namespaces.insert(alias, target);
            }
            Item::Bind(b) => items.push(Item::Bind(Bind {
                target: b.target,
                value: rewrite(b.value, &namespaces, exports, &HashSet::new())?,
                exported: b.exported,
            })),
            Item::SlotDecl(mut s) => {
                s.init = rewrite(s.init, &namespaces, exports, &HashSet::new())?;
                items.push(Item::SlotDecl(s));
            }
            Item::ActBind(mut a) => {
                a.lambda.body = Box::new(rewrite(
                    *a.lambda.body,
                    &namespaces,
                    exports,
                    &bound_names(&a.lambda.params),
                )?);
                items.push(Item::ActBind(a));
            }
            Item::Stmt(e) => items.push(Item::Stmt(rewrite(
                e,
                &namespaces,
                exports,
                &HashSet::new(),
            )?)),
            other @ (Item::Import(_) | Item::Where(_)) => items.push(other),
        }
    }
    Ok(Module {
        name: m.name,
        items,
    })
}

/// Rewrite `NS.field` (and `alias.field`) to the mangled `"NS.field"` reference;
/// reject a namespace name in any other seat. `shadowed` tracks locally bound names.
fn rewrite(
    e: Expr,
    ns: &HashMap<String, String>,
    exports: &HashMap<String, Vec<String>>,
    shadowed: &HashSet<String>,
) -> Result<Expr, LinkError> {
    let walk = |e: Expr, shadowed: &HashSet<String>| rewrite(e, ns, exports, shadowed);
    Ok(match e {
        Expr::Access {
            target,
            form: AccessForm::Field(field),
            total,
        } => {
            if let Expr::Ref(Ref::Immutable(BindingRef::Name(n))) = &*target
                && !shadowed.contains(n)
                && let Some(module) = ns.get(n)
            {
                if !exports[module].contains(&field) {
                    return Err(LinkError::NotExported {
                        module: module.clone(),
                        name: field,
                    });
                }
                return Ok(Expr::Ref(Ref::Immutable(BindingRef::Name(format!(
                    "{module}.{field}"
                )))));
            }
            Expr::Access {
                target: Box::new(walk(*target, shadowed)?),
                form: AccessForm::Field(field),
                total,
            }
        }
        Expr::Ref(Ref::Immutable(BindingRef::Name(n))) => {
            if !shadowed.contains(&n)
                && let Some(module) = ns.get(&n)
            {
                return Err(LinkError::ModuleInValueSeat {
                    module: module.clone(),
                });
            }
            Expr::Ref(Ref::Immutable(BindingRef::Name(n)))
        }
        Expr::Const(_) | Expr::Ref(_) => e,
        Expr::Lambda(mut l) => {
            let mut inner = shadowed.clone();
            inner.extend(bound_names(&l.params));
            l.body = Box::new(walk(*l.body, &inner)?);
            Expr::Lambda(l)
        }
        Expr::Apply { callee, args } => Expr::Apply {
            callee: Box::new(walk(*callee, shadowed)?),
            args: args
                .into_iter()
                .map(|a| {
                    Ok(match a {
                        Arg::Expr(x) => Arg::Expr(walk(x, shadowed)?),
                        Arg::Spread(x) => Arg::Spread(walk(x, shadowed)?),
                    })
                })
                .collect::<Result<_, LinkError>>()?,
        },
        Expr::PrimOp { op, args } => Expr::PrimOp {
            op,
            args: args
                .into_iter()
                .map(|x| walk(x, shadowed))
                .collect::<Result<_, _>>()?,
        },
        Expr::Match(m) => {
            let scrutinee = match m.scrutinee {
                Some(s) => Some(Box::new(walk(*s, shadowed)?)),
                None => None,
            };
            let mut scope = shadowed.clone();
            let mut items = Vec::new();
            for item in m.items {
                match item {
                    MatchItem::Bind(b) => {
                        let value = walk(b.value, &scope)?;
                        match &b.target {
                            BindTarget::Name(n) => {
                                scope.insert(n.clone());
                            }
                            BindTarget::Pattern(p) => scope.extend(pattern_names(p)),
                        }
                        items.push(MatchItem::Bind(Bind {
                            target: b.target,
                            value,
                            exported: b.exported,
                        }));
                    }
                    MatchItem::Stmt(x) => items.push(MatchItem::Stmt(walk(x, &scope)?)),
                    MatchItem::Arm(arm) => {
                        let mut arm_scope = scope.clone();
                        if let Some(p) = &arm.pattern {
                            arm_scope.extend(pattern_names(p));
                        }
                        items.push(MatchItem::Arm(crate::ast::Arm {
                            guard: arm.guard.map(|g| walk(g, &arm_scope)).transpose()?,
                            result: walk(arm.result, &arm_scope)?,
                            pattern: arm.pattern,
                        }));
                    }
                }
            }
            Expr::Match(Match { scrutinee, items })
        }
        Expr::TupleCons(els) => Expr::TupleCons(
            els.into_iter()
                .map(|el| {
                    Ok(match el {
                        Element::Expr(x) => Element::Expr(walk(x, shadowed)?),
                        Element::Spread(x) => Element::Spread(walk(x, shadowed)?),
                    })
                })
                .collect::<Result<_, LinkError>>()?,
        ),
        Expr::RecordCons(fs) => Expr::RecordCons(
            fs.into_iter()
                .map(|f| {
                    Ok(match f {
                        Field::Field { key, value } => Field::Field {
                            key,
                            value: walk(value, shadowed)?,
                        },
                        Field::Spread(x) => Field::Spread(walk(x, shadowed)?),
                        Field::Computed { key, value } => Field::Computed {
                            key: walk(key, shadowed)?,
                            value: walk(value, shadowed)?,
                        },
                    })
                })
                .collect::<Result<_, LinkError>>()?,
        ),
        Expr::Access {
            target,
            form,
            total,
        } => Expr::Access {
            target: Box::new(walk(*target, shadowed)?),
            form: match form {
                AccessForm::Field(f) => AccessForm::Field(f),
                AccessForm::Index(x) => AccessForm::Index(Box::new(walk(*x, shadowed)?)),
                AccessForm::Slice { lo, hi } => AccessForm::Slice {
                    lo: lo.map(|x| walk(*x, shadowed).map(Box::new)).transpose()?,
                    hi: hi.map(|x| walk(*x, shadowed).map(Box::new)).transpose()?,
                },
            },
            total,
        },
        Expr::Template(parts) => Expr::Template(
            parts
                .into_iter()
                .map(|p| {
                    Ok(match p {
                        TemplatePart::Interp(x) => TemplatePart::Interp(walk(x, shadowed)?),
                        lit => lit,
                    })
                })
                .collect::<Result<_, LinkError>>()?,
        ),
        Expr::Write { slot, value } => Expr::Write {
            slot,
            value: Box::new(walk(*value, shadowed)?),
        },
    })
}

fn bound_names(p: &Pat) -> HashSet<String> {
    pattern_names(p).into_iter().collect()
}

fn pattern_names(p: &Pat) -> Vec<String> {
    let mut out = Vec::new();
    collect_pattern_names(p, &mut out);
    out
}

fn collect_pattern_names(p: &Pat, out: &mut Vec<String>) {
    match p {
        Pat::Bind(n) => out.push(n.clone()),
        Pat::Const(_) | Pat::Wild => {}
        Pat::Tuple(elems) => {
            for e in elems {
                match e {
                    PatElem::Pat(p) => collect_pattern_names(p, out),
                    PatElem::Rest(Some(n)) => out.push(n.clone()),
                    PatElem::Rest(None) => {}
                }
            }
        }
        Pat::Record { fields, .. } => {
            for f in fields {
                match f {
                    PatField::Field { pat, .. } => collect_pattern_names(pat, out),
                    PatField::Rest(Some(n)) => out.push(n.clone()),
                    PatField::Rest(None) => {}
                }
            }
        }
        Pat::Contract(_) => {}
    }
}
