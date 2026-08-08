//! Runtime environments (semantics companion §1: `ρ` — name → binding).
//!
//! A [`Scope`] is a frame in a lexical chain; bindings are added as they are
//! established. During a construction window, only unresolved capture operands
//! retain this shared frame, so late-bound siblings can arrive. Window close
//! rewrites them to positional value/group captures. A closed closure retains no
//! `Env`, and invocation runs canonical code over those explicit captures.
//!
//! This is the oracle's evaluation environment. It carries surface *names*
//! (de-Bruijn/§5 canonicalization is deferred — see DECISIONS.md).

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::value::ValueRef;

/// A runtime store slot (Box location). Locations are never values (B1).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SlotId(pub u32);

/// What a name is bound to (semantics §1): an immutable value, a Box location,
/// an open construction graph, or an *under-initialization* marker. Observing
/// either construction state traps; only group construction may retain it.
#[derive(Clone, Debug)]
pub enum Binding {
    Value(ValueRef),
    /// A value graph still inside its construction window. It may be captured
    /// by another member of that window, but observing it is an unbound-value
    /// trap until the whole graph closes and the interner returns canonical
    /// handles for every exposed root.
    Open(ValueRef),
    Slot(SlotId),
    UnderInit,
}

/// A lexical scope frame. Cheap to clone as `Env` (an `Rc`).
#[derive(Debug)]
pub struct Scope {
    parent: Option<Env>,
    vars: RefCell<HashMap<String, Binding>>,
}

/// A shared, chainable environment handle.
pub type Env = Rc<Scope>;

impl Scope {
    /// A fresh root environment.
    pub fn root() -> Env {
        Rc::new(Scope {
            parent: None,
            vars: RefCell::new(HashMap::new()),
        })
    }

    /// A fresh child environment extending `parent`.
    pub fn child(parent: &Env) -> Env {
        Rc::new(Scope {
            parent: Some(parent.clone()),
            vars: RefCell::new(HashMap::new()),
        })
    }

    /// Bind (or rebind — shadowing) a name in *this* frame.
    pub fn define(&self, name: &str, binding: Binding) {
        self.vars.borrow_mut().insert(name.to_string(), binding);
    }

    /// Resolve a name up the chain, returning a clone of its binding.
    pub fn lookup(&self, name: &str) -> Option<Binding> {
        if let Some(b) = self.vars.borrow().get(name) {
            return Some(b.clone());
        }
        self.parent.as_ref().and_then(|p| p.lookup(name))
    }

    /// Snapshot the bindings visible from this scope, with child bindings
    /// shadowing parents. The analyzer uses this at a program boundary so the
    /// compile-time environment starts with the same prelude/import values as
    /// evaluation, without evaluating any of them.
    pub(crate) fn visible_bindings(&self) -> HashMap<String, Binding> {
        let mut visible = self
            .parent
            .as_ref()
            .map(|parent| parent.visible_bindings())
            .unwrap_or_default();
        visible.extend(
            self.vars
                .borrow()
                .iter()
                .map(|(name, binding)| (name.clone(), binding.clone())),
        );
        visible
    }
}
