//! Runtime environments (semantics companion §1: `ρ` — name → binding).
//!
//! A [`Scope`] is a frame in a lexical chain; bindings are added as they are
//! established. Because a closure captures the `Rc<Scope>` it was built in and
//! bindings are inserted into the shared frame, **late binding** (B4) and mutual
//! recursion work for free: a lambda body can reference a name bound after the
//! lambda was constructed, because the lookup happens when the reference is
//! evaluated, against the same (now-populated) frame.
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

/// What a name is bound to (semantics §1): an immutable value, a Box location, or
/// an *under-initialization* marker (evaluating a reference to which traps).
#[derive(Clone, Debug)]
pub enum Binding {
    Value(ValueRef),
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
        Rc::new(Scope { parent: None, vars: RefCell::new(HashMap::new()) })
    }

    /// A fresh child environment extending `parent`.
    pub fn child(parent: &Env) -> Env {
        Rc::new(Scope { parent: Some(parent.clone()), vars: RefCell::new(HashMap::new()) })
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
}
