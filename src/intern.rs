//! Generic **enum interning** — hash-consing for tagged data, so `==` is a pointer test.
//!
//! The value interner ([`crate::interner::Interner`]) hash-conses NEXT *values*. This module
//! does the same for the tagged/variant data the implementation is built from — canonical
//! function code, contracts, and, when NEXT's enums land as a language feature, their values
//! too. Author ruling 2026-08-01: **NEXT enums map to Rust enums directly**, so one mechanism
//! serves both, and nothing here is contract-specific.
//!
//! The rule it enforces is the project's first one: *same value = same pointer; `==` is
//! pointer comparison, universally*. An [`Interned<T>`] compares and hashes by address, so a
//! cache key holding one is a word, not a walk over a syntax tree. Structural hashing happens
//! **once, at interning**; every comparison afterwards is a pointer test.
//!
//! **Children first.** As with values, interning is exact only when a term's children are
//! already canonical — `Interned<T>` inside `T` rather than `Box<T>`. A type that boxes its
//! children still dedups correctly (the derived `Hash`/`Eq` walk them), it just pays a walk
//! per intern instead of per comparison. Both are correct; only the cost differs.

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

/// A handle to an interned `T`: **pointer identity**.
///
/// Deliberately not `Rc<T>`, whose derived `PartialEq`/`Hash` walk the whole term. The
/// interner guarantees one allocation per distinct value, so the address already decides it.
pub struct Interned<T>(Rc<T>);

impl<T> Interned<T> {
    /// The address, as the identity it is.
    pub fn as_ptr(&self) -> *const T {
        Rc::as_ptr(&self.0)
    }

    /// Whether two handles are the same interned term. Identical to `==`; named for sites
    /// that want the pointer nature to be visible at the call.
    pub fn ptr_eq(&self, other: &Interned<T>) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<T> Clone for Interned<T> {
    fn clone(&self) -> Self {
        Interned(Rc::clone(&self.0))
    }
}

impl<T> Deref for Interned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> PartialEq for Interned<T> {
    fn eq(&self, other: &Interned<T>) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl<T> Eq for Interned<T> {}

impl<T> Hash for Interned<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

impl<T: fmt::Debug> fmt::Debug for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The term, not the address — an address in a test failure tells you nothing.
        self.0.fmt(f)
    }
}

/// Hash-consing tables, one per interned type.
///
/// Type-indexed rather than a field per type, so a new interned enum costs nothing here —
/// which is the point, given NEXT's enums are coming and each will want the same treatment.
#[derive(Default)]
pub struct EnumInterner {
    tables: HashMap<TypeId, Box<dyn Any>>,
}

impl EnumInterner {
    pub fn new() -> EnumInterner {
        EnumInterner::default()
    }

    /// The canonical handle for `value`, creating it if absent.
    ///
    /// Two structurally equal `T`s always yield the same handle, so `==` on handles coincides
    /// with structural equality — the same guarantee the value interner gives, by the same
    /// means.
    pub fn intern<T: Any + Hash + Eq + Clone>(&mut self, value: T) -> Interned<T> {
        let table = self
            .tables
            .entry(TypeId::of::<T>())
            .or_insert_with(|| Box::new(HashMap::<T, Interned<T>>::new()))
            .downcast_mut::<HashMap<T, Interned<T>>>()
            .expect("one table per TypeId, installed with a matching map");
        if let Some(existing) = table.get(&value) {
            return existing.clone();
        }
        let handle = Interned(Rc::new(value.clone()));
        table.insert(value, handle.clone());
        handle
    }

    /// How many distinct terms of `T` are interned — for tests and diagnostics.
    pub fn count<T: Any + Hash + Eq + Clone>(&self) -> usize {
        self.tables
            .get(&TypeId::of::<T>())
            .and_then(|t| t.downcast_ref::<HashMap<T, Interned<T>>>())
            .map_or(0, HashMap::len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, PartialEq, Eq, Hash, Debug)]
    enum Toy {
        Leaf(i64),
        Pair(Interned<Toy>, Interned<Toy>),
    }

    #[test]
    fn equal_terms_share_one_allocation() {
        let mut i = EnumInterner::new();
        let a = i.intern(Toy::Leaf(1));
        let b = i.intern(Toy::Leaf(1));
        assert!(
            a.ptr_eq(&b),
            "structural equality must coincide with pointer equality"
        );
        assert_eq!(i.count::<Toy>(), 1, "and only one allocation exists");
    }

    #[test]
    fn different_terms_do_not_collapse() {
        let mut i = EnumInterner::new();
        let a = i.intern(Toy::Leaf(1));
        let b = i.intern(Toy::Leaf(2));
        assert!(!a.ptr_eq(&b));
        assert_eq!(i.count::<Toy>(), 2);
    }

    /// The children-first property: with canonical children, a compound term interns by
    /// comparing its children's *pointers*, so deep structures cost no deep walk.
    #[test]
    fn compound_terms_intern_through_canonical_children() {
        let mut i = EnumInterner::new();
        let one = i.intern(Toy::Leaf(1));
        let two = i.intern(Toy::Leaf(2));
        let p = i.intern(Toy::Pair(one.clone(), two.clone()));
        let (one2, two2) = (i.intern(Toy::Leaf(1)), i.intern(Toy::Leaf(2)));
        let q = i.intern(Toy::Pair(one2, two2));
        assert!(p.ptr_eq(&q), "same children ⇒ same compound");
        assert_eq!(
            i.count::<Toy>(),
            3,
            "Leaf(1), Leaf(2), Pair — nothing duplicated"
        );
    }

    /// Distinct types keep distinct tables.
    #[test]
    fn tables_are_per_type() {
        #[derive(Clone, PartialEq, Eq, Hash, Debug)]
        struct Other(i64);
        let mut i = EnumInterner::new();
        i.intern(Toy::Leaf(7));
        i.intern(Other(7));
        assert_eq!(i.count::<Toy>(), 1);
        assert_eq!(i.count::<Other>(), 1);
    }

    /// Deref reaches the term, so an interned handle reads like the enum it wraps.
    #[test]
    fn a_handle_derefs_to_its_term() {
        let mut i = EnumInterner::new();
        let a = i.intern(Toy::Leaf(42));
        assert!(matches!(*a, Toy::Leaf(42)));
    }
}
