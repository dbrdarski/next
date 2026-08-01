//! The proven-fact cache — C§13.4.
//!
//! > **Proven-return-fact cache** ((analysis instance, row-set I, demanded C) → verdict;
//! > unproven entries per-compilation). Every key interned pointers; every entry a fact or
//! > an appropriately-scoped shrug.
//!
//! **Why this had to come before the T1.4 wiring.** Moving `analyze_apply` onto the settled
//! facts means a settlement analyzes bodies whose calls reach `analyze_apply` again. Guarding
//! that with a *global* "am I settling?" flag is unsound: it answers every nested query from
//! the hypotheses, including for callees that are not members of the graph and hold no
//! hypothesis, which silently drops their traps. Measured on 2026-08-01: ten lib failures,
//! one of them `Proven` where the suite demands a refutation — a false accept.
//!
//! The key is therefore the **fact node**, not a flag. A re-entrant query on *the same*
//! node is a recursive reference and resolves through its hypothesis (correct vector
//! induction, C§13.2a); a query on a *different* node is genuinely settled.
//!
//! **The instance half of the key is the canonical shape** — `FnValue::shape()`, produced by
//! `oracle::canon` — paired with the de-Bruijn-ordered capture contracts. Without it the key
//! would be a closure allocation, and closures are plain allocations rather than hash-consed
//! values, so two spellings of one function would miss each other.
//!
//! The shape is **interned** (`Interner::intern_code`) and the key compares it by pointer,
//! per "every key interned pointers". Structural hashing happens once per distinct shape at
//! closure construction, never per lookup. The capture and input contracts are still compared
//! structurally — contracts are not interned anywhere in this implementation, which is a
//! separate and larger gap against the same rule, recorded here rather than fixed.
//!
//! **KNOWN GAP — this is the layer-1 shape, and C§13.4 specifies the layer-2 shape.**
//! `oracle::canon` implements algorithm A (α-renaming, capture slots, polynomial NF).
//! The μ-binder minimization — SCC grouping, positional μ-refs, canonical slot order — lives
//! in `oracle::mu`, whose own header says it "is the layer-2 shape used by C§13.4 cache keys
//! … it has no runtime consumer yet". This cache is not that consumer, because the join does
//! not exist: `mu::canonicalize_group` takes `(name, Expr)` binding lists while `make_closure`
//! builds from one `Lambda` + env and stores the raw body, so no closure knows it belongs to
//! a group (the obstacle already recorded in blocker 2b's pin). Law 4 (bisimulation slot
//! merging) is absent outright.
//!
//! Consequence: mutually recursive members do not share keys the way C§13.4 intends. The
//! failure direction is **false negatives** — a missed hit, never a wrong verdict — so this
//! is a precision and completeness gap, not a soundness one. It must be closed before the
//! cache can be claimed conformant.
//!
//! **Scope: per-compilation.** The cache lives for one analysis run and is not persisted, so
//! the namespace/versioning regime C§13.4 requires for durable entries does not apply yet.
//! Unproven entries are per-compilation *by construction* rather than by policy.
//!
//! **Only top-level settlements are cached.** A settlement running inside another one sees
//! ambient hypotheses, so its verdict is hypothesis-relative and must not be recorded as a
//! fact. `begin`/`finish` are no-ops in that case, which costs hits and never soundness.

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::analyzer::induction::Claim;
use crate::analyzer::safety::BodySafety;
use crate::ast::Lambda;
use crate::contract::Contract;
use crate::value::ValueRef;

/// A fact node: (analysis instance, row-set `I`, demanded `C`).
///
/// The instance is `(canonical shape, capture contracts)`; the claim carries the demanded
/// contract for a return fact and is the discriminator for safety/completion facts.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct FactKey {
    shape: CodePtr,
    captures: Vec<Contract>,
    input: Vec<Contract>,
    claim: Claim,
}

/// Interned canonical code, compared and hashed **by pointer**.
///
/// `Rc<Lambda>`'s derived `PartialEq`/`Hash` walk the whole syntax tree; since
/// `Interner::intern_code` guarantees identical shapes share one allocation, the pointer
/// already decides it. This is the "same value = same pointer" rule applied to code, and it
/// turns a per-lookup tree walk into one word of comparison.
#[derive(Clone, Debug)]
struct CodePtr(Rc<Lambda>);

impl PartialEq for CodePtr {
    fn eq(&self, other: &CodePtr) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for CodePtr {}
impl Hash for CodePtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

/// What the cache knows about a node.
pub(crate) enum Cached {
    /// Currently being settled — a query for it is a **recursive reference**, which never
    /// unfolds (C§13.2) and must resolve through the node's hypothesis instead.
    InProgress,
    /// Settled this compilation.
    Settled(BodySafety),
}

thread_local! {
    static CACHE: RefCell<HashMap<FactKey, Option<BodySafety>>> = RefCell::new(HashMap::new());
    /// Depth of active settlements — non-zero means ambient hypotheses are in scope, so
    /// nothing settled right now is a fact.
    static DEPTH: RefCell<usize> = const { RefCell::new(0) };
}

/// The node for a call, or `None` when the callee is not a resolvable function instance
/// (nothing to key on — the caller settles uncached).
pub(crate) fn key(callee: &ValueRef, args: &[Contract], claim: &Claim) -> Option<FactKey> {
    let f = callee.as_fn()?;
    let closure = callee.as_closure()?;
    // De-Bruijn order: `free_vars` is the ordered capture-slot list `shape`'s `@cap`i
    // refer to, so iterating it gives a positional tuple independent of name spelling.
    let captures = f
        .free_vars()
        .iter()
        .map(|n| match closure.env.lookup(n) {
            Some(crate::env::Binding::Value(v)) => Contract::Equals(v),
            _ => Contract::Top,
        })
        .collect();
    Some(FactKey { shape: CodePtr(f.shape_rc()), captures, input: args.to_vec(), claim: claim.clone() })
}

/// What is known about `key`, if anything.
pub(crate) fn lookup(key: &FactKey) -> Option<Cached> {
    CACHE.with(|c| {
        c.borrow().get(key).map(|e| match e {
            None => Cached::InProgress,
            Some(v) => Cached::Settled(v.clone()),
        })
    })
}

/// Mark a node as being settled, and enter a settlement. Always paired with [`finish`].
pub(crate) fn begin(key: &FactKey) {
    CACHE.with(|c| c.borrow_mut().insert(key.clone(), None));
    DEPTH.with(|d| *d.borrow_mut() += 1);
}

/// Record a settled verdict and leave the settlement.
///
/// At depth > 1 the verdict was reached with ambient hypotheses in scope, so it is
/// **removed** rather than recorded — a hypothesis-relative answer is not a fact.
pub(crate) fn finish(key: &FactKey, verdict: &BodySafety) {
    let outer = DEPTH.with(|d| {
        let mut d = d.borrow_mut();
        *d -= 1;
        *d == 0
    });
    CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if outer {
            c.insert(key.clone(), Some(verdict.clone()));
        } else {
            c.remove(key);
        }
    });
}

/// Drop everything. The cache is per-compilation; tests that build several programs in one
/// process are several compilations.
///
/// Unused today: `analyze_program` is a single compilation per process and the entries are
/// keyed by canonical shape + captures, so cross-program collisions do not arise. Kept
/// because a driver that checks several modules in one process needs it, and finding out
/// then is worse than having it now.
#[allow(dead_code)]
pub(crate) fn clear() {
    CACHE.with(|c| c.borrow_mut().clear());
    DEPTH.with(|d| *d.borrow_mut() = 0);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner::Interner;
    use crate::oracle::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    /// The property the key rests on: identical canonical code is **one allocation**, so
    /// shape identity is a pointer comparison. Without this the key would silently fall back
    /// to walking a syntax tree on every lookup, which is what it did before 2026-08-01.
    #[test]
    fn identical_functions_share_one_interned_code_pointer() {
        let mut i = Interner::new();
        let a = f("g = (n) => n + 1\ng", &mut i);
        let b = f("h = (n) => n + 1\nh", &mut i);
        assert!(
            Rc::ptr_eq(&a.as_fn().unwrap().shape_rc(), &b.as_fn().unwrap().shape_rc()),
            "same code must be one interned allocation"
        );
    }

    /// And the reason canonicalization comes first: bound names are not part of a function's
    /// identity, so α-variants must reach the *same* pointer. A key built on parsed code
    /// (the interim your notes describe) would miss this pair.
    #[test]
    fn alpha_variants_share_one_interned_code_pointer() {
        let mut i = Interner::new();
        let a = f("g = (n) => n + 1\ng", &mut i);
        let b = f("h = (x) => x + 1\nh", &mut i);
        assert!(
            Rc::ptr_eq(&a.as_fn().unwrap().shape_rc(), &b.as_fn().unwrap().shape_rc()),
            "alpha-variants are the same shape"
        );
    }

    /// The complement — pointer equality must not over-collapse.
    #[test]
    fn different_functions_do_not_share_a_code_pointer() {
        let mut i = Interner::new();
        let a = f("g = (n) => n + 1\ng", &mut i);
        let b = f("h = (n) => n + 2\nh", &mut i);
        assert!(
            !Rc::ptr_eq(&a.as_fn().unwrap().shape_rc(), &b.as_fn().unwrap().shape_rc()),
            "different code is different shapes"
        );
    }

    /// Two closures over the same code but different captures are the same *shape* and
    /// different *instances* — which is exactly why the key carries capture contracts
    /// alongside the code pointer.
    #[test]
    fn same_shape_different_captures_are_distinct_fact_nodes() {
        let mut i = Interner::new();
        let a = f("k = 1\ng = (n) => n + k\ng", &mut i);
        let b = f("k = 2\nh = (n) => n + k\nh", &mut i);
        assert!(
            Rc::ptr_eq(&a.as_fn().unwrap().shape_rc(), &b.as_fn().unwrap().shape_rc()),
            "same code, so one shape"
        );
        let args = [Contract::Top];
        let (ka, kb) = (
            key(&a, &args, &Claim::Safety).expect("keyed"),
            key(&b, &args, &Claim::Safety).expect("keyed"),
        );
        assert_ne!(ka, kb, "different captures are different fact nodes");
    }
}
