//! The instance-chain cutoff — §4a of the Application & Induction package (v0.8.1).
//!
//! The **admitted-instance inventory** is the projection onto instances of a finite
//! state closure over `InventoryState = (analysis instance, active code sequence)`.
//! It is **constructed, traversal-free** — a closure that depends on the program
//! alone, never an effort-dependent fixpoint — so its *membership* is
//! order-independent (the returned `Vec` is discovery-ordered, a set representation,
//! never a canonical sequence):
//!
//! 1. Seed with the instances the program's nonrecursive/root demands reach, each
//!    with its canonical code appended to an empty sequence.
//! 2. From each state, symbolically enumerate its call transitions (`transitions`).
//!    Every instance the fixed metadata-intersection / narrowing rules can produce
//!    belongs here — meet-derived instances are admitted through this ordinary path.
//! 3. Target code **not** in the active sequence → **admit** the target; continue
//!    from `(target, sequence ++ target.code)`.
//! 4. Target code **already** in the sequence → **no admission through that path**
//!    (the cutoff); the induction ladder (§6) applies at analysis time instead.
//!
//! Finite: no admitted path repeats canonical code, so path depth ≤ the program's code
//! count, and the reachable instance universe is advance-bounded (the fixed rule
//! inventory). This construction *is* the definition of "an instance some non-cutoff
//! path admits".
//!
//! This module is the **closure algorithm**, parameterized by `transitions` — the
//! symbolic call-target enumeration. Deriving `transitions` from a real closure body
//! (μ-structure-aware callee resolution) and consuming the inventory for the return
//! induction (§6) and `analyze_apply` are the wiring that follows.

use crate::analyzer::domain::Instance;

/// Construct the admitted-instance inventory (§4a). `roots` are the instances the
/// program's root demands reach; `transitions` symbolically enumerates an instance's
/// call targets. Returns the deduplicated admitted instances.
///
/// **The result is a set** — its *membership* depends on `roots`/`transitions` alone,
/// not on the traversal order (the suite checks this across reversed root and
/// transition orders). The returned `Vec` is discovery-ordered and is **not** a
/// canonical sequence; a consumer that needs stable candidate identity must sort it
/// by its own key, never rely on this order.
pub fn build_inventory(
    roots: Vec<Instance>,
    transitions: impl Fn(&Instance) -> Vec<Instance>,
) -> Vec<Instance> {
    build_inventory_by(roots, Instance::code_handle, transitions)
}

/// The §4a closure over an arbitrary node type `N` keyed by its **canonical code** — the
/// cutoff fires when a transition's target code already appears on the active path.
/// Used both for abstract [`Instance`]s and, in the induction tail, for closure
/// values (the μ-aware body-walk call graph).
pub fn build_inventory_by<N: Clone + PartialEq, K: Clone + PartialEq>(
    roots: Vec<N>,
    shape_of: impl Fn(&N) -> K,
    transitions: impl Fn(&N) -> Vec<N>,
) -> Vec<N> {
    let mut inventory: Vec<N> = Vec::new();
    let mut visited: Vec<(N, Vec<K>)> = Vec::new();
    let mut work: Vec<(N, Vec<K>)> = Vec::new();

    for r in roots {
        let seq = vec![shape_of(&r)];
        push_node(&mut inventory, &mut visited, &mut work, r, seq);
    }

    while let Some((node, active)) = work.pop() {
        for target in transitions(&node) {
            let ts = shape_of(&target);
            if active.contains(&ts) {
                continue; // cutoff — the shape repeats on this path
            }
            let mut seq = active.clone();
            seq.push(ts);
            push_node(&mut inventory, &mut visited, &mut work, target, seq);
        }
    }

    inventory
}

/// Admit `node` (deduplicated) and enqueue its state, unless the exact `(node, active
/// code sequence)` was already processed — the visited guard bounds the closure
/// against the advance-bounded, code-cutoff state space.
fn push_node<N: Clone + PartialEq, K: Clone + PartialEq>(
    inventory: &mut Vec<N>,
    visited: &mut Vec<(N, Vec<K>)>,
    work: &mut Vec<(N, Vec<K>)>,
    node: N,
    active_shapes: Vec<K>,
) {
    let key = (node.clone(), active_shapes.clone());
    if visited.contains(&key) {
        return;
    }
    visited.push(key);
    if !inventory.contains(&node) {
        inventory.push(node.clone());
    }
    work.push((node, active_shapes));
}
