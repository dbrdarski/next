//! The instance-chain cutoff — §4a of the Application & Induction package (v0.8.1).
//!
//! The **admitted-instance inventory** is the projection onto instances of a finite
//! state closure over `InventoryState = (analysis instance, active shape sequence)`.
//! It is **constructed, traversal-free** — a closure that depends on the program
//! alone, never an effort-dependent fixpoint — so its result is order-independent:
//!
//! 1. Seed with the instances the program's nonrecursive/root demands reach, each
//!    with its shape appended to an empty sequence.
//! 2. From each state, symbolically enumerate its call transitions (`transitions`).
//!    Every instance the fixed metadata-intersection / narrowing rules can produce
//!    belongs here — meet-derived instances are admitted through this ordinary path.
//! 3. Target shape **not** in the active sequence → **admit** the target; continue
//!    from `(target, sequence ++ target.shape)`.
//! 4. Target shape **already** in the sequence → **no admission through that path**
//!    (the cutoff); the induction ladder (§6) applies at analysis time instead.
//!
//! Finite: no admitted path repeats a shape, so path depth ≤ the program's shape
//! count, and the reachable instance universe is advance-bounded (the fixed rule
//! inventory). This construction *is* the definition of "an instance some non-cutoff
//! path admits".
//!
//! This module is the **closure algorithm**, parameterized by `transitions` — the
//! symbolic call-target enumeration. Deriving `transitions` from a real closure body
//! (μ-structure-aware callee resolution) and consuming the inventory for the return
//! induction (§6) and `analyze_apply` are the wiring that follows.

use crate::analyzer::domain::Instance;
use crate::ast::Lambda;

/// A node in the inventory closure: an admitted instance and the **active shape
/// sequence** on the path that admitted it. The cutoff fires when a transition's
/// target shape already appears in this sequence.
struct InventoryState {
    instance: Instance,
    active_shapes: Vec<Lambda>,
}

/// Whether a call from `state` to `target` is a **shape repeat** — the cutoff
/// condition (§4a step 4). A target whose shape is already active on the path is not
/// admitted through it; the induction handles the cycle.
fn is_cutoff(active_shapes: &[Lambda], target: &Instance) -> bool {
    active_shapes.contains(&target.shape)
}

/// Construct the admitted-instance inventory (§4a). `roots` are the instances the
/// program's root demands reach; `transitions` symbolically enumerates an instance's
/// call targets. Returns the deduplicated admitted instances — the projection of the
/// state closure. Order-independent: the result depends on `roots`/`transitions`, not
/// on the traversal order (verified across seed orders in the suite).
pub fn build_inventory(roots: Vec<Instance>, transitions: impl Fn(&Instance) -> Vec<Instance>) -> Vec<Instance> {
    let mut inventory: Vec<Instance> = Vec::new();
    let mut visited: Vec<(Instance, Vec<Lambda>)> = Vec::new();
    let mut work: Vec<InventoryState> = Vec::new();

    for r in roots {
        let seq = vec![r.shape.clone()];
        push_state(&mut inventory, &mut visited, &mut work, r, seq);
    }

    while let Some(state) = work.pop() {
        for target in transitions(&state.instance) {
            if is_cutoff(&state.active_shapes, &target) {
                continue; // cutoff — the shape repeats on this path
            }
            let mut seq = state.active_shapes.clone();
            seq.push(target.shape.clone());
            push_state(&mut inventory, &mut visited, &mut work, target, seq);
        }
    }

    inventory
}

/// Admit `instance` (deduplicated) and enqueue its state, unless the exact
/// `(instance, active shape sequence)` was already processed — the visited guard
/// bounds the closure against the advance-bounded, shape-cutoff state space.
fn push_state(
    inventory: &mut Vec<Instance>,
    visited: &mut Vec<(Instance, Vec<Lambda>)>,
    work: &mut Vec<InventoryState>,
    instance: Instance,
    active_shapes: Vec<Lambda>,
) {
    let key = (instance.clone(), active_shapes.clone());
    if visited.contains(&key) {
        return;
    }
    visited.push(key);
    if !inventory.contains(&instance) {
        inventory.push(instance.clone());
    }
    work.push(InventoryState { instance, active_shapes });
}
