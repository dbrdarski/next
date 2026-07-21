//! Value equality — Algorithm B (μ-Canonicalization Spec **v0.5**, where it is
//! rescoped as *canonicalization-internal*; see the architecture note below).
//!
//! `==` on values is a **bisimulation over value graphs** with a visited-pair
//! set: node labels are canonical-code (shape) and atom labels; children are
//! compared positionally; a **revisited pair is assumed equal** (the coinductive
//! step that terminates `y == z` and makes `a == y` true).
//!
//! Data `==` stays a pure pointer test (interned values): only comparisons that
//! transitively involve a function ever walk. Locations are **nominal** atoms
//! (binding identity) — same-body closures over distinct slots stay distinct.
//!
//! **Architecture note (known interim deviation, logged in DECISIONS):** μ v0.5 §6
//! rules *universal interning* — closures intern shallowly (key = canonical-code
//! pointer + capture pointers) and runtime `==` is a pointer test, with Algorithm B
//! running only inside the canonicalizer. This module instead runs Algorithm B at
//! compare time over plainly-allocated closures. The two agree on every `==`
//! *result* (bisimulation equality coincides with canonical-form pointer equality);
//! they differ only in harness-level pointer observability for functions. The
//! re-architecture lands with the §5 canonicalizer wiring (suite register
//! PENDING-§5).

use std::collections::HashSet;

use crate::env::Binding;
use crate::value::{FnValue, ValueData, ValueRef};

/// Whether two values are equal (the language's `==`).
pub fn values_equal(a: &ValueRef, b: &ValueRef) -> bool {
    let mut visited: HashSet<(usize, usize)> = HashSet::new();
    equal(a, b, &mut visited)
}

fn ptr_key(v: &ValueRef) -> usize {
    v.data() as *const ValueData as usize
}

fn equal(a: &ValueRef, b: &ValueRef, visited: &mut HashSet<(usize, usize)>) -> bool {
    // Fast path: interned data (and the same allocation) compare by pointer.
    if a.ptr_eq(b) {
        return true;
    }
    match (a.data(), b.data()) {
        (ValueData::Function(f), ValueData::Function(g)) => equal_fns(f, g, visited),
        (ValueData::Tuple(xs), ValueData::Tuple(ys)) => {
            xs.len() == ys.len()
                && with_pair(visited, a, b, |visited| {
                    xs.iter().zip(ys).all(|(x, y)| equal(x, y, visited))
                })
        }
        (ValueData::Record(xs), ValueData::Record(ys)) => {
            xs.len() == ys.len()
                && with_pair(visited, a, b, |visited| {
                    xs.iter().zip(ys).all(|(x, y)| x.key == y.key && equal(&x.value, &y.value, visited))
                })
        }
        // Any other kinds: pure-data leaves are interned, so equal ones already
        // took the pointer fast path; reaching here means unequal.
        _ => false,
    }
}

/// Compare two function values: equal shape (canonical code) and bisimilar
/// captures (§4B, §3 law 6). Captures resolve their names against each closure's
/// environment — value captures recurse; location captures are nominal atoms.
fn equal_fns(f: &FnValue, g: &FnValue, visited: &mut HashSet<(usize, usize)>) -> bool {
    let key = (
        f.closure() as *const _ as usize,
        g.closure() as *const _ as usize,
    );
    if !visited.insert(key) {
        return true; // coinductive: a revisited pair is assumed equal
    }
    let result = f.shape() == g.shape()
        && f.free_vars().len() == g.free_vars().len()
        && f.free_vars()
            .iter()
            .zip(g.free_vars())
            .all(|(fname, gname)| capture_equal(f, fname, g, gname, visited));
    visited.remove(&key);
    result
}

/// Compare one capture slot of `f` against one of `g`, resolving each name in its
/// closure's environment.
fn capture_equal(
    f: &FnValue,
    fname: &str,
    g: &FnValue,
    gname: &str,
    visited: &mut HashSet<(usize, usize)>,
) -> bool {
    match (f.closure().env.lookup(fname), g.closure().env.lookup(gname)) {
        (Some(Binding::Value(fv)), Some(Binding::Value(gv))) => equal(&fv, &gv, visited),
        // Locations are nominal (fork 13 split rule): equal iff the same slot.
        (Some(Binding::Slot(fs)), Some(Binding::Slot(gs))) => fs == gs,
        // Open-value edge (§4C): a still-unresolved capture compares as its
        // binding atom — nominal by name while open.
        (Some(Binding::UnderInit), Some(Binding::UnderInit)) | (None, None) => fname == gname,
        _ => false,
    }
}

/// Run `body` with the pair `(a, b)` recorded as visited, then unrecord it.
fn with_pair(
    visited: &mut HashSet<(usize, usize)>,
    a: &ValueRef,
    b: &ValueRef,
    body: impl FnOnce(&mut HashSet<(usize, usize)>) -> bool,
) -> bool {
    let key = (ptr_key(a), ptr_key(b));
    if !visited.insert(key) {
        return true;
    }
    let result = body(visited);
    visited.remove(&key);
    result
}

#[cfg(test)]
mod tests {
    //! MU-07: algorithm B agrees with a bounded naive unfolding on small graphs
    //! (the spec's own cross-check for B). The unfolding uses no visited set — it
    //! just recurses to a fixed horizon deeper than any test graph; two rational
    //! trees agree at every depth iff they are bisimilar.

    use super::*;
    use crate::env::Binding;

    /// Naive depth-bounded structural equality (no coinductive memo).
    fn equal_unfold(a: &ValueRef, b: &ValueRef, depth: u32) -> bool {
        if a.ptr_eq(b) {
            return true;
        }
        if depth == 0 {
            return true; // horizon: assume equal beyond the bound
        }
        match (a.data(), b.data()) {
            (ValueData::Function(f), ValueData::Function(g)) => {
                if f.shape() != g.shape() || f.free_vars().len() != g.free_vars().len() {
                    return false;
                }
                f.free_vars().iter().zip(g.free_vars()).all(|(fname, gname)| {
                    match (f.closure().env.lookup(fname), g.closure().env.lookup(gname)) {
                        (Some(Binding::Value(fv)), Some(Binding::Value(gv))) => {
                            equal_unfold(&fv, &gv, depth - 1)
                        }
                        (Some(Binding::Slot(fs)), Some(Binding::Slot(gs))) => fs == gs,
                        (Some(Binding::UnderInit), Some(Binding::UnderInit)) | (None, None) => {
                            fname == gname
                        }
                        _ => false,
                    }
                })
            }
            (ValueData::Tuple(xs), ValueData::Tuple(ys)) => {
                xs.len() == ys.len()
                    && xs.iter().zip(ys).all(|(x, y)| equal_unfold(x, y, depth - 1))
            }
            (ValueData::Record(xs), ValueData::Record(ys)) => {
                xs.len() == ys.len()
                    && xs.iter().zip(ys).all(|(x, y)| x.key == y.key && equal_unfold(&x.value, &y.value, depth - 1))
            }
            _ => false,
        }
    }

    /// A program producing `[a, b]`; returns the two elements.
    fn pair(src: &str) -> (ValueRef, ValueRef) {
        let v = crate::oracle::run_program_value(src).expect("no trap");
        let t = v.as_tuple().expect("a tuple [a, b]");
        (t[0].clone(), t[1].clone())
    }

    #[test]
    fn mu07_bisimulation_agrees_with_bounded_unfolding() {
        let cases = [
            "y = [() => y]\nz = [() => z]\n[y, z]",
            "a = [() => b]\nb = [() => a]\ny = [() => y]\n[a, y]",
            "a = [() => b]\nb = [() => a]\n[a, b]",
            "isEven = (n) => n == 0 ? true : isOdd(n - 1)\nisOdd = (n) => n == 0 ? false : isEven(n - 1)\n[isEven, isOdd]",
            "f = (n) => n == 0 ? 0 : f(n - 1)\ng = (n) => n == 0 ? 0 : g(n - 1)\n[f, g]",
            "[(x) => x, (y) => y + 1]",
            "[[() => 1], [() => 2]]",
        ];
        for src in cases {
            let (a, b) = pair(src);
            assert_eq!(
                values_equal(&a, &b),
                equal_unfold(&a, &b, 30),
                "B disagrees with bounded unfolding for:\n{src}",
            );
        }
    }
}
