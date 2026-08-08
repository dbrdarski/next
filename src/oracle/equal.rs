//! Function/value identity support (μ-Canonicalization Specification v0.5 §7).
//!
//! Runtime [`values_equal`] is universally a pointer test. Algorithm B lives in
//! [`canonical_graphs_equal`] only: the function interner uses it to verify a
//! recursive fingerprint-bucket candidate before reusing the candidate pointer.

use std::collections::HashSet;

use crate::env::Binding;
use crate::value::{FnValue, ValueData, ValueRef};

/// Whether two values are equal (the language's `==`).
pub fn values_equal(a: &ValueRef, b: &ValueRef) -> bool {
    a.ptr_eq(b)
}

/// Algorithm B — exact bisimulation over provisional/closed value graphs. This
/// is canonicalization- and conformance-internal; language `==` never calls it.
pub(crate) fn canonical_graphs_equal(a: &ValueRef, b: &ValueRef) -> bool {
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
                    xs.iter()
                        .zip(ys)
                        .all(|(x, y)| x.key == y.key && equal(&x.value, &y.value, visited))
                })
        }
        // Any other kinds: pure-data leaves are interned, so equal ones already
        // took the pointer fast path; reaching here means unequal.
        _ => false,
    }
}

/// Compare two function values: equal shape (canonical code) and bisimilar
/// positional captures (§4B, §3 law 6). Value captures recurse; locations are
/// nominal atoms on the separate Effect/Mutator path.
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
        && (0..f.free_vars().len()).all(|index| capture_equal(f, index, g, index, visited));
    visited.remove(&key);
    result
}

/// Compare one positional capture slot of each function.
fn capture_equal(
    f: &FnValue,
    findex: usize,
    g: &FnValue,
    gindex: usize,
    visited: &mut HashSet<(usize, usize)>,
) -> bool {
    match (f.capture_binding_at(findex), g.capture_binding_at(gindex)) {
        (Some(Binding::Value(fv)), Some(Binding::Value(gv))) => equal(&fv, &gv, visited),
        (Some(Binding::Open(_)), _) | (_, Some(Binding::Open(_))) => false,
        // Locations are nominal (fork 13 split rule): equal iff the same slot.
        (Some(Binding::Slot(fs)), Some(Binding::Slot(gs))) => fs == gs,
        // Open construction values are not candidates for closed equality.
        (Some(Binding::UnderInit), Some(Binding::UnderInit)) | (None, None) => false,
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
                (0..f.free_vars().len()).all(|index| {
                    match (f.capture_binding_at(index), g.capture_binding_at(index)) {
                        (Some(Binding::Value(fv)), Some(Binding::Value(gv))) => {
                            equal_unfold(&fv, &gv, depth - 1)
                        }
                        (Some(Binding::Open(_)), _) | (_, Some(Binding::Open(_))) => false,
                        (Some(Binding::Slot(fs)), Some(Binding::Slot(gs))) => fs == gs,
                        (Some(Binding::UnderInit), Some(Binding::UnderInit)) | (None, None) => {
                            false
                        }
                        _ => false,
                    }
                })
            }
            (ValueData::Tuple(xs), ValueData::Tuple(ys)) => {
                xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys)
                        .all(|(x, y)| equal_unfold(x, y, depth - 1))
            }
            (ValueData::Record(xs), ValueData::Record(ys)) => {
                xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys)
                        .all(|(x, y)| x.key == y.key && equal_unfold(&x.value, &y.value, depth - 1))
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
                canonical_graphs_equal(&a, &b),
                equal_unfold(&a, &b, 30),
                "B disagrees with bounded unfolding for:\n{src}",
            );
        }
    }
}
