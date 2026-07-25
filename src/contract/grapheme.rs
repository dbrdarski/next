//! Boundary-state seams — the string half of the tuple-length family (§5).
//!
//! Grapheme-cluster count is **not additive across concatenation**. Extended
//! grapheme clustering (UAX #29) can merge clusters across the seam by **more than
//! one**: `👩` (1) ++ `‍👩‍👧` (2) → `👩‍👩‍👧` (1), a seam delta of −2. That leading-ZWJ
//! family retired the unsound `−1` interval (round 1). The count is therefore
//! **segmenter-owned** — the seam is derived from the pinned `unicode-segmentation`
//! table, never a guessed constant.
//!
//! A string is summarized by its **boundary state**, and concatenation is
//! **composition of summaries**. For literal strings the summary is exact by
//! construction: composition reduces to re-segmentation of the join, so
//!
//! ```text
//! compose(of_literal(a), of_literal(b)).count == count(a ++ b)   for all a, b
//! ```
//!
//! — checked exhaustively over a generated corpus (property testing is a
//! cross-check, never the proof). Two invariants hold for every concatenation, and
//! back the analyzer bound [`concat_len_bound`]. Clustering only ever **merges**
//! (never splits), and merging is **asymmetric**: appending to the right cannot
//! change the left operand's internal boundaries (breaks and RI parity are decided
//! left-to-right), but *prepending* can rewrite the right operand's segmentation —
//! a leading joiner is absorbed (the flagship: `count = 1 < count(b) = 2`). Hence
//!
//! ```text
//! count(a)  ≤  count(a ++ b)  ≤  count(a) + count(b)
//! ```
//!
//! — the floor is the **left** count, never `count(b)` and never their max.
//!
//! The finite boundary-state *compression* that lifts this to abstract string
//! **contracts** — RI-parity normalization, the ZWJ-chain / Hangul states over the
//! segmenter's finite state space — is the recorded exactness upgrade; it needs the
//! segmenter's category tables, and a string-length *contract* form does not yet
//! exist in the algebra, so that lift is owed (see `OwedItems`).
//! `// [ask-author]`: the boundary-state space enumeration is deferred with that lift.

use unicode_segmentation::UnicodeSegmentation;

/// Grapheme-cluster count of a UTF-16 unit string. The pinned `unicode-segmentation`
/// fixes the UAX #29 table version (C§13.4 re-pin invalidation applies).
pub fn count(units: &[u16]) -> usize {
    String::from_utf16_lossy(units).graphemes(true).count()
}

/// The boundary-state summary of a string. `count` is its isolated grapheme count;
/// `units` retains the UTF-16 body because the seam is segmenter-owned — the finite
/// boundary-state compression is the owed upgrade (see the module note). The summary
/// composes associatively and is **exact for every literal concatenation**.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Summary {
    pub count: usize,
    units: Vec<u16>,
}

impl Summary {
    /// Summarize a literal string.
    pub fn of_literal(units: &[u16]) -> Summary {
        Summary { count: count(units), units: units.to_vec() }
    }

    /// Concatenate two summaries. Exact for literals: the seam is recomputed by the
    /// segmenter over the joined boundary, so every cross-seam merge — ZWJ emoji
    /// cascades, regional-indicator re-pairing, a leading combining mark — is
    /// accounted for, with no interval guess.
    pub fn compose(&self, rhs: &Summary) -> Summary {
        let mut joined = self.units.clone();
        joined.extend_from_slice(&rhs.units);
        Summary { count: count(&joined), units: joined }
    }

    /// The seam delta `count(a ++ b) − count(a) − count(b)`. Always `≤ 0` (clustering
    /// only merges), and demonstrably below `−1` — the leading-ZWJ family reaches
    /// `−2` and deeper, which is why the `−1` interval was unsound.
    pub fn seam_delta(&self, rhs: &Summary) -> isize {
        self.compose(rhs).count as isize - self.count as isize - rhs.count as isize
    }
}

/// A sound bound on the grapheme count of `a ++ b` from bounds on the operands,
/// each `(lo, hi)` with `hi = None` meaning unbounded. Concatenation only merges
/// clusters, and only rightward: the result lies in `[a.lo, a.hi + b.hi]`. The floor
/// is the **left** operand's minimum — `count(b)` is *not* a lower bound, since a
/// leading joiner on the right can be absorbed into the left's trailing state. This
/// is the `Approx` fallback for abstract string operands, until string-length
/// contracts and the finite boundary-state lift land; use [`Summary::compose`] for
/// the exact literal seam.
pub fn concat_len_bound(a: (usize, Option<usize>), b: (usize, Option<usize>)) -> (usize, Option<usize>) {
    let lo = a.0;
    let hi = match (a.1, b.1) {
        (Some(x), Some(y)) => Some(x + y),
        _ => None,
    };
    (lo, hi)
}
