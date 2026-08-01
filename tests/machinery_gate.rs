//! Mechanical enforcement of the forbidden-machinery boundaries.
//!
//! The boundaries are recorded in `IMPLEMENTATION-STATUS.md` and restated in the module
//! docs of `analyzer::safety` and `analyzer::grounding`: **no reaching-domain fixpoint, no
//! widening, no candidate synthesis, no grounding-as-analysis-cutoff.** Until now they
//! existed only as prose, and prose did not hold — a forward-reaching/widening engine was
//! built on 2026-07-31, passed all four blockers, and was reverted whole.
//!
//! This file is the part of that boundary a machine can check. It is deliberately narrow:
//! it catches the *literal* return of the reverted engine and the spread of the quarantined
//! one. It cannot catch a renamed reimplementation — that remains a review obligation, and
//! the standing rule is that when a pinned blocker goes green, the **mechanism** is stated,
//! not just the outcome.
//!
//! **If a check here fires, the fix is never to relax the check.** Imprecision produces
//! `unproven` — the third voice — never another prerequisite and never a growth loop.

use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Every `.rs` file under `src/`, as (repo-relative path, source with `//` comments
/// stripped). Comments are stripped so that *prose about* the boundary — which the module
/// docs are required to carry — does not trip a check on the machinery itself.
fn sources() -> Vec<(String, String)> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        for e in std::fs::read_dir(dir).expect("readable src dir").flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|x| x == "rs") {
                out.push(p);
            }
        }
    }
    let mut files = Vec::new();
    walk(&root().join("src"), &mut files);
    files.sort();
    files
        .into_iter()
        .map(|p| {
            let rel = p.strip_prefix(root()).unwrap().to_string_lossy().replace('\\', "/");
            let src = std::fs::read_to_string(&p).expect("readable source");
            let stripped: String =
                src.lines().map(|l| l.split("//").next().unwrap_or("")).collect::<Vec<_>>().join("\n");
            (rel, stripped)
        })
        .collect()
}

/// Whether `hay` contains `needle` as a whole identifier (Rust identifier characters on
/// neither side) — so `grow` does not match `growing_domain_recursion_has_a_finite_row_closure`.
fn has_ident(hay: &str, needle: &str) -> bool {
    let bytes = hay.as_bytes();
    let ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    hay.match_indices(needle).any(|(i, _)| {
        let before_ok = i == 0 || !ident(bytes[i - 1]);
        let j = i + needle.len();
        let after_ok = j >= bytes.len() || !ident(bytes[j]);
        before_ok && after_ok
    })
}

/// The reverted forward-reaching/widening engine must not come back as a file.
///
/// `src/analyzer/summary.rs` was the SCC reaching-domain engine: it passed all four
/// blockers and was reverted whole on 2026-07-31 as imported machinery. Its return under
/// its own name is the single most likely repeat.
#[test]
fn the_reverted_reaching_engine_does_not_exist() {
    for banned in ["src/analyzer/summary.rs", "src/analyzer/reaching.rs", "src/analyzer/widening.rs"] {
        assert!(
            !root().join(banned).exists(),
            "{banned} exists. This is the reverted forward-reaching/widening engine (or a \
             successor under a sibling name). It is forbidden machinery, not a missing feature: \
             a domain that cannot be proven small enough yields `unproven`, never a growth loop."
        );
    }
}

/// The retired recursive body checker and its reaching core stay deleted.
///
/// Ordinary application now consumes the domain-indexed fact graph. Keeping the old file,
/// its module reference, or one of its three reaching primitives would leave two competing
/// implementations and make a later accidental rewire possible.
#[test]
fn the_quarantined_reaching_core_is_deleted() {
    const RETIRED: &[&str] = &["bodycheck", "check_recursive_body", "reachable_rows", "grow"];
    const HOME: &str = "src/analyzer/bodycheck.rs";

    assert!(
        !root().join(HOME).exists(),
        "{HOME} returned. Ordinary application must have one body-safety implementation: \
         the settled candidate graph."
    );
    for (path, src) in sources() {
        for name in RETIRED {
            assert!(
                !has_ident(&src, name),
                "retired identifier `{name}` appears in {path}. The reaching checker must not \
                 be called, copied, or re-exported; an unsettled fact remains `unproven`."
            );
        }
    }
}

/// `analyze_apply` takes a call's completion from the settled fact, never by asserting it.
///
/// The 2026-07-31 routing made `Completion::Produces` reachable at a call site *only* from
/// a proven completion fact; a coarse body pass may no longer assert it. This pins the
/// shape of `callee_completion` against a silent regression to "assume it produces", which
/// is a false **accept** — the dangerous direction.
#[test]
fn a_call_sites_completion_is_not_asserted_by_the_body_pass() {
    let src = std::fs::read_to_string(root().join("src/analyzer/mod.rs")).expect("readable");
    let body = src
        .split_once("fn callee_completion")
        .expect("callee_completion exists")
        .1
        .split_once("\nfn ")
        .map_or_else(|| src.clone(), |(b, _)| b.to_string());
    let code: String =
        body.lines().map(|l| l.split("//").next().unwrap_or("")).collect::<Vec<_>>().join("\n");
    assert!(
        has_ident(&code, "completes"),
        "callee_completion no longer consults the settled completion fact. `Produces` at a \
         call site must come from a proven fact — asserting it from a body pass is a false \
         accept at every expecting seat."
    );
}

/// Application has one alternative driver. The expression-facing function may analyze
/// operands and supply fact-backed contributions, but it must not independently enumerate
/// and join callee alternatives beside `application.rs`'s joint driver.
#[test]
fn application_uses_the_canonical_joint_driver() {
    let src = std::fs::read_to_string(root().join("src/analyzer/mod.rs")).expect("readable");
    let body = src
        .split_once("fn analyze_apply")
        .expect("analyze_apply exists")
        .1
        .split_once("\nfn ")
        .map_or_else(|| src.clone(), |(b, _)| b.to_string());
    let code: String = body
        .lines()
        .map(|l| l.split("//").next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        has_ident(&code, "drive_application"),
        "analyze_apply bypasses the canonical application driver. Keep expression analysis as \
         the adapter and let application.rs own alternative traversal and outcome joining."
    );
    assert!(
        !has_ident(&code, "callee_alternatives") && !has_ident(&code, "join_completions"),
        "analyze_apply still carries its old parallel alternative/join implementation"
    );
}
