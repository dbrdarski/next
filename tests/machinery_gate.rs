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

/// The quarantined recursive body checker stays inside its own file.
///
/// `bodycheck.rs` is non-authoritative (per `IMPLEMENTATION-STATUS.md`) and scheduled for
/// deletion when the native body check lands. Until then the live risk is not that it
/// exists — it is that its internals get *called* from the new fact machinery, which would
/// launder the reaching engine into the replacement. These names are its reaching core.
#[test]
fn the_quarantined_reaching_core_stays_in_its_own_file() {
    const CORE: &[&str] = &["check_recursive_body", "reachable_rows", "grow"];
    const HOME: &str = "src/analyzer/bodycheck.rs";

    for (path, src) in sources() {
        if path == HOME {
            continue;
        }
        for name in CORE {
            assert!(
                !has_ident(&src, name),
                "`{name}` appears in {path}, outside its quarantine ({HOME}). The quarantined \
                 reaching core must not be called from — or copied into — the fact machinery \
                 that replaces it. If a fact cannot be settled without it, the honest answer is \
                 `unproven`."
            );
        }
    }
}

/// The demand/fact machinery does not depend on the quarantined body checker.
///
/// `safety.rs` (BodySafe facts), `induction.rs` (the settlement driver) and the claim
/// consumers are the replacement for `bodycheck`. A code reference from any of them to
/// `bodycheck` means the replacement is resting on the thing it replaces — the exact shape
/// of the 2026-07-31 revert. Doc-comment references are stripped before this check and are
/// fine; they are how the quarantine is documented.
#[test]
fn the_fact_machinery_does_not_call_the_quarantined_checker() {
    const REPLACEMENTS: &[&str] = &[
        "src/analyzer/safety.rs",
        "src/analyzer/induction.rs",
        "src/analyzer/refute.rs",
        "src/analyzer/obligation.rs",
        "src/analyzer/grounding.rs",
    ];
    for (path, src) in sources() {
        if REPLACEMENTS.contains(&path.as_str()) {
            assert!(
                !has_ident(&src, "bodycheck"),
                "{path} references `bodycheck` in code. The fact machinery must not depend on \
                 the quarantined body checker it replaces — that is how a reverted engine gets \
                 laundered back in. (Doc comments are stripped before this check; describing \
                 the quarantine is expected.)"
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
