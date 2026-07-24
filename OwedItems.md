# OwedItems.md — current open gaps (fresh registry)

The author's original four-item registry is **closed and archived** in
`OwedItems-CLOSED.md` (2026-07-18). This is the fresh registry it invited: normative
gaps and registered implementation drift found *since*, that a design/review chat
should see. Everything here is **sound today** — nothing accepts what a spec leaves
trap-worthy; these are precision, interface, or not-yet-built gaps.

> Rewritten 2026-07-24 after the canonical-library sync (manifest verified green).

---

## Registered implementation drift (spec settled, code carries an older shape)

1. **C§16 obligation-3 interface [1.0.7]** — every transfer rule should be
   `analyzeOperation(op, jointOperands: Correlated<AnalysisContract>, seat) →
   OperationOutcome { safety, produced: AnalysisContract, completion }`. My
   `OpResult { safety, output: Contract }` is the pre-upgrade degenerate shape; the
   reshape lands with the **application/induction package** (v0.8.1, not yet
   implemented — it supplies `AnalysisContract` and `CompletionEvidence`).

2. **Universal interning (μ v0.5 §6; companion §1/§3)** — closures should intern
   shallowly (canonical-code pointer + capture pointers), runtime `==` a pointer
   test, Algorithm B canonicalization-internal. I run Algorithm B **at compare
   time** over plain allocations. Equal on every `==` *result* (all FE rows green,
   including FE-07 act-kind); differs only in harness pointer observability. The
   companion scopes the mechanism (group windows, joint μ-canonicalization,
   late-twin fold-in) to **§5** → this is the §5 canonicalizer-wiring increment.
   Consequence: **MU-18** (open-member observation trap) needs the group window and
   ships `#[ignore]` PENDING-§5.

3. **`Record(fields, Exact | Open)`** — openness is ruled as a Record-contract
   parameter (`HasField(k) ≡ Record({k: Top}, Open)`; exact where users write, open
   only as analyzer-derived demand). I model exact `Record` + a separate `HasField`;
   membership coincides, but open-record *patterns* narrow to `∩ HasField` and lose
   per-field contracts. Sound, precision-lossy.

4. **Tuple family §3–§5 not yet built** — `Concat` §1 + `len` §2 (stamps,
   weighted-SCC solver) are in. Still owed by me: §3 refutation discipline +
   `restrictLen`/`LengthRestricted`; **§4 segment alignment** (which closes the
   `Concat ⊑ Concat` / kind-vs-Concat C.2 rows, currently `Unproven`); §5 grapheme
   seam summaries. All specified in v0.3.1; ordinary build-order work.

## Still owed in the docs (Compendium C§17, patch 1.0.8)

- **Per-pair contract tables** — `Geo`, `Difference`/emptiness, finite-interval
  coverage (no-flattening rule). My `subcontract`/`disjoint` land these `Unproven`.
- **`analyzeOperation` tables for the remaining operations** (the *application* rule
  is specified — induction package). Mine are oracle-derived + brute-tested, not an
  authored transcription.
- **Union/Intersection completeness or documented incompleteness**; region-table /
  boolean-DNF procedures; §13 optimization table + error/warning templates; the
  provenance audit; **C§16 discharge per rule**.

## Open design threads (no spec change; block nothing) — see the handovers

- **Thread B** — the jagged function-equality boundary under the freeze slice
  (`x+3` == `x+2+1`, `x+x` == `2*x`, but `x*2` ≠ `x*3−x`). Author position not yet
  stated. `HANDOVER-open-threads-2026-07-23.md` Part 3.
- **Thread C** — the equality-freeze exclusions (reviewer-originated, unratified)
  and the future **canonical-DAG Number** direction: no generic `Indeterminate(_/0)`
  (`1/0 ≠ 2/0`), derive-contracts-then-canonicalize. `HANDOVER-indeterminate-
  canonical-number-dag-2026-07-24.md`. **Tests that would move if ruled:** the
  `(1/0) == (2/0)` assertion (`src/oracle/tests.rs`), PR-04's shared render, and the
  MU-10 exclusion enforcement in `poly.rs`. The C§11 scope erratum (exclusions bind
  the `==`-set only, not the analyzer NF) is cheap and independent — my `poly.rs` is
  already scoped to the `==`/canonical slice, so no action pending.

## Author-flagged opens (implemented per their stated law)

- **Mutator returns** — return-nothing implemented; the returns-leaning is an
  extension point.
- **Module in a value seat** — unimplemented by intent; a clear error is correct.
- **Module system** (linking, module-file top-level world, store modules,
  duplicate-module error) — MOD-01/03/04/05 + P-27b `#[ignore]`; imports parse only.
- **`DIVERGES` verdicts** — need a fuel-limited harness; M-04 `#[ignore]`.
- **`String.units`/`points` element representation** — E8 doesn't pin it; Tuples of
  Numbers here, lengths only asserted (S-02). `// [ask-author]` in `harness.rs`.
