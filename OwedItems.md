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
   OperationOutcome { safety, produced: AnalysisContract, completion }`. The
   **`AnalysisContract` abstract domain now exists** (`src/analyzer/domain.rs`, 8.1a:
   γ, the metadata lattice, `intersectA`/`meetInstance`, `proveSubcontractA`). Still
   owed: the primitive `analyze_operation`'s `OpResult { safety, output: Contract }`
   is the pre-upgrade degenerate shape — the `OperationOutcome`/`completion` reshape
   and the joint-correlated-operand plumbing land with the **application transfer
   rule** (8.1b, §1 of v0.8.1).

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

4. **Tuple family built (§1–§5); three precision tails owed** — §1 `Concat`, §2
   `len`, §3 refutation/`restrictLen`, **§4 segment alignment** (closed the
   `Concat ⊑ Concat` unequal-count C.2 gap), and **§5 grapheme boundary-state seams**
   (segmenter-owned `compose`/`seam_delta`, exact for every literal, corpus-verified)
   are all in. Owed, all precision/lift — none a soundness gap:
   - **§5 finite-state lift to string *contracts*** — RI-parity normalization, the
     ZWJ-chain / Hangul states over the segmenter's finite state space. Needs the
     segmenter's category tables **and** a string-length *contract* form the algebra
     does not yet have; `Summary` currently retains `units` and is segmenter-exact
     for literals. The recorded exactness upgrade.
   - `restrict_len`'s recursive certified-unfolding rule (demand-depth-bounded `D`,
     the `interner` is carried for it).
   - §4's **`ElementRefutation` *structured* witness** (alignment map + projected
     branch) — refutation returns the complete concrete inhabitant, a strictly
     stronger witness, so this is a presentation detail only.

6. **Rest-parameter accepted domain — length-precise form owed [induction tail, 07-25]** —
   `accepted_domain` (§1 step 3) derives the callee's accepted input set from its
   parameter pattern via `pattern_contract`, which is sound only for **no-rest**
   patterns; a rest parameter `(a, …rest)` widens to `Kind(Tuple)` (unsound as an
   accepted domain, since it would admit the empty tuple). It currently **declines**
   rest patterns (`None` → obligation `Unproven`). The sound length-precise domain is
   the tuple-family §4 `restrictLen`/`Concat` form (`≥ k` positions) — a precision
   refinement, not a soundness gap.

7. **Return-fact inference precision — two sound gaps [induction tail step 6, 07-25]** —
   `infer_return_fact` proposes a claim over each function's *accepted input domain*
   (the parameter pattern; `Top` for a bare `(n)`) and re-verifies it with the driver.
   Both gaps are precision, not soundness (a coarser fact is always sound):
   - **Untyped-domain Indeterminate-passthrough** — over `Top`, arithmetic passes an
     Indeterminate operand through, so e.g. `factorial`'s inferred return is `Number ∪
     Indeterminate` (an Indeterminate `n` really does propagate). **Call-site argument
     contracts** sharpen this to pure `Number` — that arrives with the `analyze_apply`
     rewiring. The grounding-derived input domain (C§10) that would tighten the
     *autonomous* case is the separate, unbuilt recursion-grounding arc.
   - **Helper-base functions get no fact** — the proposal Bottom-pins the *whole*
     reachable group, so a function whose only base contribution is a **non-recursive
     helper call** proposes `Top`/`Bottom` → no fact (→ coarse `Top` at the call site).
     The fix is a **reverse-topological claim proposal** (propose a helper's claim
     before its callers'), owed with the wiring.
   - **No persistent inference cache** — `analyze_apply` (`call_return`) runs a fresh
     inference per call site; repeated calls to the same function re-run the driver. The
     **C§13.4 evaluation cache** (keyed on the seat/world-independent core) is the
     optimization; correctness holds without it (the re-entrancy guard bounds each run).
   - **AP-30 structured `ProvenPresent` witness** — the *wired* analyzer path now
     carries the three-voice completion (`Completion` on `Analysis`; a partial/mutator
     callee is flagged, guarded fall-throughs warn), but the **outcome algebra**'s
     `summarize_instance` still maps a proven fall-through to `UnprovenPossible`, not
     `ProvenPresent(witness)` — minting a fake `(callee, args)` witness would violate the
     §7 discipline. The represented-witness construction (feeding `seat_demand`'s
     `Refuted`) is the deferred AP-30 half.

5. **`Known(∅)` normalization — doc-integration mismatch [analyzer review, 07-25]** —
   the application spec (`next-application-induction-specification-v0-8.md:19`)
   normalizes `(C, Known(∅)) → Bottom` for the function-position `AnalysisContract`.
   My `AnalysisContract::leaf` collapses to `Bottom` **only when `C` is function-only**;
   off function positions the metadata is vacuous (`(Number, Known(∅)) → Number`). The
   reviewer calls this generalization *defensible* if `AnalysisContract` may represent
   arbitrary values (non-function members stay inhabited while the function alternative
   is empty) — but it must be made explicit in the spec before the domain is frozen.
   **Not unsound**; a wording reconciliation owed from the author.

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
