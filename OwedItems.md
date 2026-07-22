# OwedItems.md — normative gaps the implementation defers to

This registry tracks items that are **owed or open in the normative documents
themselves** — not work I have merely sequenced for later. Implementation-only
gaps (a decided design I haven't built yet) do *not* belong here; they live in the
build-order tasks and `DECISIONS.md`.

Status vocabulary mirrors the compendium: **[owed]** (design intends a rule, not
yet written), **[open]** (a decision the author has flagged as unresolved),
**[specified]** (written and design-closed — implementation owed by me, tracked as
tasks, *not* here).

Each entry records the source, the current implementation behavior (always
**sound** — we never accept what a spec leaves trap-worthy), and what closing it
requires.

> **Rewritten 2026-07-21** against compendium patch **1.0.8**. Everything this file
> previously listed has been **discharged by the author** — see "Recently closed"
> below. Read the compendium's C§17 as the authority; this file is a working index.

---

## Recently closed — do not treat these as owed

| Was owed here | Now |
|---|---|
| Tuple-length / concatenation family | **[specified]** `next-tuple-length-family-specification-v0-3.md` (+0.3.1) — C§17 discharge confirmed round three |
| Print doctrine for structure interpolation | **[ruled]** total [user, 2026-07-18] — implemented; suite PR-01…05 green |
| `analyzeOperation` application table; return induction; instance / global-fact-graph machinery | **[specified]** `next-application-induction-specification-v0-8.md` (+0.8.1) — design-closed |
| First-class function-shape (arrow) contract | **superseded** — `AnalysisContract` + the `Known/Unknown` instance-metadata lattice (induction package §2) is the mechanism |
| Open-value group identity | **[ruled]** shape via strict openness — FE-05/FE-06 fixed, PENDING-§5 for mechanism only |
| A/B regression suite | **[specified]** `next-test-suite-specification-v0-1.md` |

---

## Still owed in the docs (C§17, patch 1.0.8)

Verbatim from the compendium's **Owed:** list, with the ones that actually bite the
current implementation called out first.

### 1. Per-pair contract tables — **[owed]**
`Geo`, `Difference`/emptiness, and finite-interval coverage rows, honoring the
**no-flattening precision rule** (unions of Tuple shapes are never flattened — the
argument-tuple contract model depends on it).
*Implementation today:* `subcontract`/`disjoint` implement the rows I could derive
soundly; `Geo` pairs and several `Difference` rows fall to `Unproven`. Sound,
incomplete.

### 2. `analyzeOperation` tables for the **remaining** operations — **[owed]**
The *application* rule is now **specified** (the induction package). What remains
owed are the per-operation tables for the other operations.
*Implementation today:* `contract::operation` derives arithmetic/ordering rows from
the oracle and brute-tests them; it is not a transcription of an authored table.

### 3. Union / Intersection completeness — **[owed]**
"Completeness or documented incompleteness" for the set-operation rows.
*Implementation today:* documented incompleteness in practice — the or-rules are
sound and deliberately partial.

### 4. Indeterminate enumerations; division / NF coupling — **[owed]**
*Implementation today:* two `IndetForm`s (`_/0`, `0/0`) per the semantics companion;
division totality implemented; no NF coupling.

### 5. Region-table computation steps; boolean-DNF procedure; certified-procedure inventory — **[owed]**
Not yet reached by the implementation.

### 6. Mutual-recursion spec + executable examples; the case-6 composed example; §10.4's four soundness obligations — **[owed]**
Bears on the induction package's discharge, not on current code.

### 7. §13's optimization table and origin-phrased error template; error/warning templates — **[owed]**
*Implementation today:* `Finding` messages are ad-hoc prose, not the authored
templates.

### 8. Provenance audit; C§16 discharge per rule — **[owed]**

---

## Registered implementation drift (audit 2026-07-22 — specified, awaiting rebuild)

Items where the *docs* are settled but the implementation still carries an older
shape. Sound today; tracked here so the rebuild is deliberate.

- **C§16 obligation 3 upgraded [1.0.7]:** every transfer rule's interface is
  `analyzeOperation(op, jointOperands: Correlated<AnalysisContract>, seatContext) →
  OperationOutcome { safety, produced: AnalysisContract, completion }`. Our
  `OpResult { safety, output: Contract }` is the pre-upgrade degenerate shape; the
  reshape lands with the application/induction package (which supplies
  `AnalysisContract` and `CompletionEvidence`).
- **`Record(fields, Exact | Open)` [1.0.7]:** openness is a Record-contract
  parameter (analyzer-internal; surface writes exact only). We model exact `Record`
  + bare `HasField`, so open record *patterns* lose per-field contracts (they narrow
  to `∩ HasField` only). Sound, precision-lossy.
- **μ v0.5 §6 universal interning:** closures should intern shallowly with runtime
  `==` a pointer test and Algorithm B canonicalization-internal; we run Algorithm B
  at compare time over plain allocations. Equal on every `==` result; differs in
  harness pointer observability (suite register PENDING-§5). Noted in
  `src/oracle/equal.rs`.
- **`Concat` C.2 rows:** `Concat ⊑ Kind(Tuple)`, kind-vs-Concat disjointness, and
  unequal-segment-count alignment (family §4) are absent — all land `Unproven`
  (sound). The §4 alignment procedure is the scheduled fix.

## Doc errata (for the author)

- The **semantics companion v0.1** still lists the deleted `unprintable-interpolation`
  trap (§3 Template row and the §6 concordance table) — superseded by the
  interpolation-total ruling [user, 2026-07-18] and test-suite line 57.
- **[ask-author] T-10 / D-01 conflict — ternary on a non-Boolean.** The kernel-AST
  §4 catalog lowers `c ? t : e` to `Match(c, [Arm(PConst(true), t),
  Arm(PConst(false), e)])`, under which `5 ? 1 : 2` *completes without value*
  (trapping **expecting-seat** only at a demanding seat). The semantics companion's
  trap-seed list and suite row T-10 instead expect **TRAP tested-seat** ("post-
  desugar guard"), which would require a guard-based lowering (e.g. bind-then-
  guard: `{ tmp = c; when tmp => t; => e }` — also single-evaluation). The same
  choice governs non-Boolean `a && b` / `a || b` / `!x`. The implementation follows
  the closed catalog; T-10 ships `#[ignore]` with the conflict recorded, and
  T-10a (a non-Boolean *arm guard* traps tested-seat — true under either ruling)
  runs in its place. **Needs a ruling.**

## Author-flagged opens (implemented per their stated law)

- **Mutator returns** — return-nothing is **[decided]** and implemented; the
  returns-leaning is a tagged **extension point [open]**.
- **Partial-correctness returns for gray functions** — **[open]** (C§17 surface
  list). The induction package's reference path deliberately does not sharpen the
  gray fallback by inference (AP-22).
- **Module in a value seat** — unimplemented by intent; a clear error is correct.
- **Full-language number representation (Phase 1 Reals); call-site gray warnings;
  sign/abs perimeter** — **[open]**, out of current scope.

---

*Not in this file:* specified-but-unimplemented work (the tuple family, the
application/induction package, the test-suite IDs, `Concat`, `Record(Exact|Open)`,
`sourceProgress`). Those are ordinary build-order tasks — the docs already pin them.
