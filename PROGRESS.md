# PROGRESS.md — implementation state

> **How to read this file (for the design/review chat).** This is the *state
> snapshot* of the NEXT implementation, rewritten in place at every increment —
> read it top to bottom for current position. It never carries rationale:
> **provenance and per-decision detail live in `DECISIONS.md`** (append-only,
> newest-first, dated headings — the anchors referenced here point at those
> entries). **Doc-side gaps, active asks, and registered drift live in
> `OwedItems.md`.** The three files are maintained in the same commit as the work
> they describe.

**Snapshot:** 2026-07-24 · canonical library synced (manifest green) · reconciliation pass.

---

## 1. Scoreboard (machine-checked)

| Suite | Result |
|---|---|
| Unit tests (`cargo test --lib`) | **234 passed, 0 failed, 0 ignored** |
| Conformance suite (`tests/conformance.rs`, stable IDs) | **111 passed, 0 failed, 13 ignored** |
| Clippy (`--all-targets`) | **0 warnings** |
| Manifest (`MANIFEST.sha256.txt`) | **all 14 files verify** |

Conformance by phase: **Phase 0** N-01…05, I-01…04, FE-01…07 green ·
**Phase 1** P-01…30 green (P-27b ignored) · **Phase 2** D-01…16 all green ·
**Phase 3** T-01…13 green, PR-01…09, O-01…06, S-01…03, X-01/02, M-01…06
(M-04 ignored), FL-01…03, MOD-02 green / MOD-01,03,04,05 ignored · **Phase 4**
H-01…05 green · **Phase A** 6 recorded stubs · **μ** MU-19 green / MU-18 ignored.

The 13 ignores, by reason:
- **module system staged** (5): P-27b, MOD-01, MOD-03, MOD-04, MOD-05 — imports
  parse; linking, module-file world distinction, and project errors are unbuilt.
- **fuel harness absent** (1): M-04 (`DIVERGES` verdicts).
- **PENDING-§5** (1): MU-18 (open-member observation trap needs the group window).
- **Phase A** (6): program-level analyzer verdicts pending (A-WRK's RECOVER is now
  discharged — grids recovered; verification still needs the analyzer).

## 2. Doc-sync matrix

Which normative document state this implementation is currently reconciled
against. If the design side updates a doc, this table says whether the change has
been absorbed.

All 14 canonical files verified against `MANIFEST.sha256.txt` (2026-07-24). Every
row below is the manifest-canonical version.

| Document | Version/patch | Reconciled | Notes |
|---|---|---|---|
| Design compendium | v1.0 patch **1.0.8** (frozen) | ✅ | C§17 owed list in OwedItems |
| Grammar | v0.1 | ✅ | L1/L2 enforced in the parser |
| Kernel AST | v0.1 + **§4 tested-seat amendment (author, 07-24)** | ✅ | canonical now carries the guard-based rows `[RULED 2026-07-22]`, matching `tested_match` |
| Semantics companion | v0.1 + **review round (07-21) + §7 RULED** | ✅ | 13 classes; total interpolation; open-value obs = Option A (`unbound-evaluation`); actKind in the closure key (FE-07) |
| μ-canonicalization | v0.5 | ✅ | §6 universal interning: registered drift, PENDING-§5 (OwedItems) |
| Recursive contracts | v0.2 patch **0.2.2** | ✅ | Concat guardedness + sourceProgress |
| Tuple-length family | v0.3 patch **0.3.1** | 🟡 | §1–§2 built; §3–§5 next |
| Application & induction | v0.8 patch **0.8.1** | ⬜ | not yet implemented (the analyzer-core rebuild) |
| Test suite | v0.1 + **07-24 additions** | ✅ | PR-06…09, FE-07, MU-18/19 implemented; A-WRK grids recovered |
| Phase-A worked examples (recovered) | 2026-07-21 | 📄 | RECOVER discharged; verification needs the analyzer |

## 3. Needs design-side action

**Nothing is blocking.** All recent asks were resolved this cycle: T-10 ruled
(guard-based, implemented + now in the canonical §4); open-value observation ruled
Option A (implemented incidentally); A-WRK RECOVER discharged (grids recovered).

Low-stakes / for-info only:
1. **E8 `String.units`/`points` element representation** — docs don't pin it;
   Tuples of Numbers here, lengths only asserted (S-02). `// [ask-author]` in
   `src/oracle/harness.rs`.
2. **Open design threads B & C** — no spec change, block nothing; the tests that
   would move if Thread C is ruled are catalogued in `OwedItems.md`.

## 4. Subsystem status map

**Legend:** ✅ built & tested · 🟡 partial (honest scope note) · ⬜ not started.

| Subsystem | Spec | State |
|---|---|---|
| Value layer: exact rationals (B2 printing), interner, values | Compendium B1/B2 | ✅ |
| Lexer + parser (L1/L2, T1–T3, pipes/hasks/match/patterns) | Grammar v0.1 | ✅ (module headers parse; no linking — see below) |
| Desugar (closed catalog §4, incl. ruled tested-seat rows, splice write, hasks, pins, alternation binding-free) | Kernel AST §4 | ✅ |
| Oracle interpreter: worlds/admission, Match, completion, mutator staging, `?.` totals, clamped slices, graphemes, total interpolation, Failure/host effects | Companion §§1–5 | ✅ (contract-free by design; the truth source) |
| `String` prelude (`length`/`units`/`points`) | E8 | ✅ (element repr: ask #2) |
| Normalization + property harness (H-01…05) | Part I step 4 | ✅ |
| μ-canonicalization: Algorithm A (code), Algorithm B (value bisimulation), narrow `==`-slice (poly) | μ v0.5 | 🟡 `==` results fully conform (all FE rows green); *mechanism* differs — bisimulation-at-compare instead of intern-at-construction; re-architecture = the §5 wiring increment (OwedItems “drift”) |
| Contracts C.1: algebra + denotational membership | C§4/C§16 | ✅ (incl. `Concat`, exact `Record`+`HasField`) |
| Contracts C.2: three-valued subcontract | C§8 | ✅ (`Concat` rows land Unproven — §4 alignment pending) |
| Contracts C.3: operation transfer rules | C§7 | 🟡 oracle-derived + brute-tested; interface is the pre-1.0.7 shape — `OperationOutcome` rebuild lands with app-induction |
| Recursive contracts C§9 (admissibility, emptiness/productivity, progress-guarded subcontract, product-graph intersection, witness refutation) | RC v0.2.2 | ✅ (RC-01…19 covered) |
| Named contracts (C§12.2 static eval) + contract patterns | C§12.2/E9 | ✅ non-recursive; 🟡 recursive/mutual *source* contracts don't yet build a `RecGroup` (sound: unresolved → Top) |
| Tuple-length family §1 (`Concat` NF) + §2 (`len` with Exact/Approx stamps, weighted-SCC solver) | family v0.3.1 | ✅ (TL-13/14/15/19/22) |
| Tuple-length family §3 (refutation discipline, `restrictLen`/`LengthRestricted`) · §4 (alignment) · §5 (grapheme seams) | family v0.3.1 | ⬜ **next planned** |
| Analyzer, expression layer: Const/Ref/PrimOp/Tuple/Record/Template/Access/Match/Apply — exact closed-expression trap concordance + sound open-term reasoning, narrowing, named contracts | §6 concordance | ✅ for the listed nodes; 🟡 `Lambda` bodies, `Write`/worlds type as Top; open-call returns Top |
| Application & induction package (`AnalysisContract`, γ, instance metadata, fact graph, return induction) | v0.8.1 | ⬜ (the analyzer-core rebuild; unblocks A-NEG/A-ACC/A-SND/A-VER) |
| Module system (linking, module-file top-level world, store modules, duplicate-module error) | E12 | ⬜ (imports parse only) |
| Reactive layer / concurrency / UI | G1 fence | 🚫 fenced, out of scope |

## 5. Known deviations & doc gaps (summary)

Full detail in `OwedItems.md`. Currently registered: the C§16 **OperationOutcome**
interface rebuild (with app-induction) · **`Record(Exact|Open)`** precision ·
**universal interning** mechanism (PENDING-§5) · **`Concat` C.2 rows** (§4
alignment) · C§17's still-owed doc items (per-pair tables, remaining
`analyzeOperation` tables, error templates, …).

## 6. Next increments (planned order)

1. **Tuple family §3** — refutation discipline (Approx refutes intersection
   emptiness via disjoint uppers, never subcontract witnesses — TL-16/20) +
   `restrictLen`/`LengthRestricted` canonical rows (TL-17).
2. **Tuple family §4** — segment alignment (forced-boundary peeling,
   `ElementRefutation`, TL-01a/18/21); closes the `Concat ⊑ Concat` gap.
3. **Tuple family §5** — grapheme boundary-state seams (TL-09).
4. **Application & induction package** (v0.8.1) — the analyzer core; then the
   Phase A batteries activate.
5. Opportunistic: recursive named *source* contracts → `RecGroup`; module system;
   fuel harness (M-04).

## 7. Increment ledger (thin — full provenance at the DECISIONS anchor)

| Date | Commit | Increment | DECISIONS anchor |
|---|---|---|---|
| 2026-07-19 | `25cd1ac`…  | Build order 1–4: value layer → lexer/parser → desugar → oracle → normalization harness | entries of 2026-07-19 |
| 2026-07-19 | — | μ-canonicalization: Algorithm B value identity; poly NF; Algorithm A | 2026-07-19/20 entries |
| 2026-07-20 | — | Contracts C.1 algebra + membership | “Contracts C.1” |
| 2026-07-20 | `07c1552` | Spec reconcile: narrow `==`-slice (μ v0.5 §8) | “Reconcile with updated specs” |
| 2026-07-20 | `38f1eda` | C.2 three-valued subcontract | “Contracts C.2” |
| 2026-07-20 | `7f91f7c` | C.3 operation transfer rules | “Contracts C.3” |
| 2026-07-20 | `76c0cdd` | C§9 recursive contracts | “Contracts C§9” |
| 2026-07-20 | `773abc8` | RC-14 product graph + §5.3 refutation | “Follow-up … owed rows closed” |
| 2026-07-20 | `1bd8c5a` | Analyzer: pure fragment + §6 concordance | “Analyzer (Part D begins)” |
| 2026-07-20 | `849c8a4` | Analyzer: Template + C.2 kind rows | “implement Template” |
| 2026-07-20 | `f7f9194` | Analyzer: access demands (E6) | “access demands” |
| 2026-07-20 | `0db4d56` | Analyzer: Match (narrowing, seats, exhaustiveness) | “Analyzer: `Match`” |
| 2026-07-20 | `412efcb` | Analyzer: Apply | “Analyzer: `Apply`” |
| 2026-07-20 | `f806dcc` | Apply deferrals recorded as doc-owed | “Provenance correction” |
| 2026-07-21 | `9362138` | **Author:** app-induction v0.8 + tuple family v0.3 land; compendium →1.0.8 | — |
| 2026-07-21 | `45d9698` | Named contracts (C§12.2) + contract patterns | “Named contracts” |
| 2026-07-21 | `517a4a4` | **Correction:** interpolation total; trap deleted; PR-01…05 | “CORRECTION: structure interpolation” |
| 2026-07-21 | `6c48419` | MIT license, README, metadata | — |
| 2026-07-21 | `133b753` | Tuple family §1: `Concat` + `sourceProgress` (RC 0.2.2) | “`Concat` + `sourceProgress`” |
| 2026-07-21 | `461eb61` | Tuple family §2: `len` with exactness stamps | “Tuple family §2” |
| 2026-07-22 | `e5a7968` | **Audit** vs evolved docs: 4 bug classes fixed | “AUDIT” |
| 2026-07-22 | `7508c8c` | Conformance suite: stable IDs; 7 parser/desugar fixes | “Conformance suite aligned” |
| 2026-07-22 | `017f5ae` | Author doc updates read + synced (T-13, §7 RULED) | commit message |
| 2026-07-22 | `dac88d1` | **Ruling implemented:** strict tested seats (T-10) | “RULING [user]: strict tested seats” |
| 2026-07-22 | `5e41ecb` | PROGRESS.md added (state snapshot for the design loop) | commit message |
| 2026-07-24 | (this) | Canonical library synced (manifest); reconciliation: PR-06…09, FE-07, MU-18/19; A-WRK RECOVER discharged; lossless renderer | “Canonical-library sync + suite reconciliation” |
