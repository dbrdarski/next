# PROGRESS.md — implementation state

> **How to read this file (for the design/review chat).** This is the *state
> snapshot* of the NEXT implementation, rewritten in place at every increment —
> read it top to bottom for current position. It never carries rationale:
> **provenance and per-decision detail live in `DECISIONS.md`** (append-only,
> newest-first, dated headings — the anchors referenced here point at those
> entries). **Doc-side gaps, active asks, and registered drift live in
> `OwedItems.md`.** The three files are maintained in the same commit as the work
> they describe.

**Snapshot:** 2026-07-25 · induction tail step 7 — recursive call sites infer their return (analyze_apply rewiring).

---

## 1. Scoreboard (machine-checked)

| Suite | Result |
|---|---|
| Unit tests (`cargo test --lib`) | **296 passed, 0 failed, 0 ignored** |
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
| Tuple-length family | v0.3 patch **0.3.1** | ✅ | §1–§5 built; contract-level string-length lift owed |
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
| Contracts C.2: three-valued subcontract | C§8 | ✅ (`Concat ⊑ Concat` unequal-count gap closed by §4 alignment) |
| Contracts C.3: operation transfer rules | C§7 | 🟡 oracle-derived + brute-tested; interface is the pre-1.0.7 shape — `OperationOutcome` rebuild lands with app-induction |
| Recursive contracts C§9 (admissibility, emptiness/productivity, progress-guarded subcontract, product-graph intersection, witness refutation) | RC v0.2.2 | ✅ (RC-01…19 covered) |
| Named contracts (C§12.2 static eval) + contract patterns | C§12.2/E9 | ✅ non-recursive; 🟡 recursive/mutual *source* contracts don't yet build a `RecGroup` (sound: unresolved → Top) |
| Tuple-length family §1 (`Concat` NF) + §2 (`len` with Exact/Approx stamps, weighted-SCC solver) | family v0.3.1 | ✅ (TL-13/14/15/19/22) |
| Tuple-length family §3 (refutation discipline, `restrictLen`/`LengthRestricted`) | family v0.3.1 | ✅ (TL-16/17/20) |
| Tuple-length family §4 (segment alignment: forced-boundary peeling, interior residual, uninhabited-shape guard) | family v0.3.1 | ✅ (TL-01a/18/21) |
| Tuple-length family §5 (grapheme boundary-state seams: segmenter-owned `compose`/`seam_delta`, merges-only bound) | family v0.3.1 | ✅ (TL-09); 🟡 finite-state lift to string *contracts* owed |
| Analyzer, expression layer: Const/Ref/PrimOp/Tuple/Record/Template/Access/Match/Apply — exact closed-expression trap concordance + sound open-term reasoning, narrowing, named contracts | §6 concordance | ✅ for the listed nodes; a call to a known closure now **infers** its return (§6, call-site args); 🟡 `Lambda` bodies, `Write`/worlds type as Top; an unknown-callee call returns Top |
| Application & induction §2 — `AnalysisContract` **structural/correlated** domain (Leaf/Tuple/Record/Alt, γ, `intersectA`/`meetInstance`, `proveSubcontractA`) | v0.8.1 | ✅ 8.1a + bridge (AP-27/28, correlation survival) |
| Application & induction §1 — the outcome algebra + **joint operand driver** (`ApplicationOutcome` tri-state, `analyze_application` per-alternative, structural `ApplicationWitness`/`SeatVerdict`) | v0.8.1 | ✅ 8.1b + bridge-2 (AP-15/17/18/21/23/24/29 + structural witness); **AP-30** ⬜ tail-dependent (row-contribution) |
| Application & induction §4a — the constructed instance-chain inventory (traversal-free closure + shape-repeat cutoff) | v0.8.1 | ✅ 8.1c (AP-16 mutual/self/diamond, order-independent set) |
| Application & induction — μ-aware body walk (call graph off closure values, §4a shape-cutoff over real recursion) | v0.8.1 | ✅ tail step 1 (self / mutual / leaf / chain) |
| Application & induction §1 step 3 — input obligation (`accepted_domain` from the param pattern, `input_obligation` with structural witness) | v0.8.1 | ✅ tail step 2 (arity / contract / const; rest-domain owed §4) |
| Application & induction §1 steps 4–5 — outcome contribution (`summarize_instance`: produced + completion off the body, recursion coarse-Top) | v0.8.1 | ✅ tail step 3 (identity / const / partial-match / recursion; AP-30 `ProvenPresent` half owed to §6) |
| Application & induction §6 — return induction, the joint vector pass (hypothesis injection in `analyze_apply`; sharpens recursive `Top`) | v0.8.1 | ✅ tail step 4 (factorial → Number; false-claim reject; mutual even/odd + vector failure) |
| Application & induction §6/§13.2a — multi-SCC driver (call-graph SCC decomposition + reverse-topo; carry each proven component's facts to its dependents) | v0.8.1 | ✅ tail step 5 (dependent-after-dependency; order-independent; mutual-as-one-component; vector-failure isolation) |
| Application & induction §6 — return-fact **inference** (autonomous claim proposal: `Contract::generalize` over a Bottom-pinned group summary, then the driver) | v0.8.1 | ✅ tail step 6 (factorial→Number over its domain; even/odd→Boolean; identity→sound over-approx; baseless→no fact) |
| Application & induction §6/C§13.2 — **`analyze_apply` rewiring** (`call_return`: recursive call sites infer their return over the call-site args; re-entrancy guard in `summarize_instance`) | v0.8.1 | ✅ tail step 7 (`f(x:Number)`→Number; `even(x)` satisfies a tested seat; `f(x:Top)` stays sound) |
| Application & induction §6/§5 — realized-witness `(e,x,v)` refutation, **AP-30 `ProvenPresent`** (completion tri-state → `may_complete`), domain-indexed facts, the C§13.4 evaluation cache | v0.8.1 | ⬜ **next**: refutation + completion threading + cache (with A-ACC/A-SND; A-NEG needs the separate C§10 grounding arc) |
| Module system (linking, module-file top-level world, store modules, duplicate-module error) | E12 | ⬜ (imports parse only) |
| Reactive layer / concurrency / UI | G1 fence | 🚫 fenced, out of scope |

## 5. Known deviations & doc gaps (summary)

Full detail in `OwedItems.md`. Currently registered: the C§16 **OperationOutcome**
interface rebuild (with app-induction) · **`Record(Exact|Open)`** precision ·
**universal interning** mechanism (PENDING-§5) · `restrict_len`'s recursive
certified-unfolding rule and the §4 `ElementRefutation` *structured* witness (the
complete-inhabitant witness is stronger) · C§17's still-owed doc items (per-pair
tables, remaining `analyzeOperation` tables, error templates, …).

## 6. Next increments (planned order)

1. **Application & induction — the induction tail** (steps 1–7 done: body walk, input
   obligation, outcome contribution, the joint vector pass, the multi-SCC driver,
   autonomous return-fact inference, **and the `analyze_apply` rewiring**): next is
   (a) the realized-witness `(e, x, v)` **refutation** (the third voice, permanent
   in-namespace); (b) **AP-30's `ProvenPresent` half** — thread the outcome
   contribution's completion tri-state into `analyze_apply`'s `may_complete` (currently
   the mutator-only check); (c) the **C§13.4 evaluation cache** (one call site drives
   one bounded inference today — no persistent cache); (d) §5 domain-indexed facts and
   the sampled γ soundness battery. That set activates **A-ACC/A-SND** (A-NEG's
   `factorial → REJECT` needs the separate **C§10 grounding / derived-input-contract**
   arc — not this tail). (Deferred non-blocking: per-alternative `witness_status`;
   rest-parameter length-precise domain via §4; the reverse-topological *claim
   proposal* for helper-base functions; indirect deps through non-candidate helpers
   coarsen to `Top`, sound.)
3. Opportunistic: recursive named *source* contracts → `RecGroup`; module system;
   fuel harness (M-04); the string-length contract form + §5 finite-state lift.

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
| 2026-07-24 | `2d368c7`+`b404083` | Canonical library synced (manifest); reconciliation: PR-06…09, FE-07, MU-18/19; lossless renderer | “Canonical-library sync + suite reconciliation” |
| 2026-07-24 | `75b8338` | Tuple family §3: refutation discipline + restrictLen/LengthRestricted (TL-16/17/20) | “Tuple family §3” |
| 2026-07-25 | `5e98194` | Tuple family §4: segment alignment — forced-boundary peeling (TL-01a/18/21) | “Tuple family §4” |
| 2026-07-25 | `90f9c85` | Tuple family §5: string boundary-state seams — segmenter-owned (TL-09) | “Tuple family §5” |
| 2026-07-25 | `e581e72` | App/induction 8.1a: AnalysisContract abstract domain — γ, lattice, ⊑ᴬ, intersectA (AP-27/28) | “App/induction 8.1a” |
| 2026-07-25 | `2e693c0` | App/induction 8.1b: application transfer rule §1 outcome algebra — tri-state completion, seat demand, join, admission (AP-15/17/18/21/23/24) | “App/induction 8.1b” |
| 2026-07-25 | `eae2b43` | App/induction 8.1c: instance-chain inventory §4a — traversal-free closure + shape-repeat cutoff (AP-16) | “App/induction 8.1c” |
| 2026-07-25 | `254c24d` | Analyzer-core bridge: correlated structural AnalysisContract (Leaf/Tuple/Record/Alt) — no false cross-pairs; review items closed | “Analyzer-core bridge” |
| 2026-07-25 | `552079b` | Analyzer-core bridge-2: joint operand driver + structural ApplicationWitness/SeatVerdict (AP-24/29 + witness; AP-30 owed to tail) | “Analyzer-core bridge-2” |
| 2026-07-25 | `2006975` | Review corrections: AP-30 tail-dependent; reversed-root inventory test | commit message |
| 2026-07-25 | `59e3ea4` | Induction tail step 1: μ-aware body walk — call graph off closure values, §4a cutoff over real recursion | “Induction tail step 1: μ body walk” |
| 2026-07-25 | `7d14bbf` | Induction tail step 2: input obligation — accepted-domain derivation + structural witness | “Induction tail step 2: input obligation” |
| 2026-07-25 | `d968904` | Induction tail step 3: outcome contribution — per-instance body summary (recursion coarse-Top, terminating) | “Induction tail step 3: outcome contribution” |
| 2026-07-25 | `b973ce6` | Induction tail step 4: return induction — joint vector pass + hypothesis injection (factorial → Number; mutual even/odd) | “Induction tail step 4: return induction” |
| 2026-07-25 | `c467764` | Induction tail step 5: multi-SCC driver — call-graph SCC decomposition + reverse-topo, carry proven facts to dependents (double/quad; order-independent; mutual; failure isolation) | “Induction tail, step 5: the multi-SCC driver” |
| 2026-07-25 | `4660634` | Induction tail step 6: return-fact inference — autonomous claim proposal (`Contract::generalize` over a Bottom-pinned group summary + the driver); factorial/even-odd/identity/baseless | “Induction tail, step 6: return-fact inference” |
| 2026-07-25 | (this) | Induction tail step 7: analyze_apply rewiring — `call_return` infers a known callee's return over call-site args; re-entrancy guard in `summarize_instance` (f(x:Number)→Number; even(x) tested seat; f(x:Top) sound) | “Induction tail, step 7: the analyze_apply rewiring” |
