# PROGRESS.md — implementation state

> **How to read this file (for the design/review chat).** This is the *state
> snapshot* of the NEXT implementation, rewritten in place at every increment —
> read it top to bottom for current position. It never carries rationale:
> **provenance and per-decision detail live in `DECISIONS.md`** (append-only,
> newest-first, dated headings — the anchors referenced here point at those
> entries). **Doc-side gaps, active asks, and registered drift live in
> `OwedItems.md`.** The three files are maintained in the same commit as the work
> they describe.

**Snapshot:** 2026-07-30 · **recovery spec-unblocked.** The Phase-1 audit's four
"blocking rulings" are resolved by the 07-30 landing (region-table + grounding
specs; `InferredAcceptedDomain`/eager-vs-lazy **dissolved** by errata E-6/E-7/E-8 —
§3). Next: build the demand core → region table → call-site body check; delete the
superseded call-site machinery (audit §5). This maintainer file was rebaselined to
the specs 07-30 — the intervening tail/Archive `✅` rows below are development
history the recovery supersedes, not the target architecture.

---

## 1. Scoreboard (machine-checked)

All rows verified by `cargo test` / `cargo clippy` / `shasum -c` on **2026-07-30**
(not inherited). **Caveat:** many of the 323 lib tests exercise the superseded
call-site machinery (§4 recovery note); they pass but count wrong-layer code the
recovery deletes.

| Suite | Result |
|---|---|
| Unit tests (`cargo test --lib`) | **339 passed, 0 failed, 0 ignored** |
| Conformance suite (`tests/conformance.rs`, stable IDs) | **111 passed, 0 failed, 13 ignored** |
| Clippy (`--all-targets`) | **0 warnings** |
| Manifest (`MANIFEST.sha256.txt`) | **all 19 files verify** (07-30 grounding landing) |

Conformance by phase: **Phase 0** N-01…05, I-01…04, FE-01…07 green ·
**Phase 1** P-01…30 green (P-27b ignored) · **Phase 2** D-01…16 all green ·
**Phase 3** T-01…13 green, PR-01…09, O-01…06, S-01…03, X-01/02, M-01…06
(M-04 ignored), FL-01…03, MOD-02 green / MOD-01,03,04,05 ignored · **Phase 4**
H-01…05 green · **Phase A** 6 recorded stubs · **μ** MU-19 green / MU-18 ignored.

The 13 ignores, by reason:
- **module system staged** (5): P-27b, MOD-01, MOD-03, MOD-04, MOD-05 — imports
  parse; linking, module-file world distinction, and project errors are unbuilt.
- **program-level fuel harness owed** (1): M-04 (`DIVERGES` verdicts) — the eval-level
  bound now exists (`eval_expr_bounded`, tail step 9); a bounded `run_module` + the M-04
  wiring is the remaining step.
- **PENDING-§5** (1): MU-18 (open-member observation trap needs the group window).
- **Phase A** (6): program-level analyzer verdicts pending (A-WRK's RECOVER is now
  discharged — grids recovered; verification still needs the analyzer).

## 2. Doc-sync matrix

Which normative document state this implementation is currently reconciled
against. If the design side updates a doc, this table says whether the change has
been absorbed.

All **19** canonical files verified against `MANIFEST.sha256.txt` (**2026-07-30 —
grounding landing; compendium 1.0.18**). Every row below is the manifest-canonical
version. `⬜` = design absorbed, implementation is the recovery Phase-2 build.

| Document | Version/patch | Reconciled | Notes |
|---|---|---|---|
| Design compendium | v1.0 patch **1.0.18** (frozen) | ✅ | C§17 owed list in OwedItems; region-table + grounding flipped owed→specified |
| Grammar | v0.1 | ✅ | L1/L2 enforced in the parser |
| Kernel AST | v0.1 + **§4 tested-seat amendment (author, 07-24)** | ✅ | canonical carries the guard-based rows `[RULED 2026-07-22]`, matching `tested_match` |
| Semantics companion | v0.1 + **review round (07-21) + §7 RULED** | ✅ | 13 classes; total interpolation; open-value obs = Option A; actKind in the closure key (FE-07) |
| μ-canonicalization | v0.5 | ✅ | §6 universal interning: registered drift, PENDING-§5 (OwedItems) |
| Recursive contracts | v0.2 patch **0.2.2** | ✅ | Concat guardedness + sourceProgress |
| Tuple-length family | v0.3 patch **0.3.1** | ✅ | §1–§5 built; string-length contract lift owed; §16 proofs owed |
| **Region-table computation + call-site body check** | **v0.3 patch 0.3.2 + E3/E-7** | 🟡 | design-closed; **built** (`analyzer/region.rs` §2–§4 + `analyzer/bodycheck.rs` = `BodySafe(instance, arg)`, RT-14 witness discipline). Gates 14.1–14.3 (`bad()` rejected / `f("hello")` rejected / `helper(0)` accepted, path-sensitive). Capture-free 1-param; **not yet wired into `analyze_apply`** (audit §5 delete pending). Owed: captures (b/c), arg-tuple projection (§5), instance cache, wiring+delete |
| **Grounding v1** | **v0.5 patch 0.5.1** | ⬜ | **design-closed** (compendium 1.0.18); GR-01…30, Phase GR; implementation + §16 owed |
| Late-resolution / termination-decisions | v0.5 / v4 | ✅ | method + pre-spec source for grounding (design record) |
| Application & induction | v0.8 patch **0.8.2** | ⬜ | design-closed; **call-site build superseded by the region-table recovery** (audit §5 — §4 map below) |
| Test suite | v0.1 + **07-30 (Phase GR added)** | 🟡 | PR/FE/MU implemented; Phase GR + A-WRK grids stubbed |
| Phase-A worked examples (recovered) | 2026-07-21 | 📄 | RECOVER discharged; verification needs the analyzer |

## 3. Needs design-side action

**The Phase-1 audit's four "blocking rulings" are RESOLVED by the 2026-07-30
landing** — the audit (2026-07-26) predated the region-table + grounding specs:

1. **Region-table computation procedure — SPECIFIED.** `next-region-table-specification-v0-3.md`
   (0.3.1–0.3.2, *architecturally closed*; C§17 records the item **discharged**, erratum
   2026-07-24). Not owed.
2. **Eager-vs-lazy / `InferredAcceptedDomain` — DISSOLVED.** Errata E-6 (C§12.1), E-7
   (E3), E-8 (E11), all 2026-07-24: **no materialized accepted-domain object.** `where`
   is `BodySafe(instance, DeclaredInput) = proven`. The mechanism is region-table
   reachability × ordinary C§7 body demands (C§13.1 subscriptions; eager preimage an
   *optimization*). No separate accepted-domain spec. Not a question anymore.
3. **Grounding arc (C§10) — SPECIFIED.** `next-grounding-specification-v0-5.md` (0.5.1,
   DESIGN-CLOSED; compendium 1.0.18). Implementation + §16 discharge owed, not design.
4. **Empty accepted domain (reframed)** — the only residual, and narrow: no
   "empty-domain" object exists, so the question is whether an *uncalled* proven-unsafe
   body (`() => 1 + "x"`) is flagged at the **definition** (E3/E-7 checks the body *at
   the call*, so it's otherwise unflagged). Not explicitly ruled; off the recovery's
   critical path. E10's goes-nowhere lint tier is the natural home. **[ask-author]**

So the recovery is **spec-unblocked**: build the demand core → region table →
call-site body check (region-table §3's 14.1–14.3 as the gate), deleting the
superseded call-site machinery per audit §5 (nothing deleted until the replacement
passes `bad()`-rejected / `f("hello")`-rejected / `helper(0)`-accepted / divergence
-terminates / no-user-fn-executed). Full owed picture in `OwedItems.md`.

**Open policy pick (author's, not blocking the build):** P-1 / Principle 9 —
warn-and-compile vs reject for unproven grounding (blocker (4) now SATISFIED [1.0.18];
(2)(3) open). No action until stamped.

Low-stakes / for-info only:
1. **E8 `String.units`/`points` element representation** — docs don't pin it;
   Tuples of Numbers here, lengths only asserted (S-02). `// [ask-author]` in
   `src/oracle/harness.rs`.
2. **Open design threads B & C** — no spec change, block nothing; the tests that
   would move if Thread C is ruled are catalogued in `OwedItems.md`.

## 4. Subsystem status map

**Legend:** ✅ built & tested · 🟡 partial (honest scope note) · ⬜ not started.

> **Recovery note.** The `Application & induction` rows and the tail/Archive rows
> below (`body_safety`, `InstanceBodySummary`, `domain_admitted`, the induction-tail
> steps, `accepted_domain`) are `✅` as *built call-site machinery* — but the
> architecture review + Phase-1 audit found that layer is the wrong one, and the
> region-table recovery (§3) **supersedes most of it**. Read those rows as
> development history, not the target architecture. The *keep* set (return-fact SCC
> induction, instance+domain identity, correlated alternatives, dead-arm narrowing)
> survives; the rest is Phase-3 delete. `OwedItems.md §0` has the Build/Delete/Keep split.

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
| Analyzer, expression layer: Const/Ref/PrimOp/Tuple/Record/Template/Access/Match/Apply — exact closed-expression trap concordance + sound open-term reasoning, narrowing, named contracts | §6 concordance | ✅ for the listed nodes; a known-closure call **infers** its return (call-site args) and surfaces **interprocedural body-safety** traps (`body_safety`) — the analyzer no longer executes user functions; 🟡 `Write`/worlds type as Top; unknown-callee call returns Top |
| Analyzer, oracle boundary — no user-function execution in normative analysis (Archive6 §8/§9): closed-call `eval_expr` fold removed; only finite `eval_prim` + `eval_expr`-on-`Const`-access remain | Archive6 | ✅ 7-test gate incl. diverging `loop()` terminates without execution |
| Body safety over **actual call edges** (Archive7): follows abstract applications (param/local callees resolved from the value; each callee over its edge domain); + `analyze_match` **dead-arm elimination** (proven-empty region / proven-false guard skipped; proven-true guard consumes) | Archive7 | ✅ §11 gate (param callee reject; edge-domain reject; narrowed dead branch accept) |
| **InstanceBodySummary unification** (Archive8): `instance_body_summary` keyed by `(instance, input-domain)` — safety + completion + non-recursive return share one node; instance identity (not shape); exact non-recursive returns | Archive8 | ✅ §11 gate (same-shape/diff-captures; same-instance/diff-domain; multi-callee; return-dependent) |
| **Finite admitted-domain basis + total alternatives** (Archive9): `domain_admitted` (program literals + Kinds) admits exact recursive domains, computed ones widen via total `kind_abstraction` → advance-bounded state universe; widened findings **downgraded** (no false refutation); `CalleeAlt::{Known,UnknownFunction,NotAFunction}` — no live alternative dropped | Archive9 | ✅ §17 gate (widened-refutation accept; non-function reject; unknown not sharpened; growing-`Range` terminates); 🟡 candidate-graph/SCC proper + memo, joint-operand driver (§12), `may_not_complete` owed |
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
| C§13.2 domain-indexed facts — **hypotheses keyed by instance + input domain** (`Hypothesis{callee, input, contract}`; `args ⊑ input` guard; mutual groups over a consistent domain) | v0.8.1 | ✅ Archive4 §3/§4 fix (same-shape/diff-captures not aliased; false `h:Number` rejected; `make(1)`/`make("s")` distinct) |
| E10 / §1.6 — **completion tri-state** (`Completion` on `Analysis`; three-voice `demand`; remainder inhabitance via `has_proven_inhabitant`; callee completion threaded — partial/mutator callee flagged) | v0.8.1 | ✅ tail step 8 (partial callee at expecting seat → error; guarded fall-through → warning; closes the mutator-only gap) |
| §6 — **realized-witness refutation** (`realized_refutation`/`check_return_claim`, three-voiced: permanent refute vs per-compilation unproven) + the **fuel/call-depth-bounded oracle** (`eval_expr_bounded`, `run_source_in`) | v0.8.1 | ✅ tail step 9 (factorial: Number Proven / String Refuted-with-witness / Greater(0) Unproven; divergence → OutOfFuel, no hang) |
| Application & induction §6/§5 — **AP-30 `ProvenPresent`** structured witness (outcome algebra), domain-indexed facts, the C§13.4 evaluation cache, `where`/demand consumers of `check_return_claim` | v0.8.1 | ⬜ **next**: the structured ProvenPresent witness + cache + a claim consumer (A-ACC/A-SND; A-NEG needs the separate C§10 grounding arc) |
| Module system (linking, module-file top-level world, store modules, duplicate-module error) | E12 | ⬜ (imports parse only) |
| Reactive layer / concurrency / UI | G1 fence | 🚫 fenced, out of scope |

## 5. Known deviations & doc gaps (summary)

Full detail in `OwedItems.md` (rebaselined 2026-07-30). Headlines: **`InferredAcceptedDomain`
/ eager-vs-lazy DISSOLVED** (errata E-6/E-7/E-8); **region-table + grounding
design-closed, implementation owed**; the **call-site body-safety machinery
superseded** (Phase-3 delete); the C§16 **OperationOutcome** interface rebuild ·
**universal interning** (PENDING-§5) · **`Record(Exact|Open)`** · tuple-family §16
proofs + string-length contract lift · C§17's doc-owed set (per-pair tables,
boolean-DNF, remaining `analyzeOperation` tables, error templates, …).

## 6. Next increments (planned order)

1. **Application & induction — the induction tail** (steps 1–9 done: body walk, input
   obligation, outcome contribution, the joint vector pass, the multi-SCC driver,
   autonomous return-fact inference, the `analyze_apply` rewiring, the completion
   tri-state, **and realized-witness refutation**): next is (a) **AP-30's structured
   `ProvenPresent` witness** in the outcome algebra (a represented `(callee, args)`
   fall-through feeding `seat_demand`); (b) a **consumer for `check_return_claim`** — a
   `where` return-check (E11) or a demand-driven return obligation, the natural home for
   the three-voiced verdict; (c) the **C§13.4 evaluation cache** (one call site drives
   one bounded inference today); (d) the **program-level bounded run + M-04 wiring**
   (eval-level fuel exists now); (e) §5 domain-indexed facts and the sampled γ soundness
   battery. That set activates **A-ACC/A-SND** (A-NEG's `factorial → REJECT` needs the
   separate **C§10 grounding / derived-input-contract** arc — not this tail). (Deferred
   non-blocking: per-alternative `witness_status`; rest-parameter length-precise domain
   via §4; the reverse-topological *claim proposal* for helper-base functions; indirect
   deps through non-candidate helpers coarsen to `Top`, sound.)
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
| 2026-07-25 | `25793dd` | Induction tail step 7: analyze_apply rewiring — `call_return` infers a known callee's return over call-site args; re-entrancy guard in `summarize_instance` (f(x:Number)→Number; even(x) tested seat; f(x:Top) sound) | “Induction tail, step 7: the analyze_apply rewiring” |
| 2026-07-25 | `1472fdf` | Induction tail step 8: completion tri-state — `Completion` on `Analysis`, three-voice `demand`, remainder inhabitance, callee completion threaded (partial callee → error; guarded → warning) | “Induction tail, step 8: the completion tri-state” |
| 2026-07-25 | `9d72f90` | Induction tail step 9: realized-witness refutation (`refute.rs`, three-voiced) + fuel/call-depth-bounded oracle (`eval_expr_bounded`, `run_source_in`, `proven_members`) | “Induction tail, step 9: realized-witness refutation” |
| 2026-07-26 | `124d604` | Review correction (Archive4 §3/§4): instance + domain-indexed hypothesis key — `Hypothesis{callee,input,contract}`, `args ⊑ input`, same-arity domain propagation; aliasing adversarial test | “Review correction: instance + domain-indexed hypothesis key” |
| 2026-07-26 | `efae058` | Review cleanup (Archive4 §11): remove `segment_nullable(..., 8)` magic depth → path-based cycle detection (advance-bounded by the RecGroup, more precise) | “Review cleanup: remove segment_nullable magic depth” |
| 2026-07-26 | `a9cf0af` | Archive5 §4: direct out-of-domain hypothesis regression (`hypothesis_for` law locked); §8/§9 fold-removal analyzed (needs lambda-body analysis — OwedItems) | “Archive5 §4: direct out-of-domain hypothesis regression” |
| 2026-07-26 | `37dbf6e` | Archive6 §8/§9: interprocedural `body_safety` (direct + transitive traps, errors-only) + remove the closed-call `eval_expr` fold; 7-test gate incl. diverging `loop()` terminates | “Archive6 §8/§9: interprocedural body safety” |
| 2026-07-26 | `bd99ca0` | Archive7 correction: `body_safety` over actual call edges (`SAFETY_STACK` cutoff — param callees, edge domains) + `analyze_match` dead-arm elimination; §11 adversarial gate | “Archive7 correction: body safety over actual call edges” |
| 2026-07-26 | `c3bb5ca` | Archive8: InstanceBodySummary unification — `instance_body_summary` keyed by `(instance, input-domain)`, multi-callee enumeration, exact non-recursive returns; §11 gate (A/B/C/D) | “Archive8: the InstanceBodySummary unification” |
| 2026-07-26 | `e81c1f7` | Archive9: finite admitted-domain basis (`domain_admitted` + `kind_abstraction`) → advance-bounded termination; widened findings downgraded; total `CalleeAlt` enumeration; §17 gate | “Archive9: the finite admitted-domain basis” |
| 2026-07-26 | (this) | Archive10 small corrections: atoms-only admitted domains (termination, verified overflow), widened-completion downgrade, `NotAFunction` inhabitance; **design question raised** (accepted domains) | “Archive10 small corrections + a design question raised” |
