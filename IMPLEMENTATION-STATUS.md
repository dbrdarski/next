# NEXT — IMPLEMENTATION STATUS (AUTHORITY)

**Created 2026-07-31 (Tier-0 rebaseline). This file is the single current authority on
implementation status.** Where any other maintainer document disagrees with this file about *what
is built, what is trusted, or what to do next*, **this file wins**.

**What this file is not.** It makes **no semantic rulings**, defines no mechanism, and changes no
design. It does not rewrite history: contradictory documents keep their text and are *labelled*
below. Design authority remains entirely with the manifest-verified normative specifications (§1).

**Doc status vocabulary used here:** `CURRENT` · `HISTORICAL` (true when written; not guidance) ·
`SUPERSEDED` (contains guidance that must not be followed) · `KNOWN UNSOUND` (code that can return
a wrong verdict).

---

## 1. Normative specifications — CURRENT (design authority)

All 19 manifest-verified files (`shasum -c MANIFEST.sha256.txt` → 19/19 OK, checked 2026-07-31).
**These are not to be edited as part of any implementation work.**

`next-design-compendium-v1-0.md` (patch 1.0.18) · `next-grammar-specification-v0-1.md` ·
`next-kernel-ast-specification-v0-1.md` · `next-semantics-companion-v0-1.md` ·
`next-test-suite-specification-v0-1.md` · `next-mu-canonicalization-specification-v0-5.md` ·
`next-recursive-contracts-specification-v0-2.md` · `next-application-induction-specification-v0-8.md` ·
`next-tuple-length-family-specification-v0-3.md` · `next-region-table-specification-v0-3.md` ·
`next-phase-a-worked-examples-recovered.md` · `CLAUDE.md` · `OwedItems-CLOSED.md` ·
`HANDOVER-open-threads-2026-07-23.md` · `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md` ·
`next-termination-decisions-v4.md` · `next-late-resolution-v0-5.md` ·
`next-grounding-spec-v1-handover.md` · `next-grounding-specification-v0-5.md`

**Recorded staleness inside normative files — NOT to be "fixed" by implementation work.** These are
noted so no one implements a phantom; correcting them is an author/design action:

| Where | Stale text | The governing statement |
|---|---|---|
| region-table §6 / §11 | describes a "separate, deliberately small specification" deriving `InferredAcceptedDomain` | **Dissolved** by the 2026-07-24 erratum (compendium Appendix M): no accepted-domain object exists |
| region-table header | title says patch 0.3.1; body describes 0.3.2 | body is the later text |
| compendium C§7 | generic `x/0 → Indeterminate(_/0)` marker model | a **later ruling** (`HANDOVER-indeterminate-…-2026-07-24.md` Part XI, 2026-07-27) adopts specific `a/0` identity + `Numeric`; **not yet carried into any spec** — unresolved, author-owned |
| grounding v0.5 header | "DRAFT … nothing herein is closed until stamped" | compendium 1.0.18 records it DESIGN-CLOSED; the stamp record itself is **not present** — author-owned |

---

## 2. Document status register

| Document | Status | Note |
|---|---|---|
| **`IMPLEMENTATION-STATUS.md`** (this file) | **CURRENT** | The implementation-status authority |
| The 19 manifest'd specs (§1) | **CURRENT** | Design authority; staleness recorded above, not edited |
| `DECISIONS.md` | **CURRENT** as an append-only provenance log | Newest dated entry wins per topic; **individual older entries are HISTORICAL** and must not be read as present-tense guidance |
| `NEXT-completion-plan.md` | **CURRENT (subordinate)** | Tier structure and the owed/liveness synthesis stand; where it conflicts with this file, this file wins |
| `PROGRESS.md` | **SUPERSEDED** | Snapshot, doc-sync rows, "§6 next increments", and the increment-ledger detail are stale (they describe the retired app-induction-tail plan, cite `SAFETY_STACK` which does not exist, and list 10 analyzer modules where there are 13). Retained as history |
| `OwedItems.md` | **SUPERSEDED as guidance; CURRENT as an owed catalogue** | §0.1 is the later framing; §0.1-history and the "swap is DONE / LANDED" passages are **HISTORICAL**. Item lists remain useful; ordering/priority claims do not bind |
| `NEXT-owed-breadth-foundation-map.md` | **SUPERSEDED** | Its F0-before-demand-core ordering was **incorrect** (see §5) and its "replace-and-rebuild" framing is not authorized (§5). Diagnosis of the missing foundation stands as history |
| `NEXT-F0-operation-rulebook-draft.md` | **HISTORICAL** | Design record for a feature that is now built |
| `NEXT-spec-audit-accepted-domains-phase1.md`, `NEXT-architecture-review-*.md`, `NEXT-implementation-finding-accepted-domains.md` | **HISTORICAL** | Superseded by the 2026-07-24 errata and later work |
| `NEXT-implementation-review-Archive{4,5,7,8,9,10}.md`, `NEXT-analyzer-core-checkpoint-review-8.1a-8.1c.md`, `NEXT-implementation-progress-review-Archive4-updated.md` | **HISTORICAL** | Author review rounds; record only |
| `next-mu-canonicalization-specification-v0-1.md` | **HISTORICAL** | Superseded by v0.5 (manifest'd) |
| `next-semantics-companion-v0-1-update-review.md`, `next-grounding-landing-ledger-patches-1-0-18.md` | **HISTORICAL** | Review/patch records |

---

## 3. Quarantined — code that is NON-AUTHORITATIVE

These paths **execute and are tested, but may return a wrong verdict**. No result from them may be
treated as a settled judgment, and no new work may be layered on them.

| Path | Status | Nature |
|---|---|---|
| `analyzer::bodycheck` recursive body checker — `body_summary` → `body_check` → `check_recursive_body`, the callee-keyed `ACTIVE` cutoff, `grow`, `reachable_rows` | **KNOWN UNSOUND** | Forward reaching-domain accumulation (see §5, forbidden). Documented false rejection **and** false acceptances (§4). It is the wired path of `analyze_apply` today |
| `BodySummary::cycle()` supplying `Completion::Produces` | **KNOWN UNSOUND** | A cycle *assumption* cannot claim production |
| Safety-unproven severity | **RESOLVED 2026-07-31 — RULED [user]: it is an `Error`** | Aligned with late-resolution §5 (*"safety-unproven → compile error, un-suppressible"*). Ten emission sites flipped. **Completion (`MayFallThrough`) deliberately excluded** — a different judgment class (application §1.6). Exposed six pre-existing false positives (§4) that `Warning` had been hiding |
| `analyze_apply`'s `summary.errors()` call-site filter | **NOW LIVE — it discards blocking findings** | Since unproven is an `Error`, this filter no longer merely loses a message: it is the boundary at which a callee body's blocking findings would be dropped. Currently they pass (they are Errors); the filter should be revisited when the three voices are carried structurally |
| `analyzer::grounding` — `ground()` / `drift_away` / `Verdict` | **CORRECTED 2026-07-31; still UNWIRED** | The §6 slice is complete: forced-path selection, witness-bearing `Refuted(Refutation)`, superseded header claim removed. Its *coverage* gaps (GR-18 point-base, peel-k, oscillator, closed-orbit, §8 WorldDecided, multi-param mutual) remain owed — those are incompleteness (→ `Unproven`), not unsoundness. **Wiring still requires separate authorization** |
| `analyzer::safety` — the **candidate graph** (§6 / C§13.2a) | **BUILT, not yet wired** | Discovery closure (candidates + edges, **no verification during discovery**) → SCC collapse → reverse-topological → **one joint vector pass** per component, with §5's partition rule as each member's verification. Finiteness = C§13.3(2)'s shape cutoff + domain-covering reuse, **not** a budget. Measured: mutual `f→g→f` **Refuted**; `countDown` over its declared domain **Proven**; a divergent body **Proven and terminating**; an uncovered concrete chain **cut off, not expanded**. **Not the wired path** — `analyze_apply` still calls `bodycheck::body_summary`, which is why nine pins are unmoved |
| `oracle::mu` — **Algorithm A group canonicalization** | **BUILT but UNWIRED** (`#![allow(dead_code)]`) | SCC grouping (Tarjan over the binding-reference graph), positional μ-refs `⟨d,i⟩`, law 1/3 (only genuine cycles become groups), law 5 canonical slot order. Its own header: *"No runtime consumer yet."* **Deferred inside it: law 2 (nested-binder merge) and law 4 (bisimulation slot merging / partition refinement — spec step 3)**, on which the MU-14/15/16 identity claims rest |
| `oracle::canon` — per-lambda shape | **BUILT, wired** | α-renaming (`$0`), capture slots (`@cap0`), polynomial NF. This is what `make_closure` (`eval.rs:239`) actually calls |
| **The join between them** | **MISSING — this is 2b's real blocker** | `mu::canonicalize_group` takes `(name, Expr)` binding lists; `make_closure` builds closures from a single `Lambda` + env and stores the **raw** body. So no constructed closure knows it belongs to a μ-group, and a mutual partner remains an ordinary *capture* rather than a μ-ref. The group structure is computed and discarded |
| `analyzer::induction` pipeline — candidate discovery, domain derivation (`obligation::accepted_domain`, a **dissolved** concept), `summarize_instance` consumption, same-arity domain propagation (marked interim), candidate-to-candidate-only edges | **NON-AUTHORITATIVE** | Not a ready foundation. **Its independently valid SCC utilities (e.g. `scc_reverse_topo`, the reverse-topological order) may be reused.** There is **no** authorized broad replace-and-rebuild project |

**Not quarantined** (trusted): the lexer, parser, desugar, oracle interpreter, normalization harness,
value/interner layer, and the contract algebra including `contract::numeric` + `contract::operation`
(F0), whose soundness is brute-tested against the oracle.

---

## 4. Known failing gates — **PARKED 2026-07-31** (4 `#[ignore]`d in lib)

Acceptance criteria, not bugs to route around. **All four are parked**: none is to be worked until
its own blocker below is built. They are **not** parked under one cause — filing them all under
"canonicalization" would set up a false expectation, and the moment Algorithm A lands and three of
them still fail is exactly when someone reaches for machinery to close the gap.

| Gate | How it fails | Its actual blocker |
|---|---|---|
| **2b** mutual/helper domain-changing recursion (**false acceptance**, reports `[]`) | `f → g → f`: the loop is discoverable only by chasing name → value → body, so the changed domain never returns to `f`'s trapping row | **μ-canonicalization Algorithm A** — the group/SCC layer. In canonical μ-form the pair is **one group** with entry slots and the mutual edge is a **μ-marker**, structurally visible. `canon.rs`'s own header says this layer "ships with the analyzer"; it has not |
| **1b** coarse recursive target (**false rejection**) | `bodycheck.rs:213` binds the parameter to the **row region**, so `x-1` becomes "anything above −1" | **RE-FILED 2026-07-31 (oracle-verified): grounding §4 exact-singleton fact chains** — *not* the fact graph. `f(0.5)` genuinely **traps**, and `0.5` sits in the **same row** as `1`, so `BodySafe(f, {row x>0})` is **false**. No row-set-keyed fact can prove `f(1)` safe; it needs the exact chain `1 → 0`, a domain finer than a row |
| **2a** multi-parameter domain-changing recursion (**false acceptance**, reports `[]`) | no multi-parameter branch map, so the whole-body fallback **cuts** the recursion and never sees `a` become a String | **region-table §5** (argument-tuple projection), plus the same fact bound |
| **3** recursive fall-through completion lost (reports `Produces`) | the cycle assumption *asserts* `completion: Produces` rather than settling it | **completion carried on the fact** (the same fact layer as 1b) — not canonicalization |

### Additionally pinned 2026-07-31 — six **false positives** exposed by the severity ruling

`factorial` / `countDown` / the induction + summary recursion tests / `safety.rs`'s
`declared_domain_recursion_proves_by_induction`. All assert that an ordinary **safe** program is
accepted; all now fail.

- **Root:** `bodycheck.rs:213` computes the recursive target under the **row region**, growing the
  reaching domain back up to `Top`, so `n - 1` stops being provably a Number. Verified the algebra
  is innocent — `Difference(Number, {0}) ⊑ Number` is *Proven*; only `Difference(Top, {0})` is not.
  **Same root as blocker 1b.**
- **Not a regression.** They were green *only because* the finding was a `Warning` that
  `analyze_apply`'s `errors()` filter discarded. The honest state is that the analyzer **cannot
  currently prove `factorial` safe** — and never could.
- **Consequence:** blocker **1b now gates six further tests**, all ordinary safe programs.

**Do not un-ignore any of these by other means.** Making one green without its blocker is a
regression dressed as progress — and in particular, do **not** fix these six by reverting the
severity ruling or by adding widening/reaching machinery.

Conformance additionally holds 13 `#[ignore]`s (6 Phase A · 5 module system · MU-18 · M-04).

---

## 5. Forbidden machinery (binding)

1. **No reaching-domain fixpoint, no widening, no candidate synthesis, and no
   grounding-as-analysis-cutoff.** (Grounding is a behavioural judgment; C§13.3 bounds the symbolic
   procedure independently.)
2. **Imprecision produces `unproven` — never another prerequisite.** A sound-but-coarse rule
   returning unproven is a correct outcome; it is not a reason to build a preceding layer. *(This
   supersedes the foundation map's F0-before-demand-core ordering, which rested on the opposite
   assumption.)*
3. **Fact domain `I` and demanded contract `C` remain distinct** — everywhere, as separate fields.
   `I` is the input/row domain a fact is claimed under; `C` is the demanded contract. An operand
   obligation is **not** automatically a fact's input domain.
4. **No broad replace-and-rebuild project.** The quarantined paths are non-authoritative; that is a
   trust statement, not a licence for a sweeping rewrite. Independently valid utilities may be reused.
5. Previously killed by ruling and still killed: fuel of any kind in normative analysis, tier-0
   evaluation-as-grounding, constructed-witness inventories, supplied-measure annotations,
   invariant synthesis, generic state-carrier framing (grounding §14).

---


### Mechanical enforcement — `tests/machinery_gate.rs` (added 2026-07-31)

The five boundaries above were prose only, and prose did not hold them: a forward-reaching
/widening engine was built on 2026-07-31, passed all four blockers, and was reverted whole.
Four checks now enforce the part a machine can see. **Each was verified to fail on an
injected violation before landing** — a gate that cannot fire is not a gate.

1. `src/analyzer/summary.rs` (the reverted engine) and sibling names must not exist.
2. The quarantined reaching core — `check_recursive_body`, `reachable_rows`, `grow` — appears
   only inside `src/analyzer/bodycheck.rs`.
3. The fact machinery (`safety`, `induction`, `refute`, `obligation`, `grounding`) carries no
   *code* reference to `bodycheck`; doc comments are stripped first, since documenting the
   quarantine is expected.
4. `callee_completion` still consults the settled completion fact — `Produces` at a call site
   may not be asserted by a coarse body pass (a false **accept**, the dangerous direction).

**Scope, stated rather than glossed:** the gate catches a literal repeat and the spread of the
quarantined engine. It does **not** catch a renamed reimplementation. That stays a review
obligation, under the standing rule that when a pinned blocker goes green the **mechanism** is
reported, not merely the outcome. If a check fires, the fix is never to relax it — imprecision
yields `unproven`, never another prerequisite and never a growth loop.


### T1.4 (the wiring) — ATTEMPTED 2026-08-01, REVERTED. Gated on a per-node in-progress key.

The swap of `analyze_apply` off `bodycheck::body_summary` and onto the settled facts was
attempted and reverted whole. All three inputs now exist (`safety::prove` for findings,
`safety::completes` for completion, and a partition-based `body_outcome` for `produced`),
so the blocker is no longer a missing input.

**The blocker is re-entrancy granularity.** A settlement analyzes bodies, whose calls reach
`analyze_apply`, which would launch a nested settlement. Guarding that with the existing
**global `SETTLING` boolean is unsound**: during any settlement, *every* nested `prove` gets
answered from the hypotheses — including callees that are not members of the graph and have
no hypothesis at all. Those return `Unproven(vec![])`, silently dropping a real transitive
trap. Measured effect: 10 lib failures, of which
`safety::graph_tests::mutual_recursion_closes_via_the_joint_vector_pass` reported **Proven
where it must refute** — a false accept, the dangerous direction.

**What it needs:** the in-progress key must be the fact node `(instance, I)`, not a global
flag — so a member resolves through its hypothesis (vector induction, correct) while a
non-member is genuinely verified. That is C§13.4's proven-fact cache keyed
`(analysis instance, row-set I, demanded C)`, and the quarantined `bodycheck` carried the
weaker per-callee form of it in its `ACTIVE` stack.

**Consequence for ordering:** C§13.4's fact cache moves *before* T1.4, not after. The
canonicalizer lands with that cache (it is the key's consumer), so the two travel together.
No part of the attempt was kept — `body_outcome` included — because unused machinery ahead
of its consumer is the pattern this project is recovering from.

## 6a. In progress — `BodySafe(instance, I)` (authorized once §6 completed)

**Landed:** the safety fact keyed `(instance, I)`, `I` taken from the call site (never synthesized),
and **assume-and-check** discharge so a recursive reference resolves through the fact instead of
unfolding. Proven natively for the clean case (`countDown` over a declared domain).

**Not landed — the named gap:** a recursive call whose domain is *not* contained in `I` has no
principled bound yet, so it falls back to the quarantined checker. The spec's answer is `I` ranging
over the instance's **finite row-set lattice** (C§13.2 / GR-03) — that is what makes the fact graph
finite. Until it exists the four blockers stay pinned.

**A measurement discipline worth keeping:** a probe through the new entry point answered all four
blockers correctly, but the **pinned tests still failed** — the probe was measuring two cutoffs
composing, not the mechanism. Always check the pinned gate, never a convenience probe.

---

## 6. The authorized slice — ✅ COMPLETE 2026-07-31

> **Status: done.** All three corrections landed; grounding remains **unwired**; no forbidden
> machinery introduced; existing suites unchanged. **The next slice is not yet authorized** —
> `BodySafe(instance, I)` was gated on "this rebaseline and the grounding gates", both of which are
> now complete, but the ordering question (whether the program-level entry point / demand core come
> first, per `NEXT-completion-plan.md` T1.1–T1.2) is open and author-owned.

**Correct `analyzer::grounding` while it remains unwired.** Nothing else is authorized; in
particular **`BodySafe(instance, I)` must not be started** until this is complete.

1. **Forced-path selection.** A recursive transition may be admitted only when the path to it is
   *forced* — exact selection, or another applicable must-condition, at every step. Syntactic
   presence of a self-call is not sufficient (this is the G-BUG cause).
2. **Persistent refutation evidence.** Every refutation must carry its admitted represented-exact
   **root witness and certificate**, persistently. *(The Rust representation is not predetermined.)*
3. **Remove the superseded claim** in the module header that grounding bounds or terminates
   analyzer unfolding / replaces widening as the analysis's termination bound.

**Done means:** G-BUG's gate passes on the mechanism above; grounding remains **unwired**; no
forbidden machinery introduced; existing suites unchanged. — **All satisfied.** Detail in
`DECISIONS.md` (2026-07-31 grounding-correction entry).

---

## 7. Test baseline (measured 2026-08-01, not inherited)

| Suite | Result |
|---|---|
| `cargo test --lib` | **410 passed, 0 failed, 10 ignored** (4 parked blockers + 6 pinned false positives) |
| `cargo test --test conformance` | **111 passed, 0 failed, 13 ignored** |
| `cargo test --test machinery_gate` | **4 passed, 0 failed** |
| `cargo clippy --all-targets` | **0 warnings** |
| `shasum -c MANIFEST.sha256.txt` | **19/19 OK** |

Earlier counts appearing in other documents (323 / 371 / 377 / 380 / 383 / 384 / 396 / 409) are
**HISTORICAL**; this table is current.
**Green ≠ sound:** the suite does not cover the §4 gates, which is why they are pinned.
