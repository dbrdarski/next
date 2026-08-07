> ## ⚠️ STATUS: **SUPERSEDED as guidance · CURRENT as an owed catalogue**
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. The item lists
> here remain useful; **ordering and priority claims in this file do not bind.** Within it, §0.1 is
> the later framing, while §0.1-history and any "the swap is DONE / LANDED" passages are
> **HISTORICAL**. Historical content is deliberately left unedited.

# OwedItems.md — open gaps, reconciled to the specs

**Maintainer file (not spec).** This is Claude Code's development registry. The
**canonical library (manifest'd specs) is the source of truth**; when this file
disagrees with a spec, the spec wins and this file is what's stale.

> Rebaselined **2026-07-30** against `MANIFEST.sha256.txt` (19 files verify;
> **compendium 1.0.18 — grounding landing**). The prior rebase (2026-07-24, "14
> files") predated the region-table + grounding landings and is superseded.

---

## 0. The accepted-domain recovery — context for everything below

A design review (`NEXT-architecture-review-…md`) and its spec-first audit
(`NEXT-spec-audit-accepted-domains-phase1.md`, author-agreed 2026-07-26) found the
analyzer's **call-site body-safety** machinery was built at the wrong layer. The
specs describe a **demand core → symbolic summary template (per shape) → instantiated
region table (per instance) → call-site body check** substrate — the skipped Part-I
`demand core` build step. `analyze_apply` reconstructed that forward, at call sites,
which is why it grew instance/domain identity, widening, evidence downgrades, and an
admitted-domain basis it never needed.

**Dissolved by errata (2026-07-24) — OFF the owed list, retired:**
- **`InferredAcceptedDomain`** — **no materialized accepted-domain object exists.**
  C§12.1 [E-6]: the safe-input set is *semantic, not a materialized contract*. E3
  [E-7]: *"no intermediate stored 'accepted contract'."* E11 [E-8]: `where` is
  `BodySafe(instance, DeclaredInput) = proven` (run the ordinary body check under the
  declared input), **not** `DeclaredInput ⊑ InferredAcceptedDomain`.
- **Q4 (eager vs lazy materialization)** — moot: nothing is materialized. The
  mechanism is region-table reachability × the ordinary C§7 body demands, adjudicated
  per C§13.1 (subscriptions/forward, three-valued at origin); eager preimage is *an
  optimization*. There is **no separate accepted-domain spec** — the region-table §6
  "separate small spec" folds away because there is no object to spec.

**Verified development state (code read + suite run, 2026-07-30):** 323 lib + 111
conformance (13 ignored) passing, clippy 0. Analyzer = 10 modules (`mod` 1126,
`induction` 563, `domain` 493, `application` 293, `bodywalk` 278, `refute` 130,
`inventory` 98, `outcome` 83, `obligation` 78, `tests` 2220 LOC). **No region-table /
demand-core code exists — the recovery build has not started.**

**Superseded, to DELETE (recovery Phase 3), NOT to refine — verified present unless
noted:** `accepted_domain` (`obligation.rs` + `induction.rs`); `body_safety`
(`mod.rs`); `instance_body_summary` / `InstanceBodySummary`, `domain_admitted`,
`kind_abstraction` (`Contract::kind_abstraction`, `contract/mod.rs`), `literal_values`,
`ACTIVE_BODIES` (all `induction.rs`); `summarize_instance` (`outcome.rs`) in its
per-call body-analysis role. **`SAFETY_STACK` does NOT exist** (the review named it;
it was superseded in Archive7→8 — my earlier draft wrongly listed it). Nothing is
deleted until the region-table replacement passes the behaviours the current tests
encode (`bad()` rejected, `f("hello")` rejected, `helper(0)` accepted, divergence
terminates, no user function executed).

**Kept (audit §5 / review §10) — but *entangled*, not a clean file split:**
`joint_vector_pass` (return-fact SCC induction, `induction.rs`/`refute.rs`);
`analyze_application` (correlated joint driver, `application.rs`); the `Hypothesis`
instance+domain key (`induction.rs`); dead-arm/path narrowing (`analyze_match`,
`mod.rs`); `callee_targets`/`build_inventory`/`prove_subcontract_a`. **The keep and
delete sets live in the same modules** (`induction.rs` holds both `joint_vector_pass`
and `ACTIVE_BODIES`/`domain_admitted`), so Phase 3 is function-level disentangling, not
file removal. **And the keep-set is not keep-as-is:** `joint_vector_pass`/`call_return`
currently consume `summarize_instance`'s per-call body analysis — under the recovery
the SCC induction stays but is **re-plumbed** onto the region-table/body-check summary.
Also kept: the `segment_nullable` structural fix; fuel out of normative analysis; no
oracle execution of user functions.

### 0.1 [2026-07-31 — SUPERSEDES the “swap is DONE” framing below] The body check imports because a foundation is OWED

**The reaching-domain body check is the imported (abstract-interpretation) shape, not the native
one.** An SCC extension of it (`analyzer/summary.rs` + multi-position region tables) closed all four
Archive-11 blockers this session, then was **reverted whole** — it added a forward reaching-domain
fixpoint + Kind-collapse **widening**, which is foreign (Principle 7; late-resolution; "widening is
foreign"). The root cause: the body check stands on a **skipped foundation**. Recovery order is
*demand core → template → region table → body check*; the region table + body check exist but the
**demand core (C§13.1) was never built**, so recursion can't close natively and gets a forward-solve
prosthetic. **The single-param `check_recursive_body` reaching accumulation (07-30) is the same
imported shape** — less egregious (no widening) but still forward reaching; it is on the *delete*
list too, replaced by domain-indexed safety facts + induction.

**Owed foundation (dependency order), full map in `NEXT-owed-breadth-foundation-map.md`:**
- **F1 `OperationOutcome`** (C§7/C§16 obl.3) — reshape `analyze_operation` from `OpResult{safety,
  output}` to `OperationOutcome{safety, produced, completion}`. (Also §2 below.)
- **F2 demand core** (C§13.1) — backward subscription + forward resolution + three-valued origin
  adjudication. The skipped Part-I step. Not built.
- **F3 domain-indexed safety facts** (C§13.2a) — `BodySafe(instance, I)` settled by the **kept**
  `joint_vector_pass` induction (today wired only to return facts). Closes recursive/mutual safety on
  a fact, no reaching, no widening; domain lattice = region partition (+ grounding A-NEG later).

**Acceptance:** the four blockers un-ignore only when they pass with the region table + safety-fact
induction and **no forward reaching fixpoint / no widening exist in the tree** (grep gate:
`summary.rs`, `check_recursive_body`, `reachable_rows`, `grow_pos` all absent). The re-pinned
`#[ignore]` notes name this. **Do not import to make them green.**

---

### 0.1-history The swap is DONE (2026-07-30, summary-over-partition, no widening) — reframed above

**Status: LANDED.** `analyze_apply` Known-callee now runs `bodycheck::body_summary` (the
summary-over-partition check: §4a shape cutoff + `check_recursive_body`'s reachable-rows ×
reaching domains), replacing `instance_body_summary`. Full suite green, no hang; the
domain-changing trap rejects and the two growing-domain tests terminate by folding into the
finite region partition — **no widening, nothing foreign**. The dead widening machinery is
**deleted** (−288 lines: `instance_body_summary`, `domain_admitted`, `downgrade`,
`ACTIVE_BODIES`, `literal_values`/`collect_consts`); `kind_abstraction` stays only for
`subcontract`'s kind fallback. **Remaining: multi-parameter region tables (§5).** Attempted 2026-07-30 —
`region_table_multi` (per-position projection) is correct and catches multi-param
domain-changing traps, but the summary check hit a precision/termination tension
(row-region targets coarsen *carried* positions to `Top` → false Errors on accumulators;
reaching-domain targets are precise but hang on concrete numeric chains). Reverted to the
sound whole-body fallback; the resolution (fold a position into its row region only when it
grows) is in `DECISIONS.md`. The multi-revision diagnosis history is kept below.

---

### 0.1-history The swap needs grounding for *termination* — finding 2026-07-30 (superseded)

The swap (rewire `analyze_apply` Known-callee from `instance_body_summary` to
`body_summary`, then delete the superseded machinery) was **attempted and reverted**.
The diagnosis went through two readings; the second is the verified one.

**First reading (imprecise).** Wiring cost one failing test,
`body_safety::a_recursive_call_over_a_new_domain_is_analyzed`, on
`f = (x) => x==0 ? f("x") : x+1` at `f(0)` (which traps at runtime via `"x" + 1`). I
attributed this to a missing grounding arc "deriving the recursion domain."

**Corrected reading (verified).** That failure was **not** a grounding gap — it was a
**wrong cycle key** in `body_summary`'s guard. The first cut keyed on the closure
**instance** alone, so it cut the `f("x")` edge (f already active) and dropped the trap.
The spec (C§13.2a / grounding **GR-07**: nodes are *"instance × row/domain under the
region partition"*) and the old `ACTIVE_BODIES` both key the cycle on **(instance,
domain)**. `f(0)` and `f("x")` are **distinct nodes** → `f("x")` is analyzed, `"x"+1`
refutes, `f(0)` rejected. **Fixed** (`bodycheck.rs`, `ACTIVE: Vec<(ValueRef,
Vec<Contract>)>`). This example's demand chain **terminates on its own** (`f("x")`
reaches `x+1`, no further recursion) — no bound, no grounding needed. Grounding is a
*termination* judgment (GR-05 descent/landing, GR-11 closed-orbit refutation), and this
example never fails to terminate — it crashes. So grounding was the wrong tool for it.

**What actually gates the swap (verified empirically).** Wiring `body_summary` *with the
corrected key* **hangs** on `a_growing_union_recursive_domain_terminates` and
`recursive_domains::a_growing_non_singleton_recursive_domain_terminates`. The correct key
(rightly) refuses to cut distinct nodes, and a domain that **grows without end**
(`f(Range(1,3)) → f(Range(2,5)) → …`) presents an unbounded stream of distinct nodes → the
analysis never converges. The old machine bounds this with **widening** (`domain_admitted`
+ `kind_abstraction`).

**Correction (2026-07-30, verified against the specs — widening is FOREIGN; the bug is that
`bodycheck.rs` unfolds).** Two prior framings were wrong: grounding is *not* the bound
(the two hanging tests are non-terminating programs — `f = (x,y) => f(x+y,y)`,
`f = (x,b) => f(b?x:0,b)` — so grounding correctly returns Unproven; test
`baseless_divergent_recursions_are_unproven_not_grounded`), **and** re-introducing widening
was the wrong instinct. NEXT does **not** analyze recursion by unfolding an abstract
interpreter to a fixpoint; widening is a *foreign* (abstract-interpretation) mechanism the
design deliberately avoids. The spec-verified native mechanism:

- **Don't unfold — summarize.** Region-table §8: *"the recursion move: analyze the
  suspension, don't expand it."* Compendium §10.6: a return fact is a summary — *"for
  inputs ⊑ I, the return ⊑ C"*, settled jointly (SCC/vector), never unrolled.
- **Shape-repeat cutoff bounds the instance chain** (app-induction §4a): the instance
  inventory is a finite closure; *"target shape already in the sequence → no admission…
  path depth ≤ the program's shape count."* **Built** — `inventory.rs` /
  `reachable_closures`.
- **Domains are the finite region partition** (app-induction §5 "partition rule" + GR-03's
  *"instance's finite row-set lattice"*): facts index `I ⊆ GroundedRows`; a growing
  concrete domain folds into a fixed row and the chain closes. **Built** — `region.rs`.
  The trap soundness is intrinsic: each reachable row's result is checked **under the
  row's own domain** (e.g. the `else`/`n≠0` row covers 5, so a deep `n==5` trap is caught
  without tracing concrete `f(10)→f(9)→…`).
- **Grounding derives `GroundedRows`** (the safe/reachable domain) and **refutation** stops
  the divergent case. **Built** — `grounding.rs` (G-1…G-8).

**So the "design fork" (keep widening vs row-set lattice) is retired — widening is not an
option; the row-set/partition mechanism is the only one, and its substrate is already
built.** The real bug: `bodycheck.rs` **unfolds** (re-enters `body_summary` on recursive
calls over concrete/growing domains). It must become a **summary-over-partition body
check**: for a recursive callee, a **reachable-rows fixpoint** over `region.rs`'s finite
partition — check each reachable row's result under its row domain, summarize recursive
calls (shape-repeat cutoff), consult grounding/refutation for completion. This is the
**demand core** (OwedItems §1) — a genuine rebuild of the body check from *unfolding* to
*summary*, not a wire, but it reuses the built substrate and introduces nothing foreign.

- Owed sub-pieces: multi-parameter region tables (§5 arg-tuple projection — the two growing
  tests are 2-param); the **A-NEG derived-input-domain** output from grounding (the domain
  the body is checked under); then wire + delete the old `instance_body_summary` /
  `domain_admitted` / `kind_abstraction` (the crude widening the partition rule replaces).

---

## 1. Design-closed — implementation (and §16 discharge) owed

All specified; code state varies (verified 2026-07-30): **demand core, region-table,
grounding, μ-binder — no code yet** (the Phase-2 build); **app-induction — machinery
exists but at the superseded call-site layer** (§0, re-plumb/delete); **tuple family —
built in code, §16 proofs owed**.

- **Demand core** (Part I build step; C§13.1) — backward subscriptions + forward
  resolution through the operation rules, three-valued adjudication at origin. The
  substrate the recovery builds first.
- **Region-table computation** — `next-region-table-specification-v0-3.md` (0.3.1–0.3.2,
  *architecturally closed; C§17 item **discharged***). **§2–§4 computation BUILT**
  (`analyzer/region.rs`, 2026-07-30): `region_table` (cases (a) exact-vs-constant + (d)
  total fallback; pattern∩guard) + the `select` remainder walk (singleton fast path).
  Capture-free single-parameter. The **call-site body check** `BodySafe(instance, arg)`
  is **BUILT** too (`analyzer/bodycheck.rs`, 2026-07-30): consumes the table, binds the
  parameter per selected row, analyzes each result with the RT-14 witness discipline
  (only a definitely-reached row refutes). Gates 14.1–14.3 (`bad()`/`f("hello")`
  rejected, `helper(0)` accepted, path-sensitive). Owed: cases (b)/(c) over captures,
  arg-tuple projection (§5, multi-param), the guards' own path demands, the
  annotated-tuple **instance cache** (C§13.4), and the **wiring**. The `body_summary`
  wrapper (`{produced, completion, findings}` + `errors()`) is built and green
  standalone, but the **swap is blocked on grounding** — see §0.1. Compound/negated
  guards currently read as case (d) (sound).
- **Grounding v1** (the termination bound) — `next-grounding-specification-v0-5.md` (0.5.1,
  DESIGN-CLOSED, compendium 1.0.18; GR-01…GR-30; Phase GR suite; *ACCEPTED pending author
  stamp* — judgment rules stable, only the P-1 unproven-consequence open). **G-1 BUILT**
  (`analyzer/grounding.rs`, 2026-07-30): `ground(callee, domain) → {Grounded, Refuted,
  Unproven}`, the numeric constant-drift descent certificate (GR-05) — well-founded
  descent (negative-constant drift, floor δ) + landing (half-line structural / point-base
  grid for the unit-drift integer lattice). **G-2 BUILT** (drift-away refutation, §7 /
  GR-23a): from an admitted represented-exact witness (`Equals(v)`), a single forced linear
  descent whose forward lattice misses every base region → `Refuted` (specimen 12: witness
  1 refuted, witness 2 Unproven — parity-split; a broad domain has no admitted witness →
  Unproven, GR-22). **G-3/G-4 BUILT** (program-expressed linear-measure descent, §6
  GR-15a/16): a base arm's half-line stop `E ⋈ c` with a **linear** measure `E` over the
  params, drift read by **substitute-and-normalize** (own `LinComb`/`linear_form`); grounds
  `2a+b <= 0 ? … : f(a-1, b+1)` where no single argument descends; coefficient-0 positions
  carried; two-varying-side relational stops [permanent]-unprovable. **G-5 BUILT**
  (lexicographic descent, §5 GR-13/14 — path-sensitive): a dictionary of argument positions
  that lex-decreases per call, each decreasing position bounded below by a path guard
  (component-grain landing); the reset pattern (`a<=0 ? b : b<=0 ? f(a-1,10) : f(a,b-1)`)
  grounds; relational floors (`a==b` stop) Unproven. Unified the self-call walker into a
  path-threading `walk` carrying per-param lower-bound flags. **G-6 BUILT** (structural
  descent, §2b): peel recursion `l :: { [] => …; [h, ...rest] => f(rest) }` — the peeled
  tuple parameter's length is intrinsically `GE(0) ∧ Mod(1,0)` and strictly descends, so it
  terminates with no domain and no base check (exhaustiveness is E10's concern); the
  accumulator variant grounds, rebuild-the-whole (`f([h, ...rest])`) Unproven. **G-7 BUILT**
  (constant-drift refutation generalized): `drift_away` refutes any constant drift —
  descending (GR-23a), ascending, and the **period-1 self-loop** `f(n)` (GR-11 degenerate
  closed orbit); one forced linear path, witness-gated. **G-8 BUILT** (mutual recursion,
  GR-07): the reachable closure group is the SCC; if every cross-call decreases a shared
  single-param measure and every recursive member has a descending half-line base, every
  cycle composes to a decrease → grounded (`isEven`/`isOdd` on `n <= 0`); the enumeration-free
  per-edge sufficient case. Generalized the self-call walker to a group (`resolves_to_target`).
  `ground` is three-voiced. Candidate-locality (GR-04). **Owed:** point-base / **Ackermann**
  (GR-18 grid + domain — `==0` stops give no lower bound), **peel-k grid** (base must cover
  lengths `0..k-1`), `restrict_len` structural facts (GR-08), nonlinear measures,
  **oscillator** cycle composition (mixed-sign, GR-07), general **closed-orbit cycle**
  refutation (GR-11; specimen 22b), §4 exact-singleton chains, §8 WorldDecided; multi-param
  mutual;
  the **wiring** into the body check (the swap gate, task #50); §13/§16 discharge (exact-chain
  bound theorem; lex joint-settlement; multigraph decomposition lemma; per-rule soundness;
  GR-27 preservation check). This is A-NEG's second domain source.
- **Application & induction v0.8 (+0.8.2)** — design-closed (*"the design condition
  dissolved when the tuple family closed"*, C§13.2). Implementation + C§16 discharge
  owed. The 0.8.2 GR-26 effect-world seat row (consumes, never establishes).
- **μ-binder canonicalization v0.5** — Algorithm A full (SCC grouping / group
  templates). Runtime uses shared-env late binding; the μ-structure form is the
  destination (relevant to the body-walk's capture resolution).
- **Tuple-length family** — §1–§5 **built** in code; **§16 discharge (proofs)** owed,
  plus the three precision tails: the §5 finite-state lift to string *contracts* (a
  string-length contract form does not exist yet); `restrict_len`'s recursive
  certified-unfolding rule; §4's structured `ElementRefutation` witness (the complete
  inhabitant is a stronger witness — presentation only).

## 2. Registered implementation drift (spec settled, code carries an older shape)

- **C§16 obligation-3 `OperationOutcome` interface [1.0.7]** — every transfer rule
  should return `OperationOutcome { safety, produced: AnalysisContract, completion }`.
  The `AnalysisContract` domain exists (`analyzer/domain.rs`); the **primitive**
  `analyze_operation` still returns the pre-upgrade `OpResult { safety, output }`. The
  reshape lands with the region-table/demand-core rebuild.
- **Universal interning (μ v0.5 §6) — DISCHARGED 2026-08-01.** Resolved closures
  use the shallow `(canonical-code pointer, capture pointers/location atoms)` key;
  recursive SCCs stay unobservable through their construction window and close by
  fingerprint-bucket probe plus exact Algorithm-B verification. Runtime `==` is a
  pointer test. MU-18 is live and green. The broader layer-2 GroupTemplate work in
  §1 remains separately owed; this item no longer belongs to implementation drift.
- **`Record(fields, Exact | Open)`** — openness is a Record-contract parameter
  (`HasField(k) ≡ Record({k: Top}, Open)`). I model exact `Record` + separate
  `HasField`; membership coincides, but open-record patterns lose per-field contracts.
  Sound, precision-lossy.
- **`Known(∅)` normalization [analyzer review, 07-25]** — app-induction normalizes
  `(C, Known(∅)) → Bottom` at function positions; my `AnalysisContract::leaf` collapses
  only when `C` is function-only (`(Number, Known(∅)) → Number`). Reviewer: defensible
  if AC represents arbitrary values, but a spec wording reconciliation is owed. Not
  unsound. (Rides the app-induction rebuild; the AC domain is in the *keep* set.)

## 3. Still owed in the docs (Compendium C§17 "Owed", patch 1.0.18)

> **F0 BUILT (2026-07-31) — the operation rulebook, whole.** Design drafted and author-reviewed
> first (`NEXT-F0-operation-rulebook-draft.md`), then built: safety **and** image for all 13
> operations over every contract form. `contract/numeric.rs` (new) holds the shared numeric
> abstraction (`Interval`/`Bound` extracted from `subcontract.rs` + `Congruence` + `NumAbs`), with
> the **two conversions kept separate** and the direction asymmetry as a normative module note.
> Half-lines now compose; congruence (hence **integrality**) survives `±` and scaling; `×`/`/` use
> extended ±∞ arithmetic; `Geo × exact` stays `Geo`; comparisons decide when the bounds decide;
> the safety table now admits Indeterminate in arithmetic (propagates) but not in comparisons
> (traps). The audit is the **matrix**: the sweep grid went 9 → 27 forms with sign variants and
> caught a real zero-divisor-endpoint panic; five `rulebook_*` tests assert precision separately.
> **Deliberate incompleteness is listed in `operation.rs`'s module doc** (Geo beyond scaling; Mod
> through `×`-non-constant/`/`/`%`/`**`; `**` both-non-singleton; zero divisor endpoint; strictness
> through `×`/`/`; `Difference` non-singleton exclusion; `Union` as hull not distributed — the one
> open precision question). **Still owed here:** the **string-length lift** through `+` (needs the
> tuple family's §5 string-contract form, owed there); **compound-scrutinee regionalization** is
> *not* a gap — region-table §2 case (d) specifies a compound tested expression as opaque.

Per-pair contract tables (`Geo`, `Difference`/emptiness, finite-interval coverage) —
no-flattening rule · boolean-DNF procedure · certified-procedure inventory ·
mutual-recursion spec + executable examples (domain-indexed SCC induction across
functions/instances) · the case-6 composed example · §10.4's four soundness
obligations · §13's optimization table + origin-phrased error template · the remaining
per-operation `analyzeOperation` tables (the application rule itself is specified) ·
Indeterminate enumerations; division/NF coupling · Union/Intersection completeness or
documented incompleteness · error/warning templates · the provenance audit · **C§16
discharge per rule**. (My `subcontract`/`disjoint` land the per-pair rows `Unproven` —
sound.)

## 4. Open policy picks (author's — not owed-spec, not dissolved)

- **P-1 / Principle 9** — unproven **grounding**: warn-and-compile (current law) vs
  **reject** (heavily leaning). Blocker (4) grounding-readiness now **SATISFIED
  [1.0.18]**; blockers (2) hard-vs-acknowledgeable and (3) the [permanent] gray family
  remain open. Verdict vocabulary unaffected; only the unproven-grounding seat
  consequence moves. **No action until the author stamps P-1.**
- **Uncalled proven-unsafe body (reframed Q8)** — under E3/E-7 the body check happens
  *at a call*, so an **uncalled** `bad = () => 1 + "x"` is never checked → not flagged;
  `bad()` is rejected at the call. Whether to *also* emit a **definition-site**
  diagnostic (error / goes-nowhere warning / silent) is **not explicitly ruled** — I
  found no spec statement. E10's goes-nowhere lint tier is the natural home. Narrow;
  off the recovery's critical path. **[ask-author]**
- **F0 draft Q1 — the union rule in operation images** — hull (implemented) vs
  distribution vs held-image. Registered here because the framing changed under
  measurement: this is **not** a precision/cost tradeoff at the margin — the hull
  manufactures values the program cannot produce and then rejects correct programs for
  not handling them. Full record and decision space in **Thread D** (§5).
- **Literal parameter patterns `(0) => …`** — E3: *"[deferred; likely excluded]"*. (Some
  analyzer tests use const params; they'd need re-basing if excluded.)

### 1a. Analysis-instance metadata for factory products [added 2026-08-06]

**C§13.2, specified and unimplemented.** *"A call site resolves its callee to an analysis
instance (shape + environment contracts — exact for const closures, **contract-level for
factory products like `makeAdder(someInput)`**)"*; function-valued results *"retain their
possible analysis instances … as analyzer metadata riding alongside their coarse
`Kind(Function)` contract, so callables … arrive at call sites with instances recoverable
(**plumbing, not a contract constructor**)."*

Today a lambda whose captures are not all singletons analyzes to a bare `Kind(Function)`
with no metadata, so nothing is recoverable at the call site. Consequence: a `where` over
any domain that is not enumerable as points, on a function that builds a helper from its
own argument and calls it, is rejected with "callee not resolved to a known function".
The consumer half exists (region tables already take an environment of contracts and
handle contract-described captures — case (b)); the producing/carrying half does not.
**Previously mis-filed as an author deferral ("symbolic instance fact keys"); it is
neither deferred nor a question.** The fact-key identity question is downstream and
dissolves with it.

### 1b. μ laws 2 and 4 [added 2026-08-07, audit]

Design-closed with the μ package (compendium: *v0.5; design-closed, rounds 1–4 +
confirmatory*); laws 1–5 are all part of it. Implemented as **not merging** — conservative,
so the cost is duplicate cache entries for genuinely identical recursive groups, never a
wrong answer. Note in `src/oracle/mu.rs`. **Previously mis-filed as an author deferral; the
only deferral note is that code comment.**

### 1c. Exact string-length seam arithmetic [added 2026-08-07, audit]

E8: *"String-length contract design: specified and design-closed with the tuple family;
implementation, generated-table validation, and C§16 discharge remain owed."* Today the
analyzer gives the sound interval `count(a) ≤ count(a ++ b) ≤ count(a) + count(b)`; the
boundary-state compression that makes it exact needs the segmenter's category tables and a
string-length contract form. Note in `src/contract/grapheme.rs` — its `[ask-author]` marker
asks nothing and is stale. **Previously mis-filed as an author deferral.**

## 5. Open design threads (no spec change; block nothing) — see the handovers

- **Thread B** — the jagged function-equality boundary under the freeze slice
  (`x+3` == `x+2+1`, `x+x` == `2*x`, but `x*2` ≠ `x*3−x`). `HANDOVER-open-threads-2026-07-23.md`.
- **Thread C** — the equality-freeze exclusions + the future canonical-DAG Number
  (`1/0 ≠ 2/0`). `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md`. Tests
  that move if ruled: `(1/0) == (2/0)` (`oracle/tests.rs`), PR-04's render, MU-10 in
  `poly.rs`.
- **Thread D** — the **operation rulebook's union rule** (F0 Q1 / A6): interval hull
  (implemented) vs distribution vs a **held-and-forced image**. Not a precision dial —
  measured 2026-08-05: the hull rejects a *correct, total* program over its own declared
  domain, because exact rationals make an interval dense and no finite set of point rows
  can consume one; the same file accepts under distribution. Carries two sub-threads: the
  emptiness check's bounded-arithmetic-progression gap (`Range ∧ Mod` denotes a finite
  set the algebra cannot enumerate — independently useful for user-written bounded
  integer contracts), and a third candidate rule modelled on region-table §8's parked
  held-relation suspension (hold the image, let the consuming seat force it; the coarse
  form answers `Proven`, anything else forces and re-asks — RT-14's discipline).
  `HANDOVER-hull-vs-distribution-2026-08-05.md`, superseded for the design by
  `DRAFT-demand-stopping-and-branch-routing-v0-1.md` (author's demand-stopping spec, with
  the branch-routing draft folded in as §12–15). **First slice landed 2026-08-07** — the
  routing-forced exact operation image; conformance `exact_images` pins it.

## 6. Author-flagged opens (implemented per stated law)

- **Mutator returns** — return-nothing implemented; the returns-leaning is an extension point.
- **Module system** — MOD-01/03/04/05 + P-27b `#[ignore]`; imports parse only. Module-in-value-seat: clear error is correct.
- **`DIVERGES` verdicts (M-04)** — need a fuel-limited *harness* (eval-level bound exists); `#[ignore]`.
- **`String.units`/`points` element representation** — E8 doesn't pin it; Tuples of Numbers, lengths asserted (S-02). `// [ask-author]` in `harness.rs`.
