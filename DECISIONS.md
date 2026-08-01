> ## 📒 STATUS: **CURRENT as an append-only provenance log**
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Newest dated entry
> wins per topic; **individual older entries are HISTORICAL** and must not be read as present-tense
> guidance. Entries are never edited after the fact.

# DECISIONS.md — NEXT implementation changelog

Provenance discipline (CLAUDE.md § Process): what the specs **mandated**, what I
**chose** where a representation was left open, and what I'm **asking** the author.
Status tags mirror the compendium's vocabulary. Newest entries first.

---

## 2026-07-31 — The candidate graph (app-induction §6 / C§13.2a) — built, mutual recursion closes

The feature, not a fix. **383 lib passed / 9 ignored, 111 conformance, clippy 0.** No reaching
fixpoint, no widening, no candidate synthesis.

- **Followed §6 rather than reinventing it:** seed from the call's safety obligation → **discovery
  closure** interning every referenced candidate *and edge*, with **no verification during
  discovery** → **SCC collapse** → **reverse topological** order → **one joint vector pass** per
  cyclic component (assume every member's fact jointly; all must hold; a vector failure leaves the
  whole component unproven). `induction::scc_reverse_topo` reused — the SCC utility is
  independently valid, and reusing it is explicitly permitted; nothing else was rebuilt.
- **The joint pass is what mutual recursion needed.** Proving `f` alone cannot discharge its call
  to `g`, because only `f`'s own fact is assumed — which is exactly why `safety::prove`'s
  single-fact form could not have closed 2b however it was wired. Verified: `f → g → f` with a
  String reaching `f`'s `x + 1` now **Refuted**.
- **Finiteness is C§13.3(2)'s instance-chain cutoff, not a budget.** A target whose *shape* already
  appears on the discovery path is not instantiated; it is admitted as a `cutoff` node resolving to
  the ladder's **(c) rung — unproven**. An existing candidate whose domain **covers** the target is
  reused instead of minting a node, which is what collapses `countDown` into a self-loop component.
  Tested: `f(5)` (a concrete chain, never covered) is **cut off, not expanded**, and stays unproven
  rather than acquiring an invented covering domain.
- **Measured:** mutual `f→g→f` Refuted · `countDown` over its declared domain Proven · a divergent
  body (`f(n) = f(n)`) Proven **and terminating** (safety ≠ termination). Four graph tests pin these.
- **One entry point.** `prove` *is* the graph now; the single-fact form is gone rather than left
  beside it (`with_assumed` deleted — the joint pass installs a whole table).
- **Correction that produced this.** I had proposed "next is the wiring." The author challenged it,
  and the challenge was right: I had built a single-fact verifier and was about to wire a *fragment*
  into `analyze_apply`. The graph is what the plan actually named, and 2b proves the difference is
  not cosmetic.
- **Still not wired** — `analyze_apply` calls `bodycheck::body_summary`, so the nine pins are
  unmoved. That replacement (and deleting `check_recursive_body`/`reachable_rows`/`grow`) is the
  next step, and *now* it is genuinely wiring.
- **`// [ask-author]`:** none.

---

## 2026-07-31 — The partition rule lands: `countDown` proves by induction, natively

First working piece of the fact-graph build. **379 lib passed / 9 ignored (was 10), 111
conformance, clippy 0.** No reaching fixpoint, no widening, no synthesis.

- **`safety::prove` now verifies per region-table row (§5's partition rule)** rather than the
  whole body under `I`. `region::select` — until now **dead code** — is exactly the rule: it
  returns each selected row already narrowed to `remaining ∩ row.region`. So the `n != 0` row of
  `countDown`, intersected with the declared `n >= 0`, gives `n >= 1`.
- **Two specified-but-unimplemented F0 entries completed** to make that land. Both were in the
  author-reviewed F0 draft; I had skipped them:
  1. **Singleton exclusion tightens an endpoint** — draft Part 3: *"`Difference(A,B)` → use A;
     additionally, when B is a singleton at an endpoint of A's interval, tighten that endpoint to
     strict."* `[0,∞) ∖ {0}` is now `(0,∞)`. Handles **both** point spellings, `Equals(v)` and
     `Range(v,v)` — the region table emits the latter, and the spec's `Range(v,v) → Equals(v)`
     normalization is still unenforced (recorded in `IMPLEMENTATION-STATUS` §1).
  2. **Grid alignment** (`snap_to_lattice`) — an exclusive bound on an integer lattice snaps to the
     next lattice point: over the integers `> -1` *is* `≥ 0`. Without it the two facets disagree
     (interval says "above −1", congruence says "an integer") and their conjunction cannot be
     recognised as `≥ 0`. Same idea as grounding's landing/grid step, applied to the abstraction.
- **Measured result:** `row1 - 1` goes from `GreaterEq(-1)` (escaping the domain, `⊑ nonneg`
  **Refuted** with witness `-1`) to `GreaterEq(0) ∧ Mod(1,0)`, `⊑ nonneg` **Proven** — so the
  recursive call is discharged by the assumed fact and the body is never re-entered.
  `declared_domain_recursion_proves_by_induction` **un-ignored**.
- **The other nine pins are unmoved, and why:** they exercise `bodycheck::body_summary` — the
  quarantined path — not `safety::prove`. Releasing them is the wiring step (T1.4), where
  `body_summary` is replaced and `check_recursive_body` / `reachable_rows` / `grow` are deleted.
  The mechanism now exists to replace it with.
- **`// [ask-author]`:** none — both additions were already in the reviewed F0 draft.

---

## 2026-07-31 — Fact-graph design pass: scope fixed, and blocker 1b RE-FILED (oracle-verified)

Started the C§13.2a fact-graph design by **reading** the normative text (app-induction §5/§6,
C§13.2a/13.3) rather than inventing a mechanism. Two results, one of which corrects the plan.

- **The spec already answers what `I` ranges over.** C§13.2a: fact nodes are `(analysis instance,
  **row-set I**, demanded C)`; C§13.3(2) repeats it. I had proposed "step 1: a design pass to decide
  what `I` ranges over" — that was about to design something already ruled. §6 likewise gives the
  algorithm outright: seed from the program's safety obligations → discovery closure interning every
  referenced candidate **and edge**, with *no verification during discovery* (premature unproven is
  non-conforming) → SCC collapse → reverse-topological processing → **one joint vector pass** per
  cyclic component. Failure kinds are given too (vector failure ⇒ all members per-compilation
  unproven; individual refutation needs a **realized completing witness** `(e, x, v)`).
- **BLOCKER 1b RE-FILED — it is NOT the fact graph.** Verified against the oracle, not reasoned:
  for `f = (x) => x > 0 ? f(x-1) : (x == 0 ? 0 : x + "s")`, **`f(0.5)` traps** (`+ requires two
  Numbers or two Strings`) while `f(1)` returns `0`. **`0.5` and `1` are in the same region-table
  row.** Therefore `BodySafe(f, {row x>0})` is **genuinely false**, and *no* row-set-keyed fact can
  prove `f(1)` safe however well the graph is built. Proving it needs a domain **finer than a row** —
  the exact chain `1 → 0`, i.e. grounding **§4's exact-singleton fact chains under the native
  exact-chain finiteness license**, a listed owed item. This is the third re-filing of 1b (after
  "SCC summary", then "finite row-set bound"); the first two were reasoned, this one is measured.
- **What the fact graph WILL release, on the same analysis:** `factorial` over `Number` (the
  recursive `n-1 : Number ⊑ Number = I`, so the fact discharges directly); `countDown` over its
  declared domain (needs §5's **partition rule** — verify per row, so `n≠0 ∧ n≥0 ⇒ n-1 ≥ 0`);
  blocker 2b (mutual recursion resolves by ordinary proving — no canonicalization needed); blocker 3
  (completion carried on the fact); and the remaining false positives. **Not** 1b; **not** 2a
  (region-table §5 first).
- **Method note.** The design pass paid for itself before any code: it caught a plan that would have
  built the right feature while expecting it to release a test it cannot. Cost: two oracle runs.
- **`// [ask-author]`:** none.

---

## 2026-07-31 — RULING [user]: safety-unproven is an **Error**, not a Warning — landed

**[user, 2026-07-31]:** *"Warning was an early wording and since then I'm leaning towards Error."*
This aligns the implementation with late-resolution §5 (*"Safety-unproven → compile error.
Un-suppressible; the Mutators-cannot-fail theorem stands on exactly this"*). **378 lib passed /
10 ignored (was 4), 111 conformance, clippy 0.**

- **The change.** Ten safety-unproven emission sites in `analyzer/mod.rs` flipped `Warning → Error`:
  operation safety, field/index/slice access, unknown callee, not-a-function (uninhabited),
  argument obligation, spread kind, destructuring irrefutability, guard Boolean.
  **Deliberately NOT changed:** `demand()`'s `MayFallThrough` (line 127) — *completion* is a
  different judgment class (application §1.6: a merely-possible fall-through is the third voice,
  never a rejection). Flagged rather than assumed.
- **Seven tests moved. They split into exactly two kinds — the author's framing, and it was right.**
  - **(a) The test encoded the old policy → updated (1).** `open_field_access_reasoning` asserted
    verbatim *"r.b on an unknown receiver — a warning, not a rejection."* You cannot prove field
    `b` present on an unknown receiver, so under the ruling it blocks. Test now asserts rejection.
  - **(b) Pre-existing FALSE POSITIVES, previously invisible → pinned (6).** All recursion cases
    (factorial, countDown, the induction/summary tests, and `safety.rs`'s own
    `declared_domain_recursion_proves_by_induction`).
- **Root cause isolated, not guessed.** `bodycheck.rs:213` computes the recursive call's target
  under the **row region**, then grows the reaching domain with it — widening `Number` back up to
  `Top`, after which `n - 1` is no longer provably a Number. Verified the contract algebra is
  innocent: `Difference(Number, {0}) ⊑ Number` is **Proven**; only `Difference(Top, {0}) ⊑ Number`
  is not, and that `Top` is manufactured by line 213. **Same root as blocker 1b.**
- **What this actually reveals.** Those six tests were green *only because* the finding was a
  `Warning` that `analyze_apply`'s `errors()` filter discarded. So the honest state is: **the
  analyzer cannot currently prove `factorial` or `countDown` safe** — and never could. The evidence
  was being filtered out. The ignored count going 4 → 10 is previously-hidden failure becoming
  visible, **not** a regression.
- **Correction to my own prior reasoning.** I had reported this change as "breaks 7 tests, don't
  land it." That was backwards: a failing test after a policy correction is either a false positive
  (fix the analyzer) or the correct new behaviour (fix the test) — never a reason to keep the wrong
  policy. The author made that point; it is recorded here because I got it wrong twice in one day
  (see also the `errors()` filter over-billed as a false acceptance).
- **Consequence for the parked work:** blocker **1b is now much more valuable** — it gates six
  further tests, all ordinary safe programs. Still parked; each pinned test names the root and
  states explicitly: do **not** fix by reverting the severity or by adding widening/reaching
  machinery.
- **`// [ask-author]`:** none — the policy was ruled; the completion-class exclusion is flagged
  above for review.

---

## 2026-07-31 — `BodySafe(instance, I)`: the fact + assume-and-check discharge (partial; blockers NOT closed)

First increment of the safety fact. **384 lib (4 ignored) + 111 conformance green, clippy 0.**
`analyzer/safety.rs` (new) + one surgical hook in `analyze_apply`.

- **`I` comes from the call site**, never synthesized — the argument-tuple contract (E-7) or a
  `where`'s declared input (E-8). Settled by the `numId(5)` example: the call already carries its
  own domain, so nothing needs to derive one. `I` (input domain) and `C` (a demanded contract) are
  kept as separate things throughout.
- **Assume-and-check, not unfolding.** `prove(callee, I)` installs `SafetyFact { callee, input }`,
  analyzes the body **once** under `I`, and a recursive reference whose argument domain is contained
  in `I` **resolves through the assumption** (C§13.2). Keyed `(instance, I)` — the same key shape as
  the existing return-fact `Hypothesis`, whose `args ⊑ input` guard I reused rather than reinvented.
- **The clean case works, natively.** `countDown` over a declared `GE(0) ∧ Mod(1,0)` **proves by
  induction**: `n-1` stays inside the domain, so the call discharges and the body is never re-entered.
  Worth noting *what decides `n-1 ∈ D`* — F0's interval **and congruence** transfer (integrality
  surviving `−`). That is F0 paying off, and it is the one place the earlier ordering argument was
  accidentally right for the wrong reason.
- **Honest limit, deliberately not papered over.** A recursive call whose domain is *not* contained
  in `I` is covered by no fact, and this module **does not widen `I` until it closes, nor accumulate
  reaching domains** — both forbidden. It currently falls back to the quarantined `body_summary`.
- **The four blockers are NOT closed — verified, not assumed.** A probe through `prove` gave the
  right answer on all four, which looked like a win; running the **pinned tests** showed they still
  **fail**. The probe's results were a *composite*: `prove` does not push the `ACTIVE` cutoff, so a
  non-discharged call gets one extra level of analysis from the quarantined checker. That is an
  artifact of two cutoffs composing, **not a mechanism**, and I am not reporting it as progress.
  Closing the blockers needs the non-discharged case to have a principled bound — C§13.2's `I` over
  the **finite row-set lattice** — which is not built.
- **Tests isolate what is actually new** (4): induction over a declared domain; safety ≠ termination
  (a diverging body is *safe*, and the proof still closes — proving it does not unfold); a call
  outside the fact is **not** discharged; a fact discharges any call inside it.
- **`// [ask-author]`:** none. Scope was authorized; the remaining gap is named, not filled.

---

## 2026-07-31 — Tier-0 rebaseline + the grounding correction (external review acted on)

Two author-directed slices, both bounded. **380 lib (0 failed, 4 ignored) + 111 conformance, clippy
0, manifest 19/19.**

**Tier 0 — strictly mechanical; no semantic rulings, no history rewritten.**
- **`IMPLEMENTATION-STATUS.md` created** as the single implementation-status authority: normative
  specs, the document status register, quarantined non-authoritative code, failing gates, the
  forbidden-machinery boundaries, the authorized slice, and the measured baseline.
- **19 maintainer docs bannered** CURRENT / HISTORICAL / SUPERSEDED. **No manifest-protected file
  touched** (the 19 canonical specs, `CLAUDE.md` among them) — staleness *inside* them
  (region-table's dissolved accepted-domain text and patch header; C§7 vs the later `Numeric`
  ruling; grounding's stamp status) is **recorded as author-owned**, not corrected here.
- Two of my own prior claims marked **SUPERSEDED** by author instruction: the foundation map's
  **F0-before-demand-core ordering** (imprecision yields *unproven*, so a coarse rule is never a
  prerequisite) and the **"replace-and-rebuild"** framing for the induction pipeline (it is
  *non-authoritative*; its independently valid SCC utilities may be reused; no sweeping rewrite is
  authorized).

**The grounding correction — done while it stays UNWIRED (verified: zero call sites).**
- **Forced-path selection (the G-BUG fix).** `drift_away` admitted a recursive transition on the
  *syntactic presence* of a self-call. GR-23 requires selection to be **forced** at every step. New
  `forced_self_calls` collects only calls reached under no unproven selection — a `Match`
  **scrutinee** stays on the forced path, anything inside a `Match`'s **items** does not — and any
  self-call found behind a conditional makes the candidate **decline outright** (declining is always
  sound). Verified against the review's counterexample: `flag = false; f = (n) => n == 0 ? 0 :
  (flag ? f(n-2) : 0)` at `f(1)` no longer refutes a **terminating** program.
  *Scope note:* this discipline binds **refutation only**. The descent side is untouched — a
  conditional call still must descend when taken, so `numeric_descent` keeps reading every
  syntactically present call. A gate asserts the rule is narrow, not blanket.
- **Witness-bearing refutation.** `Verdict::Refuted` was payload-free, so the admitted witness was
  computed and discarded. Now `Refuted(Refutation { witness, drift, missed_bases })` — the admitted
  represented-exact root witness plus the certificate, persistent and diagnosable. (Representation
  chosen here; the spec does not fix one.) `Verdict` loses `Copy`; blast radius was contained to
  `grounding.rs` (`contract::Verdict` is a different enum).
- **Superseded header claim removed.** The module no longer says grounding "lets the body check stop
  unfolding" / "replaces widening as the analysis's termination bound" — a claim **this session had
  already disproved** (see the 2026-07-30 entry) and which contradicts C§13.3. Replaced with the
  correction and a pointer to the forbidden-machinery boundary.
- **Gates:** G-BUG **un-ignored and passing on the built mechanism** (not routed around), plus two
  companions — `refutation_carries_its_witness_and_certificate` and
  `forced_path_discipline_is_narrow_not_blanket`. Four blockers remain pinned; the quarantined
  `bodycheck` reaching engine is deliberately still present (its removal is the un-authorized T1.4).
- **`// [ask-author]`:** none. Everything here was directed; the one free choice (the `Refutation`
  representation) was explicitly delegated.

---

## 2026-07-31 — F0: the C§7 operation rulebook, built whole (design reviewed first)

The complete operation transfer table — **safety and image, all 13 operations, every contract
form** — replacing the closed-`Range`-only arithmetic. Designed on paper and author-reviewed
**before** any code (`NEXT-F0-operation-rulebook-draft.md`), then built in the reviewed order.
**377 lib + 111 conformance green, clippy 0, no new doc warnings.**

- **Structure — three layers, not a 13×N×N grid.** The literal "per-pair table" reading gives ~78
  identical arms per operation, because the numeric forms are **projections onto two facets**. So:
  (1) algebraic plumbing uniform across ops (Indeterminate propagation, total-division forms);
  (2) exact fold for all-singleton operands (the oracle itself); (3) **leaf rules ordered
  specific → general** — a form-preserving rule gets first refusal, the numeric abstraction is the
  total fallback. Three tables of 9 / 26 / ~3 rows instead of 13 arrays of 81 cells.
- **`contract/numeric.rs` (new).** `Interval`/`Bound` **extracted from `subcontract.rs`** (they
  already existed — the earlier reverted patch had written a parallel encoding without looking),
  plus `Congruence` and `NumAbs = interval × congruence`. **Two conversions, deliberately
  separate**, with the asymmetry as a normative module note: `interval_exact` (denotes ⟦c⟧ — needed
  for subset/disjointness, returns `None` for `Mod`) vs `num_abs` (contains ⟦c⟧ — for images, may
  read `Mod`/`Geo` as unbounded). Getting these backwards would make `GreaterEq(0) ⊑ Mod(1,0)` come
  out Proven, which is false.
- **`n = 0` encodes an exact integer in `Congruence`.** That single choice makes the `gcd`
  composition rules uniform (`gcd(0,m) = m`), so an exact operand composes with a lattice operand
  correctly: even + 2 stays even, and **integrality survives `−`** (the non-negative integers minus
  1 are still integers — which matters for `Pow`'s integer-exponent demand and for grounding's grid).
- **`×` / `/` use extended (±∞) arithmetic**, not sign-case analysis: four corner products with
  `0 · ∞ = 0`, min/max under `NegInf < Fin < PosInf`. The signs fall out; no special cases.
- **Safety table completed.** The gap the draft exposed: `apply_prim` checks Indeterminate **first**
  — arithmetic *propagates* it (never traps) while ordering comparisons *trap*
  `UndischargedIndeterminate`. So arithmetic's operand demand is `Number ∪ Indeterminate`, and
  `Indeterminate + 1` is now provably **Proven** where it previously read `Unproven`.
- **The audit is the matrix.** `operation_soundness_sweep`'s grid went from 9 forms to **27** —
  every leaf form with **sign variants** (a single all-positive representative hides sign bugs in
  `×`/`/`/`%`), plus `Mod`, `Geo`, `Intersection`, `Union`, `Difference`, both Indeterminate forms.
  It **immediately caught a real bug**: dividing by a zero *endpoint* (`Greater(0)` excludes 0 as a
  value but has it as an endpoint) panicked. Fixed. Five `rulebook_*` precision tests assert the
  table's claims separately, because returning `Kind(Number)` everywhere would pass soundness alone.
- **Deliberate incompleteness is documented in the module doc** (Geo beyond scaling; Mod through
  `×`-by-non-constant, `/`, `%`, `**`; `**` with both operands non-singleton; zero divisor endpoint;
  strictness through `×`/`/`; string *length* through `+` — owed to the tuple family's §5 lift;
  `Difference` with non-singleton exclusion; `Union` read as hull rather than distributed).
- **`// [ask-author]`:** the four draft questions were answered by my stated defaults and are
  recorded there; the one still genuinely open is **Q1 — per-alternative `Union` distribution vs the
  hull** (hull is implemented; sound, and the congruence join recovers much of the precision).
- **Not in F0, deliberately:** the analyzer-level `analyzeOperation` + `OperationOutcome` (F1), the
  demand core (F2). Nothing in `analyzer/` was touched.

---

## 2026-07-31 — Two more patch-shaped attempts, both REVERTED; the operation rulebook is itself foundation

After the SCC revert (entry below) I did the same thing twice more in miniature. Both reverted; the
tree is back at **371 lib / 4 ignored, 111 conformance / 13 ignored, clippy clean** — baseline. No
code from today's session survives; only the debt markers and the foundation map.

- **Attempt A — `analyzer/opoutcome.rs` (`OperationOutcome`), reverted.** I extracted C§7's
  **return type** and wired a pass-through in `analyze_primop` (`from_primitive(...)` then
  immediately `.produced.erase()`), calling it "F1." But C§7's `analyzeOperation` takes
  `Correlated<AnalysisContract>` **and** a `seatContext` — the inputs are analyzer-level too, so the
  real F1 is a *function*, and I built a **noun without its verb**: a type with no genuine consumer,
  ahead of the thing that gives it meaning. Also misplaced — C§16 says `ApplicationOutcome` **is**
  "obligation 3's application instance," so it belongs beside it, not in a third outcome module.
- **Attempt B — additive interval arithmetic in `contract/operation.rs`, reverted.** Real verified
  gap (`GreaterEq(8) + GreaterEq(10)` → `Kind(Number)`, losing the bound; fixed it, +4 tests, green,
  confirmed end-to-end `n ≥ 0 ⊢ n − 1 : GreaterEq(−1)`). **Still wrong to keep**, for two reasons:
  (1) it **duplicated existing machinery** — `subcontract.rs:129-162` already has
  `Interval`/`Bound{Unbounded,Incl,Excl}`/`interval_of`/`meet`, a better encoding than the parallel
  one I wrote without looking; (2) more importantly it was a **patch, not the feature** — `+`/`−`/
  unary `−` fixed while `*`, `/`, `**`, `Mod`, `Geo` were left, i.e. the same edge-case-driven
  shape as the reverted SCC engine.
- **The finding that matters: the C§7 operation rulebook is FOUNDATION, not polish.** C§13.1 says
  resolution runs *"forward through the operation rules"* — so the demand core (F2) **executes** the
  operation table. An incomplete table means the analyzer loses information at exactly the moment a
  demand is resolved, and something downstream gets invented to compensate. That is this session's
  thesis applied one layer down: **F2 built on a half-built rulebook would import for the same
  reason the body check did.** So the complete per-pair table (C§17's owed item) is not a nice-to-have
  to slot in later — it is a **prerequisite**, and it must be built *whole* (every operation × every
  contract form), not per-failing-case.
- **Process lesson, third instance today.** The pattern is: find failing case → add mechanism → green.
  The correction is: **build the complete specified feature set, then see what passes.** Recorded here
  because it recurred *after* being named — naming it was not sufficient.
- **A soundness fact worth keeping from Attempt B** (costs nothing, prevents a future bug): the
  contract→interval conversion is **direction-asymmetric**. For *image over-approximation* a wider
  interval is safe, so `Mod`/`Geo` may read as unbounded; for *subset testing* widening the RHS makes
  `⊑` wrongly true (`GreaterEq(0) ⊑ Mod(1,0)` would come out Proven — false). Any future shared
  interval module needs two conversions, not one.
- **`// [ask-author]`:** none. Both reverts are the author's standing instruction, not a judgment call.

---

## 2026-07-31 — REVERTED the SCC body summary as an imported mechanism; owed-breadth foundation map produced

An SCC body-summary engine (`analyzer/summary.rs` + multi-position region tables + a `body_summary`
rewire) was built this session and **passed all four Archive-11 blockers + the full suite** — then
**reverted whole** on the author's instruction, because it was an **imported** mechanism: a forward
reaching-domain fixpoint + Kind-collapse **widening**. That is the abstract-interpretation shape NEXT
rejects (Principle 7; late-resolution law; "widening is foreign"). Passing the tests that way
**polluted** the implementation and let green mask a missing foundation.

- **The finding (author-led).** The body-safety check is built **ahead of its foundation**. The
  recovery order is *demand core → template → region table → body check*; the region table + body
  check exist, but the **demand core (C§13.1) was never built**. With no demand-and-fact substrate,
  the check cannot close recursion or hold a parameter's contract natively, so it imports a
  forward-solve (accumulate reaching contracts, widen to terminate). The "swap"/widening is a
  *symptom* of the forward shape, not a needed mechanism — in a demand+contract system `total + n`
  *demands* `total : Number`, checked against providers by induction, never by watching values.
- **Code audit (evidence).** (1) No demand core: `analyze` is forward-only; the only `demand` is the
  local expecting-seat helper. (2) `analyze_operation` still returns `OpResult { safety, output }`,
  not `OperationOutcome { safety, produced, completion }` (C§7/1.0.7 drift). (3) Return facts exist
  (`infer_return_fact`, `Hypothesis`) but **no `BodySafe(instance, I)` safety fact** — so recursive
  safety has nothing to close on by induction. Details + build order:
  **`NEXT-owed-breadth-foundation-map.md`** (new).
- **Revert.** `git checkout` of `region.rs`/`mod.rs`/`bodycheck.rs`/`tests.rs` to HEAD; `summary.rs`
  removed. **Back to 371 lib / 4 ignored, 111 conformance / 13 ignored, clippy clean** — the honest
  pre-session state. The four blockers are **re-pinned `#[ignore]`** with a note naming the
  foundational blocker (domain-indexed safety facts + demand core) and an explicit "do NOT import a
  forward reaching/widening engine to pass this."
- **The plan (b + a, author-chosen).** (b) revert + re-pin so the debt is visible; (a) build the
  foundation in dependency order — **F1 `OperationOutcome` → F2 demand core → F3 domain-indexed
  safety facts** (reusing the kept `joint_vector_pass` induction) → rewrite the body check native,
  **deleting** the forward reaching engine (both `summary.rs` and the single-param
  `check_recursive_body` accumulation). Keep the region table (branch reachability is a single-domain
  contract question, not an import). Full map + open questions in the foundation-map doc.
- **Process correction.** Per CLAUDE.md hard rule #3, a gap is an owed item / a question for the
  author — **not** something to fill silently with an imported mechanism. This session did the latter
  (documented, but still filled). The re-pinned tests + the foundation map are the correction.
- **`// [ask-author]`:** build order F1-vs-F2-first; staging (full-native vs minimal-F3-first);
  whether to wire grounding's A-NEG basin as the safety-fact domain now; whether `where` (E-8) is the
  first demand-origin consumer. All in the map §7.

---

## 2026-07-30 — Archive-11 review: fixed blocker 1a; pinned 1b/2a/2b/3 (one root cause) as adversarial tests

An adversarial review found the summary body check over-claimed soundness: it passes the
suite but the suite covered none of the hard cases. Three of five findings **silently
accept trapping programs**. Owned it; fixed the one clean regression, pinned the rest.

- **Blocker 1a — FIXED (false reject I introduced).** `check_recursive_body` had dropped the
  old `body_check`'s `all_prior_exact` discipline — it downgraded on the *current* row's exact
  bit only. Restored the full RT-14 rule: a finding refutes (`Error`) only from a row that is
  exact **and every earlier reachable row is exact**. `f = (n) => n == n ? 0 : n + "x"` (the
  `n+"x"` sits in an exact row reached only if the unprovable `n==n` is false) is no longer
  rejected. Test `rt14_exact_row_after_uncertain_prefix_does_not_refute`; suite green.
- **Blockers 1b / 2a / 2b / 3 — pinned, NOT fixed.** They are **not** independent patches;
  they collapse to one root cause = the review's prescription, **a unified `(instance,
  row-set)` SCC summary carrying safety + produced + completion**:
  - **1b** (coarse recursive target → false *reject*) and **2a** (multi-param → false
    *accept*) both need the reaching domain tracked **precisely** (concrete chains exact,
    growing ones bounded). Verified: a naive 1b downgrade trades the false-reject for a
    **false-accept on computed deep traps** (`f(10)→…→f(5)` with an `n==5` trap) — strictly
    worse. So 1b is not safely patchable alone.
  - **2b** (mutual `f→g→f`) needs the closure to span **across instances**; `collect_self_calls`
    is syntactic-self-only.
  - **3** (recursive fall-through completion) needs completion carried through that same
    closure; today it comes from a one-shot `whole_body` and reports `Produces`.
  - Landed all four as `#[ignore]` tests (verified they *fail* when run — they catch the
    bugs). Un-ignore when the SCC engine lands.
- **Honest correction:** I previously called the summary check "sound + terminating, verified"
  and the swap "done, green." It **terminates and passes the current suite**, but is **not
  sound** — two of the blockers accept crashing programs. Over-reporting soundness was the
  worse error.
- **`// [ask-author]`:** none — the fix path (unified SCC summary) is the review's and the
  spec's (app-induction §4a/§5).

---

## 2026-07-30 — §5 multi-parameter region tables: attempted, reverted; the precision/termination tension mapped

Built `region_table_multi` (per-position argument-tuple projection — a single guard `pᵢ ⋈ c`
constrains position i, `Top` elsewhere; §5) and `check_recursive_body_multi` (the tuple lift
of the summary check). The projection is correct and **catches multi-parameter
domain-changing traps** (`(a,b) => a==0 ? f("x", b) : a+b` at `(0, _)` → rejected — a real
precision win the whole-body fallback misses). But the two *accept* cases produced **false
Errors**, so it is not sound to wire; reverted to the whole-body fallback (sound). Recorded
the finding.

- **The tension (the crux).** The per-row reaching-domain fixpoint needs a domain to compute
  each recursive-call target under:
  - Under the fixed **row region** (what single-param `check_recursive_body` does): converges
    for concrete numeric chains (`f(5)→f(4)…` folds to `Number`), **but** coarsens a *carried*
    position to `Top` — so an accumulator `f = (n, acc) => n<=0 ? acc : f(n-1, acc+n)` sees
    `acc` as `Top` and `acc + n` **false-traps**. Single-param has no carried positions, so
    this never bit before.
  - Under the **reaching domain** (precise — `acc` stays `Number`): correct for abstract args,
    **but** hangs on concrete numeric chains (`Equals(5) ⊔ Equals(4) ⊔ …` grows unboundedly).
  - Neither is both sound-precise and terminating; the resolution is a **bounded abstraction
    over the finite partition** (the classic AI precision/termination point, solved natively
    by folding a growing position into its partition row — the single-param row-region trick,
    but *only where the position actually grows*, not for carried positions).
- **Also found:** the reaching-domain `⊔` fixpoint needs `union2` (collapse `Top`/`Bottom`)
  **and** a structural `covers` check (`cur == add`, or `add` a `Union` component) — plain
  `subcontract` is incomplete on reflexive `Intersection`s and loops.
- **Deferred.** Multi-param stays on the whole-body fallback (sound; catches direct traps,
  recursion cut). Next attempt: track reaching domains precisely per position, and fold a
  position into its row region **only when it grows** (a per-position growth detector), giving
  precision for carried positions and termination for genuinely-growing ones. `// [ask-author]`:
  none — this is an implementation-strategy choice within the specified partition mechanism.

---

## 2026-07-30 — Demand core step 4: delete the widening machinery (−288 lines, suite green)

With the summary body check wired and `instance_body_summary` dead, deleted the old
call-site/widening machinery. **370 lib + 111 conformance green, clippy clean; −288 lines.**

- **Deleted (`induction.rs`):** `instance_body_summary` + `InstanceBodySummary` struct/impl
  (the wrong-layer call-site safety node), `domain_admitted` (the finite-literal admission
  basis), `downgrade` / `downgrade_completion` (the widened-evidence third-voice drops), and
  the `ACTIVE_BODIES` cycle stack. **Deleted (`bodywalk.rs`):** `literal_values` +
  `collect_consts` + `collect_pattern_consts` (the program-literal vocabulary the admission
  basis read). The widening (`Contract::kind_abstraction`) is **retired as an analyzer
  mechanism** — the region partition (GR-03) replaces it.
- **Kept (correctly not touched):** `kind_abstraction` itself stays in `contract/mod.rs` —
  it is *also* used by three-valued `subcontract`'s kind fallback (a coincidental share, not
  the widening role). The return-fact induction (`joint_vector_pass`, `call_return`,
  `hypothesis_for`, `HYPOTHESES`, `Hypothesis`, `summarize_instance`, `analyze_instance_body`,
  `is_recursive`) is untouched — it is the KEEP set, orthogonal to body safety.
- **No test regression** — the widening never had a soundness role the partition rule
  doesn't now cover; its only observable behaviours (growing-domain termination, the
  widened-trap downgrade) are handled by the finite row-set closure + RT-14.
- **The recovery arc is closed.** Region table + demand core + summary body check + §4a
  cutoff + grounding (orthogonal), all wired; the wrong-layer machinery the Phase-1 audit
  named is gone. Remaining: multi-parameter region tables (§5 — whole-body fallback now).
- **`// [ask-author]`:** none.

---

## 2026-07-30 — Demand core step 3: THE SWAP — summary body check wired, green, no widening

The recovery's goal since the drift-away finding: `analyze_apply`'s Known-callee path now
runs the **summary-over-partition** body check instead of `induction::instance_body_summary`.
**370 lib + 111 conformance green, no hang, clippy clean.** Done the NEXT way — nothing
foreign.

- **The wire.** `analyze_apply` Known(cv) → `bodycheck::body_summary`. `body_summary` bounds
  recursion by the **§4a shape-repeat cutoff** (`ACTIVE` now instance-keyed — sound because
  the row closure covers every reachable row, so the cutoff only prevents re-unfolding).
  Safety findings from `check_recursive_body` (single-param); a whole-body fallback for
  multi-param (§5 owed); `produced`/`completion` from `whole_body` with recursion cut; the
  recursive `produced` still sharpened by the kept `call_return` induction.
- **Empirical result — the swap that hung before now passes.** First run: **one** failure
  (`rt14_a_may_region_trap_does_not_refute`) — I'd dropped the RT-14 downgrade; restored it
  (a non-exact row's trap → warning). Second run: **all green.** Verified end-to-end: the
  domain-changing trap `f(0)→f("x")` **rejects**; the two growing-domain tests
  (`f(x+y,y)`, `f(b?x:0,b)`) **terminate** (folded into the finite row set — no widening);
  factorial / even-odd / the induction battery unchanged.
- **`instance_body_summary` is now dead** (referenced only in doc comments). The delete of
  it + `domain_admitted` + `kind_abstraction` + `ACTIVE_BODIES` (the crude widening the
  partition rule replaces) is the next step — deferred so the swap lands as one reviewable
  change.
- **`// [ask-author]`:** none. Widening-retirement is spec-grounded; the swap is verified.

---

## 2026-07-30 — Demand core step 2: the summary body check (sound + terminating, no widening)

The body check reworked from **unfolding** to **summary-over-partition**. `bodycheck.rs`
+3 tests; **370 lib** + 111 conformance green, clippy clean. Still unwired.

- **`check_recursive_body(callee, param, arg)`.** Per region-table row, compute the
  **reaching domain** (values that reach it through recursion) as a growing union, then
  check each reachable row's result **under its reaching domain**. Recursive calls are
  summarized (covered by the reachable-row set), not unfolded.
- **The design insight that resolves the precision/termination tension** (the crux I mapped
  building this): **recursive-call target domains are computed under the fixed row
  `region`**, not the accumulated domain — so only finitely many target contracts feed each
  union and growth stops by a semantic `⊑` check (`grow`). A growing recursion (`f(x+1)`)
  folds its reaching domain into the row region and converges — **no widening, no fuel**.
  Yet precision is kept where it matters: a trap-bearing arm is guarded by an **exact** test
  (`x==0`) whose row region *is* the exact reaching domain.
- **Both hard soundness cases pass, standalone:**
  - `f(0) → f(1) → 1` **accepted** — the `1+"x"` arm (x∉{0,1}) is checked under the middle
    row's exact reaching domain `Equals(1)`, which prunes it. (The old machine needed
    widening + evidence downgrade for exactly this.)
  - `f(0) → f("x") → "x"+1` **rejected with an Error** — the else row's reaching domain is
    `Equals("x")` (String), so `x+1` definitely traps. Right severity from the exact domain,
    not a downgraded warning.
  - countDown accepted and the fixpoint terminates (`Equals(5) ⊔ Number = Number` by `⊑`).
- **Next:** wire it (shape cutoff at `analyze_apply` so recursive calls summarize instead of
  routing through the live `instance_body_summary`); multi-parameter region tables (§5 — the
  two growing tests are 2-param); then delete `instance_body_summary` / `domain_admitted` /
  `kind_abstraction`. **`// [ask-author]`:** none.

---

## 2026-07-30 — Demand core step 1: reachable-rows fixpoint (spec-verified; widening retired)

Verified the body-check recursion mechanism against the specs, then built the substrate.
`bodycheck.rs` +3 tests; **367 lib** + 111 conformance green, clippy clean.

- **Spec verification.** NEXT does **not** unfold recursion (region-table §8: "analyze the
  suspension, don't expand it"; compendium §10.6: return facts are summaries). The
  termination bound is the **finite region partition** — app-induction §4a shape-repeat
  cutoff (*"path depth ≤ the program's shape count"*, built: `inventory.rs`) + §5's
  partition rule / GR-03's *"instance's finite row-set lattice"* (built: `region.rs`).
  **Widening is a foreign (abstract-interpretation) mechanism NEXT deliberately avoids** —
  the "keep widening vs row-set lattice" fork from the prior entry is **retired**; widening
  was never an option. Grounding is orthogonal (A-NEG derived domain + return-fact
  admission), not the bound.
- **The real bug:** `bodycheck.rs` **unfolds** (re-enters `body_summary` over concrete/
  growing domains). Fix: a **summary-over-partition** body check.
- **Built — `reachable_rows(callee, param, arg)`** (GR-03 finite row-set lattice): the finite
  set of `region_table` row indices a call reaches through recursion — seed with the rows
  `arg` selects, and for each reachable row that recurses, add the rows its recursive-call
  argument domain selects. A **growing** concrete domain folds into a fixed row → the
  closure is finite (bounded by row count), **no widening**. Plus `selected_indices` (the
  remainder walk returning indices). Verified: `f(0) → f("x")` reaches **both** rows (the
  `else`/Top row where `x+1` traps is covered — so a summary check catches the trap without
  unfolding); `f(x) => f(x+1)` folds into **one** row (finite, no hang); countDown reaches
  base+step.
- **Next:** the summary body check that walks these rows (check each row's result under its
  row domain, summarize recursion via the shape cutoff), then multi-parameter region tables
  (§5 — the two growing tests are 2-param) and the A-NEG derived domain; then wire + delete
  `instance_body_summary`/`domain_admitted`/`kind_abstraction`.
- **`// [ask-author]`:** none — widening-retirement is spec-grounded (§8/§10.6/§4a/§5/GR-03).

---

## 2026-07-30 — Wiring finding: grounding is NOT the swap's termination bound (third revision)

Set out to wire `ground()` into the body check to bound the growing-domain unfolding (the
swap gate). **The premise was wrong**, verified before implementing. `grounding.rs` +1
test; **364 lib** green.

- **The two hanging tests are non-terminating PROGRAMS.** `a_growing_non_singleton…` is
  `f = (x, y) => f(x + y, y)` and `a_growing_union…` is `f = (x, b) => f(b ? x : 0, b)` —
  neither has a base case; both diverge at runtime. Their comments say "No claim about the
  verdict — only that analysis terminated." So they test **analyzer** termination on a
  divergent program, not a provable property.
- **Grounding correctly returns Unproven for both** (new test
  `baseless_divergent_recursions_are_unproven_not_grounded`). A grounding verdict therefore
  cannot cut them — grounding is a *termination judgment*, and these do not terminate.
- **So grounding is not the bound.** The analyzer must terminate even on divergent programs
  (GR-05: C§13.3 bounds the symbolic procedure, not runtime recursion). That bound is the
  **finite-domain abstraction** — GR-03's "instance's finite row-set lattice," of which the
  old `domain_admitted` + widening is a crude version (literals exact so deep concrete traps
  are still traced; computed domains folded into the finite lattice so growth stabilizes).
- **Correction to steps 4/5.** Step 5 said "grounding is the specified replacement for that
  bound." Wrong on this point. Grounding is **orthogonal** to analysis-termination: it is
  A-NEG's derived-input-domain source and per-row return-fact admission (GR-02), now built
  (G-1…G-8) and useful — but it does not unblock the swap. The swap needs the finite-domain
  abstraction ported/refined, which **contradicts audit §5's "delete widening"** → an author
  design fork (keep+port widening vs implement the GR-03 row-set lattice). Detail in
  `OwedItems.md §0.1`. Tasks #50/#51 reframed.
- **`// [ask-author]`:** the swap's finite-domain bound (widening vs row-set lattice) —
  surfaced in OwedItems §0.1.

---

## 2026-07-30 — Grounding G-8: mutual recursion (§5 GR-07)

Grounding crosses function boundaries — mutual-recursion SCCs. `grounding.rs` +2 tests;
**363 lib** + 111 conformance green, clippy clean. Still unwired.

- **`mutual_descent(callee)`** — the reachable closure group (`reachable_closures`, from
  `bodywalk`) is the mutual SCC. If **every** cross-call in the group decreases a shared
  single-parameter measure by a constant and every recursive member has a descending
  half-line base on it, then every simple cycle composes to a strict decrease (a sum of
  negatives) and the measure is bounded below — the whole group terminates. This discharges
  GR-07's per-cycle obligation by the **stronger, enumeration-free per-edge** condition (no
  Johnson-style cycle walk); landing is structural (domain-independent).
- **Generalized the self-call walker to a group.** `walk`'s target went from one closure
  (`&ValueRef`) to a group (`&[ValueRef]`); `resolves_to_self` → `resolves_to_target`
  (membership). Self-recursion (G-1..G-7) is the singleton-group case
  (`std::slice::from_ref(cv)`) — behaviour unchanged. `member_descends` reads each member's
  arms, collecting group-calls and descending half-line stops (`descending_stop`).
- **Grounds** `isEven`/`isOdd` on `n <= 0` (each edge −1). **Sound Unproven:** a
  `ping`/`pong` cycle carrying `n` unchanged (no descent). A single function → `group.len()
  < 2` → skipped (the self-recursion candidates own it).
- **Deferred:** mixed-sign oscillator cycles (composed descent needs the full cycle
  composition, GR-07), point-base mutual (even/odd on `n == 0` — grid + domain), multi-param
  / lexicographic mutual; then wiring. **`// [ask-author]`:** none.

---

## 2026-07-30 — Grounding G-7: constant-drift refutation generalized (period-1 orbit + ascending)

Rounded out the refutation side — `drift_away` now handles **any** constant drift, not just
descending. `grounding.rs` +2 tests; **361 lib** + 111 conformance green, clippy clean.

- **Generalized `drift_away`/`reaches`.** The forward orbit `{ start + drift·k : k ≥ 0 }` is
  refuting when it misses every base region, for `drift < 0` (GR-23a drift-away, descending),
  `drift > 0` (ascending mirror), **and `drift == 0`** — a **period-1 closed orbit** (GR-11's
  degenerate case: `f(n)` recurring on itself). Dropped the `d >= 0` rejection; read the drift
  with `position_drift` (so a bare `f(n)` gives drift 0). `reaches` now special-cases the
  fixed point (`p == start`) and picks the half-line crossing by drift sign.
- **Refutes** `f = (n) => n == 0 ? 0 : f(n)` at witness 5 (orbit `{5}` forever) and
  `f = (n) => n == 0 ? 0 : f(n + 1)` at witness 5 (ascends past the base 0). Existing
  descending cases (specimen 12, even/odd witness parity) unchanged.
- **Soundness preserved:** still one forced linear path (single recursive row + call); a
  broad domain has no admitted witness → Unproven (GR-22). The general closed-orbit form
  (a required-dependency *cycle*, GR-11 — specimen 22b) remains a later increment.
- **`// [ask-author]`:** none.

---

## 2026-07-30 — Grounding G-6: structural descent (§2b, tuple peel)

Grounding moves beyond numbers — list/tuple recursion. `grounding.rs` +3 tests; **359 lib**
+ 111 conformance green, clippy clean. Still unwired.

- **`structural_descent(callee)`.** The body pattern-matches a parameter
  (`l :: { [] => …, [h, ...rest] => … f(rest) … }`); every recursive arm's pattern peels
  ≥1 element and binds a named remainder, and every self-call passes that remainder back in
  the parameter's position. The parameter's **length** is intrinsically `GE(0) ∧ Mod(1,0)`
  (a non-negative integer, tuple Λ-semantics) and drops by the peel count each step —
  strictly decreasing and bounded below by 0.
- **Key insight — termination is intrinsic, no base check needed.** A length that undershoots
  the peel pattern simply stops matching it; exhaustiveness (a missing base) is **E10's**
  concern, not grounding's. So peeling ≥1 always terminates — no domain, no numeric measure,
  no landing check. `reaches`/grid machinery untouched.
- **Grounds** `f = (l) => l :: { [] => 0; [h, ...rest] => 1 + f(rest) }` and the
  accumulator variant `f = (l, acc) => … f(rest, acc + h)` (peeled position descends, `acc`
  carried). **Sound Unproven:** recursing on the rebuilt whole tuple (`f([h, ...rest])`) —
  no descent (also correctly declines specimen 22b's `f(l)` second call, which doesn't peel).
- **Machinery:** `peel_binding(pat)` (a `Pat::Tuple` with ≥1 fixed element and one *named*
  rest → the remainder name; unnamed/absent rest or `[...all]` → `None`); reuses the
  scrutinee-is-a-parameter check (`param_index`) and `collect_self_calls`.
- **Deferred:** peel-k with a length grid (a base must cover lengths `0..k-1`), `restrict_len`
  structural facts (§2b via GR-08), point-base/Ackermann, §4 exact-singleton chains, §8
  WorldDecided, mutual SCC; then wiring. **`// [ask-author]`:** none.

---

## 2026-07-30 — Grounding G-5: lexicographic descent (§5 GR-13/14)

The first **path-sensitive** grounding candidate — the lex certificate. `grounding.rs`
+2 tests; **356 lib** + 111 conformance green, clippy clean. Still unwired.

- **`lex_descent(callee)`.** Some ordered sequence of argument positions (the *dictionary*,
  GR-14) lex-decreases on every recursive call: reading in order, the first changed position
  **decreases**, and **every decreasing position is bounded below on that call's path** — a
  lower-bound guard gates its decreasing transition (landing at component grain, GR-14
  domain closure), so each component is well-founded. Grounds `(a, b) => a <= 0 ? b : b <= 0
  ? f(a-1, 10) : f(a, b-1)` — neither argument descends monotonically (b resets to 10) but
  the lex order does; both floors come from the **path guards**, not the domain.
- **New machinery — path threading.** Unified the self-call walker into one `walk` that
  carries a per-parameter **lower-bound vector** `lb`: entering a `Match` arm accumulates
  the lower bounds its guard contributes (a `p > c`/`p >= c`, or the negation of an earlier
  `p <= c`/`p < c` under first-match). `collect_self_calls` (G-1/G-2/G-4) is now a thin
  wrapper dropping paths. Plus `lex_call_ok` (the per-call lex+gating check), `position_drift`
  (`param → 0`, `param ± c → ±c`), `guard_lb`/`negate_cmp`/`param_index`, and `injective_seqs`
  (the GR-14 dictionary enumeration, arity-bounded).
- **Sound Unproven:** a relational floor (`a == b` stop puts no constant lower bound on
  `a` → its decrease is ungated) — terminates, but this route can't prove a floor.
- **Scope (honest):** v1 dictionary positions are argument positions only (GR-14);
  components are **descending**; floors come from half-line/guard lower bounds. **Ackermann
  is not yet covered** — its `m == 0`/`n == 0` point stops give `!= 0` on negation (no
  lower bound), needing the grid + domain (GR-05(2)/GR-18) — a later increment. Single
  function / one cycle; mutual SCC deferred.
- **`// [ask-author]`:** none.

---

## 2026-07-30 — Grounding G-4: program-expressed compound measures (§6 GR-15a/16)

Generalized G-3's bare counter into a **linear program-expressed measure** — the other
half of §6. `grounding.rs` +2 tests; **354 lib** + 111 conformance green, clippy clean.
Still unwired.

- **`counter_descent` → `measure_descent`.** A base arm's half-line stop `E ⋈ c` whose
  varying side `E` is a **linear** combination of the parameters (GR-15a: the expression
  the base tests — `n`, `2a + b`). Drift per recursive call read by **substitute-and-
  normalize** (GR-16): substitute the call's arguments into `E`, normalize as a linear
  form, subtract; a nonzero constant of a single sign facing the stop is a floored monotone
  measure. Coefficient-0 positions are carried freely. Structural, domain-independent
  landing (half-line). **Subsumes** the bare-argument counter (`E = n`) — the G-3 tests all
  pass unchanged.
- **New machinery (self-contained, ~60 LOC):** `LinComb { coeffs, constant }` with
  add/sub/scale; `linear_form(expr, params)` (Const/Ref/Add/Sub/Neg/Mul-by-constant → a
  linear form; `param·param`, division-by-variable, non-param refs → `None`); `drift_on`
  (the substitute-and-normalize). Written in-module rather than reusing `oracle::poly`
  (private, canonicalization-oriented, no coefficient extraction).
- **Grounds** `f = (a, b) => 2a+b <= 0 ? a : f(a-1, b+1)` — where **no single argument**
  descends (b ascends) but the linear measure `2a+b` drifts −1. **Sound Unproven:** a
  two-varying-side relational stop (`a <= b`) — the correlation is [permanent] and this
  route concludes nothing (GR-15a/18), even when it happens to terminate.
- **Deferred:** point-base grid + GR-18 range (needed for `E == c` compound stops),
  nonlinear measures, §5 lexicographic (multi-component), §7 closed-orbit, §4
  exact-singleton chains, §8 WorldDecided; then wiring. **`// [ask-author]`:** none.

---

## 2026-07-30 — Grounding G-3: multi-parameter counter descent (§6 GR-15a)

Breadth — grounding now covers the common **accumulator + counter** shape. `grounding.rs`
+4 tests. **352 lib** + 111 conformance green, clippy clean. Still unwired.

- **`counter_descent(callee)`** — the single-component case of GR-14, a bare-argument
  measure (GR-15a). Some argument position is a *counter*: a base arm reached **before**
  any recursive arm stops on it with a **half-line** test (`n <= 0` / `n >= 100`), and
  every recursive call steps that position by a constant strictly in the stopping
  direction (floor δ = |drift|); the other positions are carried freely. **Landing is
  structural and domain-independent** — a floored monotone step crosses a half-line in
  finitely many steps (Archimedean), so no per-parameter domain projection is needed. Both
  orientations (descend→lower stop, ascend→upper stop) via `stop_matches`/`flip`.
- **Grounds** `f = (n, acc) => n <= 0 ? acc : f(n-1, acc+n)` and its ascending mirror.
  **Sound Unproven:** a counter moving *away* from its stop (`f(n+1)` under `n <= 0`), and
  a carried-only recursion (stop on a non-moving position). Point (`==`) multi-param stops
  need the grid + domain → deferred (single-param point base stays with `numeric_descent`).
- **Soundness details:** the stop must be tested at an arm index **before** any recursive
  arm (`idx < first_rec`), else first-match could reach the recursion first; a spread
  self-call has no reliable positional mapping → recorded empty → rejected. The walker
  `collect_self_calls` now yields each self-call's **full positional arg list**
  (`Vec<Vec<Expr>>`); G-1/G-2 read position 0.
- **Deferred:** §6 compound measures (`2a+b`, substitute-and-normalize GR-16 — needs
  poly-NF), point-base multi-param (grid), §5 lexicographic (multi-component), §7
  closed-orbit, §4 exact-singleton chains, §8 WorldDecided; then wiring. **`// [ask-author]`:**
  none.

---

## 2026-07-30 — Grounding G-2: the drift-away refutation (§7 / GR-23a)

The negative half of the numeric certificate — the same machinery, from the other side.
`grounding.rs` +3 tests. **348 lib** + 111 conformance green, clippy clean. Still unwired.

- **`ground` now three-voiced.** After descent (GR-05) fails to prove, an **admitted
  witness** — a represented-exact start actually written at the call (GR-22, i.e. the
  domain is `Equals(v)` / a point) — may **refute** by drift-away. No witness (a broad
  domain) ⇒ `Unproven`, never a synthesized witness (GR-21; specimen 3c).
- **`drift_away(callee, start, cenv)` (GR-23a).** A single forced *linear* recursion (one
  recursive row, one self-call, constant negative drift) whose forward lattice
  `{ start + drift·k : k ≥ 0 }` provably **misses every base region** is a forced infinite
  descent → `Refuted`. `reaches(start, d, base)` decides landing per base shape: a **point**
  `p` is on the lattice iff `(start − p)/|d|` is a non-negative integer (the parity/grid
  test); a downward half-line is always reached; an upward half-line only at `k = 0`;
  unknown shapes are conservative (`true` → block the refutation). The lattice includes the
  start, so a start already in a base is correctly not a valid divergent start.
- **Specimen 12 lands as specified.** `f = n => n==0 ? 0 : f(n-2)`: from witness **1** the
  odd lattice `1, −1, −3, …` misses the even base 0 → **Refuted, witness 1**; from **2**
  the lattice hits 0 → **Unproven** (terminates, and non-unit descent isn't proved). Same
  function, opposite fate by witness parity — the whole point of witnessed refutation.
- **Soundness stance:** `drift_away` returns `true` only when the base-miss is certain;
  branching recursion, non-constant drift, and unrecognized base shapes all yield `false`
  (→ `Unproven`). No `interner` needed — the lattice test is exact rational arithmetic.
- **Deferred:** the **closed-orbit** refutation (GR-11, the required-dependency cycle,
  e.g. specimen 22b), §6 variable drift, §5 lex, §4 exact-singleton chains, §8 WorldDecided,
  multi-param/SCC; then wiring. **`// [ask-author]`:** none.

---

## 2026-07-30 — Grounding G-1: the numeric constant-drift descent certificate (GR-05)

First grounding increment — the **termination bound** the swap needs. New standalone
module `src/analyzer/grounding.rs` (6 tests). **345 lib** + 111 conformance green, clippy
clean. Not wired (same discipline as `region.rs`/`bodycheck.rs`).

- **`ground(callee, domain, cenv, interner) → Verdict {Grounded, Refuted, Unproven}`.**
  Judges a single-parameter self-recursive numeric function by GR-05's two components:
  **(1) well-founded descent** — every recursive call's drift on the parameter is a
  *negative constant* (`n - c`; exposed floor δ = |drift|); **(2) landing** — a downward
  half-line base (`k <= 1`) lands structurally, a point base (`n == 0`) needs grid
  alignment, handled for the clean unit-drift integer lattice (`GE(0) ∧ Mod(1,0)`).
- **Proves:** `countDown`, `factorial` (self-call read even when nested under `n * _`),
  half-line-base descent. **Sound Unproven (deferred):** ascending drift (no floor),
  non-unit drift to a point base (specimen 12 — refuted in a later increment, not falsely
  proved now), non-integer domain (dense measures deferred).
- **Reuse:** `region_table` for the arm split (base vs recursive rows); a `bodywalk`-style
  full-body walk to collect self-call args (resolving the callee through `closure.env` —
  recursion lives in the captures); `subcontract` for the integer-lattice + `≥ base`
  checks. **Candidate-locality (GR-04):** outside applicability → `Unproven`, never a
  false proof.
- **Deferred to later increments:** §7 refutation (drift-away / closed orbit), §6 variable
  drift, §5 lexicographic, §4 exact-singleton chains, §8 WorldDecided; multi-parameter and
  mutual SCC; then the **wiring** into the body check (the swap gate).
- **`// [ask-author]`:** none. Flagged (not blocking): grounding v0.5 is *ACCEPTED pending
  the author's stamp* — the judgment rules are stable; only the unproven **consequence**
  (P-1 warn-vs-reject) is open, and that is a wiring-time concern, not a judgment one.

---

## 2026-07-30 — Recovery Phase 2, step 5: corrected diagnosis — wrong cycle key, not a grounding gap (verified)

Step 4 called the swap failure a "soundness regression blocked on grounding." Re-reading
the grounding spec and **empirically re-running the wire**, that attribution was wrong on
the mechanism. Corrected here; the record (`bodycheck.rs` header, `OwedItems §0.1`) now
matches. 339 lib + 111 conformance green, clippy clean, unwired.

- **Grounding is a *termination* judgment** (GR-05 well-founded descent + landing; GR-11
  closed-orbit refutation), not a safe-input-domain deriver. The step-4 example
  `f=(x)=>x==0?f("x"):x+1` at `f(0)` **crashes** (`"x"+1`) — it terminates, so grounding
  was never the tool for it.
- **The real bug was my cycle key.** `body_summary`'s guard keyed on the closure
  *instance* alone, cutting the `f("x")` edge and dropping the trap. The spec (C§13.2a /
  GR-07: nodes are "instance × row/domain") and the old `ACTIVE_BODIES` key on
  **(instance, domain)**. Fixed the guard to `Vec<(ValueRef, Vec<Contract>)>`. `f(0)` and
  `f("x")` are distinct nodes → `f("x")` analyzed → trap caught. No grounding needed.
- **What actually gates the swap — verified.** Wiring `body_summary` *with the corrected
  key* **hangs** the suite on `a_growing_union_recursive_domain_terminates` and
  `recursive_domains::a_growing_non_singleton_recursive_domain_terminates`: the correct
  key won't cut distinct nodes, and a domain growing without end never converges. The old
  widening bounds this; **grounding is the specified replacement for that bound.** So a
  wired machine needs BOTH the correct key (done) AND the termination bound (grounding,
  unbuilt) — the suite proves neither alone works (instance-key: unsound; domain-key:
  hangs).
- **Net:** design has no gap (safety check + (instance,domain) cycle detection + grounding
  are all specified); the blocker is implementation of grounding's *termination bound*.
  Task #50/#51 framing updated. Reverted the wire; kept the corrected key.
- **`// [ask-author]`:** none.

---

## 2026-07-30 — Recovery Phase 2, step 4: swap attempted → reverted (soundness); blocked on grounding

Executed the swap the step-3 entry called "unblocked," and **reverted it**. The step-3
prediction of mere "precision test motion" was **wrong**: the swap is a **soundness
regression**, and the real blocker is **grounding (C§10)**, not `body_check` coverage.
Back to **339 lib** + 111 conformance, clippy clean; `body_summary` stays built-but-unwired.

- **What I did.** Added an instance-keyed re-entry guard + `errors()` to `body_summary`
  (inert standalone — 339 still green), then rewired `analyze_apply`'s `Known(cv)` branch
  and `callee_completion` to `body_summary`. Build clean; **one** test failed:
  `body_safety::a_recursive_call_over_a_new_domain_is_analyzed`.
- **Why it's soundness, not precision.** `f = (x) => x==0 ? f("x") : x+1`; `f(0)` recurses
  to `f("x")`, and `"x" + 1` **traps at runtime**. The instance-keyed guard cuts the
  `f("x")` edge (f already active) → cycle assumption (`Top`, no finding) → `f(0)`
  **accepted**. Accepting a trapping program is unsound. The old `instance_body_summary`
  is sound here because it is **domain-indexed**: `"x"` is a program literal, so the
  new-domain (String) edge is analyzed and `"x"+1` refutes.
- **Correction to the audit §5 DELETE list.** `domain_admitted` / widening / the
  domain-indexed cutoff are **soundness-load-bearing for domain-changing recursion** — not
  merely wrong-layer scaffolding. Their sound replacement is the **grounding arc (C§10)**,
  which derives the recursion's input domain (`0 → "x" → …`) so the body check covers the
  new domain. Grounding is **not built**, so the Archive9 machinery **stays** for now.
- **Reframe of task #50.** The swap is **blocked on grounding**, not "on `body_check`
  recursion." Next recovery move: **implement grounding (C§10)**, then re-attempt the swap
  with a grounding-supplied recursion domain. Recorded in `bodycheck.rs` module header,
  the `ACTIVE` guard doc, and `OwedItems.md §0.1`.
- **`// [ask-author]`:** none — the failing test already encodes the author's ruling that
  domain-changing recursion must be followed.

---

## 2026-07-30 — Recovery Phase 2, step 3: `body_summary` — the full region-table summary

The drop-in candidate for the wrong-layer `induction::InstanceBodySummary`. Extended
`bodycheck.rs`; 6 tests. Full tree **339 lib** + 111 conformance, clippy clean. Still
standalone (not wired; nothing deleted).

- **`body_summary(callee, args, cenv, interner) → BodySummary { produced, completion,
  findings }`** — same shape as `InstanceBodySummary`. `findings` = the path-sensitive
  [`body_check`] safety (RT-14 discipline); `produced`/`completion` = analyzing the whole
  body once under the captures + argument-narrowed parameters (E10 exhaustiveness via
  `analyze_match`; the whole-body safety findings discarded — `body_check` owns those).
- **Terminates on recursion, verified.** `body_check`/`whole_body` route nested calls
  through the *existing* recursion-safe apply path, so a recursive body doesn't loop and
  still catches its local traps — `f = n => n==0 ? (1+"x") : f(n-1)` is rejected;
  factorial summarizes coarsely (`produced` Top via the cycle) and completes. (The
  re-entry guard that a *wired* `body_summary` needs — so it doesn't re-enter itself —
  lands with the swap.)
- **14.4 confirmed** — `capture_env` gives capture-dependent operation domains
  (`make(1)` inner → Number, `make("s")` inner → String) for free.
- **Now unblocked: the swap.** `body_summary` matches `InstanceBodySummary`'s interface
  and verdicts on the gate. The remaining swap is: add the re-entry guard; rewire
  `analyze_apply`'s `Known(cv)` branch to `body_summary` + the kept `call_return`
  (recursive-produced sharpening); **delete** `instance_body_summary`, `domain_admitted`,
  `kind_abstraction`, `literal_values`, `ACTIVE_BODIES`, the widening/downgrade pair
  (audit §5). Expect some *precision* test motion — Archive9's domain-indexed recursion
  precision is deliberately replaced by the coarser cycle + return induction.
- **`// [ask-author]`:** none.

---

## 2026-07-30 — Recovery Phase 2: wiring/delete investigation — swap blocked on recursion

Investigated the swap (replace `analyze_apply`'s body-safety with `body_check`, delete
the superseded machinery). **Finding: premature — the swap is blocked; deferring it.**
333 lib green. One test added (14.4).

- **The current live path already passes the gate.** `instance_body_summary` (the live
  safety path, Archive6–9) already rejects `bad()`, transitive body traps, and a
  recursive body with a local trap (tests `direct/transitive_body_trap_is_rejected`,
  `a_recursive_body_with_a_local_trap_is_rejected`). So `body_check` and the old path
  **agree on verdicts**; the difference is architecture (region table vs call-site
  body-safety propagation), not correctness — no smoking gun left to fix by swapping.
- **14.4 already works.** `body_check`'s `capture_env` binds captures to `Equals(value)`,
  so a capture-dependent *operation* domain falls out: `make = y => x => x + y`;
  `make(1)`'s inner demands `x : Number`, `make("s")`'s demands `x : String`. Added
  `bodycheck_captures::inner_closure_domain_depends_on_the_capture`.
- **The blocker.** `instance_body_summary` bundles `{ produced, completion, findings }`
  **and** handles recursion (the `ACTIVE_BODIES` re-entry cutoff + domain widening) and
  multi-parameter. `body_check` returns only findings, over the non-recursive
  single-parameter fragment. Wiring `body_check` into `analyze_apply` for a **recursive**
  callee would **infinite-loop** (it analyzes the recursive call's body → `analyze_apply`
  → `body_check` → …, with no re-entry guard). So the swap cannot land until `body_check`
  becomes a full summary with recursion handling.
- **Corrected order (audit §5's own):** extend `body_check` → a `{produced, completion,
  findings}` summary; add the re-entry cutoff + re-plumb `call_return` (return induction,
  the *keep* set) onto it (14.5); the capture-dependent-**guard** case (region-table
  b/c) and multi-parameter (§5). **Then** the swap+delete is a clean drop-in. Reported
  to the author before proceeding.

---

## 2026-07-30 — Recovery Phase 2, step 2: the call-site body check (the 14.1–14.3 gate)

The safety proof that consumes the region table — `BodySafe(instance, argument)`, the
dissolved accepted-domain (E3/E-7, errata). New module `src/analyzer/bodycheck.rs`;
5 tests; the recovery's gate examples pass. Full tree **332 lib** + 111 conformance,
clippy clean. **Still no superseded machinery deleted** (audit §5 — the check is
standalone, not yet wired into `analyze_apply`).

- **`body_check(callee, args, cenv, interner) → Vec<Finding>`** — there is no
  materialized accepted domain (dissolved); a call is proven safe by **running the
  ordinary body check under the actual input**. For a single-parameter callee: build
  the region table, `select` the reachable rows for the argument, bind the parameter to
  each selected row's region, and `analyze` the row's result — reusing the existing
  operation-safety machinery. Captures bind to `Equals(value)`. Zero-parameter bodies
  analyze directly.
- **RT-14 witness discipline [chose].** A row's finding is an `Error` only when the row
  is **definitely reached** — this row exact **and** every earlier selected row exact —
  so a real input reaches it; a may-region (non-exact) row's `Error` downgrades to a
  `Warning` (an over-approximate candidate invents no witness).
- **The gate, verified:** **14.1** `() => 1 + "x"` → `bad()` rejected (the body traps
  for its one input `()`). **14.2** `x => x + 1` → `f(Number)` ok, `f(String)` rejected,
  `f(Top)` flagged. **14.3** `n => n == 0 ? 1 : n + "x"` → the accepted region
  `Equals(0) ∪ String` proved **path-sensitively**: `f(0)` ok, `f(5)` **rejected** (the
  exact else-arm's `5 + "x"` traps, a definite refutation with witness 5), `f(String)`
  ok (the else arm is `String + String`), `f(Top)` rejected (witness 5). RT-14: an
  opaque-guard row's trap is a warning, never a rejection.
- **Correction while writing:** I first expected `f(Top)` in 14.3 to be *unproven*; it's
  a genuine **refutation** — over `Top` the sampler produces `n = 5`, which reaches the
  exact else and traps, so the input obligation (`n : String` on that path) is refuted
  by a represented witness. `Top ⊄ (Equals(0) ∪ String)`. (14.2's `f(Top)` is only a
  warning today — the `Top + Number` sampler is incomplete; sound, less precise.)
- **Scope / next:** capture-free, zero-/single-parameter. Owed: multi-parameter
  (argument-tuple projection §5), the guards' own path demands, the C§13.4 instance
  cache, and the **wiring** — replace `analyze_apply`'s call-site body-safety machinery
  with `body_check`, then delete the superseded functions (audit §5, once the current
  behaviours hold).
- **`// [ask-author]`:** none.

---

## 2026-07-30 — Recovery Phase 2, step 1: the region-table computation

The first build of the recovery (author-directed: demand core → region table →
call-site body check). New module `src/analyzer/region.rs` (`next-region-table-
specification-v0-3.md` §2–§4); 5 tests. Full tree **328 lib** + 111 conformance,
clippy clean. **No superseded machinery deleted yet** (audit §5: nothing goes until
the replacement passes the current behaviours).

- **`region_table(body, param, cenv) → Vec<Row>`** — branch **reachability** as ordered
  `(region, exact, result)` rows read forward from the arms. Guard case **(a)** (a
  supported comparison of the parameter against a constant → the direct region,
  `exact`): `n == v → Range(v,v)`, `n != v → Difference(Top, Equals)`, `< / <= / > / >=`
  → `Less/LessEq/Greater/GreaterEq`, flip-aware. Case **(d)** (anything else — a
  non-parameter tested side, an unsupported op) → `Top`, non-exact (total). Patterns
  via `pattern_contract` with a no-rest exactness bit (§4).
- **`select(table, arg_domain) → Vec<Selected>`** — the ordered remainder walk (§3):
  a row is selected when `remaining ∩ region` is not proven empty; an **exact** row
  subtracts, a non-exact row consumes nothing (so an opaque guard leaves the else-arm
  live). First-match is the walk, never pre-carved (W-5).
- **Chose — the singleton fast path.** A known argument `Equals(v)` selects by
  denotational `Contract::contains(v)` (exact rows resolve first-match, §3), sidestepping
  the accumulated-`Difference` imprecision the general algebra can't always simplify;
  open domains use the general walk where over-selection is sound (branches carried +
  joined). Verified: `n == 0 ? 1 : n+"x"` → 2 rows; `f(0)`/`f(5)`/`f(3.5)` each land in
  one arm; opaque guard keeps both; the RT-05 ladder's `3.5` lands in the middle arm.
- **Scope / next:** capture-free single-parameter fragment. Kernel-desugar note —
  `&&`/`||`/`!` are Matches, so compound/negated guards read as case (d) (sound); a
  `?:` chain nests (else-result is a Match the body check recurses into). Owed:
  case (b)/(c) (captures), argument-tuple projection (§5, multi-param), and the
  **call-site body check** that consumes this table (gates 14.1–14.3, replaces the
  superseded machinery).
- **`// [ask-author]`:** none.

---

## 2026-07-30 — Record rebaseline against the grounding landing (no code)

Author feedback: my maintainer files (`PROGRESS`/`OwedItems`/`DECISIONS`) are dev
progress, **not spec** — the manifest'd canonical library is truth, and my files were
stale. A deep spec re-read (verified against the 07-30 / compendium-1.0.18 manifest,
19 files) corrected the record. **No code changed.**

- **Manifest**: 19/19 verify; landed files carry their patches (compendium **1.0.18**,
  app-induction **0.8.2**, test-suite **Phase GR**). My prior response wrongly leaned on
  PROGRESS's stale "14 files / 07-24" line and the 07-26 audit's "owed" claims.
- **`InferredAcceptedDomain` — DISSOLVED [errata E-6 (C§12.1), E-7 (E3), E-8 (E11),
  2026-07-24].** No materialized accepted-domain object; `where` is `BodySafe(instance,
  DeclaredInput) = proven` (run the ordinary body check under the declared input).
  **Q4 (eager vs lazy) is therefore moot**; eager preimage is *an optimization*
  (C§13.1). No separate accepted-domain spec (region-table §6 folds away). My last
  turn's "region-table procedure owed / I'll draft it" and "grounding arc owed" were
  both wrong.
- **Region-table** — `next-region-table-specification-v0-3.md` (0.3.2), *architecturally
  closed; C§17 item **discharged***. **Grounding** — `next-grounding-specification-v0-5.md`
  (0.5.1), DESIGN-CLOSED (compendium 1.0.18). Both: **implementation owed, design not**.
- **Record fixes:** `OwedItems.md` rewritten to the spec-truth (§0 the recovery
  Build/Delete/Keep; dissolutions off the list; region-table/grounding as
  design-closed-impl-owed; the genuine C§17 doc-owed set; P-1 + the reframed
  uncalled-unsafe-body policy pick). `PROGRESS` §1/§2/§3/§4/§5 rebaselined (19 files /
  1.0.18; the four "blocking rulings" marked resolved/dissolved; the call-site
  machinery marked superseded-by-recovery, not owed).
- **Residual open policy pick [ask-author]:** an *uncalled* proven-unsafe body
  (`() => 1 + "x"`) — flagged at the definition (error / goes-nowhere warning / silent),
  or only at the call per E3/E-7? No explicit ruling found. Narrow; off the recovery's
  critical path.

---

## 2026-07-26 — Recovery Phase 1: the spec-first audit (no code)

The author agreed the analyzer's body safety was built in the wrong layer and asked for
a spec-first audit before any further code. Delivered:
`NEXT-spec-audit-accepted-domains-phase1.md`. **No code changed.**

- **The finding is bigger and more precisely specified than "accepted domains".** The
  documents describe a **three-layer substrate**: *symbolic summary template* per lambda
  **shape** → *instantiated region table* per **instance** → call-site **input
  obligation + row selection**. C§13.2's opening line states it outright — *"One symbolic
  control summary per lambda shape; instantiated regional analyses parameterized by
  captured-environment contracts"* — and its call-site procedure says a call **obtains**
  the instantiated region table, never *analyzes the body*. C§13.4 caches both layers;
  C§18 says the split *"enters with the demand core"*.
- **It is a skipped build-order step, not a design gap.** Part I: *"contracts +
  three-valued checker → **demand core + additive recursion** → the re-entry ladder"*,
  and CLAUDE.md marks the order "do not reorder". Verified: no demand core exists in
  `src/` (no backward/subscription/preimage machinery), no summary template, no region
  table. C§13.2's *consumers* (instances, return facts, induction) were built on the hole;
  the Archive(6)–(10) mechanisms were reconstructing the substrate forward at call sites.
- **The region table is why one structure suffices.** Worked in the audit §3: for
  `x => x == 0 ? 1 : x + "x"` the rows are `(Equals(0) | — | Equals(1))` and
  `(Difference(Top, Equals(0)) | x:String | Kind(String))`, giving
  `AcceptedDomain = Equals(0) ∪ String` **and** the per-row return **and** the safety
  verdict from one artifact, computed once. `() => 1 + "x"` gets `AcceptedDomain = ∅` at
  the *template* level — no captures, no call site.
- **Recursion has two independent domain sources.** Operation demands (C§5/C§7/C§13.1)
  *and* **grounding** (C§10) — the Phase-A grids' *"Derived input contract:
  `Intersection(GreaterOrEqual(0), Mod(1, 0))`"* comes from drift/base/orbit reasoning,
  not from any operation's safety demand. The grounding arc is unbuilt; A-NEG depends on
  it.
- **Four items owed from the author** (audit §4), gating Phase 2/3: region-table
  computation steps (already in C§17's owed list — the load-bearing one); whether
  `InferredAcceptedDomain` is eagerly materialized or a subscription set (C§13.1 calls
  preimage an *"optimization"*, E11 needs a comparable contract); empty-domain semantics
  at a definition (unspecified anywhere); and the C§10 grounding arc.
- **One draft ask withdrawn — my error, corrected same day [user-caught].** The draft
  listed a fifth item, *"app spec v0.2 is absent from the repo"*. Wrong: `MANIFEST.sha256.txt`
  lists only v0.8, so no canonical file is missing, and **"As v0.2" is a changelog idiom**
  (*"unchanged since v0.2"*) used six times in v0.8 — where content matters it is restated
  in place (§5 *"As v0.2: admission `I ⊆ GroundedRows(instance)`; straddles partition…"*;
  §10 *"As v0.2, plus: `GeneralizationDomains` is extraction-rule-bounded…"*), and the
  header records the v0.2 round as *"all integrated here"*. §3 **is** thin — its content is
  a list of named ingredients rather than a procedure — but that is item 1 (region-table
  computation steps), not a missing document. Folded into item 1.
- **What survives the recovery** (per the architecture review §10, confirmed by the
  audit): instance+domain fact identity, the `segment_nullable` structural fix, fuel out
  of normative analysis, no oracle execution of user functions, correlated-alternative
  work, and dead-arm/path narrowing — which becomes *more* central, since region rows
  **are** path conditions.
- **A test-quality correction recorded:** the existing body-safety tests assert
  call-site behaviour over *unconditionally* invalid bodies (`() => 1 + "x"`), which under
  this architecture are **definition-site** facts. They pass either way — which is exactly
  why they never caught the design error. They are to be re-framed as domain assertions.
- **`// [ask-author]`:** the five §4 items. Nothing is being built on them until ruled
  (CLAUDE.md rule 3).

---

## 2026-07-26 — Archive10 small corrections + a design question raised (body safety is in the wrong layer)

Two parts: three **small** corrections from Archive(10), and — prompted by a reader's
question — a **finding raised to the author** that the mechanism those corrections
maintain is not the one the documents specify. Full tree 323 lib + 111 conformance,
clippy clean.

**The corrections** (each tightens or *shrinks* the mechanism; none grows it):

- **Termination [§11–§13] — my finiteness argument was invalid, verified.** I claimed
  the exact-domain state space was finite because the *literal vocabulary* is finite. But
  contract keys compare **structurally** and `union_of` never flattens/dedups, so
  `Equals(0)`, `Union(E0,E0)`, `Union(Union(E0,E0),E0)`, … are infinitely many distinct
  keys over one literal. I built the reviewer's counterexample
  (`f = (x, b) => f(b ? x : 0, b)`) before acting on the claim: **stack overflow**. Fixed
  by Archive10's Option A — `domain_admitted` accepts **atoms only** (Kind / Top / Bottom
  / Indeterminate / `Equals(program literal)`), so a union widens on the first recursive
  edge and the space per position is bounded by `|literals| + |Kinds| + 3`. Now
  terminates in 0.00s; kept as a permanent regression. (Union *precision* would need a
  canonical union normal form before a union can be a key — Option B, not done.)
- **Completion variance [§6–§9].** I had downgraded widened-domain *findings* but not
  *completion* — the same variance argument applies to both existential channels, so a
  fall-through provable only in `D_broad ∖ D_narrow` could still refute at an expecting
  seat. `downgrade_completion`: `FallsThrough → MayFallThrough` when widened; `Produces`
  and `MayFallThrough` unaffected (a universal over a superset still holds on a subset).
- **Inhabitance [§14–§16].** `NotAFunction { inhabited }` — *disjointness proves what
  happens **if** a value exists, never that one **does***. A proven inhabitant refutes
  (Error); an empty-but-not-`Bottom` leaf (`Intersection(Number, String)`, which
  narrowing can build) now warns instead of manufacturing a refutation.

**The finding — `NEXT-implementation-finding-accepted-domains.md` [ask-author].**
A reader asked why `bad = () => 1 + "x"` needs call-site machinery at all: it traps
unconditionally, so it should simply not compile. Measured: `analyze(() => 1 + "x")` →
`accepted, findings=[], contract=Top` — `Expr::Lambda` hits the catch-all and the body is
**never analyzed at its definition**. That is why five rounds have been about propagating
traps outward from call sites.

But E11 (*"DeclaredInput ⊑ **InferredAcceptedDomain** … every demand **the body
derives**"*), C§12.1 (*"the body's domain"*) and E3 (*"**body-derived domain**"*) specify a
different mechanism: analyze each body **once** to derive the inputs it is safe for, then
check calls against that. Under it `() => 1 + "x"` has an *empty* accepted domain and dies
at its definition, while `(x) => x + 1` keeps a perfectly good definition and only
`f("hello")` is rejected — the case that genuinely needs call-site reasoning.
`obligation.rs::accepted_domain` derives from the **parameter pattern only**; the
`InferredAcceptedDomain` E11 names does not exist here.

**Why it matters:** Archive(10)'s two structural blockers are artifacts of the layer, not
of NEXT — widened-domain evidence exists only because a body is re-analyzed under a
domain other than the one demanded, and advance-bounded domain universes exist only
because call-site domains form a chain. Analyzing a body once removes both. (The
recursive fixpoint does *not* vanish, but it becomes one lattice element per function —
the SCC/hypothesis machinery already built and already terminating — rather than a body
walk per call-site domain.)

**Therefore:** the larger Archive(10) recommendations (canonical union basis,
preconstructed candidate-domain inventory, full witness plumbing) are **deliberately not
done**, pending the author's ruling. Continuing to scaffold the mechanism without one
would be filling silently (CLAUDE.md rule 3).

---

## 2026-07-26 — Archive9: the finite admitted-domain basis + total alternative enumeration

Archive(9) approved the `InstanceBodySummary` unification but found three blockers: a
widened domain could **refute** a narrower call (false rejection), `callee_alternatives`
**dropped** non-`Equals(fn)` leaves (false acceptance), and dynamic widening did **not
guarantee termination** (a live hang). All three fixed. Full tree 322 lib + 111
conformance, clippy clean.

- **Alternative enumeration is now total** [§9–§11]. `CalleeAlt = Known(fn) |
  UnknownFunction | NotAFunction`; `callee_alternatives` classifies **every** live leaf
  (`Union` recurses; `Bottom` drops as proven-empty), and `analyze_apply` combines them
  conjunctively: `NotAFunction` → operation-safety **Error** + `Bottom`;
  `UnknownFunction` → **Warning** + `produced = Top` + `MayFallThrough` (never a
  sharpening); `Known` → the precise body summary. So `(b ? good : 1)()` rejects (§17.2)
  and `Equals(good) ∪ Kind(Function)` no longer sharpens to `good`'s `Equals(1)` (§17.3).
  The old whole-contract `disjoint(cc, Function)` check is subsumed and removed.
- **A widened domain may not refute** [§6–§8]. Findings from a state reached by widening
  are **downgraded to `Warning`** — the trap need not have a witness represented in the
  demanded domain. Never dropped silently (they stay visible as the third voice), never a
  refutation. This is the variance rule: *broad-domain safety ⇒ narrow safe; broad-domain
  refutation ⇒ narrow refuted only with a represented witness.*
- **Termination from a finite admitted basis, not dynamic widening** [§13–§16]. A
  recursive edge is analyzed at its **exact** domain only when that domain lies in the
  program's finite, advance-known vocabulary — `domain_admitted`: every leaf is a
  `Kind`/`Top`/`Bottom`/`Indeterminate`, or an `Equals(v)` whose value appears as a
  literal in the reachable group (`bodywalk::literal_values`, §4b's "derived from the
  finite program"). A **computed** domain outside it (`Range(1,3) → Range(2,5) → …`)
  widens into the **Kind basis** via the new total `Contract::kind_abstraction` (defined
  on every form, so it reaches a fixed point in one step, unlike `generalize`), and the
  state universe is thereby bounded in advance: exact states ⊆ vocabulary^arity, widened
  states ⊆ Kind-basis^arity.
  - **Why exact-when-admitted matters:** it is what keeps `f(0) → f(1) → 1` precise
    (§17.1 accepts — `1` is a program literal, so the dead-arm rule prunes the trapping
    branch) *while* Archive8's `f(0) → f("x")` still rejects (`"x"` is a literal too, so
    that genuine trap is found at its own narrow domain). Widening those would have
    broken one or the other.
- **Verified — the §17 gate:** widened-domain false refutation → **accept** (§17.1);
  non-function alternative → **reject** (§17.2); unknown-function alternative → not
  sharpened, downstream unproven (§17.3); growing `Range` recursion → **terminates by
  construction** (§17.4, 0.00s — no fuel, no stack limit). All Archive6/7/8 gates
  unchanged.
- **`// [ask-author]`:** none. Still owed toward the spec's full §4a/§4b form: the
  admitted basis is computed per call (`literal_values` re-walks the group — a
  memo/cache item, not correctness), and the *candidate graph* proper (pre-constructed
  inventory + SCC over `(instance, admitted-domain)`) is still the destination; the
  joint-correlated-operand driver is still not the normal `analyze_apply` path (§12);
  `may_not_complete` and the AP-30 witness remain owed.

---

## 2026-07-26 — Archive8: the InstanceBodySummary unification — (instance, input-domain) body analysis

Archive(8) confirmed the Archive7 fixes but found `SAFETY_STACK` keyed by `Lambda`
**shape** reintroduces the identity mistake already fixed for return facts, plus two
more gaps. Fixed by making the unit of interprocedural body analysis the **(instance,
input-domain)** node — the unification the reviews have pointed at for rounds. Full tree
318 lib + 111 conformance, clippy clean.

- **`instance_body_summary(callee, args) → InstanceBodySummary { produced, completion,
  findings }`** [mandated — Archive8 §10]. One analysis of an `(instance, input-domain)`
  node, **shared** by safety, completion, and the non-recursive return, replacing the
  three separate body walks + `SAFETY_STACK`. Nested applications recurse through
  `analyze → analyze_apply → instance_body_summary`, following the actual edges.
- **Identity is the concrete instance + domain, never shape** [Archive8 §3–§5]. The
  cycle stack is `Vec<(ValueRef, Vec<Contract>)>`. Fixes: **A** — `make(bad)` vs
  `make(b)` (same shape, different captures) are distinct nodes, not cut off; **B** —
  `f(0)` recursing to `f("x")` is analyzed over `[String]` (where `x+1` traps), not cut
  by a shape/instance match. Termination without a magic bound: an exact
  `(instance, domain)` cycle returns the assumption (a cycle adds no new *direct* trap);
  the **same instance** re-entered over a *finer* domain **generalizes to Kinds** and
  re-enters (`f(5)→f(4)→…→f(Number)`), so the abstract node stabilizes — a diverging
  `loop()` is analyzed once, never run.
- **Multi-alternative callees** [Archive8 §6]. `analyze_apply` enumerates every live
  `Equals(cv)` alternative of the callee contract (a singleton or a `Union` —
  `b ? bad : good`) and summarizes each over the actual args; results join. So a union
  callee's trapping alternative can no longer bypass safety.
- **Non-recursive return is the body's exact contract** [Archive8 §8/§11.4]. A callee's
  return is `instance_body_summary(...).produced` (exact) when non-recursive
  (`always() → Equals(true)`, not the generalized `Boolean`), so a return-dependent dead
  branch (`always() ? 1 : 1+"x"`) is pruned; recursive returns still use the induction
  (`call_return`) to sharpen the coarse cycle assumption (`is_recursive` gates the two).
- **Verified — the §11 gate:** same-shape/different-captures (A) → reject;
  same-instance/different-domain (B) → reject; multi-callee (C) → reject;
  return-dependent safe (D) → accept; the Archive6/7 body-safety + dead-arm tests
  unchanged. One driver test **improved**: a non-recursive dependency (`quad` over
  `double`) now resolves `double(n) → Number` directly (no reverse-topo needed for
  non-recursive deps; the mutual even/odd test still exercises the driver).
- **`// [ask-author]`:** none. Owed toward the *full* merge: the **recursive** return is
  still the separate induction rather than computed inside the summary's cycle
  resolution (so a recursive callee's `summary.produced` is coarse, sharpened at the call
  site) — folding the induction into the SCC-closed summary, plus `may_not_complete` and
  a memo/cache, are the remaining unification steps. `group_domains`/same-arity
  propagation now lives only in `infer_inner`, still interim.

---

## 2026-07-26 — Archive7 correction: body safety over actual call edges + dead-arm elimination

Archive(7) confirmed the oracle-execution removal but found the Archive6 `body_safety`
**unsound**: it walked syntactic `reachable_closures` over propagated `group_domains`,
which (1) misses parameter/local callees and (2) checks a callee under the wrong domain
— both **false acceptances**. Rewritten to follow **actual abstract call edges**; plus
dead-arm elimination for the paired false-rejection. Full tree 314 lib + 111
conformance, clippy clean.

- **Withdrawn rationale [§12].** The Archive6 entry's "safety is monotone reachability,
  so `reachable_closures` is the right tool" is **withdrawn**. Correct statement: *safety
  propagation is monotone only over semantically live instance/domain call edges;
  syntactic closure reachability alone is insufficient — it omits dynamically-resolved
  (parameter/local) callees and loses the input-domain a caller-level refutation needs.*
- **Edge-following `body_safety` [mandated — Archive7 §9].** Now analyzes `callee`'s body
  over the **actual argument domain** `args`; nested applications surface their own body
  safety through the ordinary body analysis (`analyze → analyze_apply → body_safety`), so
  the walk follows the **actual edges** — a **parameter callee is resolved from the
  abstract value** at the call site (`invoke(bad)` → `f = bad` → bad's trap), and each
  callee is checked over **its own edge domain** (`root(Number)` calling `helper("x")` →
  helper over `[String]`, where `"x" + 1` traps), never a reachable-closure set nor a
  propagated root domain. Recursion is cut by `SAFETY_STACK` (a shape under analysis
  contributes no new body), so a diverging `loop()` is analyzed once, never run.
  Suppressed under *pure* inference (a return-fact summarize, whose findings are
  discarded) but active within a safety walk — how transitive traps propagate.
- **Dead-arm elimination [Archive7 §11.3].** `analyze_match` now skips a **provably
  dead** arm: its narrowed region proven empty (a prior total arm consumed the remainder,
  or the pattern is disjoint), or its guard **proven false**. A guard **proven true**
  fires on its whole region like an unguarded arm (consumes → empties the remainder → the
  next arm is dead), and no longer muddies the fall-through classification. So `helper(0)`
  with body `x == 0 ? 1 : 1 + "x"` accepts — the `1 + "x"` branch is dead for `x = 0` and
  is not a false trap. Sound (an unreachable branch never executes) and precise.
- **Verified — the §11 adversarial gate:** parameter-callee trap → reject (§11.1);
  actual-edge-domain trap → reject (§11.2/§11.4); narrowed dead branch → accept (§11.3);
  the original 7 body-safety tests unchanged; no `analyze_match` regression across the
  suite.
- **`// [ask-author]`:** none. Owed toward the final §5/§6 form: fold body findings into
  an `InstanceBodySummary { produced, completion, may_not_complete, findings }` carried
  through `ApplicationOutcome` so return facts, completion, and safety share one
  (instance, input-domain) node over the SCC machinery (removes the separate walk and the
  repeated per-call-site analysis — into the C§13.4 cache). Same-arity `group_domains`
  stays only in `infer_inner`, still flagged interim.

---

## 2026-07-26 — Archive6 §8/§9: interprocedural body safety — remove the full-function oracle fold

The last oracle coupling in the analyzer, removed per the author's Archive(6) directive:
static analysis no longer **executes** a user function to find a trap. New
`induction::body_safety`; `analyze_apply`'s closed-call `eval_expr` fold deleted; 7
acceptance tests. Full tree 311 lib + 111 conformance, clippy clean.

- **The problem [mandated — Archive6 §8/§9].** `analyze_apply` folded a closed call by
  running the whole user call through the **unbounded** `eval_expr` — the last place the
  analyzer executed user code, and the divergence path. Bare deletion was unsound: the
  fold also **propagated body traps** (`badFn = () => 1 + "x"; badFn()`), which
  `infer_return_fact` discards.
- **`induction::body_safety(callee, root_args, cenv, interner) → Vec<Finding>`.** The
  proven-trap findings of the callee's body **and its transitive callees**. Reuses
  `analyze_instance_body` (already produces a full `Analysis` with findings) and
  `reachable_closures` (the call graph) — **not a new function analyzer**. The key
  subtlety the author flagged: a one-level `caller += analyze_instance_body(callee)` catches
  only *direct* traps, because a nested `helper()` coarsens under `without_inference`. So
  body-safety **walks the whole reachable group explicitly**, analyzing each body once
  over its domain (`group_domains`, shared with `infer_inner`) and surfacing its
  **Error**-severity findings — transitive coverage without a fixpoint (safety is
  monotone reachability, so `reachable_closures` is the right tool, not the SCC vector
  pass).
- **Errors only [chose, sound].** A `Warning` (unproven safety) over a coarsened domain
  is spurious — `factorial`'s `Number * Top` cannot be *proven* safe but does not trap —
  so propagating warnings would manufacture false findings (breaking the no-false-findings
  test). An `Error` is `OpSafety::Refuted`, a proven trap: sound to surface. Coarser
  callee **warnings** staying local is a precision/diagnostic gap, never unsoundness.
- **Structurally terminating.** Each reachable body is analyzed **once**, never executed
  — so `loop = () => loop()` is *analyzed*, not run. Guarded by `currently_inferring()`
  (the same re-entrancy bound), so a nested call during a body walk does not relaunch
  body-safety.
- **The fold is gone.** `analyze_apply` now: spread/function/act-kind/arg-obligation
  checks + `body_safety` (traps) + `call_return` (return) + `callee_completion`
  (completion). Closed-call exact-value folding is lost (a closed call types by inference,
  not `Equals(v)`) — no test relied on it (measured earlier), and it is the intended
  trade. `eval_prim` and `eval_expr` on a `Const` *access* stay (finite, terminating;
  re-homing into a neutral `semantics::*` shared kernel is naming/architecture, owed).
- **Verified — the author's 7-test gate:** direct trap → reject; transitive trap →
  reject; safe transitive → accept; factorial → terminates, **no false findings**;
  recursive local trap → surfaced; mutual-partner trap → reaches the caller; **diverging
  `loop()` → analysis terminates without execution** (the architectural proof the oracle
  coupling is gone). Also removed the stale even/odd out-of-domain comment (§the direct
  test superseded it).
- **`// [ask-author]`:** none. Same-arity domain propagation stays flagged **interim**
  (§5). Owed: warning-severity interprocedural propagation; the `InstanceBodySummary`
  unification (findings threaded through `ApplicationOutcome`, SCC driver over the full
  summary); neutral `semantics::*` re-homing of the finite kernel.

---

## 2026-07-26 — Archive5 §4: direct out-of-domain hypothesis regression + the §8/§9 fold-removal analysis

Archive(5) signed off on both Archive(4) fixes and asked for two follow-ups. The first
is landed; the second is analyzed and sharpened (it is larger than a deletion). Full
tree 304 lib + 111 conformance, clippy clean.

- **§4 — direct out-of-domain regression [done].** The even/odd mutual test no longer
  exercises domain *rejection* (the same-arity domain propagation removed the
  out-of-domain lookup), so the review asked for a direct unit test of the law.
  `fact_identity::a_hypothesis_applies_only_within_its_input_domain` installs `f :
  [Number] → Boolean` via the now-`pub(crate)` `with_hypotheses`/`Hypothesis` and locks:
  `hypothesis_for(f, [Number]) = hypothesis_for(f, [Equals(1)]) = Boolean`;
  `hypothesis_for(f, [String]) = hypothesis_for(f, [Top]) = None`. No execution,
  recursion, or oracle.
- **§8/§9 — remove the full-function `eval_expr` fold [analyzed; larger than a
  deletion].** Measured: disabling the closed-call fold in `analyze_apply` breaks **no**
  test (304 + 111 still green). But the fold is **not only precision** — for a *closed*
  call it also executes the body, so it **catches body traps** (`badFn()` with body
  `1 + "x"`). Removing it, `call_return → infer_return_fact` analyzes the body via
  `summarize` but **discards its findings**, so the analyzer would silently accept a
  closed call to an unconditionally-trapping function — an **unsoundness gap** the
  conformance suite happens not to cover. So the sound removal must **pair with
  lambda-body analysis** (surface the callee body's findings at the call site / at
  definition — the standing "Lambda bodies type as Top" increment), not a bare deletion.
  Also note: only *recursive* closed calls can diverge (a non-recursive callee's call
  graph is acyclic → terminates), so the divergence risk is narrower than the
  architectural coupling. Registered in OwedItems with this dependency; the same-arity
  domain propagation stays flagged **interim** (§5), to be replaced by call-edge/domain-
  derived candidates.
- **`// [ask-author]`:** none. The §8/§9 removal is real debt but its sound form is an
  increment (lambda-body findings), not a one-liner — flagged for a deliberate call
  rather than rushed.

---

## 2026-07-26 — Review cleanup: remove `segment_nullable(..., 8)` magic depth (Archive4 §11)

The review's one genuine analyzer-internal fuel: recursive-contract nullability
(`segment_nullable`, `recursive.rs`) bounded `Ref` recursion by a hard-coded `fuel = 8`,
returning `false` on exhaustion — conservative (not unsound) but Principle-7-violating
(precision on a magic number). Replaced with **path-based cycle detection**: a group
member already on the active unfolding path is a back-edge admitting no *new* length-0
realization → `false` for that branch; the path holds each member at most once, so its
depth is bounded by the group's member count — an advance bound from the finite
`RecGroup`, not a constant.

- **Strictly more precise:** a *non-cyclic* segment of any depth is now followed fully
  (the old cap wrongly cut at 8); only genuine `Ref` cycles are stopped.
- **No regression:** all RC-01…19 (and the full 303 lib + 111 conformance) pass
  unchanged — no tested case had depth > 8, so behavior on them is identical; the change
  only removes the false-negative tail and the magic number.
- **`// [ask-author]`:** none. `REFUTE_FUEL`/`OutOfFuel` (the other fuel the review
  audited) stays as external bounded witness-search / diagnostics — not wired into any
  normative verdict; kept in OwedItems as a standing scope rule.

---

## 2026-07-26 — Review correction: instance + domain-indexed hypothesis key (Archive4 §3/§4 — soundness blocker)

The author's Archive(4) review flagged the **one soundness blocker** before the tail is
complete: return-induction hypotheses were keyed by `Lambda` **shape** only, but
v0.8.1 requires `(shape, annotated env, input domain)` — "shape alone never suffices."
Now a soundness issue because `analyze_apply` consumes these facts. Fixed. Full tree
303 lib + 111 conformance, clippy clean.

- **The bug [mandated — v0.8.1 domain-indexed facts].** `HYPOTHESES: Vec<(Lambda,
  Contract)>` / `hypothesis_for(shape)` discarded the instance and input domain. Two
  aliasing classes: (a) **same shape, different captures** — `make=(v)=>()=>v; a=make(1);
  b=make("s")` share a shape, so a shape lookup could return `b`'s `String` fact for `a`;
  `h=(c,d)=>c?0:(d?a():b())` could falsely close `h:Number` though `h(false,false)→"s"`;
  (b) **wrong argument domain** — a fact proved over `[Number]` must not be reused on a
  `[String]` call.
- **The fix.** `Hypothesis { callee: ValueRef, input: Vec<Contract>, contract }`, keyed
  by the **concrete instance** (the closure value carries its captured environment) and
  the **input domain**. `hypothesis_for(callee, args, interner)` applies a fact only when
  `hyp.callee == callee` **and** `args ⊑ hyp.input` (`args_within` via `subcontract`) —
  the interim of the spec's `(shape, annotated env, I)` key. `call_return` passes the
  call's `(cv, arg_contracts)`, never `f.shape()`.
- **Consequence — mutual groups need a consistent domain [chose, sound].** With the root
  `even` pinned to the call-site `[Number]` but the partner `odd` analyzed over its wider
  accepted `[Top]`, `odd`'s `even(n-1)` carries the `Top`-domain Indeterminate-passthrough
  (`Number ∪ Indeterminate`), which is **not** `⊑ [Number]`, so `even`'s domain-indexed
  fact correctly declines it — breaking the mutual proof. Fix: `infer_inner` propagates
  the root's call-site domain to **same-arity partners**, so a mutual nest is analyzed
  over one consistent domain. Sound: the driver verifies each member over its assigned
  domain, so a mismatched propagation only fails, never falsely proves. Factorial's
  call-site sharpening (`f(k:Number)→Number`) is preserved.
- **Instance identity via `ValueRef ==` [chose].** Sound whichever way closure equality
  resolves (pointer or structural bisimulation): equal ⇒ genuinely the same instance
  (same captures) ⇒ same behavior ⇒ reuse is sound; unequal ⇒ no reuse (at worst a
  precision miss, never an alias).
- **Verified — `fact_identity::same_shape_different_captures_are_not_aliased`:** `a`/`b`
  are distinct values, keep distinct return facts (one Number, one String), and `h` does
  **not** falsely infer a Number return (with shape-only keying it would). The mutual
  `even(x)`-satisfies-a-tested-seat wiring test now exercises the consistent-domain path.
- **`// [ask-author]`:** none. Registered in OwedItems: the fold-path divergence (a
  *closed* recursive call like `f("x")` folds through the **unbounded** `eval_expr` and
  can diverge — orthogonal to the key, related to the review's oracle-boundary point) and
  the two remaining review items (`segment_nullable(..., 8)`, `REFUTE_FUEL` scope).

---

## 2026-07-25 — Induction tail, step 9: realized-witness refutation + the fuel/depth-bounded oracle (§6)

The permanent third voice for return facts: a concrete completing execution that
disproves a claim. Needs a **bounded** oracle run (a non-completing input is never a
witness, §6), which is also the long-owed M-04 fuel mechanism at the eval level. New
`src/analyzer/refute.rs`; fuel + call-depth bound on the oracle; `run_source_in`;
`Contract::proven_members`; 4 tests. Full tree 302 lib + 111 conformance, clippy clean.

- **The bounded oracle [mandated — §6's "non-completing input is never a witness"].**
  `eval_expr_bounded(expr, fuel, interner) → BoundedOutcome` (Produced / CompletedWithoutValue
  / Trapped / **OutOfFuel**). Two bounds on `Oracle` (unlimited by default — the truth
  source is unchanged): a step `fuel`, and — the load-bearing one — a **call-depth
  bound** (`FUELED_MAX_CALL_DEPTH = 256`). A loop-free functional program can only
  diverge by unbounded recursion depth, so the depth bound is the primary divergence
  guard **and** it caps the interpreter's own Rust stack — a diverging input yields
  `OutOfFuel`, never a stack overflow (the step-fuel bound alone overflowed the stack
  first). Exhaustion is a **machine limit** (Part A), surfaced via `out_of_fuel`, never
  a language trap.
- **`realized_refutation(callee, args, claim, interner) [mandated — §6].** Samples
  genuine argument tuples (`Contract::proven_members`), runs each through the bounded
  oracle, and returns the first `(arguments, v)` that **completes** with `v ∉ γ(claim)`
  — a *represented* completing execution. OutOfFuel / CompletedWithoutValue / Trapped
  are all skipped (never a witness against a return bound). The closure carries a
  concrete environment, so `e` is fixed and the search is over inputs `x`.
- **`check_return_claim` — three-voiced (§6).** Refutation is tried **first**
  (permanent in-namespace) — it is the sound ground truth, catching a false claim the
  abstract vector pass could otherwise leave merely unproven — then the inductive proof
  (per-compilation). Verified: `factorial : Number` → Proven; `factorial : String` →
  Refuted (witness `f(0)=1 ∉ String`); `factorial : Greater(0)` → Unproven (true, but
  the abstract pass can't prove it and no *completing* input disproves it — negatives
  diverge).
- **`run_source_in(src, interner)` [chose — the cross-interner subtlety].** Interned
  `==` is pointer identity, so a value **evaluated** in a different interner than it was
  built in gets `n == 0` wrong (cross-interner numbers compare unequal → factorial never
  grounds). `run_source_in` builds into a supplied interner; the refutation tests use one
  interner throughout. Analysis alone is cross-interner-safe (structural), which is why
  every prior test got away with two.
- **The bounds are sound-only [chose].** `FUELED_MAX_CALL_DEPTH`/`REFUTE_FUEL` govern
  only *what gets skipped* — a skipped input is never mistaken for a witness, so no
  bound value can produce a false refutation; a larger bound only finds *more* real
  witnesses. Far above the depth any refutation sample needs (`factorial(100)` is depth
  100).
- **Not yet consumed [scope].** `check_return_claim` is the building block a `where`
  return-check (E11) or a demand-driven return obligation will call; those aren't wired,
  and the driver's *proposed* claims are base-derived (sound, not refutable), so this
  changes no current verdict. The eval-level fuel now exists; a **program-level bounded
  run + the M-04 `DIVERGES` wiring** is a small remaining step (registered).
- **`// [ask-author]`:** none.

---

## 2026-07-25 — Induction tail, step 8: the completion tri-state — three-voice expecting-seat verdicts + callee threading (E10 / §1.6)

Closes a real soundness gap and adds the three-voice severity. `analyze_apply` only
set `may_complete` for mutators, so a call to a **partial-`Match` pure callee** bound
at an expecting seat was **not** flagged — yet the oracle traps expecting-seat. Now the
callee's completion threads through, and the seat verdict is three-voiced. New
`Completion` enum on `Analysis`; `Contract::has_proven_inhabitant`; 2 tests. Full tree
298 lib + 111 conformance, clippy clean.

- **`Analysis.may_complete: bool` → `completion: Completion` [mandated — E10 / §1.6].**
  `Produces` (ProvenAbsent) / `MayFallThrough` (UnprovenPossible) / `FallsThrough`
  (ProvenPresent). `demand` maps them to the **three voices**: `Produces` → ok;
  `FallsThrough` → **error** (a represented input completes without a value — refuted);
  `MayFallThrough` → **warning** (unproven, never a rejection). `may_complete()` stays
  as a bool helper.
- **`analyze_match` classifies the remainder [mandated].** Proven empty → `Produces`;
  **proven inhabited** (a sampled witness, `Contract::has_proven_inhabitant`) **and no
  guarded arm** → `FallsThrough`; else → `MayFallThrough`. The **guard exclusion** is
  load-bearing: a guard (not the pattern) decides and consumes nothing, so an inhabited
  remainder no longer *proves* a fall-through — at most `MayFallThrough`. This is
  strictly more precise than the old `may_complete = !exhaustive → error`: proven cases
  stay errors (`match 5 { 1 => 10 }`), opaque/guarded cases become warnings.
- **Callee completion threading [mandated — the soundness fix].** `callee_completion`
  reads the callee's body completion (via the factored `analyze_instance_body`) at the
  call site: a partial-`Match` callee → `FallsThrough`; a **mutator** → `FallsThrough`
  (its return is discarded, by law); a total callee → `Produces`. So `g(x) + 1` with
  `g = (n) => n :: { 0 => 1 }` is now the expecting-seat error it should be.
- **The re-entrancy guard extends to `callee_completion` [chose — required].**
  `analyze_instance_body` re-enters `analyze` (hence `callee_completion`), so a
  recursive callee overflowed the stack. Fix: `callee_completion` returns coarse
  `Produces` while `currently_inferring()` — the same bound `call_return` uses, and
  `analyze_instance_body` already sets that guard. One level of body analysis, bounded.
- **`summarize_instance` stays conservative [chose].** It still maps a proven
  fall-through to `UnprovenPossible` (not `ProvenPresent`) — the structured
  `ProvenPresent` **witness** (an represented `(callee, args)` that falls through, §7
  discipline) is genuinely owed and I will not mint a fake one. The wired analyzer path
  gets the precise three-voice from `Completion` directly; the outcome **algebra**'s
  `ProvenPresent` (feeding `seat_demand`) is the deferred AP-30 half.
- **Verified** — `a_partial_callee_at_an_expecting_seat_is_an_error` (`g(x) + 1` →
  error); `a_guarded_fall_through_is_a_warning_not_an_error` (`n :: { when b => 1 }` →
  warning, accepted). Existing `match_exhaustiveness_and_expecting_seat` and the
  outcome/inference tests pass **unchanged**.
- **`// [ask-author]`:** none. The structured `ProvenPresent` witness (AP-30) and the
  realized-witness `(e,x,v)` refutation remain the tail's open items.

---

## 2026-07-25 — Induction tail, step 7: the analyze_apply rewiring — recursive call sites infer their return (§6/C§13.2)

The payoff: top-level program analysis now uses the induction. A call to a known
recursive closure returns its **inferred** return contract, sharpened by the call-site
arguments, instead of coarse `Top`. `call_return` in `analyze_apply`; the re-entrancy
guard threaded through `summarize_instance`; 3 tests. Full tree 296 lib + 111
conformance, clippy clean.

- **`call_return(cv, arg_contracts, has_spread, cenv, interner)` [mandated — C§13.2].**
  At a call to a known closure: an active return-induction hypothesis (inside a driver
  pass) wins directly; else — outside a spread and outside an in-progress inference —
  `infer_return_fact` runs over the **call-site argument contracts**; else `Top`. So
  `factorial(k)` with `k : Number` now types `Number` (the call-site arg drops the
  untyped-domain Indeterminate-passthrough), and `even(x)` types `Boolean` — enough to
  satisfy a tested seat with no warning.
- **`infer_return_fact` gains `root_args: Option<&[Contract]>` [mandated].** The root
  callee takes the call-site domain when supplied (`Some([Number])`); reachable helpers
  keep their accepted domains; `None` is the autonomous form (unchanged). The fact is
  the (instance, I, C) form with I fixed by the call — the spec's call-parameterized
  return fact.
- **The re-entrancy guard, placed in `summarize_instance` [chose — the load-bearing
  decision].** Wiring inference into `analyze_apply` means the fact machinery's own body
  analysis (`summarize_instance` → `analyze` → `analyze_apply`) would spontaneously
  infer, letting a dependent prove itself by inferring its dependency mid-pass (and
  making a bare summary non-coarse). Fix: `summarize_instance` runs its body analysis
  under `without_inference`, so **all fact-proving stays coarse** (calls resolve through
  the pass's hypotheses or `Top`), and inference fires **only at genuine top-level
  `analyze` call sites**. The driver stays in control of fact-proving; the reverse-topo
  `base` remains the only channel for dependency facts. This kept
  `recursion_is_coarse_and_terminating` and `a_dependent_proves_only_after_its_dependency`
  green **unchanged** — the guard is exactly what those two properties require.
- **Behavior change [sound].** A call to a known closure with *abstract* arguments
  previously typed `Top`; it now infers. Strictly more precise, always sound (the driver
  verifies `F(C) ⊑ C`); folding of singleton-argument calls is untouched (still exact
  via the oracle).
- **No persistent cache [owed — C§13.4].** One call site drives one bounded inference;
  repeated call sites re-run the driver. The C§13.4 evaluation cache (keyed on the
  seat/world-independent core) is the optimization, registered in OwedItems.
- **Verified** — `a_recursive_call_infers_its_return_over_the_argument`
  (`f(x)`, `x:Number` → Number, accepted); `an_inferred_boolean_return_satisfies_a_
  tested_seat` (`even(x) ? 1 : 2` → no finding, where `Top` would warn);
  `an_unconstrained_argument_stays_sound` (`f(x)`, `x:Top` → Number ⊑ result, never a
  false rejection).
- **`// [ask-author]`:** none. Threading the completion tri-state into `may_complete`
  (AP-30) and the realized-witness refutation remain the tail's open items; A-NEG's
  input-domain rejection still needs the separate C§10 grounding arc.

---

## 2026-07-25 — Induction tail, step 6: return-fact inference — autonomous claim proposal (§6)

Closes the loop so the driver's claims need not be supplied: the analyzer now *infers*
a recursive function's return fact. `infer_return_fact` + `Contract::generalize`; 4
tests. Full tree 293 lib + 111 conformance, clippy clean.

- **`infer_return_fact(callee, cenv, interner) → Option<Contract>`** — reaches the
  whole call graph from `callee` (`reachable_closures`), **proposes** a return claim per
  function, runs the multi-SCC driver (step 5) over those candidates, and returns the
  callee's proven return contract (`None` when nothing informative is proven → coarse
  `Top`, sound).
- **The claim proposer [chose — sound, never trusted].** `Contract::generalize` widens
  `Equals(v) → Kind(v)` and drops `Bottom` alternatives in a `Union`. It is applied to
  each function's body summary **with the whole reachable group pinned to `Bottom`**:
  a mutual/identity recursive tail drops out of the base union (`even`'s `odd(n-1)` →
  `Bottom`, leaving `true` → `Boolean`), while an arithmetic use still types
  (`factorial`'s `n * f(n-1)` → `Number`, since `*` outputs `Number` and `Bottom ⊑
  Number` is absorbed). **The proposal is never trusted** — the driver re-verifies
  `F(C) ⊑ C` over real hypotheses (D§5's "candidates verified by the standard
  obligations, never trusted"), so a bad proposal fails or lands coarse, never a false
  proof. Top/Bottom proposals (trivial / baseless) yield no fact.
- **Domain [chose — the honest current precision].** The claim is proposed over each
  function's *accepted input domain* (the parameter pattern — `Top` for a bare `(n)`),
  so the fact is call-site independent. Consequence, surfaced by the factorial test:
  over the **untyped `Top` domain the return carries the arithmetic
  Indeterminate-passthrough** — `factorial(1/0)` really returns an Indeterminate, so the
  inferred fact is `Number ∪ Indeterminate`, sound and strictly tighter than `Top`. A
  call site that constrains `n : Number` sharpens it to pure `Number` — that is exactly
  what the `analyze_apply` wiring (call-site args) will supply. The grounding-derived
  input domain (C§10) that would tighten the autonomous case is a separate subsystem,
  unbuilt.
- **Verified** — `infers_factorial_returns_number_over_its_domain` (Number ⊑ fact, no
  String — tighter than Top); `infers_even_and_odd_return_boolean` (mutual, Boolean via
  the Bottom-pin drop-out); `identity_recursion_infers_a_sound_overapproximation`
  (`n==0 ? 0 : f(n-1)` → Number, a sound over-approx of the true `Equals(0)`);
  `a_baseless_recursion_yields_no_fact` (`loop = n => loop(n)` → `None`, no overclaim).
- **Scoped to the follow-up.** A function whose *only* base contribution is a
  **non-recursive helper call** proposes `Top`/`Bottom` (the helper is Bottom-pinned
  too) and so yields no fact — a precision gap (sound); the reverse-topological
  *proposal* that would close it lands with the `analyze_apply` rewiring, alongside
  call-site args, the persistent fact cache, the re-entrancy guard, AP-30's
  `ProvenPresent` half, and the realized-witness refutation.
- **`// [ask-author]`:** none. The `Top`-domain Indeterminate-passthrough and the
  helper-base gap are registered in `OwedItems.md` (sound precision, not asks).

---

## 2026-07-25 — Induction tail, step 5: the multi-SCC driver — reverse-topological hypothesis carrying (§6/§13.2a)

The step that turns step 4's single-component pass into a whole-program fact solver.
`prove_facts` in `src/analyzer/induction.rs`; 4 tests on real closures. Full tree 289
lib + 111 conformance, clippy clean.

- **The driver [mandated — §6/§13.2a].** `prove_facts(candidates, cenv, interner) →
  FactResult { proven, unproven }` decomposes the candidates' **call graph** into
  strongly-connected components, processes them in **reverse-topological order**
  (dependencies first), and carries each proven component's return facts as hypotheses
  for its dependents. A self/mutual nest is one component settled by a joint vector
  pass; a non-recursive candidate is a singleton component whose body sees the
  already-proven facts of everything it calls. This is the §13.2a global-fact-graph
  SCC collapse at the granularity the tail has so far — components over the direct call
  graph, one vector pass each.
- **`run_pass(base, members, …)` [refactor].** The vector pass now takes a **base
  hypothesis set** — the facts of dependency components already settled — installed
  alongside the component's own claims. `joint_vector_pass = run_pass(&[], …)`, so
  step 4's single-component entry is unchanged; the driver threads `settled` (the
  accumulating proven facts) as the base for each successive component.
- **Reverse-topological order via Tarjan [chose the algorithm].** `scc_reverse_topo`
  is Tarjan's SCC; it emits components in reverse-topological order (a component before
  every component that depends on it) as a **property of the graph, not the traversal**
  — so the driver is order-independent (tested: reversing the candidate list changes
  nothing). Edge `i → j` means "fact `i` depends on fact `j`" (C§13.2a's orientation),
  so `j` is settled first.
- **Edges are direct calls among candidates [chose the scope].** `call_edges` links
  `i → j` iff candidate `j`'s closure is a **direct** callee (`callee_targets`) of
  candidate `i`'s body. An indirect dependency through a **non-candidate** helper is
  not an edge, so that helper's call coarsens to `Top` — sound (the dependent lands
  *unproven*), never a false proof. The driver **orders and proves the candidates it is
  given**; deriving the candidate set and its claimed contracts from seat demands /
  grounding (C§10) is a separate concern, unchanged here.
- **Verified on real closures** — `a_dependent_proves_only_after_its_dependency`
  (`quad = (n) => double(n) + double(n)` is unprovable **alone** — `double(n)`
  coarsens to `Top` — but the driver settles `double : Number` first and carries it, so
  both close); `the_driver_is_independent_of_candidate_list_order` (reversed list, same
  proven set); `a_vector_failure_leaves_only_its_component_unproven` (claiming `quad :
  String` fails while `double : Number` stays proven — and `double`'s fact is what
  reduces `quad`'s body to fail against String, not Top); `a_mutual_nest_is_one_
  component_in_the_driver` (even/odd as one component, one pass).
- **Scoped to the follow-up.** The realized-witness `(e, x, v)` **refutation** (the
  third voice — permanent in-namespace, distinct from vector-failure *unproven*),
  AP-30's `ProvenPresent` half in the outcome contribution, and the **`analyze_apply`
  rewiring** onto the driver (so top-level program analysis uses these facts — the
  Phase A unlock) are the remaining tail work.
- **`// [ask-author]`:** none.

---

## 2026-07-25 — Induction tail, step 4: return induction — the joint vector pass (§6)

The fixpoint step that sharpens step 3's coarse recursive `Top`. New module
`src/analyzer/induction.rs`; a hypothesis injection in `analyze_apply`; 3 tests on
real recursive closures. Full tree 285 lib + 111 conformance, clippy clean.

- **The induction step.** `joint_vector_pass(members, cenv, interner)` — a recursive
  component's members each claim a return contract `C`; **assume** every member returns
  its `C` (installed as hypotheses), then verify each member's body produces `⊑ C`. The
  component closes iff **all** members verify; any failure is a **vector failure** —
  the whole component is unproven (§6).
- **Hypothesis injection — a dynamic-scope table [chose].** `analyze_apply` now
  consults a thread-local `HYPOTHESES` table: a recursive/mutual call whose callee
  shape is under an active hypothesis returns the assumed contract instead of the
  coarse `Top` (step 3's fallback). This is a bounded, contained mechanism (the
  analyzer is synchronous, single-threaded) that avoids threading a hypothesis
  parameter through the whole analyzer; `with_hypotheses` saves/restores the table so
  passes compose. This is what turns factorial's coarse `Union(Equals(0), Top)` into a
  proof that `f` returns `Number`.
- **Verified on real closures** — `factorial_returns_number_by_induction`
  (`f = (n) => n==0 ? 1 : n * f(n-1)` proves `Number`); `a_false_return_claim_is_rejected`
  (claiming `String` fails — the body `n * f(n-1)` is a type error under it);
  `mutual_recursion_closes_jointly` (even/odd both `Boolean`, provable **only** with
  both hypotheses installed; and the vector-failure case — one wrong claim fails the
  whole component).
- **Scoped to the follow-up** — this lands the **joint vector pass over one
  component**. The **multi-SCC driver** (call-graph SCC decomposition via the body
  walk + reverse-topological ordering, carrying each proven component's contract as a
  hypothesis for its dependents), the realized-witness `(e, x, v)` refutation, AP-30's
  `ProvenPresent` half, and the `analyze_apply` rewiring onto the driver are the
  remaining tail work.
- **`// [ask-author]`:** the thread-local hypothesis table is an implementation
  strategy (dynamic scope for the induction), flagged for visibility — sound, and
  swappable for a threaded context later.

---

## 2026-07-25 — Induction tail, step 3: outcome contribution (per-instance body summary)

Third tail step — §1 steps 4–5, the callee body summary. New module
`src/analyzer/outcome.rs`; 4 tests. Full tree 282 lib + 111 conformance, clippy clean.

- **`summarize_instance(callee, arg_contracts, cenv, interner)`** reads a single
  instance's `ApplicationOutcome` off its body: bind the captures (to their exact
  `Equals(value)`) and the argument-narrowed parameters (`bind_pattern`, now
  `pub(crate)`), then `analyze` the body. The existing Match analysis (E9/E10) already
  does **row selection** — arm-by-arm narrowing, the unioned produced contract, the
  fall-through flag — so the map is direct: `produced = body contract`, `completion =
  may_complete ? UnprovenPossible : ProvenAbsent`.
- **Recursion is coarse and terminating [chose].** A recursive/mutual call resolves
  its callee to a captured `Equals(closure)`; with abstract (non-singleton) argument
  contracts the call does **not** constant-fold, so `analyze_apply` returns `Top` for
  the recursive result instead of re-entering the body — the summary terminates
  (verified on `f = (n) => n == 0 ? 0 : f(n-1)`, producing `Union(Equals(0), Top)` ⊇
  Top). Sound but coarse; the **§6 return induction** sharpens the recursive result
  from `Top` to a proven contract under the induction hypothesis (that is the next
  step, and where the fixpoint lives).
- **`may_not_complete = false`** — divergence feeds no safety verdict (§1.5); its
  precise value on a gray SCC is the §6 concern.
- **AP-30, partial [note].** This lands the `ProvenAbsent`/`UnprovenPossible` halves —
  a possible fall-through row contributes `UnprovenPossible` (→ expecting-seat
  `Unproven`), tested on `(n) => n :: { 0 => 1 }`. The `ProvenPresent` half (a
  fall-through **proven reachable** with a witness → refute) needs proven
  non-exhaustiveness over `E × A`, which is the §6 row-reachability work — still owed.
- **`// [ask-author]`:** none.

---

## 2026-07-25 — Induction tail, step 2: the input obligation (accepted-domain derivation)

Second tail step — the real §1 step 3, replacing bridge-2's test-only `accepts`
callback. New module `src/analyzer/obligation.rs`; 4 tests. Full tree 278 lib + 111
conformance, clippy clean.

- **`accepted_domain(callee, cenv)`** — the contract the callee's parameter pattern
  requires of the argument tuple, via `pattern_contract` (now `pub(crate)`; contract-
  pattern names survive canonicalization, so the same derivation works on the shape).
- **Soundness subtlety [chose]** — `pattern_contract` is built for *narrowing* and
  **over-approximates** matched values, so it is a sound accepted domain **only when
  the pattern has no tuple rest**: `(a, …rest)` widens to `Kind(Tuple)`, which would
  bless `f()` even though the pattern rejects the empty tuple. `accepted_domain`
  therefore **declines a rest-bearing pattern** (returns `None` → the obligation is
  `Unproven`) rather than emit an unsound domain. The length-precise domain for rest
  parameters is the tuple-family (§4 `restrictLen`) refinement — **owed** (OwedItems).
- **`input_obligation(callee, arg_contracts, cenv, interner)`** — `Tuple(arg_contracts)
  ⊑ AcceptedInputs`, three-valued: `Proven` on subcontract; `Refuted` with a
  **represented** `ApplicationWitness { callee, arguments }` (the concrete callee + the
  rejecting argument tuple from `subcontract`'s counterexample — the §7 witness
  discipline, now on a real derivation); else `Unproven`. Tested: arity match/mismatch,
  `(Number)` accepting `5` / refuting `"hi"` (witnessed) / `Top` unproven, a const
  param accepting only its value, and the rest-param deferral.
- **Chose / scoped** — operates on a **concrete callee closure value** (the tail's
  working representation from step 1's body walk), where a refutation can carry the
  actual callee. Wiring it into the abstract driver (`analyze_application`) and into
  `analyze_apply` at real call sites is a later step; the callback in bridge-2's tests
  is now backed by this real derivation.
- **`// [ask-author]`:** none.

---

## 2026-07-25 — Induction tail, step 1: the μ-aware body walk (call graph)

First step of the return-induction tail (the bridge having passed the follow-up
review). New module `src/analyzer/bodywalk.rs`; `build_inventory` generalized to
`build_inventory_by<N>`; 4 tests on real recursive/mutual closures. Full tree 274 lib
+ 111 conformance, clippy clean.

- **Recursion lives in the captures, so the call graph reads off a closure value.**
  A recursive/mutual callee `f` is a *free variable* in its body → canonicalized to a
  capture slot `@capᵢ` (`free_vars[i] = "f"`); the closure's **shared** environment
  late-binds it to the target closure as a plain `Binding::Value` (slots are only for
  `@:` mutables — I verified `f = (n) => f(n-1)` rebinds `f` to `Value(closure)` in the
  captured env). So `callee_targets(v)` walks `v`'s shape body for applications and
  resolves each capture-slot callee to the captured function value — **no μ-binder
  minimization needed**, since a recursive edge closes as a §4a shape repeat.
- **`reachable_closures`** runs the §4a cutoff (`build_inventory_by`, keyed by shape)
  over the concrete closure graph: self-recursion admits `{f}`, mutual `even`/`odd`
  admits `{even, odd}`, a leaf function has no edges, a non-recursive helper chain is
  bounded — all on **real closures** built via `run_source`, terminating on every
  cycle.
- **Two sound under-approximations [chose].** The walk does not descend into nested
  `Lambda` bodies (distinct instances) and resolves only capture-slot callees (a
  parameter/local callee gives no edge). Both can only *drop* an edge, never add a
  spurious one — a missing instance lands `unproven` in the induction, never a false
  proof.
- **Fork resolved without an author ruling.** The spec's Choice A (self/group refs as
  μ-structure edges) would need the μ-binder SCC minimization ("ships with the
  analyzer", unbuilt). But the current runtime's shared-env late binding makes the
  value-based walk sound and sufficient for the call graph + cutoff — so the μ-binder
  minimization is **not** on the critical path for the induction; the abstract-instance
  self-capture (a cyclic env) is only relevant to precise input-obligation/return
  contracts, where a self-capture can be represented coarsely (`Unknown`) soundly.
- **`// [ask-author]`:** none — the value-based-walk choice is an implementation
  strategy (sound either way); flagged here for visibility.

---

## 2026-07-25 — Analyzer-core bridge-2: the joint operand driver + structural witness

Completes the review's held bridge before the induction tail. `src/analyzer/
application.rs` extended; 2 new tests (AP-24/29 + the structural-witness hardening),
the existing algebra tests migrated to the structural witness. Full tree 269 lib + 111
conformance, clippy clean. **[Corrected per the follow-up review, same day]:** the
structural-witness test is *not* normative AP-30 (that is the fall-through / row-
contribution case, tail-dependent) — see below.

- **`analyze_application`** processes the joint operand — the correlated
  `[callee, …args]` AnalysisContract — **per live alternative** (admission step 1 +
  the input obligation step 3 via an `accepts` callback), conjunctively across
  alternatives. `live_alternatives` distinguishes **correlated** (an `Alt` of tuples,
  or a bare tuple) from **projected** (a tuple carrying positional `Alt`s → the
  cross-product); a correlated alternative may refute with its witness, a projected
  cross-pair failure **degrades to `Unproven`, never `Refuted`** (AP-29).
- **AP-24 / AP-29 tested end-to-end** — the operand `[numFn, 5] | [strFn, "hi"]`
  proves (each callee accepts its own arg, cross-pairs never formed); the projected
  `[numFn|strFn, 5|"hi"]` expands to four cross-pairs, `(numFn,"hi")`/`(strFn,5)` fail,
  and the driver lands **Unproven** — never a refutation from a pair the program does
  not represent.
- **Structural witness (review §7)** — `ProvenPresent(ValueRef)` → `ProvenPresent(
  ApplicationWitness { callee: ValueRef, arguments: Vec<ValueRef> })`, and the seat
  demand now returns a `SeatVerdict { Proven | Refuted(ApplicationWitness) | Unproven }`.
  A refutation carries the **represented execution** (callee applied to arguments),
  not a fakeable token — `refutation_carries_a_represented_application_witness` asserts
  the witness is `numFn` applied to `"hi"`.
- **AP-30 is NOT yet implemented [follow-up review correction].** Normative AP-30 is
  the *completion / fall-through* version of the cross-pair problem: a fall-through row
  inhabited only by a projected cross-pair `(e₁,a₂) ∈ (E×A)∖R_alt` must contribute
  `UnprovenPossible` (→ expecting-seat `Unproven`), flipping to `ProvenPresent` only on
  a **proved** `R_alt ∩ row` inhabitant. That needs the row-selection / outcome-
  contribution machinery of the tail; the three `CompletionWithoutValue` states exist,
  but nothing yet *selects* a row and *decides* the contribution. AP-30 is **owed with
  the tail** (the misnamed test was renamed, and no longer claims it).
- **Chose / scoped:** the input obligation is supplied by an `accepts` callback so the
  correlation discipline is exercised independently — deriving the accepted domain from
  the callee's param pattern (§1 step 3 proper) is threaded in the induction tail.
  `analyze_apply` is still the coarse path; the driver is not yet wired into it.
- **Known precision loss (non-blocking, sound) [review].** `live_alternatives` returns
  a **collection-wide** `correlated` flag: a mixed outer `Alt` (one correlated branch +
  one already-projected branch) degrades the *whole* set, so a genuine refutation from
  the correlated branch is downgraded to `Unproven`. Sound (only loses precision, never
  manufactures a verdict); the per-alternative `witness_status: Represented | Projected`
  upgrade is deferred.
- **`// [ask-author]`:** none.

The review's bridge prerequisite is now discharged (correlated domain + joint witness
+ AP-24/29). The **induction tail** — μ body-walk → real accepted-domain derivation →
row selection / outcome contribution (**where real AP-30 lands**) → candidate graph →
SCC return induction → `analyze_apply` → Phase A — is unblocked.

---

## 2026-07-25 — Analyzer-core bridge: the correlated structural AnalysisContract

Responds to the author's checkpoint review (`NEXT-analyzer-core-checkpoint-review-
8.1a-8.1c.md`), which **held the return-induction tail for one bridge increment**: my
`AnalysisContract { contract, metadata }` carried function metadata only at the top
level, so metadata nested in a tuple/union alternative was lost and `[numFn, 5] |
[strFn, "hi"]` would flatten into false cross-pairs. Full tree 267 lib + 111
conformance, clippy clean.

- **`AnalysisContract` is now structural / correlated** — an enum `Leaf { contract,
  metadata } | Tuple(Vec<AC>) | Record(Vec<(String, AC)>) | Alt(Vec<AC>) | Bottom`.
  Function metadata survives through tuples, record fields, and **correlated union
  alternatives** (never positionally flattened). `erase`, `gamma_contains`,
  `prove_subcontract_a`, and `intersect_a` all recurse through the structure;
  constructors (`tuple`/`record`/`alt`) Bottom-normalize and collapse.
- **The finding, tested directly** — `correlated_alternatives_do_not_synthesize_cross_pairs`:
  γ of `Alt(Tuple(f, 5), Tuple(g, "hi"))` holds `[f,5]` and `[g,"hi"]` but **not** the
  synthesized `[f,"hi"]` / `[g,5]`. `union_ac` (8.1b) now builds an `Alt`, not a
  positional `Union`.
- **⊑ᴬ / intersectA structural** — `Alt`-left ⊑ X iff every alternative ⊑ X; X ⊑
  `Alt`-right iff X ⊑ some alternative (sound, incomplete); tuples/records pointwise;
  the leaf/mixed path proves through the erased contracts only when the **target is
  metadata-free** (then `γ(b) = ⟦erase b⟧`) or both sides are leaves with covering
  metadata, and refutes only with a **γ-representable** witness. `intersect_a`
  distributes over `Alt`, meets tuples/records structurally, and falls back to a leaf
  over the erased intersection for mixed pairs.
- **Review's smaller items, closed:** the mislabeled `ap24_union_join_*` test renamed
  to `outcome_join_*` (it is the join algebra, **not** spec AP-24); the inventory §4a
  ordering claim corrected — the returned `Vec` is documented as a discovery-ordered
  **set** representation (not canonical), with `membership_is_independent_of_root_and_
  transition_order` added; the `Known(∅)` doc-integration mismatch registered in
  `OwedItems` (my generalized off-function-position reading — defensible, owed a spec
  wording).
- **Still owed for the tail (author's sequence):** the joint operand **application
  driver** (per-live-alternative processing) with a structural `ApplicationWitness
  { callee, arguments }` (replacing the `ProvenPresent(ValueRef)` token) + the real
  **AP-24 / AP-29 / AP-30** batteries — that is bridge-2, before the μ body-walk →
  candidate graph → SCC return induction → `analyze_apply` → Phase A.
- **`// [ask-author]`:** the `Known(∅)` off-function-position semantics (registered) —
  no other judgment calls.

---

## 2026-07-25 — Application/induction 8.1c: the instance-chain inventory (§4a)

Third sub-step of the analyzer-core rebuild. New module `src/analyzer/inventory.rs`,
3 tests. Full tree 265 lib + 111 conformance, clippy clean.

- **`build_inventory`** — the admitted-instance inventory of §4a: the projection onto
  instances of the finite state closure over `InventoryState = (instance, active
  shape sequence)`. Seed with the root instances; from each state, enumerate call
  transitions; a target whose shape is **not** on the active path is admitted and
  extends the sequence; a target whose shape **is** on the path is the **cutoff** — no
  admission through it, the induction (§6) handles the cycle at analysis time.
- **Traversal-free / order-independent** — the closure depends on `roots` +
  `transitions` alone, not the traversal order. A visited-set over `(instance, active
  shapes)` bounds it; no admitted path repeats a shape, so path depth ≤ the program's
  shape count, and the reachable instance universe is advance-bounded.
- **Parameterized by `transitions`** — the symbolic call-target enumeration. **Chose:**
  land the closure algorithm now, tested against synthetic transition graphs (AP-16
  the two-shape mutual program → cutoff on the shape-repeat; self-recursion → only the
  root admitted; a non-recursive diamond → the join deduped). Deriving `transitions`
  from a real closure body needs μ-structure-aware callee resolution (self/group refs
  are the μ package's internal edges), which lands with the wiring below.
- **Owed (the §6 induction + wiring, the remaining 8.1c tail):** the μ-structure body
  walk that yields real `transitions`; the candidate graph (§6) with SCC-ordered
  return induction and realized-witness `(e, x, v)` refutation; §5 domain-indexed
  facts; rewiring `analyze_apply` onto the outcome algebra; the sampled γ soundness
  battery. Those together activate the Phase A batteries. `analyze_apply` stays the
  sound coarse path until then.
- **`// [ask-author]`:** none.

---

## 2026-07-25 — Application/induction 8.1b: the application transfer rule §1 (outcome algebra)

Second sub-step of the analyzer-core rebuild. New module `src/analyzer/application.rs`,
5 tests. Full tree 262 lib + 111 conformance, clippy clean.

- **What this is.** The **outcome algebra** of `analyzeOperation(application,
  AC_operands)` — steps **1** (act-kind admission), **5** (the summary shape), **6**
  (the three-voiced completion demand), **7** (union of callees) — as pure,
  seat-applied combinators over the `AnalysisContract` domain (8.1a).
- **`ApplicationOutcome { produced: AnalysisContract, completion, may_not_complete }`**
  with `CompletionWithoutValue = ProvenAbsent | ProvenPresent(witness) |
  UnprovenPossible` — the §1.5 tri-state (a Boolean erased the witnessed-vs-
  undisproved distinction; `may_not_complete` stays Boolean because it feeds no
  safety verdict).
- **`seat_demand` (step 6)** — three-voiced at the seat, never cached: an expecting
  seat rejects *only* a witnessed fall-through (`ProvenPresent → Refuted(witness)`,
  `ProvenAbsent → Proven`, `UnprovenPossible → Unproven`); a statement seat accepts
  all three; `may_not_complete` violates nothing (AP-23; AP-18 for the
  fall-through-only / `produced = Bottom` callee).
- **`join` / `join_all` (step 7)** — componentwise: produced by `union_ac` (Bottom is
  the identity; metadata joined), completion by the evidence-preserving join (any
  `ProvenPresent` dominates with its witness, else `UnprovenPossible`, else
  `ProvenAbsent`), `may_not_complete` by `or`. The empty join is
  `ApplicationOutcome::empty` — the `Known(∅)` cached core (AP-21/24).
- **`admit_callee` (step 1)** — over `Known(S)` every non-empty member's act-kind
  must be admitted (proven-empty members dropped); `Known(∅)` passes **vacuously**
  (AP-21); `Unknown → Unproven` (no witness can exist, AP-15). **Chose:** an
  inadmissible member lands `Unproven` at this layer — the witness-backed refutation
  needs a represented closure, which flows in 8.1c; unproven is sound.
- **Scoped to 8.1c (deliberately not here):** computing a single instance's summary
  from its body — steps **2–4** (instance resolution, the `E × A` input obligation,
  row selection) — and rewiring `analyze_apply`. Those need the constructed instance
  inventory (§4) and the candidate graph (§6) so a **recursive** callee is summarized
  soundly under the cutoff; wiring body analysis now would be unsound on self-
  application. The current `analyze_apply` stays the sound coarse path (return `Top`).
- **`// [ask-author]`:** none.

---

## 2026-07-25 — Application/induction 8.1a: the AnalysisContract abstract domain (§2)

First sub-step of the analyzer-core rebuild (Application & Induction v0.8.1). The
package is large (10 sections, AP-01…30); it lands in three commits — **8.1a** the
abstract domain (this), **8.1b** the application transfer rule (§1), **8.1c** the
instance inventory + candidate graph (§4/§6/§5, which activates Phase A). New module
`src/analyzer/domain.rs`, 4 tests. Full tree 257 lib + 111 conformance, clippy clean.

- **The domain.** `AnalysisContract { contract, metadata }` with `InstanceMetadata =
  Known(Vec<Instance>) | Unknown` and `Instance { shape: Lambda, env: Vec<AC> }` —
  the μ-canonical shape (structural `Lambda` identity, per the value layer) plus the
  annotated captured environment. `erase = .contract` is the untouched language
  denotation; **γ** is the analyzer concretization: a non-function member of
  `⟦contract⟧` is always in γ (metadata vacuous off function positions); a function
  member is in γ iff the metadata admits it — every function under `Unknown`, or one
  **realizing** an instance under `Known(S)` (shape match + each capture ∈ γ of its
  annotated slot). `realizes`/`gamma_contains` implement this (added `ValueRef::as_fn`
  / `is_function`).
- **Normalization** to one canonical bottom (§2): `(Bottom, _) → bottom`, and
  `(C, Known(∅)) → bottom` **only when C is function-only** (`is_function_only`, a
  value-free test) — a `Known(∅)` on a *non*-function contract is not empty (metadata
  is vacuous there), which the tests pin.
- **`prove_subcontract_a` (⊑ᴬ).** Three-valued, sound, deliberately incomplete:
  `Proven` iff ordinary-contract inclusion **and** metadata coverage; a `Refuted`
  witness is kept **only when it is γ-representable** (`gamma_contains(a, w)`) — a
  bare contract counterexample outside γ(AC₁) downgrades to `Unproven`. Coverage
  (`covers`) is the §2 round-5 triage: proven-empty sources ignored; every other
  source (uncertain inhabitance never silently skipped) needs a same-shape target
  whose env covers it recursively — so `instance(shape, Equals(1)) ⊑ instance(shape,
  Range(1,5))` despite distinct keys (AP-27). `Known(S) ⊑ Unknown` proven;
  `Unknown ⊑ Known(T)` unproven; `Known(∅) ⊑ X` proven.
- **`intersect_a` / `meet_instance` (AP-28).** Sound by containment only
  (`γ(A) ∩ γ(B) ⊆ γ(intersect_a(A,B))`). `Unknown ∩ M = M`; `Known(S) ∩ Known(T)` is
  the coverage-normalized same-shape meet — `s ⊑ t ⇒` keep `s`, else `meet_instance`
  (env-wise `intersect_a`, empty only when a capture meet is **proven** bottom). So
  `Known({Eq(1)}) ∩ Known({Range(1,5)}) = Known({Eq(1)})`, never Bottom; disjoint
  **shapes** meet to Bottom (a genuine disjointness). No lower-bound/idempotence
  reasoning is applied to a fallback result.
- **Chose / scoped:** ⊑ᴬ uses the *non-recursive* C.2 `subcontract` for erased
  inclusion — recursive-annotated contracts (C§9 lifted to annotated form) and the
  full sampled **γ soundness battery** (joint operand realizations through the oracle,
  §9) land with the application rule in 8.1b, where real applications produce/consume
  closures. `ConjAC` interned-conjunction (the optional intersection-closure) stays
  unbuilt (v1-optional per the spec). Capture γ-recursion handles `Binding::Value`;
  a slot/under-init capture is conservatively unrealized (sound under-approx).
- **`// [ask-author]`:** none.

---

## 2026-07-25 — Tuple family §5: string boundary-state seams

`src/contract/grapheme.rs` — the segmenter-owned seam — plus 6 tests (TL-09's five
boundary characters, the round-2 leading-ZWJ flagship, an exhaustive corpus
cross-check, and the analyzer bound). Full tree 253 lib + 111 conformance, clippy
clean. Completes the tuple-length family (§1–§5).

- **Grapheme count is not additive across concatenation** — extended clustering
  (UAX #29) can merge across the seam by **more than one**. The flagship: `👩` (1)
  `++` `‍👩‍👧` (2) → `👩‍👩‍👧` (1), a seam delta of **−2**. That retired the unsound `−1`
  interval (round 1). **`grapheme::count` / `Summary` / `compose` / `seam_delta`**
  are **segmenter-owned** — every seam is recomputed by the pinned
  `unicode-segmentation` (`=1.13.3`), never a guessed constant (C§13.4 re-pin
  invalidation rides the version pin).
- **Boundary-state summary, exact for literals** — a string is a `Summary { count,
  units }`; concatenation is `compose`, which re-segments the join, so
  `compose(of(a), of(b)).count == count(a ++ b)` for all `a, b`. The **mandated
  soundness check** (spec §5: "exhaustive over the generated finite transition
  table; property testing is a cross-check, never the proof") is a corpus sweep over
  the boundary-relevant fragments — flagship, RI runs, combining, Hangul, ASCII,
  empty — asserting composition reproduces direct segmentation and stays associative.
- **The merge is asymmetric [chose — the spec states the delta, not the floor]** —
  clustering only merges (never splits), and appending to the right cannot change
  the **left** operand's internal boundaries (breaks and RI parity are decided
  left-to-right), whereas prepending can rewrite the right's segmentation (a leading
  joiner is absorbed — the flagship gives `count = 1 < count(b) = 2`). Hence the
  sound envelope is `count(a) ≤ count(a ++ b) ≤ count(a) + count(b)` — the floor is
  the **left** count, *never* `count(b)` and never their max. My first bound used
  `max` and the flagship corpus check caught it. `concat_len_bound` is the `Approx`
  analyzer fallback carrying this.
- **TL-09** — leading-ZWJ (1+2→1); RI pairing (`🇦`+`🇧`→1, delta −1) *and* parity
  (`🇦🇧`+`🇨`→2, delta 0); combining mark (`e`+´→1); Hangul `L`+`V`→1; ASCII seamless;
  `"" + s` exact (the proven-zero case, 0.1.1) — all against the pinned segmenter.
- **Scope / owed:** the finite boundary-state **compression** that lifts the exact
  seam to abstract string **contracts** — RI-parity normalization, the ZWJ-chain /
  Hangul states over the segmenter's finite state space — needs the segmenter's
  category tables *and* a string-length contract form the algebra does not yet have.
  The current `Summary` retains `units` and is segmenter-exact for every literal; the
  finite-state lift is the recorded upgrade (OwedItems).
- **`// [ask-author]`:** the boundary-state space enumeration is deferred with that
  lift (noted in the module header) — no semantics invented in the interim.

---

## 2026-07-25 — Tuple family §4: segment alignment

`prove_segments` — the forced-boundary peeling procedure — plus 8 tests (TL-01a,
TL-18 ×4, TL-21, the ≥2⊑≥1 interior case, and a nullable-boundary soundness guard).
Full tree 247 lib + 111 conformance, clippy clean. Closes the `Concat ⊑ Concat`
unequal-segment-count gap that §1 left `Unproven`.

- **Routing** — a concatenation, or an exact `Tuple` read as one fixed segment, is
  aligned against another by `prove_segments`. New `prove_body` arms: `(Concat,
  Concat)`, `(Concat, Tuple)`, `(Tuple, Concat)`. The old aligned-only rule
  (`sa.len() == sb.len()`) is subsumed as the procedure's variable core.
- **Forced boundaries first (spec §4.1)** — a fixed segment is peeled off a
  boundary **only when the segment facing it is also fixed**; a zero-or-more segment
  on the far side could otherwise slide the edge, so the split would not be unique.
  Peeling a fixed pair consumes `min(m, n)` positions element-wise and carries the
  longer side's remainder forward as a residual `Tuple`. Both the front and the back
  boundary are peeled (forced, never merely outermost). RC 0.2.2 `source_progress`
  carries **consumed source extent** through the peel so the coinductive guard still
  advances (Repeat covariance closes exactly as in RC-17).
- **Interior — one variable binds the residual (spec §4.2)** — after the forced
  boundaries, an equal-count residual takes the aligned segment-wise rule; an
  *unequal*-count residual with a **single** variable segment on one side is
  reconstituted and handed back to the guarded `prove`, whose μ-head/`Union`
  machinery unfolds the collapsed `Ref`/`Repeat` against the opposite concatenation.
  This is what proves `≥2 Number ⊑ ≥1 Number`. A residual that stays variable on
  *both* sides with no unique split lands **`Unproven`** (spec §4.3) — e.g.
  `Concat(Repeat(N), Repeat(N)) ⊑ Repeat(N)` is a real subcontract left unproven,
  never fabricated.
- **Nullability is sound-must** — `segment_nullable` returns `true` only when a
  segment *certainly* admits a length-0 realization (`Tuple([])`, `Kind(Tuple)`,
  a `Union`/`Ref` reaching such, or a `Concat` of such, fuel-bounded). This gates
  the source-consumed residual case, so `≥0 Number ⊄ ≥1 Number` correctly **refutes**
  (empty-list witness) rather than proving.
- **Refutation + the uninhabited-shape guard (spec §4 round 2 / TL-21)** — negatives
  come from the existing inhabitant enumeration, which only ever yields *complete*
  concrete witnesses. So a positional element mismatch alone never refutes: the same
  `Tuple(Number, U) ⊑ Tuple(String, Top)` row is **Refuted** when `U` is inhabited
  (a witness `[num, ⋆]` exists) and **Proven** when `U = ⊥` (the source is empty, the
  inclusion vacuous). The identical position-0 mismatch, opposite verdicts — the
  guard is the inhabitation of the *other* positions.
- **Termination** — every `prove_segments` branch drops a whole segment or splits
  one (strictly decreasing segment-count + arity), and the reconstitute-and-defer
  step re-enters only through the progress-guarded `prove`; the created residual
  `Tuple`s are sub-slices of finitely many source tuples, so the reachable pair
  space stays finite.
- **Scope / owed:** §5 grapheme boundary-state seams (TL-09) is next.
  `restrict_len`'s recursive certified-unfolding rule remains owed. The
  `ElementRefutation` *structured witness* (alignment map + projected branch) is not
  materialized — refutation returns the complete inhabitant, which is a strictly
  stronger witness; the structured form is a presentation detail for later.
- **`// [ask-author]`:** none.

---

## 2026-07-24 — Tuple family §3: refutation discipline + restrictLen/LengthRestricted

`Contract::LengthRestricted` + `restrict_len` + `intersection_empty_by_length` + 6
tests (TL-16/17/20 + canonical rows + exact-tuple filter). Full tree 239 lib + 111
conformance, clippy clean.

- **`Contract::LengthRestricted(T, D)`** — the analyzer-derived form denoting
  `{ t ∈ ⟦T⟧ : |t| ∈ ⟦D⟧ }`. Smart constructor `Contract::length_restricted`
  applies the canonical rows: `Bottom` on either side → `Bottom`; `TopLength`
  (`GE(0)`/`Top`) → `T`; nested → merge domains by intersection. Membership
  (`t ∈ T ∧ value_length(t) ∈ D` via `nat_in`, a value-free numeric-nat test),
  `len` (`Λ(T) ∩ D`, `Exact` when `len(T)` is, disjoint→`Bottom` exact), sample,
  and group-aware `recursive::contains` all handle it.
- **`intersection_empty_by_length` (§3.i/v)** — `⟦a⟧ ∩ ⟦b⟧` is empty when the two
  length contracts are disjoint. **Sound even when both stamps are `Approx`** —
  upper approximations of disjoint length sets are sound disjointness evidence.
  This is the *one* refutation `Approx` lengths may make. **TL-20:** a `(GE(5),
  Approx)` shape against a `Tuple(a, b)` (length 2) → intersection refuted.
- **`restrict_len` (the reverse transfer)** — lowers structurally: exact tuple →
  keep/`Bottom` by its fixed length; `Union` distributes (dropping `Bottom`
  branches); **`Repeat(E)` against a pure lower bound `GE(n)` unrolls** to
  `Concat(Tuple(E×n), Repeat(E))` (recognized via `repeat_element`); everything
  else → the symbolic form. **TL-17:** `restrict_len(Repeat(Number), GE(1))` →
  `Concat(Tuple(Number), R)` (excludes `[]`, includes `[7]`); a modular `D` falls
  to `LengthRestricted` with exact membership (even lengths only).
- **The refutation discipline (§3.ii/iii/v) holds by construction** — `subcontract`
  carries **no length-based refutation**, so an `Approx`-source length mismatch can
  never *manufacture* a `Refuted`; a recursive `Refuted` still comes only from an
  enumerated realizable inhabitant witness (**TL-16**: `Repeat(Number) ⊄
  Tuple(Number, Number)` is `Refuted` by the real witness `[1]`, or `Unproven` —
  never a length fabrication).
- **Scope:** §4 segment alignment (forced-boundary peeling, `ElementRefutation`,
  which closes the `Concat ⊑ Concat` unequal-count gap) and §5 grapheme seams are
  next. `restrict_len`'s recursive certified-unfolding rule (demand-depth-bounded D)
  is owed — `interner` is carried for it.
- **`// [ask-author]`:** none.

---

## 2026-07-24 — Canonical-library sync + suite reconciliation

The author dropped in a `MANIFEST.sha256.txt` "stale-upload guard" and evolved the
kernel-AST, semantics companion, and test-suite. Verified all 14 canonical files
green, then reconciled the implementation to the new material. Full tree: 234 lib +
111 conformance, 13 ignores, clippy clean.

- **Manifest caught real desync across three rounds** (recorded because the guard is
  worth trusting): first pass flagged 3 stale specs + 2 absent files; a mid-round
  upload *regressed* the test-suite to a pre-erratum T-14 copy (caught); the final
  drop resolved everything. The kernel-AST §4 now carries my guard-based tested-seat
  rows tagged `[RULED — user, 2026-07-22]`, so **implementation ↔ canonical spec are
  aligned** on T-10 (I had flagged the risk that a re-export could drop my amendment;
  it didn't).
- **Two rulings landed in the canon**, both of which my code already satisfied:
  T-10 (guard-based tested seats — `tested_match`); and **open-value observation =
  Option A** (companion §6 folds it into `unbound-evaluation`) — my oracle already
  traps an open-member read as `UnboundEvaluation` incidentally.
- **New suite cases implemented (PR-06…09, FE-07, MU-19):**
  - **PR-07 / PR-08 needed real renderer work** — `render_value` now sorts record
    keys in **UTF-16 code-unit order** and renders non-identifier keys with
    **computed-key syntax** (`["a-b"]: 2`), and quoting moved to `quote_units(&[u16])`
    so a **lone surrogate escapes losslessly** (`\uD800`, never U+FFFD). Both
    round-trip to the same pointer, verified.
  - PR-06 (top-level raw String), PR-09 (deterministic `<Function>` in an aggregate),
    FE-07 (act-kind distinguishes closures — `shape()` already includes `act_kind`),
    MU-19 (same-group construction reference is legal) all passed as-is; added rows.
- **MU-18 is PENDING-§5** — the open-member-observation trap needs the
  group-construction-window mechanism (the §5 canonicalizer); without windows a
  member closes at its own statement and `a == a` is reflexively true. `#[ignore]`
  with that reason.
- **A-WRK RECOVER discharged** — the grids are recovered in
  `next-phase-a-worked-examples-recovered.md` (`journal.txt` was the drafting
  agent's transcript mount, never a repo file). The stub's ignore reason updated:
  no longer author-blocked; verification still needs the program-level analyzer.
- **Registries reconciled:** the author's `OwedItems-CLOSED.md` archives the original
  four items; `OwedItems.md` rewritten as the fresh current registry (drift +
  C§17-remaining + Threads B/C). `PROGRESS.md` doc-sync matrix now all-green with a
  manifest line.
- **`// [ask-author]`:** the `String.units`/`points` element representation (E8
  doesn't pin it) — unchanged.

---

## 2026-07-22 — RULING [user]: strict tested seats — the T-10/D-01 conflict resolved

**The ruling:** plain ternary conditions, `&&`/`||` left operands, and `!` operands
are **strict tested seats** and trap **tested-seat** on non-Booleans *regardless of
result position*. The lowering is guard-based with bind-then-guard preserving
single evaluation. Escaped `~` forms remain falsy-set matches. (T-10's survival of
the erratum pass reflected the intended law; the catalog's PConst-arm rows were the
stale side.)

**Catalog amended** (kernel-AST §4, provenance-marked [RULED — user, 2026-07-22]):

- `c ? t : e` ⇒ `Match(∅, [Arm(guard: c, t), Arm(e)])`
- `a && b` ⇒ `Match(∅, [Arm(guard: a, b), Arm(Const(false))])`
- `a || b` ⇒ `Match(∅, [Arm(guard: a, Const(true)), Arm(b)])`
- `!x` ⇒ `Match(∅, [Arm(guard: x, Const(false)), Arm(Const(true))])`

**Bind-then-guard, degenerate:** each tested operand occurs **exactly once**, in
the guard — so single evaluation holds with no tmp binding at all (the tmp is the
general recipe's provision for lowerings that reference the tested value again;
none of these four do — their results are the branch expressions or Boolean
constants). Recorded in the catalog row so the simplification is visibly the same
law, not a shortcut.

**Implementation:** `bool_match` (Const-pattern arms over a scrutinee) replaced by
`tested_match` (guard-based, scrutinee-less) — one function, all four forms plus
the `&&:=`/`||:=` compound writes inherit it. Behavior changes exactly on
non-Boolean operands: previously silent fall-through (CompletedWithoutValue;
ExpectingSeat only at demanding seats), now **TestedSeat immediately**. Boolean
operands are observably unchanged.

**Tests:** T-10 flipped **live** (both bare-statement and bound positions);
`tested_seats_are_strict_boolean` extended (`1 || 9`, `0 && 1`, `!5` all
TestedSeat); D-01/02/03/06 extended with the non-Boolean trap asserts; the desugar
structural tests tightened to assert the guard shape (pattern `None`, guard
`Some`, scrutinee-less). Analyzer concordance holds for free: `analyze_match`
already routes guards through `check_tested_seat`, so a closed `5 ? 1 : 2` is a
TestedSeat **error** exactly as the oracle now traps. Whole tree: 230 lib + 105
conformance green, 12 ignores, clippy clean.

---

## 2026-07-22 — Conformance suite aligned to the stable IDs (tests/conformance.rs)

The suite spec's stable IDs are now executable: **104 ID-keyed tests + 13 honest
`#[ignore]`s** in `tests/conformance.rs` (phases 0–4 + the Phase A stubs), on top
of the 230 unit tests. Writing the ID rows immediately exposed **seven real
parser/desugar conformance bugs** and **one new doc conflict** — exactly what ID
alignment is for. All fixed; whole tree green, clippy clean.

**Parser/desugar bugs the suite caught (all grammar/catalog-mandated):**
- **L1 unenforced** (P-20): two statements on one line parsed. Was a documented
  deferral ("later diagnostic pass"); now a parse error in `program()` and
  `block()` (grammar §1.1 — a statement may not begin on the line where the
  previous statement's last token sits).
- **L2 unenforced** (P-21): two arms on one line parsed. Now a parse error in
  `arm_block()`.
- **`when` was effectively reserved** (P-22): `when = 5` failed to parse — a
  zero-reserved-words violation. The demand-arm head now parses under
  **backtracking**: if the whole `when <guard> => <result>` shape does not parse,
  `when` is an ordinary name. (`where = 2` already worked — its keyword check
  looks at position 1.)
- **Match-postfix operators missing** (P-10): `x :: {…} |> f` was a parse error;
  the §3 ladder note says operators after the block attach to the completed
  match. `pipe_expr` split into head + `pipe_tail`, and `match_expr` loops
  `::`-blocks and pipe-tails (the closed match form resets the mixing ban).
- **Duplicate literal record keys accepted** (P-26): now a parse error (E5 —
  "rejected upstream"); computed keys/spreads stay exempt (later-wins governs).
- **Multiple rests per level accepted** (P-29): now a parse error, tuples and
  record patterns both.
- **Alternation binding rule unenforced** (P-30): `1 | x => …` ran. Desugar's arm
  expansion now rejects any binding inside an alternative (`first_binding`:
  `Bind`, captured rests, record shorthand; pins stay legal — they compare).
- **Splice write unimplemented** (D-14): the §4 row `items[a...b] := r` ⇒
  `Write(items, [...items[...a], ...r, ...items[b...]])` now lowers (absent bound
  → that side's spread drops); compound-assign on a slice stays a clear error.
  The old "index/slice mutation" blanket error now covers only index/non-terminal
  cases.

**New doc conflict, [ask-author] (OwedItems "Doc errata"):** **T-10 vs D-01.**
The AST §4 catalog lowers `c ? t : e` to `PConst(true)/PConst(false)` arms —
`5 ? 1 : 2` completes-without-value — while the companion's seed list and suite
T-10 expect **TRAP tested-seat** ("post-desugar guard"). Implementation follows
the closed catalog; T-10 ships `#[ignore]` with the conflict recorded, T-10a
(non-Boolean *arm guard* traps tested-seat — true under either ruling) runs in
its place. The same ruling governs non-Boolean `&&`/`||`/`!` operands (D-03 keeps
to the agreeing Boolean cases meanwhile).

**Test-side lessons the grammar taught (not bugs):**
- `x = 2` ⏎ `-x ** 2` is ONE statement (§1.1's stated hazard — the leading-`-`
  continuation; P-23's lint case). P-12 binds on one line.
- **Blocks produce via `=>` exit-arm statements** (grammar §2), not a trailing
  expression (that is a discarded `Stmt` — the goes-nowhere lint). D-09 now uses
  `=> y * 2` and a guarded `when x > 0 => x` exit. Both forms already worked.
- H-03/H-05 observe the canonicalization laws through `==` (canonical code):
  `x => x + x == x => 2 * x` and the commutative-reorder pair are already true —
  ahead of the PENDING-§5 register, which is legal (the register forbids
  asserting the *interim inequality* as desired, not early success). FE-03/04/05/06
  likewise assert final expectations and pass today.
- **`String` prelude added** (harness `prelude_env`, pure natives, both run
  paths): `String.length` (grapheme count, the pinned segmenter), `String.units`
  / `String.points` views — unblocks S-01…03 (PIN-UNICODE rows green).
  `// [ask-author]`: the element representation of the views (Tuples of Numbers
  here) is not pinned by E8; only lengths are asserted.

**The 13 `#[ignore]`s, each with its reason in-file:** T-10 (doc conflict),
M-04 (needs a fuel harness), P-27b + MOD-01/03/04/05 (module-system semantics
staged), Phase A × 6 (program-level analyzer pending; A-WRK additionally RECOVER —
grid texts must come verbatim from the author's transcripts, `journal.txt`).

---

## 2026-07-22 — AUDIT: full codebase check against the evolved docs

A systematic walk of every module against the current normative set (compendium
1.0.8, RC 0.2.2, tuple family 0.3.1, app-induction 0.8.1, test suite v0.1, μ v0.5,
grammar/kernel-AST/semantics v0.1). Four bug classes found and fixed — three of
them introduced by `Concat` landing after older exhaustive logic, one a
day-one analyzer gap. Full suite 230, 0 ignored, clippy clean.

**Fixed — soundness:**
- **S1** `recursive::exact_eval` had no `Concat` arm, so a Concat definition fell to
  the `NonEmpty` leaf default. Consequence: `L = Union(Function, Concat(Tuple(E), L))`
  was voiced NonEmpty at the def while unproductive, so the exactness pass left it
  **proven Empty** — and emptiness feeds subcontract step 0, so `L ⊑ Number` would
  falsely prove. Fixed: Concat joins segments by the product rule (as Tuple).
  Regression: `audit_concat_emptiness_voice_is_sound` (plus the genuinely-empty
  no-base control).
- **S2** `contains_tuple_window` / `window_contains` had no `Equals` arm —
  `Concat(Equals([1]), Tuple(Number))` wrongly rejected `[1, 5]`. Membership is the
  denotational truth source; a false negative there is a bug, not conservatism.
  Fixed with elementwise `values_equal` (no interner needed). Regression:
  `audit_equals_segment_membership`.
- **S3** `length::classify` recursed `len → solve → classify` unboundedly when an
  own-SCC reference sat *nested inside* a segment (e.g. under a Union) — stack
  overflow. Fixed with `length_path_hits`: own-SCC refs on **length-relevant**
  paths (Union/Concat/Intersection/Difference/Ref) decline to `Opaque`; refs inside
  Tuple elements / Record fields stay admissible because arity never recurses into
  element lengths (`N = Tuple(E, N-or-base)` stays exactly 2 — asserted in the
  regression's control).
- **S4** analyzer concordance holes: closed `[...5]`, `{...[1]}`, `{[5]: v}` were
  **accepted** while the oracle traps (spread-kind / computed-key). `Apply` had the
  spread check; the constructors never did — and the concordance corpus never
  generated those forms, so the sweep couldn't catch it (test-coverage gap
  compounding the code gap). Fixed: `check_spread_kind` generalized over the
  expected kind and applied at TupleCons/RecordCons spreads; `check_computed_key`
  added; computed/spread subexpressions now sit in expecting seats (`demand`).
  Corpus gained all six rows (three trapping, three fine).
- **Bonus precision (family §1):** a `TupleCons` with spreads now types as a
  **Concat** instead of `Top` — `[1, ...t]` with `t : Tuple([Number])` fuses to the
  exact `Tuple([Equals(1), Number])`; an unknown spread keeps a `Kind(Tuple)`
  segment (sound: on the non-trapping path the spread value *is* a tuple).
- **A-VER computed-key demand implemented:** a computed key must be a
  **proven-finite string set** (E5, fork 12 = R) — finite unions accept,
  `Kind(String)` REJECTs. Recorded nuance: that rejection is a *domain demand*
  (analyzability), not a trap prediction — noted in the code.
- **`Concat` added to the C§12.2 constructor list** (`expr.rs`), through the
  normalizing smart constructor.

**Registered, not rebuilt (OwedItems "Registered implementation drift"):** C§16's
upgraded `OperationOutcome` interface [1.0.7] (needs the app-induction package's
`AnalysisContract`); `Record(Exact | Open)` [1.0.7] (open patterns lose per-field
contracts); μ v0.5 §6 universal interning vs bisimulation-at-compare (equal on all
`==` results; `equal.rs` header now carries the architecture note — its stale v0.1
citation fixed); missing `Concat` C.2 rows (all `Unproven`, sound — §4 alignment is
the scheduled fix).

**Doc errata flagged to the author:** the semantics companion still carries the
deleted `unprintable-interpolation` trap row.

**Checked clean:** poly.rs against μ v0.5 §8 (the narrow slice, abort semantics);
B2 printing (N-03 rows); expecting-seat `eval_value`; `eval_record`'s
computed-key/spread traps; PR-01…05; RC guardedness/positivity Concat arms;
`structurally_uninhabited`; no test asserts a PENDING-§5 interim inequality as
desired behavior.

**Known coverage gaps (staged work, not staleness):** suite IDs not aligned to the
spec's stable names; Phase A `#[ignore]` stubs absent; `String.length/units/points`
prelude functions missing (S-01…03 blocked); MOD-01…05 module-system semantics
partial (imports are link-metadata only; no module-header world distinction).

- **`// [ask-author]`:** none.

---

## 2026-07-21 — Tuple family §2: `len` — Λ-semantics with exactness stamps

`src/contract/length.rs` (new) + `recursive::contract_emptiness` + 6 TL cases.
Full suite 225, 0 ignored, clippy clean.

- **`len(group, c) → Len { contract, stamp }`** with `Stamp = Exact | Approx`. The
  soundness law `Λ(T) ⊆ ⟦contract⟧` holds always; `Exact` additionally claims
  `⟦contract⟧ = Λ(T)`, provenly. An **uninhabited shape yields `(Bottom, Exact)`** —
  impossible shapes are never realizable lengths, and this is checked *first*, so it
  governs every other row.
- **Non-recursive rows:** exact tuples/records → `Equals(k)` stamped by the
  inhabitation triage (proven-inhabited → `Exact`; unproven → `Approx`, since an
  unproven shape may be empty); open records → `GE(n)`; `Concat` → the C§7 sum;
  `Union` → the union of branch lengths (`Exact` iff all branches are — the union of
  exact sets is exact). Summation is exact only when **both operands are finite
  exact sets**; a `GE` operand pushes the rule to the minima and stamps `Approx`,
  which is the "approximate *rule*" half of §2's condition, not just approximate
  operands.
- **Recursion — the weighted-graph solver.** SCC members are states; each recursive
  alternative is an edge weighted by its nonrecursive length contribution; base
  alternatives contribute accepting lengths. Achievable sets are saturated to a bound
  **computed in advance** from the finite label sets (Principle 7), then rendered as
  an ultimately-periodic contract: per residue class, the smallest point from which
  the class is complete becomes a `Mod ∩ GE` tail, and anything below stays an
  explicit `Equals` exception.
- **The period is the gcd of CLOSED-WALK weights**, computed by edge potentials
  (`pot[u] + w − pot[v]` per edge), *never* the gcd of individual transition weights.
  TL-19 is the test that separates them: `R = Tuple() | Tuple(E)++S; S = Tuple(E)++R`
  has two weight-1 edges but cycle weight 2, so `Λ(R)` is the evens and `Λ(S)` the
  odds; an edge-gcd of 1 would erase the parity. The test asserts both directions
  (R rejects every odd, S rejects every even).
- **Exactness is forfeited**, dropping to `(GE(minimum), Approx)`, when an
  alternative is **nonlinear** (>1 own-SCC reference — TL-15) or a label falls
  outside the **finite-exact boundary** (TL-22's infinite increment language). Both
  sound.
- **TL cases:** TL-13 `Repeat(Bottom)` → `(Equals(0), Exact)`, never `GE(0)` — the
  recursive branch Bottom-normalizes through `Contract::concat`'s §1 rule, so the
  base alone survives. TL-14 increments {2,3} over {0} → `{0} ∪ [2,∞)` exact, with
  **length 1 unrealizable** (the semigroup gap — the naive "smallest element of the
  residue class" rendering would have wrongly admitted it). TL-19, TL-15, TL-22 as
  above, plus the non-recursive rows.
- **Scope:** §3's refutation discipline (Approx may refute *intersection emptiness*
  by disjoint uppers, but may **never** supply a subcontract refutation witness),
  `restrictLen`/`LengthRestricted` (§3), the alignment procedure (§4), and the
  grapheme seam summaries (§5) are the remaining family pieces. `len` is not yet
  wired into `subcontract`, so no verdict currently depends on a stamp.
- **`// [ask-author]`:** none.

---

## 2026-07-21 — `Concat` + `sourceProgress` (tuple family §1; RC patch 0.2.2)

The algebra prerequisites for the tuple-length family. Full suite 219, 0 ignored,
clippy clean.

- **`Contract::Concat(segments)`** — a tuple that splits into consecutive segments,
  positive in every segment. Smart constructor `Contract::concat(..)` applies §1's
  normal forms: nested Concats **flatten** associatively; the canonical empty-tuple
  segment **erases**; adjacent exact segments **fuse**; and an **uninhabited segment
  never erases** — it Bottom-normalizes the whole Concat, since erasing it would
  turn an empty contract into an inhabited one. Uninhabitance there uses only
  *permanent structural* facts (`structurally_uninhabited`), never temporary
  analysis state, exactly as §1 requires.
- **Membership** is the denotational reference: a backtracking split over
  consecutive windows, with fixed-arity segments consuming exactly their arity. The
  analyzer's alignment procedure (§4) decides the *contract* question without
  enumerating and is a later increment.
- **Recursive layer (RC 0.2.2):**
  - positivity now descends through `Concat` segments;
  - **guardedness**: a `Concat` edge guards a segment when some *sibling* has a
    permanently proven structural minimum length ≥ 1 (`min_extent`) — segment-local,
    so the proof never consults the productivity of the group under admission (the
    non-circularity clause). This is what admits `Repeat`;
  - **`sourceDepth` → `sourceProgress`**, and the subcontract gained an aligned
    `Concat ⊑ Concat` row that carries the source's **consumed extent** as progress
    — flat sequence recursion licenses reuse by what was consumed, not by nesting;
  - group-aware `Concat` membership and inhabitant enumeration (a bare
    `Contract::contains` cannot resolve `Ref`s inside segments).
- **RC-17/18/19 implemented.** RC-17 `Repeat(Number) ⊑ Repeat(Top)` proves *only*
  through consumed-extent progress (the revisited pair closes at advanced progress).
  RC-18 `Repeat(Number) ⊄ Repeat(String)` is refuted with a **complete finite tuple**
  witness `[1]` — asserted to be a whole tuple, not a naked element (§5.3). RC-19's
  mutual Record/Concat cycle terminates and stays inhabited.
- **Scope:** only the *aligned* `Concat ⊑ Concat` case (equal segment counts) is
  decided; the general alignment procedure (§4 forced-boundary peeling over unequal
  counts) lands `unproven` rather than guessing a split. Sound. `len` with its
  `Exact | Approx` stamps (§2) is the next increment.
- **`// [ask-author]`:** none.

---

## 2026-07-21 — CORRECTION: structure interpolation is total (the trap is deleted)

**I implemented a ruling that had already been reversed.** Structure interpolation
was ruled **total [user, 2026-07-18]**; I was working from a stale CLAUDE.md that
still read *"trap, per spec — the print doctrine is deliberately open"*, and this
session I built, defended in conversation, and documented the *opposite* of the
ruling — including telling the author the doctrine was doc-open when it had been
closed three days earlier. Root cause: I trusted the CLAUDE.md snapshot in my
session context instead of re-reading the file from disk. Full suite 212, clippy
clean.

Authority: compendium 1.0.8 — *"Structure interpolation is total: every value
renders — Tuple/Record as canonical literal forms (sorted-key records; inner
strings quoted), `<Function>`, `<Indeterminate _/0>`/`<Indeterminate 0/0>` (the
form, never operands); literal-formed values round-trip (parse ∘ print = identity,
a harness law); angle-bracket forms are visibly non-parseable."* Test-suite spec
line 57 makes the deletion explicit: *"The former fourteenth class,
unprintable-interpolation, is deleted."*

- **Oracle `stringify` is now total** (`render_value`): Tuple → `[a, b]`; Record →
  `{k: v}` **sorted by key**; nested Strings quoted and JS-escaped while a
  *top-level* String interpolates raw; Numbers via B2; `<Function>` for closures and
  natives; `<Indeterminate _/0>`/`<Indeterminate 0/0>` — the **form only**, so `1/0`
  and `2/0` are indistinguishable (interning forbids remembering operands, PR-04).
- **`TrapClass::UnprintableInterpolation` removed.** Thirteen classes remain,
  bijective with suite T-01…T-14 (the ID range is stable; one case superseded —
  "never delete a case").
- **Analyzer `analyze_template`**: the printability demand is gone entirely — a
  template always yields `Kind(String)` and carries **no** finding. Interpolations
  remain expecting seats, so a genuinely trapping subexpression still reports.
  Deleted the now-dead `Printability`/`printable_value`/`printability`/`union`
  helpers.
- **Suite PR-01…05 implemented** as named cases. PR-05 (parse ∘ print = identity)
  initially failed for a methodological reason worth recording: `run_program_value`
  builds a **fresh interner per call**, so comparing values across two calls by
  pointer is meaningless. Added `eval_in(interner, src)` so the original, its
  rendering, and the re-parse all share one interner — then the law is the pointer
  test it should be. Also: `;` is not a statement separator (L1 — newline-separated).
- **`OwedItems.md` rewritten** against C§17 patch 1.0.8: every item it previously
  listed has been discharged by the author (tuple family and application/induction
  now **specified**; print doctrine **ruled**; arrow contract **superseded** by
  `AnalysisContract`). It now indexes what C§17 still owes.

---

## 2026-07-21 — Named contracts: static contract-expression evaluation (C§12.2) + patterns

`src/contract/expr.rs` (new) + a `ContractEnv` threaded through the analyzer + 5
tests. Full suite 209, 0 ignored, clippy clean.

- **Contract expressions are statically evaluated (C§12.2 / §292).** Contract
  constructors are predeclared prelude *names* and a named contract is an ordinary
  binding of a contract expression (`Percent = Range(0, 100)`), so
  `eval_contract(expr, env) → Option<Contract>` interprets a kernel `Expr`:
  constructor applications (`Range`/`Greater`/`GreaterEq`/`Less`/`LessEq`/`Mod`/
  `Geo`/`Equals`/`HasField`/`Union`/`Intersection`/`Difference`/`Tuple`), prelude
  names (the seven Kinds, `Top`, `Bottom`, and the `Failure` shape), **structural
  literals** (a tuple literal of contracts is a tuple contract; a record literal is
  a record contract), and references to already-bound named contracts.
  `build_contract_env` folds a sequence of `name = contract-expression` bindings
  into a [`ContractEnv`], so later contracts compose earlier ones
  (`Grade = Union(Percent, Null)`).
- **One resolution path.** The analyzer's `contract_ref` (contract-as-pattern, E9)
  now *delegates to* `eval_contract`, so patterns and contract expressions agree by
  construction rather than by two hand-kept name tables.
- **Threaded through the analyzer.** Every `analyze_*` now carries
  `cenv: &ContractEnv` beside the value-level `TypeEnv`, so a user contract resolves
  wherever a pattern appears — including nested `Match`es inside operands.
- **The payoff, tested with controls:** `Percent = Range(0, 100)` now (a) *narrows*
  an arm — `match x { Percent => … }` with `x : Number` is correctly **not
  exhaustive** (an unresolved name would widen to `Top` and wrongly look total), and
  (b) *refutes* a destructuring bind — `Percent = 500` is a `refuted-binding` error.
  Both tests assert the empty-env control behaves oppositely, so they prove
  resolution actually happens rather than passing vacuously.
- **Scope (implementation-owed, not doc-owed):** **recursive/mutual source
  contracts** — a named contract referencing itself or its group — do not yet build
  a `RecGroup`; a self/forward reference simply fails to resolve (`None` → `Top`, no
  narrowing; sound). The C§9 machinery it would feed is already implemented and
  green; wiring source → `RecGroup` is my next increment. Numeric/string constructor
  arguments must be literals; statically evaluating *computed* contract arguments is
  the remaining C§12.2 surface.
- **`// [ask-author]`:** none.

---

## 2026-07-20 — Analyzer: `Apply` (C§7 / B5 / E10 — application)

`src/analyzer/mod.rs` `analyze_apply` + a Tuple-arity disjoint rule + 2 tests and
closed `Apply` concordance rows. Full suite 204, 0 ignored, clippy clean.

- **Closed calls fold exactly.** Known callee value (`Equals(closure/native)`) plus
  singleton plain args → reconstruct `Apply(Const, [Const…])` and run `eval_expr`,
  predicting world-admission / argument-obligation / spread-kind / not-a-function /
  expecting-seat exactly. Corpus gained an identity call (produces), an arity
  mismatch (argument-obligation), a non-function callee (operation-safety), an
  Effect call in the pure world (world-admission), and a non-Tuple spread
  (spread-kind).
- **Open calls, reasoned:** each `Spread` arg must be `⊑ Kind(Tuple)` (else
  spread-kind error / warning); a callee provably disjoint from `Kind(Function)` is
  operation-safety; and when the callee value is **known** (`Equals`), its act-kind
  is admission-checked and the argument tuple `Tuple([arg contracts])` is checked
  against `pattern_contract(params)` (argument-obligation, reusing the `Match`
  pattern machinery). A mutator callee `may_complete` (returns discarded).
- **World context = pure** (matching the `eval_expr` truth source). World threading
  and `Lambda`-body / function-shape analysis (C§13.2) are later increments, so:
  an **open** call's *return* types as `Top`, an unknown callee's act-kind/arg
  obligation is **not** checked (Unproven, silent), and a `Pure`/`Effect` body's
  completion is not derived (`may_complete = false` for non-mutators). All sound —
  no false accept in the tested pure-world concordance; the gaps are the honest
  cost of not yet analyzing function bodies.
- **C.2 rule added:** `Tuple(pa) ⌢ Tuple(pb)` disjoint when arities differ or any
  position is disjoint — the basis of the arity-mismatch argument-obligation.
- **`// [ask-author]`:** none.
- **Provenance correction (the deferred pieces are doc-owed, not merely
  unimplemented).** Unlike `Access`/`Match` (decided design, sequenced by me), the
  *deep* `Apply` deferrals rest on genuine **C§17 Owed** items now recorded in
  `OwedItems.md` §3–§4: the **`analyzeOperation` application table** (the app rule's
  admission + expecting-seat demand — owed verbatim), **domain-indexed return
  induction** details + the **instance / global-fact-graph** machinery (open-call
  return + body completion), and the absence of a **first-class function-shape
  (arrow) contract** (unknown-callee reasoning). What *was* decided and so
  implemented: the B5 admission matrix, argument-obligation as a parameter-pattern
  match, spread-kind, and the closed-fold technique.

---

## 2026-07-20 — Analyzer: `Match` (E9/E10 — the sole control node)

`src/analyzer/mod.rs` `analyze_match` + pattern machinery + `Analysis.may_complete`
+ expecting-seat demands + 4 tests and closed `Match` concordance rows. Full suite
202, 0 ignored, clippy clean.

- **Arm narrowing (E9).** Each arm narrows the scrutinee by its pattern —
  `pattern_contract` maps a `Pat` to a *superset* of its match set (sound for
  intersection): `Const → Equals`, `Wild`/`Bind → Top`, exact `Tuple`/`Record` →
  the structural contract, open record → `∩ HasField`, `Contract(ref)` → the prelude
  Kind (user contracts owed → `Top`). The arm body sees `remainder ∩ pattern`, and
  the **remainder** for later items is the accumulated Difference; a covering
  pattern (`remainder ⊑ pattern`) empties it. `bind_pattern` threads the narrowed
  contract to the pattern's names (e.g. `[a, b]` on `Tuple([Number, Number])` gives
  `a, b : Number`, proving `a + b` safe).
- **tested-seat (E10).** A guard must be `⊑ Boolean` — else error (provably
  non-Boolean) or warning.
- **refuted-binding (E9).** A destructuring `Bind` must be irrefutable
  (`value ⊑ pattern`) — else error (disjoint) or warning.
- **expecting-seat (E10) via `Analysis.may_complete`.** A `Match` whose remainder
  is not provably empty may complete without a value; the new `demand(...)` helper,
  called at every value-demanding seat (operands, elements, field values, template
  interpolations, access receiver/index/bounds, bind RHS, guard, arm result,
  scrutinee), turns that into an expecting-seat error. Statements are *not*
  expecting seats. A standalone non-exhaustive `Match` is fine (it just completes
  without a value); the error is only at a demanding seat — matching the oracle.
- **Result contract** = union of arm results (`Top` for an arm-less match).
- **Closed `Match` folds are not needed for exactness** — the structural reasoning
  already predicts the trap classes; the concordance corpus gained `match 5 {5=>10}`
  (produces), a non-Boolean guard (tested-seat), a non-exhaustive match in an
  operand (expecting-seat), and a refuted destructuring (refuted-binding), all
  agreeing with `eval_expr`.
- **Owed within `Match`:** `Pat::Contract` to a *user* contract resolves to `Top`
  (no narrowing) until a named-contract environment exists; tuple-rest / record-rest
  patterns widen (length ← C§17). Both sound (no false accept). `// [ask-author]`:
  none.

---

## 2026-07-20 — Analyzer: access demands (E6 — Field / Index / Slice)

`src/analyzer/mod.rs` `analyze_access` + supporting C.2 disjointness rules + 2
tests (closed access rows in the concordance corpus; open field reasoning). Full
suite 198, 0 ignored, clippy clean.

- **`Access(target, form, total)` (E6).** The demand form (`total = false`) must
  prove the receiver non-null and the field present / index in bounds; the total
  form (`?.`) totalizes null/absent/out-of-bounds to `null` and never traps on
  those; slices are clamped-total on the window but still demand a sliceable
  receiver and integer bounds.
- **Closed accesses are exact.** When the receiver (and any bound) is a singleton,
  `analyze_access` reconstructs a `Const`-childed node and runs the oracle's own
  `eval_expr` — predicting NullReceiver / AbsentField / IndexBounds /
  OperationSafety(slice) exactly. Added to the concordance corpus (field present /
  absent / null-receiver / `?.` totalization / tuple index in-bounds / out-of-bounds
  / from-end / totalized).
- **Field access fully reasoned on open receivers.** `⊑ HasField(name)` → accept
  (output = the field's contract when the receiver is an exact `Record`); `?.` →
  accept (result `∪ Null`); provably-disjoint from `HasField(name)` → **error**
  (NullReceiver if the receiver can be null, else AbsentField); otherwise a warning.
- **Index/Slice bounds are owed (C§17).** Open index/slice out-of-fold cases catch
  a provably-null receiver as an error, but otherwise emit a **warning** — bounds
  reasoning needs the tuple-length family, tracked in `OwedItems.md` (C§17 owed).
  Honest: not silently accepted.
- **C.2 disjointness rules this needed (added + soundness-tested):** a non-Record
  kind ⌢ `Record`/`HasField`; a non-Tuple kind ⌢ `Tuple`; an exact `Record` lacking
  field `k` ⌢ `HasField(k)`. New `contract::disjoint` public wrapper + a
  `disjoint_soundness` sweep (no provably-disjoint pair shares a pool value).
- **`// [ask-author]`:** none.

---

## 2026-07-20 — Analyzer (Part D begins): pure-fragment contract inference + §6 concordance

`src/analyzer/mod.rs` (new) + `oracle::eval_expr` (exposed) + 7 tests incl. the
exact concordance sweep and an open-term soundness sweep. Full suite 194, 0
ignored, clippy clean. This is the first analysis pass over kernel AST — legitimate
now that the oracle, normalization harness, and contracts C.1–C.3/C§9 are green
(CLAUDE.md hard rule 1).

- **`analyze(expr, env, interner) → Analysis { contract, findings }`.** Infers a
  contract over-approximating the produced value and gathers `Finding`s tagged with
  the oracle `TrapClass` they mirror (§6). `Severity::Error` = proven-to-trap (a
  rejection); `Severity::Warning` = unproven-safe (surfaced, not a rejection).
  `Analysis::accepted()` = no error findings.
- **The §6 concordance made executable.** For each `PrimOp`, findings come from the
  contract layer: constant-fold when every operand is `Equals(v)` — run the oracle's
  own `eval_prim`, so a closed expression's trap **class is predicted exactly**;
  otherwise `analyze_operation` (C.3), with `Refuted(witness)` → an error whose class
  is read back from the oracle trapping on that witness, and `Unproven` → a warning.
- **Why constant-fold (not just `analyze_operation`):** `analyze_operation` outputs
  `Kind(Number)` for `Add(Equals,Equals)`, which loses exactness — e.g. `(2+3)^-1`
  would then sample `0` and *falsely* report a `0^neg` trap. Folding keeps
  `(2+3) → Equals(5)`, so nested closed expressions predict traps exactly and match
  the oracle. This is the analyzer doing partial evaluation on constants.
- **Truth-sourced brute-test.** Exposed `oracle::eval_expr` (evaluate a closed
  kernel expr, pure world, empty env). The concordance test runs a corpus of closed
  expressions through both: `oracle traps ⇔ analyzer errors`, and the classes agree
  (covers `OperationSafety`, `UndischargedIndeterminate`, division totality, `0^neg`,
  non-integer exponent, Indeterminate propagation, nested/tuple/record). An
  open-term test confirms the soundness direction: an *accepted* expression over a
  variable's contract never traps on sampled admitted values.
- **Scope (this increment):** the pure expression fragment — `Const`, `Ref` (against
  a `TypeEnv`; unbound → `UnboundEvaluation` error), `PrimOp`, `TupleCons`,
  `RecordCons`, plus `Template` (added below). Next: access demands (E6 →
  Null/AbsentField/IndexBounds), then `Match`, then application.

- **Provenance of the not-yet-checked nodes (the honest three-way split).** The
  remaining nodes are *not* a single "documented gap"; there are three distinct
  statuses:
  1. **Design decided, implementation owed by me** (an increment boundary, not a
     spec gap): `Access` (E6 demands), `Match` (E9/E10: tested-seat, refuted-binding,
     expecting-seat, arm narrowing via accumulated Difference), `Apply`
     (`analyzeOperation(application)` — argument-obligation, world admission B5,
     expecting-seat, spread-kind), `Write`/worlds (B5 matrix; mutator return-nothing).
     The docs pin these; I simply haven't built them. They type as `Top`, unchecked.
  2. **Doc-owed contract family**: `TupleCons`/`RecordCons` *spread* and
     *tuple-length/concatenation* lean on **C§17 (owed)**; my `Top` for spread shapes
     is backed by a genuine open in the spec.
  3. **Doc-open (E11 print doctrine)**: `Template` structure interpolation is
     *trap-until-ruled* — the correct behavior is to **reject**, not accept.

- **`Template` implemented (correcting the earlier `Top`-as-accept).** Typing
  `Template` as `Top` silently *accepted* structure interpolation — an unsound
  acceptance against E11 (the oracle already traps `UnprintableInterpolation`). Now
  `analyze_template` demands printability per interpolation, mirroring the oracle's
  `stringify` (String/Number/Boolean/Null print; structures + Indeterminate trap):
  singleton → exact; `⊑ {String,Number,Boolean,Null}` → accept; provably a
  structure (`⊑ Kind(Tuple)∪Kind(Record)∪Kind(Function)`, or an `Indeterminate`) →
  **error**; otherwise → warning. Template's result contract is `Kind(String)`.
  Added to the closed-expression concordance corpus (printable + structure cases).
- **C.2 gap this surfaced (fixed):** subcontract lacked "a structured contract
  inhabits its kind" — added `Tuple(_) ⊑ Kind(Tuple)` and
  `Record(_) | HasField(_) ⊑ Kind(Record)` to `atom_provable`, and extended the C.2
  soundness sweep with `Kind(Tuple)`, `Kind(Record)`, a `Tuple([Number])` contract,
  and tuple values. (Numeric atoms already had `⊑ Kind(Number)`; this closes the
  structural analogue.)
- **`// [ask-author]`:** none — the `Template` behavior follows E11's stated
  "trap until ruled"; when the print doctrine is ruled, only `analyze_template`'s
  accept/reject boundary moves.

---

## 2026-07-19 — Contracts C.1: the algebra + denotational membership (Part C begins)

`src/contract/` (mod.rs, tests.rs). Compendium C§4 (contract algebra) + C§16
(denotational kernel). 10 membership seeds; full suite 163, 0 ignored, clippy
clean. **First analysis-layer code** — legitimate now the oracle + harness are
green (hard rule 1).

- **Delivered:** the `Contract` enum (C§4): `Top`/`Bottom`, `Kind`, `Equals`,
  `Range`, `Greater`/`GreaterEq`/`Less`/`LessEq`, `Mod{n,r}`, `Geo{b,r}`,
  `Union`/`Intersection`/`Difference`, `Record`/`HasField`/`Tuple`,
  `Indeterminate`. Plus `Contract::contains(v)` — denotational membership
  (`v ∈ ⟦C⟧`, C§16), decidable for every constructor, brute-tested against the
  oracle's interned values.
- **Notes on specific rules:**
  - `Equals` uses the oracle's `values_equal` (bisimulation), so a fresh
    structurally-equal value satisfies it — not pointer identity.
  - `Mod{n,r}` denotes integers `x ≡ r (mod n)` (rational moduli clear to the
    integer lattice, C§3.1); non-integers are excluded.
  - `Geo{b,r}` (`r>1`, `b≠0`) is decided by dividing out `r` — terminates since
    `r>1` shrinks the quotient.
  - `NotEquals` is **not** a constructor — it is `Difference(Top, Equals(v))`
    (C§4), and tests exercise it that way.
- **`Record(fields)` field-openness — RESOLVED [user, 2026-07-20]: exact.**
  (Was flagged `[ask-author]`.) A `Record` contract denotes a record with
  **exactly** those fields (no others), each satisfying its contract — matching
  the pattern layer's exact-by-default `PRecord(fields, rest?, exact)` (E9) and
  full-keyed records (E11). `HasField(key)` is the open "at least this field"
  form. Membership updated: `record_contains` now also checks the key set matches
  (equal counts + all listed fields present ⇒ equal key sets).
- **Deferred:** named recursive contracts (C§9 `[owed]`) — no constructor yet;
  they need the certified-unfolding doctrine + μ-binder contract canonicalization.
- **Next (C.2):** three-valued subcontract `A ⊑ B` (proven/refuted/unproven),
  brute-tested against membership.

---

## 2026-07-20 — Contracts C§9: recursive contracts (admissibility, emptiness, subcontract)

`src/contract/recursive.rs` (new) + `Contract::Ref` + 10 RC tests. Recursive
Contracts Specification v0.2 (patch 0.2.1). Full suite 184, 0 ignored, clippy clean.

A recursive contract is a named binding in a `RecGroup` referencing itself/its
mutual group via `Contract::Ref`. Four subsystems, all over the finite canonical
graph (never a materialized unfolding, §4):

- **Admissibility (§1) → `admissible`, `DefError`.** Positivity by a polarity walk
  (`Difference(B,E)` flips E; a group reference at negative polarity → definition
  error) and structural guardedness by an unguarded-reachability graph (a reference
  reachable without crossing a `Tuple`/`Record` constructor; any cycle → error).
  RC-09 `Bad = Difference(Top, Bad)` rejected (negative); RC-10 `R = R` and
  `R = Union(Number, R)` rejected (unguarded, the latter with the "denotes Number"
  hint).
- **Membership (§3) → `contains`.** Inductive: `Ref`s resolve to definitions and the
  value strictly shrinks at each structural descent, so on admissible groups it
  terminates over finite acyclic data.
- **Emptiness (§6) → `emptiness` : bounded productivity closure.** Two monotone
  passes over the group's finite state space (each state flips at most once — no
  iteration budget, Principle 7): (1) *productivity* seeds inhabited leaves and
  flips a name when a `Union` branch / all `Tuple`·`Record` components / a resolved
  `Ref` become productive, **storing a finite witness at each flip**; (2)
  *exactness* marks the still-unproductive names `Empty` unless they depend on an
  opaque leaf (→ `Unproven`). RC-11 flagship `Record({next: R})` empty; RC-12 mutual
  `A/B` both non-empty with witnesses `{b: null}` / `null`; RC-13 mutual `A/B` both
  empty; RC-15 opaque `Kind(Function)` leaf → emptiness stays `Unproven`.
- **Subcontract (§5) → `subcontract` : progress-guarded pair induction.** Empty-source
  short-circuit (step 0) via the emptiness env; a per-pair **depth-stamped** hypothesis
  that closes a revisit as *holds* only at strictly greater source depth (a global
  progress flag would be non-conforming, RC-16); source depth increments only on
  `Tuple`/`Record` descent; `Ref` heads resolve without incrementing (μ-traversal);
  ordinary constructor rows otherwise; leaf pairs delegate to the C.2 check. RC-11
  `μR.Record({next:R}) ⊑ Number` **proven** via the empty source (v0.1 would have
  wrongly refuted); `NumList ⊑ AnyList` proven by closing the revisited tail-pair at
  greater depth. Soundness spot-checked against `contains`.

- **`Contract::Ref` added** to the core enum; bare (no ambient group) it denotes
  nothing — `contains` is `false`, `sample` empty — so non-recursive code is
  unaffected and recursive code resolves references first.

- **`// [ask-author]`:** none.

### Follow-up (same day) — the two owed rows closed

- **RC-14 recursive-`Intersection` emptiness over the finite product graph** is now
  built (`intersection_emptiness`/`inter`): product states are pairs `(a, b)`,
  Unions distribute, `Record`/`Tuple` descend into paired components, `Equals`
  decides exactly by membership, `Ref` pairs form product states cut on revisit
  (the least fixpoint — an intersection inhabited only *through* a cycle has no
  finite witness, so is empty), and leaf pairs bottom out in the C.2 `disjoint`
  check plus a sampled common witness. Wired into both `prod_eval` (witness) and
  `exact_eval` (voice). Tests: two individually-inhabited recursive contracts whose
  intersection is non-empty (shared base `1`) and empty (disjoint bases `1`/`2`).
- **§5.3 witness-assembled refutation** is now built: after a failed proof,
  `refute` enumerates finite inhabitants of the source at increasing unfolding
  depth (`REFUTE_DEPTH = 4`, a bounded search — no proof is ever capped) and returns
  the first re-verified `w ∈ ⟦A⟧ ∖ ⟦B⟧`. Sound (every witness re-checked), and
  empty sources yield no inhabitants so are never wrongly refuted (they short-circuit
  to `Proven` at step 0 first). Test: `NumList ⊄ StrList` refuted with a concrete
  number-list witness.
- **Remaining bounded-ness (sound, incomplete):** the refutation search and the
  leaf-pair witness sampling are depth/fan-out bounded, so a counterexample that
  only appears deeper than the bound stays `Unproven` rather than `Refuted`. No
  proof path is bounded. `// [ask-author]`: none.

---

## 2026-07-20 — Contracts C.3: operation transfer rules (`analyze_operation`)

`src/contract/operation.rs` (new) + `oracle::eval_prim` (exposed) + 5 tests incl.
an operation × input-grid soundness sweep. Compendium C§7 / C§16 obligation 3.
Full suite 174, 0 ignored, clippy clean.

- **`analyze_operation(op, [C₁…Cₙ]) → { safety, output }`** — the one uniform rule
  shape the spec mandates for every primop.
  - **`safety: OpSafety`** = `Proven` / `Refuted(witness tuple)` / `Unproven` — a
    subcontract carrying an *n-ary* witness. Proof side discharges the op's demand
    via C.2 `subcontract` (`+` wants two Numbers **or** two Strings; `- * / % < <=
    > >=` want two Numbers; `^` wants an integer exponent and no `0`-to-a-negative;
    `== !=` never trap). Refutation samples operand tuples and asks the **oracle**
    (`eval_prim`) whether they trap — the witness genuinely halts.
  - **`output: Contract`** over-approximates the image. Interval arithmetic where
    clean (`Range+Range`, `Range−Range`, `Range·Range` corner products, negation
    flips bounds), `Kind(Number)`/`Kind(Boolean)` otherwise.
- **Oracle as truth source:** extracted the value-level primop dispatch into
  `Oracle::apply_prim` and exposed `oracle::eval_prim(op, args, interner)`. The
  sweep runs every op over an input-contract grid, samples operand tuples, and
  checks: `Ok(v) ⇒ output.contains(v)` (no image escape), `Err ⇒ safety ≠ Proven`,
  and every `Refuted(w)` actually traps. This is Part I's "brute-forced per-rule
  against the oracle" applied to operations.
- **Two totality/passthrough subtleties made explicit** (both mandated by the
  semantics companion, surfaced by the sweep):
  1. **Division is total** — a `0` divisor yields `Indeterminate`, *not* a trap. So
     `/` and `%` are safety-`Proven` on any two Numbers, and the output unions in
     `Indeterminate(_/0)`/`(0/0)` exactly when `0 ∈ ⟦divisor⟧` (decided by
     `contains`).
  2. **Arithmetic passes an Indeterminate operand through unchanged** — so when any
     operand contract can contain an Indeterminate, the image includes that form
     (`with_indet_passthrough`). Without this the sweep caught `Add(Top,Top)` on an
     Indeterminate operand escaping a `Number∪String` output.
- **Known incompleteness → `Unproven`** (sound): non-interval numeric outputs fall
  back to `Kind(Number)`; `Pow` output is `Kind(Number)`; demands that C.2 can't
  yet prove (e.g. integer-exponent on a `Range`) yield `Unproven` unless a sampled
  tuple traps.
- **`// [ask-author]`:** none.

---

## 2026-07-20 — Contracts C.2: three-valued subcontract `A ⊑ B`

`src/contract/subcontract.rs` (new) + tests. Compendium C§8. 7 subcontract seeds
incl. an O(n²) soundness sweep; full suite 169, 0 ignored, clippy clean.

- **`subcontract(A, B) → Verdict`**: `Proven` (`⟦A⟧ ⊆ ⟦B⟧`), `Refuted(witness ∈
  ⟦A⟧ \ ⟦B⟧)`, or `Unproven`. Soundness is the invariant.
- **Proof side (sound):** structural rules — `A\E ⊑ B` from `A ⊑ B`; `A ⊑ B∩C` iff
  both; `A∪B ⊑ C` iff both; `A ⊑ B\E` iff `A ⊑ B` and `A ⌢ E` disjoint; the
  sound-but-incomplete "or" rules (`A ⊑ B∪C`, `A∩B ⊑ C`). Atom rules: `Kind`
  equality, numeric-atom ⊑ `Kind(Number)`, `Mod` lattice (`n2|n1` ∧ `r1≡r2 mod
  n2`), exact `Record` fieldwise, `Tuple` positional, `Equals(v)` via membership,
  and **interval containment with intersection meet** — so landing zones
  (`Intersection(Greater(T), LessEq(T+d))`, C§4) prove.
- **Refutation side (sound):** sample members of `A` and return the first that
  fails `B`. Interval sampling includes a **fractional near-bound point** (the
  rationals are dense, so a half-step witnesses gaps integer steps miss).
- **Brute-tested against membership** (the truth source): over a contract × contract
  sweep with a diverse value pool, every `Proven` has no counterexample in the pool
  and every `Refuted(w)` has `w ∈ ⟦A⟧ \ ⟦B⟧`. This is Part I's "per-pair rules
  brute-tested against the oracle."
- **Two dense-rationals subtleties surfaced** (my test expectations, not the
  checker): over rationals `(10,20] ⊄ [11,20]` (10.5 is the gap), and the
  landing-zone containment needs the interval *meet* (the conjunct-wise or-rule is
  incomplete). Both fixed — the checker was right.
- **Known incompleteness → `Unproven`** (never guessed): `Geo` subcontract rows,
  non-interval intersections/unions beyond the or-rules, and recursion. **Recursive
  contracts (C§9)** are the next layer, built directly on this pair-check as the
  progress-guarded induction (recursive-contracts spec §5).
- **`// [ask-author]`:** none.

---

## 2026-07-20 — RULING [user]: function `==` and analyzer function-equality are ONE truth

A foundational ruling from the author, superseding the μ v0.5 §8 / recursive-
contracts §2 framing where runtime `==` (syntactic, frozen) and analyzer
contract-equality (contract-directed, versioned) are *separate*. For **function
values** they must be a single notion. Recorded here; flagged for the spec author
(the two docs need a small amendment — see below).

### The principle
The whole premise of NEXT is that the contract system prevents runtime bugs. If
the contract system concludes `f == g` while the runtime computes `f != g`, the
contract system has lied about runtime reality at that point — the premise breaks.
So there must be **one** notion of function equality, used both statically
(analyzer) and dynamically (runtime `==`). Not "equal in the contract system but
not at runtime." This is a soundness/consistency requirement, not aesthetics.

### The mechanism (how one truth is realized)
There is a compilation step; canonicalize there.
1. **Compile time:** canonicalize every function to a canonical form.
   Canonicalization includes **both** the syntactic μ-laws (α, reorder, `x+x→2x`,
   μ-binder laws) **and** **contract-directed collapse** — e.g. `0*x → 0` fired
   *only* where the analyzer has proven the precondition (`x: Number`), carrying
   the domain forward so the collapsed form has the same accepted domain.
2. **Intern** functions by that canonical form.
3. **Runtime `==`** is a pointer test on the canonical form — still O(1).
4. The **analyzer** reasons about the *same* canonical form.

Consequence: `(x:Number)=>0*x` and `(x:Number)=>0` collapse to one canonical form
⇒ they are `==` at runtime *and* in the analyzer. One artifact, one truth, no
discrepancy. (No circularity: the analyzer *produces* canonical forms; the runtime
*compares* them. No non-termination: the analysis is bounded, Principle 7.)

### The "syntactic floor + contract-directed rules" model
- The μ §8 syntactic slice is **not** the permanent definition of `==`. It is the
  **floor** — what is provable with *zero* contract information.
- Contract-directed collapses are **additional canonicalization rules** that fire
  when the analyzer proves their preconditions, folding into the *same* canonical
  form.
- `==` therefore **strengthens** as the prover improves (a semantics-version
  event; the language already versions its semantics). Within a compiler version
  it is fixed and deterministic; across versions it moves *closer* to true
  equality — the right direction, and one truth at every version.

### The one hard limit (a boundary, not a discrepancy)
True extensional function equality is **undecidable** (Rice's theorem) — no
procedure decides it for arbitrary functions. So `==`, unified or not, is
necessarily **sound but incomplete**: it may fail to notice some genuinely-equal
pairs, but it never calls distinct functions equal. Crucially, when the two
systems are unified this incompleteness is **shared** — `f == g` (runtime) ⟺
analyzer-proves-`f == g` ⟺ same canonical form, always the same answer. No runtime
bug slips through a spot where the contract system said "equal," because it is
literally the same decision. The gap that remains is the shared floor of
decidability, not a rift between analyzer and runtime.

### Consequences for this implementation
- **`==` is defined architecturally as "canonical-form equality," open to
  contract-directed rules** — *not* "syntactic-only equality." The current code
  already computes `==` on the canonical shape (`equal.rs` / `canon.rs`), so this
  is forward-compatible: today `==` = the syntactic floor (`0*x != 0`, since
  nothing has proven `x: Number`); when the analyzer lands, its proven equalities
  join the canonical form and `==` strengthens, staying one truth.
- This **aligns with the deferred "universal interning" re-architecture** (μ v0.5
  §6): interning functions by canonical form + a pointer-test `==` *is* the
  mechanism above. So that deferred item and this ruling are the same work.
- **Contract-directed collapse requires the analyzer** (domain inference), which
  isn't built yet — so no code change now; the ruling fixes the *definition* and
  the forward path.

### Flagged for the spec author (small amendments)
- **μ §8:** reframe the "frozen syntactic ==-set" as the *floor* of a canonical
  form that contract-directed rules extend (each extension a semantics-version
  event) — rather than a permanently-syntactic `==`.
- **Recursive-contracts §2:** the line *"contract equality is analyzer identity,
  **not** runtime value equality"* reads as a permanent *separation*. For
  **function-value** `==` that separation is the discrepancy being rejected — it
  should read "function `==` is canonical-form equality, computed at compile time,
  shared by analyzer and runtime." (That line may have meant *contract-expression*
  equality — `Range==Range` — which is genuinely analyzer-internal; but for
  function values, unify.)

---

## 2026-07-20 — Reconcile with updated specs (μ v0.5 + recursive-contracts v0.2)

The author replaced the μ spec (v0.1 → **v0.5**, four review rounds) and added
`next-recursive-contracts-specification-v0-2.md` (the C§9 package), and amended
the compendium (B1/B3/B4/C§9/C§11/C§12.3/F1–F3). Reviewed all; made the necessary
fixes. Full suite 164, 0 ignored, clippy clean.

### Fixed now (real conformance bug)
- **Polynomial NF narrowed to the frozen `==`-slice (μ v0.5 §8).** My previous
  poly-NF did full polynomial normalization, which **over-equated**: distribution,
  cancellation (`x−x`), annihilation (`0*x`), and identity-elimination (`x+0`,
  `x*1`) — all now **permanently excluded** because they change divergence and
  operation-safety demands (`(x)=>x−x` demands `x` be a Number and traps
  otherwise; `(x)=>0` does not — so they are *not* the same function). `poly.rs`
  rewritten to the three permitted rewrites only — commutative/associative
  reordering, literal folding (no variable erased), like-term combining where
  every variable survives (`x+x → 2*x`, H-05 kept) — **aborting** (rebuild with
  normalized children, otherwise unrewritten) whenever a rewrite would erase an
  operand or drop a demand. No distribution. Verified: the four excluded
  rewrites now compare `!=` (MU-10), H-05 and reordering/folding still `==`.
- **MU-17** (mixed-aggregate flagships): the record self-reference variant
  `r = { f: () => r }` interns equal like the tuple flagship — already handled by
  algorithm B's bisimulation; added as a test.
- **Docs:** CLAUDE.md now lists six normative docs (μ → v0.5, recursive-contracts
  v0.2 added). μ-v0.1 kept on disk as history.

### Deferred (flagged — not behavioral-correctness bugs)
- **Universal interning restored (μ v0.5 §6 / B1 / F1–F3).** v0.5 *reverses* the
  v0.1 "closures are plain allocations" amendment: closures now intern shallowly
  (acyclic key = (canonical-code pointer, capture pointers); μ-group members at
  window close by group fingerprint), so runtime `==` is a **pointer test** and
  Algorithm B becomes canonicalization-internal. My current runtime `==` uses
  Algorithm B (`values_equal`) directly — which I verified is **observably
  equivalent** (intern-by-(shape,captures) yields the same `==` results). So this
  is a **mechanism/performance** re-architecture, not a behavioral fix; it is
  entangled with the construction-window machinery (§4), so it is deferred and
  logged, not silently skipped.
- **Open-value observation prohibition (μ v0.5 §4 / MU-09 / B4).** An *analyzer*
  compile-error; it does not affect the oracle's runtime for accepted programs.
  The "nominal while open" edge in `equal.rs` is withdrawn by the spec and is now
  dead for accepted programs; it becomes moot under the interning re-architecture.
- **Algorithm A capture routing + capture-space ordering + capture vector
  (μ v0.5 laws 4/8, §5).** My `mu.rs` is the pre-routing core (laws 1/3/5);
  MU-14/15/16 (the makePair code-vs-value distinction, the instantiated
  group-value graph) need capture routing and the instantiated graph — layer-2,
  deferred with the analyzer.

### Newly unblocked (next)
- **Recursive contracts (C§9)** are now fully specified (v0.2) — the C.1
  `[ask-author]`-adjacent deferral. Buildable: admissibility, vector-lfp
  denotation, progress-guarded subcontract, productivity emptiness.

---

## 2026-07-19 — Algorithm A: eager code canonicalization of binding groups (μ spec §4A)

`src/oracle/mu.rs` + `src/oracle/mu/tests.rs` (new). μ-Canonicalization Spec
§2/§3/§4A. 6 MU conformance tests; full suite 153, 0 ignored, clippy clean.

- **What it is:** canonicalizes a set of (mutually) recursive bindings into
  **canonical code** — mutual references become positional μ-refs `⟨d,i⟩`,
  recursion is grouped by SCC, each group serialized in a canonical slot order.
  This is the **layer-2 shape** for C§13.4 cache keys and recursive contracts
  (C§9). **No runtime consumer yet** (layer-1 `==` is algorithm B); `mu.rs` is
  `#![allow(dead_code)]` and exercised only by the MU tests until the analyzer
  lands.
- **Delivered (the testable core):**
  - Tarjan **SCC** over a scope-respecting free-reference graph (binder-aware, so
    a shadowed group name is not an edge).
  - **Laws 1 + 3:** only genuine cycles (a self-loop or ≥2 SCC) become μ-groups;
    acyclic neighbours split out and reference the group by canonical key.
  - **Positional encoding:** intra-group refs → μ-refs, λ/match-bound vars →
    de-Bruijn, cross-SCC refs → canonical key, free names → by name.
  - **Law 5 / canonical slot order:** the lexicographically-least serialization
    over all slot permutations (brute-forced — groups are tiny; O(k!) with k
    small, avoiding a full Paige–Tarjan implementation).
  - **Content-based constant serialization** (not pointer) so canonical codes are
    stable across interners — the cross-program rename/permutation invariant.
  - Conformance: **MU-01** (vacuous-μ erasure — non-recursive binding gets no μ),
    **MU-03** (minimal-group split — acyclic neighbour not bound in), **MU-06**
    (invariance under member renaming and permutation), plus self-recursion → a
    1-slot μ and a distinctness sanity.
- **Deferred (flagged):** **law 2** (adjacent/nested-binder merge — only arises
  with nested groups), **law 4** (bisimulation collapse of truly-symmetric slots
  — law 5 gives permutation-invariance but not slot *merging*; needs partition
  refinement), and **MU-02/MU-05** (the former needs nested groups, the latter
  needs contracts). These are precision refinements for the analyzer, not
  correctness gaps for what exists.
- **`// [ask-author]`:** none. The build-ahead nature was raised with the user and
  accepted before implementation.

---

## 2026-07-19 — Polynomial NF over arithmetic bodies (frozen ==-set, H-05)

`src/oracle/poly.rs` (new), `src/oracle/{canon.rs,eval.rs,mod.rs}`, `src/value.rs`.
μ-Canonicalization Spec §6. 3 new poly seeds; full suite 147, 0 ignored, clippy
clean. Closes the last observable gap in the frozen `==`-determining set.

- **Delivered:** shape canonicalization now puts arithmetic subterms into
  polynomial normal form, so algebraically-equal bodies share a shape and compare
  `==`: `x+x == 2*x` (H-05), constant folding, commutativity, `x-x == 0`,
  distribution, `x*x == x**2`, multivariate commute.
- **Representation:** a polynomial is `monomial → rational coefficient`; a monomial
  is `atom-key → exponent`. Atoms (variables) are non-arithmetic subterms,
  serialized canonically (so equal atoms unify) and normalized recursively;
  handled operators are `+ - *`, unary `-`, division by a **nonzero constant**, and
  a **nonnegative integer constant** power. Reconstruction emits a deterministic
  canonical `Expr` (monomials and factors in serialized order).
- **Soundness — only total exact-rational identities are used:** `x/x`, `x % y`,
  `x/0`, and variable / negative / non-integer powers are **left as atoms**, never
  simplified — so a partial op is never equated with a total one. Verified: `x/x`
  ≠ `1`, `x % x` ≠ `0`, `x` ≠ `x+1` all stay distinct; and NF-equal functions are
  shown to compute the same value. Evaluation is untouched (shapes drive identity
  only; closures run their original body).
- **Known incompleteness (conservative, flagged):** poly-NF can *eliminate a
  capture* (e.g. `(a) => k - k` ⇒ `0`), leaving a vacuous entry in `free_vars`
  that `==` still compares — so two such constant functions with different `k`
  compare unequal (a sound false negative). Closing it needs a capture
  prune/renumber pass after NF (analogous to μ-law 1's "no vacuous binder"); left
  as a follow-up since real code rarely hits it.
- **Frozen `==`-set status:** positional α-conversion ✓, μ-laws' observable effect
  via algorithm B ✓, polynomial NF ✓ — the `==`-determining set is now
  observationally complete (modulo the capture edge above). Amending the set is a
  semantics-version event (spec §6).
- **`// [ask-author]`:** none.

---

## 2026-07-19 — μ-canonicalization: value identity via bisimulation (the spec landed)

`next-mu-canonicalization-specification-v0-1.md` (new normative doc, author-
provided), `src/oracle/{canon.rs,equal.rs}`, `src/value.rs`, `src/oracle/{mod.rs,
eval.rs}`. **All ignored seeds now green — 144 tests, 0 ignored, clippy clean.**
This closes the μ half deferred earlier and *re-architects* the previous entry.

- **The ruling (author):** open-value identity = **shape**, via strict openness;
  bisimulation collapse embraced; locations nominal (fork-13 split). The prior
  three open questions are all answered by the spec.
- **Architecture correction:** the previous "de-Bruijn half" interned functions by
  a canonical *key with captures inlined*, bailing to opaque on recursion. The
  spec's arrangement (interning amendment) is different and is what I now
  implement:
  - **Closures are plain allocations, never hash-consed** — `FnValue` has pointer
    identity, so the interner treats functions (and structures containing them) as
    distinct allocations.
  - **Code shape is canonicalized (algorithm A, α + capture-slot layer, `canon.rs`):**
    bound vars → positional `$k`, free vars → capture slots `@cap`i (names kept in
    `free_vars`, resolved lazily). Captures are *not* inlined; the shape is finite,
    so shape identity is structural.
  - **Runtime `==` is algorithm B (`equal.rs`):** bisimulation over value graphs
    with a visited-pair set; a revisited pair is assumed equal (the coinductive
    step). Data `==` stays a pointer test (fast path); only function-containing
    comparisons walk. Locations compare nominally (same slot ⇒ equal); the
    open-value edge (§4C) compares an unresolved capture by name.
- **Seeds flipped:** `y=[()=>y] == z=[()=>z]` (self-ref), `a==b==y` (law-4 collapse
  at the value level, via the memo — no code μ-minimization needed for layer 1),
  mutual-recursion group equality, MU-04 (location nominality), MU-08
  (isEven/isOdd distinct), plus α-equivalence and capture-by-value. MU-07 ships:
  algorithm B is cross-checked against a bounded naive unfolding.
- **Deferred (layer 2 / analyzer, gated):** algorithm A's *full* μ-binder
  minimization — SCC grouping, Paige–Tarjan partition refinement, laws 1–5,
  canonical slot order — produces the interned canonical *code* used by C§13.4
  cache keys and recursive contracts (C§9). Layer-1 `==` does not need it (B's
  coinductive bisimulation already collapses symmetric recursion), so it lands
  with the contract phase. Also deferred: **polynomial NF** over arithmetic bodies
  (the frozen set's H-05 item, `x => x + x == x => 2 * x`) — a distinct shape
  normalization, not yet implemented.
- **Frozen `==` set (spec §6) noted:** amending it is a semantics-version event.
- **`// [ask-author]`:** none.

---

## 2026-07-19 — §5 canonical function identity (de-Bruijn half) [superseded by the μ-canonicalization entry above]

`src/oracle/canon.rs` (new), `src/value.rs`, `src/oracle/` (mod.rs, eval.rs).
Kernel AST §5. 5 new identity seeds green; the `((x)=>x)==((y)=>y)` seed
un-ignored; full suite 137 (+1 ignored); clippy clean. First slice of the §5 work
we deferred (with the author's sign-off).

- **Delivered:** function-value identity is now **canonical**, not pointer-based.
  `make_closure` computes a `FnKey`:
  - `Canonical(Lambda)` — the body with bound variables α-renamed to positional
    canonical names (`$0`, `$1`, …) and free variables replaced by the constant
    they captured (an immutable value) or a location marker (a Box slot —
    location identity participates in function identity, B1). Structurally-
    identical functions with equal captures now compare `==`.
  - `Opaque(u64)` — when a free variable is not yet resolvable (self/mutual
    recursion under initialization: the μ case), canonicalization **bails** and
    the closure gets a unique id (distinctness). Always sound: it can only fail to
    merge, never wrongly merge.
- **Value layer:** `ClosureRef` → `FnValue { closure, key }`; `==`/hash are by
  `key` only. Evaluation still walks the original body against the captured env
  (unchanged eval path), so late binding / mutual recursion are unaffected.
- **Seeds now green:** α-equivalence (incl. multi-param and nested lambdas),
  capture-by-value equality and inequality, identity through structures
  (`[(x)=>x] == [(y)=>y]`), and self-equality of recursive (opaque) functions.
- **Still deferred (μ half):** the §7 group-identity pair (`y = [() => y]` /
  `z = [() => z]`) — their bodies self-reference, so they canonicalize to opaque
  and stay `#[ignore]`d. Closing it needs μ-markers (rational-tree comparison),
  which the compendium marks `[owed]`.
- **Chosen — per-oracle opaque counter:** reset to 0 per `Oracle`, so a program
  and its normalization assign matching opaque ids (keeps the `eval ∘ normalize`
  harness consistent for recursive-function-valued programs). Correct because
  canonical dedup only fires on equal captures, and the harness compares
  structurally-equivalent programs.
- **`// [ask-author]`:** none.

---

## 2026-07-19 — Build-order step 4: normalization + property harness — **BUILD ORDER COMPLETE (the gate)**

`src/normalize/` (mod.rs, tests.rs). Kernel AST §5 + Part I harness laws. 5
normalize tests green (incl. the property harness over a 22-program corpus); full
suite 132 (+2 ignored); clippy clean.

- **Mandated (Part I), the deliverable:** the property harness enforces, against
  the oracle, `eval ∘ normalize = eval` and idempotence
  (`normalize(normalize(m)) == normalize(m)`) over a corpus spanning every node
  kind. This is the machine-checked link between the normalizer and the truth
  source.
- **Chosen — active rule set (small, spec-named, clearly eval-preserving):**
  - Template **adjacent-segment folding** (§4).
  - **Literal template → constant**: a template with no interpolations is the
    string it denotes.
  Everything else is a structure-preserving recursive map, so further rules bolt
  on in one place.
- **Deferred (consistent with the §5 sign-off):** the heavy §5 canonicalization —
  de-Bruijn free-variable ordering and μ-binder canonicalization — is *not* built
  here; it lands with canonical function identity. The harness is designed so
  those rules, once added, are checked by the same `eval ∘ normalize = eval` law.
- **Chosen — outcome comparison:** the harness runs original and normalized forms
  in the *same interner*, so produced values compare by pointer and traps by
  class (`Result<ValueRef, TrapClass>`), giving an exact "same outcome" check.
- **`// [ask-author]`:** none.

### Build-order status: **gate reached.**
Steps 1–4 (value layer → lexer/parser/desugar → oracle → normalization + harness)
are complete and green. Per Part I we **stop here**: contracts / the three-valued
checker / demand core / recursion analysis are the explicitly-gated later phase,
not to be started until the author opens it. Outstanding within the completed
scope: the two `#[ignore]`d §5 function-identity seeds, and the small B6 tail
already noted (all logged).

---

## 2026-07-19 — Build-order step 3 (part 3): B6 effect harness — **oracle complete**

`src/value.rs`, `src/interner.rs`, `src/oracle/` (harness.rs new; eval.rs,
mtch.rs). Semantics companion §4 + B6. 6 effect seeds green; full suite 126
(+2 ignored); clippy clean. **This completes build-order step 3 — the oracle.**

- **Mandated (§4/B6), implemented and tested:**
  - New value kind `ValueData::Native` (pointer-identity `NativeRef`): a
    host-callable that runs Rust when applied — the only way host effects (which
    aren't expressible in NEXT) can exist. `eval_apply` dispatches native-vs-
    closure; natives honour the world admission matrix (effect-kind ⇒ effect world
    only).
  - Host-effect doubles injected by the harness: `println`/`exit` (record into an
    observable `HostIo` buffer) and a fallible `readFile` (returns a Failure).
  - `Failure` is the one prelude Record shape (`path` + `reason`); the `Failure`
    contract pattern matches it structurally (E9 — Failure discharge dissolves
    into contract-as-pattern). A failed effect returns a Failure that flows as
    ordinary data — nothing unwinds.
  - **`then`/`catch` proven to be NEXT library code:** the seed defines them in
    NEXT source (over `Match`) and shows a success flowing through `then` while a
    Failure short-circuits it and is recovered by `catch` — no interpreter
    builtins.
- **Chosen — entry programs need not end in a value:** `run_module_in` now returns
  null when the last statement completes without a value (an entry may end in an
  effect statement), rather than trapping. The expecting-seat demand still fires
  in genuine value positions (bindings, operands, …), which the seeds check.
- **Chosen — line-leading `[`/`(` starts a new statement** (parser): a postfix
  index/call only attaches on the same line as its target; a `[`/`(` opening a
  fresh line begins a new statement (the greedy-continuation hazard, §1.1). `.` /
  `?.` still continue across lines (unambiguous). This is the same class of fix as
  the arrow `=>` line rule.
- **`// [ask-author]`:** none. `exit` as a double records the code and returns
  rather than terminating (the real host limit is outside the semantics, §4).

---

## 2026-07-18 — Build-order step 3 (part 2): worlds + mutator staging

`src/oracle/` (mod.rs, eval.rs). Semantics companion §3 (Apply/Write) + §5
staging theorems. 6 new mutation seeds green; full suite 118 (+2 ignored);
clippy clean. Covers task 3c.

- **Mandated (§3), implemented and tested:**
  - `Write` legal only in mutator world (else `world-admission` trap); stages into
    the pending set π.
  - Slot reads use **read-your-writes** (π if staged, else σ).
  - Mutator application: from mutator world **join** the current transaction (same
    π, no publish); from effect world **begin** (π := ∅), run, and **publish** at
    completion. Mutator Apply outcome is `CompletedWithoutValue` (return-nothing
    law).
  - **Publish** commits only staged slots whose value differs by pointer (the
    interning-exact equality guard, B7/G1); a trap publishes nothing (§5).
  - Effect application runs the body in effect world; the world admission matrix
    (pure→{pure}; mutator→{pure,mutator}; effect→all) is enforced with
    `world-admission` traps on violation.
- **Chosen — commit counter on the store:** the equality guard's "fires nothing"
  is otherwise unobservable without the (fenced) reactive layer, so `Store` counts
  *actual* commits and a `run_program_commits` test helper asserts an equal write
  commits zero times. Test-only observability; no semantic effect.
- **Chosen — "invisible until outermost completion" is tested via join
  accumulation:** in the sequential oracle, σ is only inspectable post-transaction,
  so the nested-join seed asserts the accumulated result (inner write visible to
  outer read via shared π, single publish) rather than mid-transaction σ.
- **Deferred to a small follow-on (B6 effect harness):** host effects (test
  doubles for `println`/`exit`), `Failure` records as plain data, and the
  `then`/`catch` prelude functions. These need a native-callable value kind; the
  mutation core (the delicate part) and effect-world mutator invocation are done.
- **`// [ask-author]`:** none.

---

## 2026-07-18 — Build-order step 3 (part 1): pure oracle core + Match

`src/env.rs`, `src/oracle/` (`mod.rs`, `eval.rs`, `mtch.rs`, `tests.rs`).
Semantics companion §3, the pure fragment. 29 oracle seeds green; full suite 112;
clippy clean. Covers tasks 3a + 3b.

- **Mandated (§3), implemented and tested:** exact rational arithmetic; total
  division (`x/0` ⇒ Indeterminate) with left-most Indeterminate propagation
  through arithmetic; `==`/`!=` as pointer equality (Indeterminate is an ordinary
  value); ordering comparisons trap `undischarged-Indeterminate`; late binding via
  a runtime environment (direct + mutual recursion work); `Match` as the sole
  control node with the completion triple; construction (tuple/record, later-wins,
  spreads); access (field/index/slice, demand vs `?.` totals, from-end,
  clamped-total slices); grapheme string index/slice (pinned `unicode-segmentation`);
  template stringification by B2 rules. Nine trap classes fire end-to-end.
- **Chosen — runtime environment (not §5 resolution):** `Scope` chain with names;
  a binding is marked `UnderInit` while its RHS evaluates, so `x = x` traps
  `unbound-evaluation` while a self/mutually-recursive lambda is fine (its body
  isn't evaluated at bind time). This is the agreed approach (see the §5 deferral
  entry below).
- **Chosen — closures capture the environment by reference** (`Rc<Scope>`), which
  is what makes late binding / mutual recursion fall out. Function identity is
  `ClosureRef` pointer identity (the conservative approximation already signed
  off).
- **Chosen, spec-faithful clarifications:**
  - `tested-seat` trap is **guard-only** (companion §3). A non-Boolean *ternary
    condition* desugars to a Boolean-exhaustive match, matches no arm at runtime,
    and surfaces as `expecting-seat` (the analyzer rejects it up front). Both are
    tested.
  - Contract-as-pattern: the runtime-decidable **Kind** checks (`Number`,
    `String`, `Boolean`, `Null`, `Tuple`, `Record`, `Function`) and
    `Indeterminate` are implemented; user-defined contract patterns trap (they
    need the contract engine — analyzer phase).
  - `%` on rationals is the truncation-toward-zero remainder; `**` supports
    **integer exponents only** (irrational-producing ops are omitted from the PoC,
    B2) — a non-integer exponent traps `operation-safety`.
  - Entry-file top level evaluates in **effect world** (the one derivation the
    companion makes, §2).
- **Deferred to step 3c (part 2):** mutator/effect *application* (worlds admission
  is checked, but a mutator/effect call currently traps a placeholder), `Write`
  evaluation, the pending-set/read-your-writes/publish staging, host effects, and
  Failure records. `DidNotComplete` (divergence) is genuine non-termination, not a
  represented value.
- **`// [ask-author]`:** none.

---

## 2026-07-18 — Decision [user-approved]: defer §5 canonicalization; approximate function identity

Sign-off recorded before starting the oracle (step 3). **What the oracle does:**
evaluates kernel AST by resolving names against a runtime environment (late
binding, B4 / semantics §1 `ρ`) — no de-Bruijn/§5 canonicalization pass is built
yet. **What that costs, in full (nothing else):**

- Function-value identity is *approximate*. Same-meaning functions with different
  written shape (α-equivalent, or equivalent-but-differently-written bodies) may
  intern distinct instead of equal. This propagates to values that *contain*
  functions; pure data (numbers/strings/tuples/records of data) stays exact.
- Observably, only `==` on functions (and function-containing structures) is
  affected. The approximation is **conservative**: it can only *fail to merge two
  equal functions*, never merge two different ones — so no wrong `true`, and no
  effect on any produced non-function value, control flow, world/mutation
  semantics, trap, or completion outcome. Soundness is untouched.
- The `y = [() => y]` / `z = [() => z]` interning seed and the §7 group-identity
  pair stay `#[ignore]`d with a note pointing here, until §5 lands.
- Function-value interning is confined to one place (a `ClosureRef` pointer
  identity for now); swapping in §5's canonical-body key later is a localized
  change and does not touch the oracle's evaluation logic.

**User: "consider it settled."**

---

## 2026-07-18 — Build-order step 2c: desugar to kernel AST

`src/desugar/` (`mod.rs`, `hask.rs`, `tests.rs`). Kernel AST spec §4 (the closed
catalog) + E10. 27 desugar-equivalence seeds green; full suite 83; clippy clean.
**This completes build-order step 2.**

- **Mandated (§4 rows), all implemented and tested:** pipes → `Apply`;
  `? :`/`&&`/`||`/`!` → `Match`; `??` → null-arm `Match` (scrutinee once); `~a||b`
  / `~a&&b` → falsy-set selection matches; `!~x` → falsy Boolean match; hasks →
  `Lambda` over holes; alternation → arm expansion; pins → equality guard; block
  bodies → scrutinee-less `Match`; compound/path mutation → `Write` of a
  functional update; arrows → pure `Lambda` over the argument-tuple pattern (the
  arity model). The `?? vs ~||` false distinction is verified structurally (2 arms
  vs 3).
- **Chosen — output is *pre-canonicalization* kernel AST:** `Ref`s carry
  `BindingRef::Name` and `Write` carries `SlotRef::Name` (added this step). Name →
  positional/location/μ resolution and de-Bruijn canonicalization are §5/analyzer
  work, deliberately not done here — desugar is purely syntactic.
- **Chosen — synthetic names use a `%` prefix** (e.g. `%h0`, `%pin1`, `%hrest0`),
  which no surface identifier can contain (identifiers are `_`/`$`-free
  alphanumerics), so generated bindings never collide with user names.
- **Chosen — hask holes collected on the fly** via a scope stack rather than a
  separate rewrite pass: a `#` pushes a scope, holes register synthetic params,
  popping builds the parameter tuple. Nested `#` opens a fresh scope (E4). v0.1
  supports all-anon, all-indexed, and single-rest shapes.
- **Deferred with a clear `DesugarError` (not silently guessed):** mixing plain
  `_` and indexed `_n` holes; index/slice *mutation* targets (field-path updates
  are done); nested pins and nested alternation; `@computed`/`@reactive` and
  anonymous `@` forms (the fenced reactive layer, G1). Each returns a specific
  error message. These are the honest v0.1 boundaries; none is a semantic
  invention.
- **`// [ask-author]`:** none. Every deferral is either a fenced subsystem or a
  syntactic corner that errors cleanly rather than guessing.

---

## 2026-07-18 — Build-order step 2b: surface parser

`src/parse/` (`surface.rs`, `parser.rs`, `mod.rs`, `tests.rs`). Grammar §§2–5.
30 seed tests green (E2 worked parses + §10); full suite 56; clippy clean.

- **Chosen — two-stage pipeline (surface AST then desugar):** the parser emits a
  faithful *surface* AST that keeps all sugar; lowering to the kernel form is a
  separate pass (2c). The kernel spec calls the desugar catalog "closed and
  normative", so keeping it a standalone, separately-tested pass is the right
  seam. The analyzer still never sees sugar.
- **Mandated (§3 ladder):** full precedence ladder as recursive descent, with the
  settled associativities — pipes `|>` left / `<|` right with the **unparenthesized
  mixing ban** (parse error); `**` right-assoc admitting unary on the right
  (`-x ** 2 ≡ -(x ** 2)`, `2 ** -3` legal); ternary right-assoc; `??`/`||` shared
  tier; unary `-`/`!`/`~` stacking. Hasks as loose prefix (tier 4) with the
  grouped `#(...)` primary for below-tier positions.
- **Mandated (§8):** brace rule (record vs block by first token) applied at arrow
  bodies, with the `@`-arrow forced-Block exception threaded via a parser flag.
  `x => {}` is the empty record.
- **Chosen — statement separation by greedy termination, not line pre-splitting:**
  the parser consumes each statement as far as the grammar allows (the documented
  greedy-continuation behavior), then the next statement begins naturally. Strict
  L1/L2 line *enforcement* (rejecting two statements on one line) is deferred to a
  later diagnostic pass; token lines are preserved for it.
- **Chosen — arrow `=>` must be on the same line as its params.** This is the one
  place L2 is load-bearing for *correctness*, not just diagnostics: without it,
  `x = n` ⏎ `=> x` inside a block greedily reads `n => x` as an arrow and swallows
  the else-arm exit. Requiring the `=>` to sit with its params (bare ident, or the
  matching `)`) resolves it. A `=>` opening a fresh line is a block-body arm.
  Flag: this rejects the unusual `(a, b)` ⏎ `=> body` split-arrow; confirm that's
  acceptable.
- **Chosen — binding/mutation/expression disambiguation** via the statement-only
  operators `=` and `:=`/compounds (which never appear in the expression grammar):
  try a bind target then `=`; else a path then a mutation op; else an expression.
  Save/restore on the token index makes the attempts cheap.
- **Chosen — contextual keywords** (`module`/`import`/`export`/`from`/`when`/
  `where`) committed by seat shape; `import` in particular only commits when a `{`
  or a name follows. A variable literally named after a contextual word in an
  ambiguous head position is a known unsupported edge — flag if it matters.
- **Chosen — pattern classification at parse time (§4/§8):** `true`/`false`/`null`
  → prelude-constant patterns; capitalized identifier → contract pattern; else a
  fresh binding. Alternation `|` and pins `^` parsed structurally (they desugar in
  2c).
- **`// [ask-author]`:** none blocking. The two "flag" items (split-arrow across
  lines; contextual-word-as-variable in head position) are the only confirmations.

---

## 2026-07-17 — Build-order step 2a: lexer

`src/lex/` (`token.rs`, `lexer.rs`, `tests.rs`). Grammar spec §1. 14 seed tests
green; full suite 27; clippy clean.

- **Mandated (§1.4 / §4 desugar):** literals resolved at lex time — `Number`
  carries an exact `Rational`, `Str` carries UTF-16, escapes processed. Numeric
  bans implemented: no BigInt `n` suffix, no legacy octal / leading zeros, no
  trailing-dot. Bases `0x`/`0o`/`0b`, exponents, `_` separators.
- **Mandated (§1.1):** no newline tokens; each token records its line so the
  parser can enforce L1/L2. Maximal munch with T1 (`?.` not before a digit — the
  `a ?.5 : b` seed), T2 (`...` beats `.`), T3 (compound mutation ops are single
  tokens).
- **Chosen — leading-dot number disambiguation:** `.5` is a number unless the
  previous token can end a postfix target (ident/`)`/`]`/`}`/number/string/
  hole), in which case `.` is member access. Tracks one token of history.
- **Chosen — trailing-dot ban scope:** `5.` erroring is required; refined so
  `5.foo` lexes as `5 . foo` (member access) and only a *dangling* dot (before
  whitespace/operator/EOF) errors. Numbers having no fields is left to the
  analyzer, not pre-judged by the lexer. Flag if the author wants `5.<ident>` to
  also be a lexical error.
- **Chosen — templates:** interpolations are captured as *pre-lexed* token
  sub-streams (`TemplateElem::Interp(Vec<Token>)`); the parser parses each as an
  Expression. Brace-depth is handled by reusing the main token loop (nested
  string/record braces are consumed as whole tokens, so a `}` inside a nested
  literal never closes the interpolation).
- **Chosen — string escape set:** the JS-standard set (`\n \t \r \0 \b \f \v \\
  \" \'`), `\xHH`, `\uXXXX` (one UTF-16 unit, surrogate halves allowed), `\u{…}`
  (astral → surrogate pair); templates add `` \` `` and `\${`. Matches §1.5's
  "JS standard set plus `\u{…}`".
- **Chosen — identifier classes:** std `is_alphabetic`/`is_alphanumeric` as an
  approximation of Unicode XID_Start/XID_Continue, excluding `_` and `$` per
  §1.3 (so `_`-holes and `$`-interpolation never collide). A `unicode-ident`
  dependency would make this exact; deferred as not worth a dep at v0.1. Flag if
  strict XID conformance is wanted.
- **Minor — `_0`:** grammar says indexed holes are `_n`, n ≥ 1. `_0` currently
  lexes as `IndexedHole(0)`; rejecting n = 0 is left to the parser/analyzer.
- **`// [ask-author]`:** none blocking. The two "flag if…" items above (strict
  XID; `5.<ident>` strictness) are the only choices worth a confirmation.

---

## 2026-07-17 — Build-order step 1: repo + value layer

### Preconditions
- All four normative documents present and read: design compendium v1.0,
  grammar spec v0.1 (added by the author this session), kernel AST spec v0.1,
  semantics companion v0.1. The grammar spec was initially missing; once added,
  its own closing line ("`cargo init` is ungated") plus Part I §365 confirmed the
  gate is open.
- **Chosen — toolchain:** no Rust was installed on the machine. Installed via
  `rustup` (author-approved) → stable `1.97.1`. Pinned in `rust-toolchain.toml`
  for reproducible conformance runs (the oracle is the truth source).

### Dependencies (Cargo.toml)
- **Mandated (Part I step-0):** `num-rational` `BigRational`; fixed-precision
  decimal crates rejected. Added `num-bigint`, `num-integer`, `num-traits`.
- **Chosen — `num-bigint = "0.4"`:** `cargo add` first resolved 0.5.1, which put
  *two* `BigInt` types in the tree (0.5 direct vs the 0.4 that `num-rational`'s
  `BigRational = Ratio<BigInt>` uses). Pinned our direct dep to 0.4 so there is
  one `BigInt`. Not a semantic decision; a tree-hygiene fix.
- **Mandated + Chosen — `unicode-segmentation = "=1.13.3"`:** grapheme ops must
  pin the Unicode table version (CLAUDE.md step 3 / semantics §3 E8). Pinned
  *exactly*. Not yet used (grapheme string ops are step 3); declared now so the
  version is fixed from the start.

### Value layer (`src/rational.rs`, `src/value.rs`, `src/interner.rs`)
- **Mandated (B1):** immutable, eagerly interned values; `==` is pointer
  comparison for every type; locations are not values.
  - **Chosen — hash-consing representation:** `ValueRef = Rc<ValueData>` with
    pointer-based `Hash`/`Eq`; `ValueData` derives structural `Hash`/`Eq`. Because
    children are already canonical, comparing children by pointer *is* structural
    comparison, so the derived key is exact. The interner is
    `HashMap<ValueData, ValueRef>`. This is a standard hash-cons; the compendium
    names the semantics (pointer equality), not the mechanism.
- **Mandated (B2):** exact rationals; decimal-iff-terminating printing. B2's
  printing predicate ("reduced denominator's primes ⊆ {2,5}") implemented exactly
  via `power_of_ten_factors`; scaling to `10^max(twos,fives)` yields no spurious
  trailing zeros (proof sketch in code comment). Flagship seed `0.1+0.2==0.3`
  green.
  - **Chosen — integer rendering:** an integer rational (`denom == 1`) prints with
    no decimal point (`3`, not `3.0`). B2 gives round-trip examples for fractions
    but is silent on the integer spelling; `3` is the natural canonical form and
    the grammar bans the trailing-dot `3.` form anyway. Low-risk; flag if the
    print doctrine later says otherwise.
  - **Chosen — `Rational::from_decimal` helper:** a value-layer convenience/B2
    demonstrator (handles sign, leading-dot, exponent, `_` separators). The lexer
    (step 2) owns *real* literal diagnostics; this is not that.
- **Mandated (semantics §1):** value kinds Boolean, Null, Number, String (UTF-16
  storage), Tuple, Record, Function, Indeterminate(form). All present.
  - **Chosen — record canonical form:** fields stored sorted by UTF-16 key, keys
    unique. Record field order is not observable (structural `==`), so `{a,b}` and
    `{b,a}` intern equal. Construction applies later-wins on duplicate keys (E5
    RecordCons); literal-literal duplicate rejection is an upstream (parser)
    concern, not enforced here.
  - **Chosen — `Indeterminate` forms:** modeled the two the semantics names
    (`_/0`, `0/0`) as an enum. Interned like any value (§3: a plain value, not a
    trap).
  - **Deferred — `FunctionValue` captures:** type defined as `(lambda, capture
    map)` with captures = value / μ-marker / location per semantics §1, but left
    empty; function *construction* and capture resolution are the oracle's job
    (step 3). Consequently the `y = [() => y]` / `z = [() => z]` interning seed is
    **deferred to step 3** — it needs μ-markers and evaluation, which do not exist
    yet. Recorded so the seed is not forgotten.

### Kernel AST (`src/ast.rs`)
- **Mandated (kernel AST spec §§1–3):** full node inventory — expressions,
  declarations/module structure, patterns — with **no source spans** (B4 side
  table) and every node deriving `Hash`/`Eq` so kernel forms intern (§5). Types
  only this pass; no evaluation, no desugaring, no canonicalization yet.
  - **Chosen — `BindingRef { Name | Positional }`:** the spec says canonical
    bodies replace immutable-binding names with positional (de-Bruijn) refs (§5),
    but the parser emits names first. Modeled both lifecycle forms in one enum;
    the normalizer (§5) will rewrite `Name → Positional`. Faithful to the spec's
    stated canonicalization, not an invented representation.
  - **Chosen — pattern rests encoded inline** as `PatElem`/`PatField` variants
    (rather than a separate `rest?` field) so a tuple's *middle* rest keeps its
    position. The "one rest per level" invariant is an analyzer/parser check, not
    a type-level constraint.
  - **Followed — extension points omitted:** reactive-fence act kinds
    (`@reactive`, `@computed`) and other §7 parked forms are deliberately absent;
    `ActKind` is `{Pure, Mutator, Effect}` only.

### Open items carried forward (implement as stated; do not resolve)
- Mutator returns = return-nothing (current law); returns-leaning is an extension
  point.
- Open-value group identity: strict-openness-with-statement-group-windows
  (semantics §7) — to be isolated behind one module when the oracle lands.
- Module in a value seat: unimplemented → clear error (later).
- Template interpolation of non-printable structures: trap (later).

### `// [ask-author]`
None this pass. No unavoidable judgment calls beyond the tagged representation
choices above, all of which the specs already sanction.

### State
`cargo test` green (13 tests): exactness flagship, B2 printing (terminating /
non-terminating / integer / negative / round-trip), interning pointer-equality
(leaves, nested tuples, record order-independence, later-wins). `cargo clippy`
clean.

## 2026-07-31 — Completion routing through the settled fact (step 1 of the critical path)

**Chosen (mine, within the ruled boundaries).** `analyze_apply` now takes a call's completion
from the settled completion fact rather than from the coarse body pass. `Produces` is
reachable *only* from a proven fact. When the fact does not prove completion, the honest
third voice `MayFallThrough` is reported — except that a **proven** fall-through survives:
`classify_remainder` mints one only with a sampled witness and no guard muddying the
remainder, and a witness is a refutation, not a shrug.

**Bug found and fixed (mine, introduced with the graph unification).** `safety::settle`'s
not-settled fallback re-verified the seed through the *safety* check regardless of the
claim. A `Completes` claim therefore reported `Proven` whenever the body merely raised no
safety finding — a different question with a wrong answer, and a live false accept.
A `Completes`/`Return` claim that does not settle is now `Unproven`, full stop.

**Blocker 3 — half released, re-pinned to its real root.** The cycle assumption no longer
asserts `Produces`. The remaining half is not a local patch: `analyze_match` derives its
completion from scrutinee coverage alone and discards the arm result's, because it demands
every arm result unconditionally. Compendium §309 makes arm-results *expecting* seats only
when the match is itself at one, and `analyze` carries no seat. That is compendium 1.0.8
verbatim — an AnalysisContract alone cannot separate equal `produced` from differing
completion behaviour — so the fix is the completion tri-state riding on the outcome and
demanded by the **consumer**, i.e. gated on F1 `OperationOutcome` (T1.2). Propagating arm
completion unconditionally is explicitly rejected: it over-reports at statement seats
(it broke `countDown` when tried, and was backed out).

No widening, no reaching fixpoint, no candidate synthesis, no grounding cutoff was added.
384 lib + 111 conformance green, clippy clean.

## 2026-08-01 — T1.1 program entry + T1.2 demand core (first increment)

**T1.1 — `analyzer::program::analyze_program`.** The analyzer had no top; `main.rs` only ran
the oracle, so every analyzer path was reachable solely from unit tests. Each `where` is now
verified as `BodySafe(instance, DeclaredInput)` (E11/E-8). Analysis never evaluates the
module — closures are built via `make_closure_in` (extracted from `Oracle::make_closure`, not
duplicated), which forces no binding. `next --check <file>` is the CLI consumer.

**Two spec clauses I had backwards, corrected by reading C§13.1 rather than my plan doc.**
My `NEXT-completion-plan.md` T1.2 entry said "eager preimage as the **primary** mechanism"
and "a demand reaches the parameter origin and is **adjudicated there**". C§13.1 says the
opposite on both: demands propagate backward *untransformed as subscriptions*, resolution is
*forward* through the operation rules, adjudication happens *where the demand was asked*, and
eager preimage is explicitly *an optimization*. The implementation follows the compendium.
The plan doc is a maintainer file and stays as written; this record is the correction.

**"No stall concept" is what makes the module safe by construction.** A demand is never
parked awaiting more information — there is no state meaning "come back when you know more".
So the slide this step was flagged for (unadjudicated demand → accumulate per-path info →
join → widen over loops) has nowhere to accumulate. Unproven is terminal for the compilation.

**One graph, three claims.** `safety::prove_claim` is now claim-general: discovery is a
property of the body, not of the question asked about it, so Safety, Completes and Return are
three questions over the *same* C§13.2a fact graph. This is unification, not a fourth path.

**Found: the return claim was not walking the region table.** Safety verifies per §5 row, so
it sees `n ≠ 0` in the else branch; the return claim analyzed the body whole, so `n` still
admitted `0`, `n − 1` reached `−1`, no assumed fact covered the recursive call, and
`countDown where (…) => Number` failed on a body that plainly satisfies it. C§13.2's
region-table walk contract-evaluates the *result expressions of the selected rows* — so the
partition applies to the return too. `safety::produced_by_partition` mirrors
`verify_by_partition`; `run_pass`'s `Return` arm uses it, falling back to the whole-body
summary where the partition does not apply (single plain parameter only — §5 multi-parameter
stays owed). No new machinery: the same partition, asked a second question.

**A failed return claim is unproven, never refuted.** Failing to show `produced ⊑ required`
is not showing `produced ⊄ required`; refutation needs a realized witness (C§13.2a), which
this pass does not mint. Unproven still rejects, per the safety-unproven discipline.

396 lib + 111 conformance + 4 gate green, clippy clean. No pinned blocker flipped — they
remain gated on T1.4, and were re-checked rather than assumed.

## 2026-08-01 — T1.4 attempted and reverted: the wiring needs a per-node in-progress key

The swap of `analyze_apply` off `bodycheck::body_summary` onto the settled facts was
attempted and reverted whole. The inputs were all present this time — `safety::prove`,
`safety::completes`, and a partition-based `body_outcome` for `produced` — so the earlier
blocker (no fact source for `produced`) was genuinely gone.

**What actually blocks it.** A settlement analyzes bodies; those bodies' calls reach
`analyze_apply`, which would launch nested settlements. I guarded that with the existing
global `SETTLING` boolean, which is **unsound at that granularity**: during any settlement
every nested `prove` is answered from the hypotheses, including for callees that are not
members of the graph and hold no hypothesis. Those returned `Unproven(vec![])`, dropping
real transitive traps. Ten lib tests failed; the one that matters is
`mutual_recursion_closes_via_the_joint_vector_pass`, which reported **Proven where it must
refute** — a false accept.

**The fix is not a better boolean.** The in-progress key must be the fact node
`(instance, I)` so that a graph member resolves through its hypothesis (correct vector
induction) while a non-member is actually verified. That is C§13.4's proven-fact cache; the
quarantined `bodycheck` carried a weaker per-callee form of it in its `ACTIVE` stack, which
is why the old path surfaced transitive traps and the new one did not.

**Ordering correction:** C§13.4's fact cache moves *before* T1.4. Canonicalization lands
with that cache, since it is the cache key's consumer — so the two travel together, earlier
than planned.

**Nothing was kept.** `body_outcome` was green and reverted with the rest: unused machinery
ahead of its consumer is the pattern this project is recovering from, and keeping it
"because it works" is how the last one got in.

Also corrected: I called the first failed run a hang and theorized an exponential blowup
from per-call-site settlement. It was neither — the suite completes in ~5s. The first
command timed out during compilation, not execution. The measurement, not the theory, was
right.

## 2026-08-01 — C§13.4 proven-fact cache landed; T1.4 retried on it and still deferred

**The cache (kept, green).** `analyzer::factcache` keys facts by the **fact node** —
`(canonical shape + de-Bruijn-ordered capture contracts, row-set I, claim)` — per C§13.4,
replacing the unsound global "am I settling?" flag. A re-entrant query on *the same* node is
a recursive reference and resolves through its hypothesis (C§13.2a vector induction); a query
on any *other* node is genuinely settled, so a callee holding no hypothesis is still checked
and its traps still surface. This is the specific defect that produced yesterday's false
accept. Only **top-level** settlements are recorded: at depth > 1 ambient hypotheses are in
scope, so the verdict is hypothesis-relative and the entry is dropped rather than stored.

**This is where canonicalization earns its keep** — the instance half of the key is
`FnValue::shape()` from `oracle::canon`, not the closure allocation. Closures are plain
allocations rather than hash-consed values, so without the canonical shape two spellings of
one function would miss each other. A miss costs a cache hit, never an answer.

**T1.4 retried on top of the cache — still deferred, new reason.** The swap no longer fails
soundly-wrong; it fails to terminate in usable time. Root: `finish` deliberately *discards*
entries settled at depth > 1, so nested settlements are unmemoized, and `analyze_apply`
calling `prove` per callee makes a depth-n call chain do exponential re-settlement. That
discard is correct — a hypothesis-relative verdict is not a fact — so the fix is not to relax
it but to memoize nested results **under their hypothesis set**, or to avoid nested
settlement entirely by having `analyze_apply` consult facts rather than settle them.

**Recorded ordering:** T1.4 now waits on that, not on the cache. The cache was the right
prerequisite and is independently green; it was not sufficient.

**Correction to my own report:** I attributed the first T1.4 timeout to exponential blowup,
then measured it as a 5-second suite and withdrew the theory. On the retry the blowup was
real — a live test process, no completion. The earlier withdrawal was still right (that run
timed out in compilation); the theory simply turned out to describe a different run.

396 lib + 111 conformance + 4 gate green, clippy clean.

## 2026-08-01 — Correction: the fact cache keys on the layer-1 shape, not C§13.4's layer-2

I committed `factcache` claiming its key was "exactly as C§13.4 specifies". It is not.
`oracle::canon` gives the **layer-1** shape (algorithm A: α-renaming, capture slots,
polynomial NF). C§13.4 cache keys are specified over the **layer-2** μ-minimized shape, which
`oracle::mu` implements (SCC grouping, positional μ-refs, canonical slot order) and whose own
header says it "has no runtime consumer yet". The cache is not that consumer.

The obstacle is the one already recorded in blocker 2b's pin: `mu::canonicalize_group` takes
`(name, Expr)` binding lists, while `make_closure` builds a closure from one `Lambda` + env and
stores the raw body, so no closure knows it belongs to a binding group and a mutual partner
stays an ordinary capture. Law 4 (bisimulation slot merging) is absent outright.

Effect: mutually recursive members do not share keys as C§13.4 intends. Direction is **false
negatives** — a missed cache hit, never a wrong verdict — so it is a completeness gap, not a
soundness one. Recorded in the module docs; the cache is not conformant until it closes.

**Prerequisite audit for the global-discovery restructure (C§13.2a/13.3(1)), asked and
answered rather than assumed:** present — `analyze_program`, SCC + reverse-topological order,
the joint vector pass, region tables, the F0 rulebook. Missing — the layer-2 instance key
(above), **per-row grounded fact admission** (`I ⊆ GroundedRows(instance)`, C§13.2a; grounding
is corrected but still unwired, its only importer the quarantined `bodycheck`), and global
discovery itself. §5 group canonicalization is also absent but is value/group identity, not
fact-graph machinery, so it blocks other pinned rows rather than this restructure.

## 2026-08-01 — Canonical code is now interned; the fact-cache key is pointers

**The defect (mine).** `factcache`'s key held `Rc::new(f.shape().clone())` — a deep clone of a
function's entire canonical syntax tree, hashed structurally on **every lookup**. The project's
first rule is "same value = same pointer; `==` is pointer comparison, universally", and C§13.4
says "every key interned pointers". I did the opposite, in a cache, on the hot path.

**Why I did it, which is the part worth recording.** Canonical code was never interned:
`canonicalize` returns a fresh `Lambda` and `FnValue` wrapped it in a fresh `Rc`, so identical
shapes had different pointers and pointer comparison would have missed them. Rather than fix
that, I reached for structural comparison because it worked — the same reflex the author
flagged at the start of this session, in a new place.

**The fix.** `Interner::intern_code` hash-conses canonical code, so identical shapes share one
allocation. `FnValue::new` now takes the interned `Rc`; `make_closure_in` interns before
constructing. `factcache` keys on a `CodePtr` newtype comparing and hashing by pointer.
Structural hashing now happens **once per distinct shape at closure construction**, never per
lookup.

**Proven, not assumed** (`factcache::tests`): identical functions share one code pointer;
**α-variants share it too** (which the interim "use the parsed-code object" scheme in CLAUDE.md
would miss — this is strictly better than the sanctioned interim); different functions do not;
and same-shape/different-capture closures are distinct fact nodes, which is why the key carries
capture contracts beside the code pointer.

**Still non-conformant, recorded in the module docs:** capture and input **contracts** are
compared structurally, because contracts are not interned anywhere in this implementation.
That is the same rule violated in a second place, larger than this fix, and not attempted here.
The layer-1-vs-layer-2 shape gap from earlier today is unchanged.

400 lib + 111 conformance + 4 gate green, clippy clean.
