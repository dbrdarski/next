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

### 0.1 The swap needs grounding for *termination*, not for the domain-changing example — finding 2026-07-30 (corrected + verified)

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
corrected key* was run against the full suite: it **hangs** on
`a_growing_union_recursive_domain_terminates` and
`recursive_domains::a_growing_non_singleton_recursive_domain_terminates`. The correct key
(rightly) refuses to cut distinct nodes, and a domain that **grows without end**
(`f(Range(1,3)) → f(Range(2,5)) → …`) presents an unbounded stream of distinct nodes →
the analysis never converges. The old machine bounds this with **widening**
(`domain_admitted` + `kind_abstraction`). **That** is the soundness-of-termination job
whose specified replacement is grounding.

**Consequence for the audit §5 DELETE list:** `domain_admitted` / widening are
load-bearing for **termination over growing domains** (not, as I first wrote, for the
domain-changing example — the key handles that). They stay until grounding replaces the
bound. Therefore:

- A **wired** `body_summary` needs **both**: the corrected `(instance, domain)` key (done
  — sound on the example) **and** a termination bound (grounding — unbuilt). The suite
  proves neither alone suffices: instance-key terminates but is unsound; domain-key is
  sound but hangs on the two `..._terminates` tests.
- `body_summary` + `errors()` + the corrected key remain in `bodycheck.rs` as
  **built-but-unwired**, correct for the non-recursive + same-/finite-domain fragment,
  and re-plumbed once grounding supplies the bound.

The correct next recovery move is still **grounding (C§10)** — but for *termination
bounding*, and the two `..._terminates` tests (not the domain-changing test) are what
move when it lands.

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
  accumulator variant grounds, rebuild-the-whole (`f([h, ...rest])`) Unproven. `ground` is
  three-voiced. Candidate-locality (GR-04). **Owed:** point-base / **Ackermann** (GR-18 grid
  + domain — `==0` stops give no lower bound), **peel-k grid** (base must cover lengths
  `0..k-1`), `restrict_len` structural facts (GR-08), nonlinear measures, §7 **closed-orbit**
  refutation (GR-11; specimen 22b), §4 exact-singleton chains, §8 WorldDecided; mutual SCC;
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
- **Universal interning (μ v0.5 §6)** — closures should intern shallowly
  (canonical-code + capture pointers), `==` a pointer test. I run Algorithm B at
  compare-time over plain allocations. All `==` results conform (FE rows green); only
  harness pointer-observability differs. Scoped to the **§5 canonicalizer wiring**.
  Consequence: **MU-18** `#[ignore]` PENDING-§5.
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
- **Literal parameter patterns `(0) => …`** — E3: *"[deferred; likely excluded]"*. (Some
  analyzer tests use const params; they'd need re-basing if excluded.)

## 5. Open design threads (no spec change; block nothing) — see the handovers

- **Thread B** — the jagged function-equality boundary under the freeze slice
  (`x+3` == `x+2+1`, `x+x` == `2*x`, but `x*2` ≠ `x*3−x`). `HANDOVER-open-threads-2026-07-23.md`.
- **Thread C** — the equality-freeze exclusions + the future canonical-DAG Number
  (`1/0 ≠ 2/0`). `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md`. Tests
  that move if ruled: `(1/0) == (2/0)` (`oracle/tests.rs`), PR-04's render, MU-10 in
  `poly.rs`.

## 6. Author-flagged opens (implemented per stated law)

- **Mutator returns** — return-nothing implemented; the returns-leaning is an extension point.
- **Module system** — MOD-01/03/04/05 + P-27b `#[ignore]`; imports parse only. Module-in-value-seat: clear error is correct.
- **`DIVERGES` verdicts (M-04)** — need a fuel-limited *harness* (eval-level bound exists); `#[ignore]`.
- **`String.units`/`points` element representation** — E8 doesn't pin it; Tuples of Numbers, lengths asserted (S-02). `// [ask-author]` in `harness.rs`.
