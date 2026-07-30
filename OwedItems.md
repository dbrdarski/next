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

### 0.1 The swap is blocked on grounding, not on `body_check` coverage — finding 2026-07-30

The swap (rewire `analyze_apply` Known-callee from `instance_body_summary` to
`body_summary`, then delete the superseded machinery) was **attempted and reverted**.
Wiring built cleanly and cost exactly **one** failing test:
`analyzer::tests::body_safety::a_recursive_call_over_a_new_domain_is_analyzed`. That is
not a precision wobble — it is a **soundness regression**:

```
f = (x) => x == 0 ? f("x") : x + 1     // f(0) → f("x") → "x" + 1  TRAPS at runtime
```

The region-table body check needs a **re-entry guard** to terminate on recursion. The
guard I built keys on the closure **instance** (cut when `f` is already on the stack).
That guard cuts the `f("x")` edge and returns the cycle assumption (`Top`, no finding),
so `f(0)` is **accepted** — a program that traps. The superseded `instance_body_summary`
is sound here because it is **domain-indexed**: `"x"` is a program literal, so the
new-domain edge (String, not admitted-from-`0`) is *analyzed*, and `"x" + 1` refutes.

**Consequence for the audit §5 DELETE list:** `domain_admitted` / widening / the
domain-indexed cutoff are **soundness-load-bearing for domain-changing recursion**, not
just wrong-layer scaffolding. Their sound replacement is the **grounding arc (C§10)**,
which derives the recursion's input domain (the orbit `0 → "x" → …`) so the body check
covers `"x"`. **Grounding is not built.** Therefore:

- The swap is **blocked on grounding**, not merely on `body_check`'s capture/multi-param
  coverage (task #50's old "BLOCKED on body_check recursion" framing was too narrow).
- The Archive9 domain-indexed machinery (`instance_body_summary`, `domain_admitted`,
  widening, `ACTIVE_BODIES`) **stays** until grounding lands — it cannot be deleted
  without regressing this soundness case.
- `body_summary` + its `errors()` + the instance-keyed re-entry guard remain in
  `bodycheck.rs` as **built-but-unwired**, correct for the non-recursive fragment and
  ready to re-plumb once grounding supplies the recursion domain.

The correct next recovery move is therefore **grounding (C§10)**, not the swap.

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
- **Grounding v1** — `next-grounding-specification-v0-5.md` (0.5.1, DESIGN-CLOSED,
  compendium 1.0.18; GR-01…GR-30; Phase GR suite). Implementation + §13/§16 discharge
  owed (exact-chain bound theorem; lex joint-settlement; multigraph decomposition
  lemma; per-rule soundness; GR-27 preservation check). This is A-NEG's second domain
  source (factorial's `GE(0) ∧ Mod(1,0)`).
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
