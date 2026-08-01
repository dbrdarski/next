> ## 📘 STATUS: **CURRENT (subordinate)**
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**; where this file
> conflicts with it, **that file wins**. The tier structure and the owed/liveness synthesis here
> stand as supporting detail.
>
> **Progress delta 2026-08-01:** the program checker now originates executable and `where` demands;
> the memo key is dependency-complete; grounding's T2.1 corrections are complete but unwired; T1.3
> and T1.4 are complete; the reaching checker is deleted; T2.2 carries realized structural
> completion witnesses through Match to the consuming seat. The only remaining lib pin is 1b
> (exact-singleton chains). T2.3 now routes the live expression adapter through the one canonical
> application driver; erased source environments still owe full annotated correlation. The
> realized-refutation voice at the existing `where` return-demand consumer is next. Older scan counts
> and “no top / bodycheck live” passages below are historical where this delta supersedes them.

# NEXT — Feature-by-feature completion plan

**Date:** 2026-07-31. **Status:** planning document (maintainer file, not spec). Synthesized from
three systematic scans: (1) a LIVE-vs-DEAD map of every item in `src/analyzer` and `src/contract`
with the live call graph; (2) a complete owed-item audit across `OwedItems.md`, `PROGRESS.md`,
compendium C§17 + Part J, and all six per-spec owed lists (~148 items, 13 doc conflicts); (3) the
17 `#[ignore]`d tests as concrete acceptance targets.

---

## 1. Historical root finding — the analyzer had no top (fixed 2026-08-01)

The original scan found that **`src/main.rs` imported only `oracle::run_source`; nothing outside
unit tests called `analyzer::analyze`; and there was no program-level checker.** That finding drove
T1.1. It is now fixed: `--check` calls the program checker, which originates typed executable and
`where` demands. The six broad Phase-A rows remain ignored for their own later feature gates.

This was the structural cause of the residue below. In a **demand-driven** design the program-level
entry point is what *originates* demands (C§13.1: demands come from source-authored seats and
fixed-rule compiler obligations). With no top, nothing pulls — so every layer was built
speculatively bottom-up, and speculation leaves exactly the residue the scan found:

- **~3,000 lines built and wired to nothing:** `contract::recursive` + `contract::length` (1,803
  lines — a closed dead island, since `Contract::Ref` and `LengthRestricted` are never constructed
  live) · `grounding`'s entire judgment (~1,000 lines; only `collect_self_calls` escapes) ·
  `analyzer::refute` · `application`'s driver and outcome algebra · `domain`'s annotated machinery
  (`Instance` never constructed live) · `contract::grapheme` · `obligation::input_obligation`.
- **~16 parallel implementations of one concept**, including two callee body summaries at the time.
  The unsound `bodycheck` branch is now deleted; `outcome::summarize_instance` remains the coarse
  outcome projection, sharpened by settled safety/completion/return facts.

**The plan's organizing rule follows from this: build the consumer before the capability.** Every
feature below must be pulled by something that already needs it. This is also the direct fix for
the failure mode this session diagnosed three times (an interface with no consumer; a mechanism
imported to fill a foundation gap).

---

## 1a. External review corrections [2026-07-31] — verified, and they change this plan

An external architectural review of the codebase landed after the first draft. **Every concrete
claim I could check, I checked; all confirmed.** Two are conceptual corrections to *my own*
reasoning, and two are defects nobody had counted.

**New defects (verified here, not previously on any list):**

- **G-BUG — RESOLVED 2026-07-31.** `drift_away` treated a *syntactically present*
  self-call as a **forced** recursive transition; GR-23 requires exact selection (or another
  applicable must-condition) at every step. Verified live: for
  `flag = false; f = (n) => n == 0 ? 0 : (flag ? f(n-2) : 0)`, `ground(f, Equals(1))` returns
  **`Refuted`** — the program terminates (the guard is false, the recursive edge is never taken).
  Claiming a terminating program diverges, on an unrealizable witness, is the worst error class.
  Pinned as `grounding::review_gates::captured_false_guard_must_not_refute`.
- **W-BUG — RESOLVED 2026-08-01.** At the time, `analyze_apply` used
  `summary.errors()`, which filters to `Severity::Error` only (`bodycheck.rs:72`). A callee whose
  body safety is *unproven* therefore contributes **no diagnostic at the call site** and the call is
  `accepted()`. Late-resolution §5 is explicit: **safety-unproven blocks, un-suppressibly.** So this
  was a false acceptance, not the "standing diagnostic gap" the doc comment called it. Ordinary
  application now consumes `BodySafety` and blocks Unproven at the seat.

**Also confirmed at the time:** the recursive cycle assumption supplied `Completion::Produces`
(`bodycheck.rs:66`); that path is now deleted. `grounding::Verdict` lacked its witness and the
module header misclassified grounding as the analysis termination bound; both were corrected in
T2.1. `induction.rs` still imports `obligation::accepted_domain` — the
**dissolved** materialized-accepted-domain concept — so the "kept" induction engine is **not**
keep-as-is.

**Correction 1 — I and C are different things (this plan conflated them).** A fact is
`BodySafe(instance, I)` / `ReturnFact(instance, I, C)`: **`I` is the input/row domain under which
the fact is claimed; `C` is the demanded contract.** My earlier note said "`total + n` demands
`total : Number`, so `Number` is `I`." Wrong: `Number` is the **obligation on the operand**. `I`
comes from the actual call/row-domain machinery. Conflating them makes it look as though the demand
core must *derive* analysis domains — which invites exactly the machinery expansion this plan
exists to stop. **Rule: carry `I` and demanded `C` as distinct fields everywhere.**

**Correction 2 — F0 was a precision project, not a prerequisite.** I argued the demand core
"executes" the operation table, so the table had to be complete first. That does not follow: an
incomplete rule returns **unproven / coarse**, which is *sound* — the three-voice architecture
exists precisely so incompleteness never needs repair by invention. F0 is worth keeping (isolated
in the contract layer, tested, and it did fix a real safety-table gap), but sequencing it as a
blocker for F2 was my error, of the same family as the others: treating *imprecise* as *must-fix-first*.

**Consequences for the tiers below:** grounding moves from "wire it" to **"fix its semantic role,
forced-path condition and witness-bearing API — then wire"**; the induction engine is
**replace-and-rebuild, not extend**; and the vertical slice (demand origin → operation obligation →
provider dependencies → domain-indexed `BodySafe` → global SCC settlement) is the *only* thing
Tier 1 builds.

---

## 2. Ground rules (earned this session; they bind the whole plan)

1. **Build complete feature sets.** A failing case may *scope* a feature; it must never *define* an
   increment. (Three reverts came from violating this.)
2. **No building ahead of the consumer.** If an interface has no caller, it is not ready to build —
   its content comes from its consumer.
3. **No imports.** When a native mechanism cannot close something, that is a missing foundation, not
   a licence for a forward-solve/widening prosthetic.
4. **Wire before adding.** Do not add a subsystem while built-unwired ones accumulate.
5. **Design on paper, author-reviewed, before code** (this is why F0 succeeded).
6. **Green ≠ done.** State what a suite does *not* cover.

---

## TIER 0 — Reconcile the record (doc-only; blocks nothing else from being trusted)

The audit found **13 places where two documents disagree**. A plan built on contradictory records
inherits the contradiction. These are cheap and must go first.

| # | Conflict | Why it matters |
|---|---|---|
| **R8** | **`Numeric = Number ∪ ZeroDen` and specific-`a/0` identity were RULED [user, 2026-07-27], but no spec carries them** — and compendium C§7 still encodes the *rejected* generic `_/0` marker model. | **F0's freshly-built safety table keys on `Indeterminate`.** A live ruling contradicts both a frozen spec and new code. Highest priority. |
| **R2** | The reaching-domain body check is simultaneously "LANDED / target architecture" (`PROGRESS` doc-sync, `OwedItems` §0.1-history) and "on the delete list" (`OwedItems` §0.1, foundation map). | The plan's Tier-1 depends on which framing is live. |
| **R3** | Grounding v0.5: compendium says **DESIGN-CLOSED**; the spec's own header says *"nothing herein is closed until stamped."* Four ledger changes already applied in advance of the stamp. | Needs an explicit stamp record or a status rollback. |
| **R5** | Region-table §6/§11 still describe a "separate accepted-domain specification"; the 2026-07-24 erratum **dissolved** it. Manifest-verified text is stale against its own erratum. | Anyone reading the spec builds a phantom. |
| R1 | Test counts differ across four docs (323 / 371 / 377), all marked verified. | Baseline honesty. |
| R4 | `PROGRESS` says Phase GR stubs exist; `tests/conformance.rs` has **zero** GR tests. | Phantom coverage. |
| R6 | Region-table header says patch 0.3.1, body describes 0.3.2. | — |
| R7 | `OwedItems` §3 says F0 built *and* re-lists per-pair tables as owed. | Needs the code-vs-prose split recorded. |
| R9 | Three docs assign `OperationOutcome` to three different increments. | — |
| R10 | `PROGRESS` ledger cites `SAFETY_STACK`; `OwedItems` says it never existed. | — |
| R11 | `PROGRESS` §6 "next increments" points at the retired app-induction tail plan. | — |
| R12 | `OwedItems` says "analyzer = 10 modules"; there are 13. | — |
| R13 | "Tuple family §16" — that spec has no §16 (ends at §8); the reference is compendium C§16. | — |

**Done means:** each conflict resolved in favour of one statement, with the loser corrected in
place; `PROGRESS`/`OwedItems`/`DECISIONS` mutually consistent; F0's uncommitted work committed and,
if it is to be canonical, manifested.

---

## TIER 1 — The spine (critical path; each step's consumer is the previous step)

### T1.1 — Program-level analyzer entry point + `where` as the first demand origin
**The missing top.** `analyze_program(module) → ProgramVerdict { accept/reject, findings }`: walk
module items, analyze each binding's expression, and — per **E-8** — verify each `Where` as
`BodySafe(instance, DeclaredInput)`. Author already confirmed the direction: *an explicit contract
given by the author is the source of truth*, so `where` is the first, cleanest demand origin (its
domain is **declared**, nothing to guess). Wire it into `main.rs` behind a check mode.
- **Consumer:** the six Phase-A conformance rows; `main.rs`.
- **Unblocks:** everything below — this is what originates demands.
- **Done means:** A-VER and at least the accept/reject half of Phase A run un-ignored; `main.rs`
  can check a file; a deliberately-trapping program is rejected.
- *Note:* thin is fine and correct here. What it *cannot* answer becomes the demand that pulls T1.2.

### T1.2 — Demand core (C§13.1) — pulled by T1.1
Backward demand propagation to origins with three-valued adjudication; **eager preimage as the
primary mechanism** per the author's model (`total + n` *demands* `total : Number`, checked against
providers — never reconstructed by watching values flow forward). Typed program origins now exist;
the broader backward propagation remains partial.
- **Absorbs the old F1**: the operation interface (`OperationOutcome`) is defined *by what the
  demand core needs to consume*, not built ahead of it. (F1 failed twice as a standalone.)
- **Dependency note:** F0 (the operation rulebook) is **built** — the demand core resolves *through*
  those rules, which is why F0 came first.
- **Done means:** a demand registered at an operation reaches the parameter origin and is
  adjudicated there; the `where`-declared contract is the truth checked against.

### T1.3 — ✅ COMPLETE: domain-indexed safety facts `BodySafe(instance, I)` (C§13.2a)
The **safety** analogue of the existing return facts, settled by the **kept** `joint_vector_pass`
induction. `I` comes from the demand (T1.2) — which is exactly why F3-before-F2 would have had to
*guess* `I`, i.e. re-import.
- **Done means:** recursion closes on a fact; mutual/SCC cases work through the existing driver.

### T1.4 — ✅ COMPLETE 2026-08-01: native body check; forward-reaching engine deleted
Ordinary application consumes domain-indexed safety/completion/return facts. `bodycheck.rs`,
`check_recursive_body`, `reachable_rows`, and `grow` are deleted; a machinery gate requires their
absence. Blockers 2a/2b no longer false-accept: an unsupported changed-domain repeated-shape fact is
Unproven and blocks at the seat. Later diagnosis split 1b and 3 from this wiring gate: 1b requires
T3.2's exact-singleton chains, while 3 required T2.2's structured completion evidence. Both remained
honestly pinned at T1.4; T2.2 has since released 3.

---

## TIER 2 — Wire what is already built (each now has a consumer from Tier 1)

| Feature | What it is | Pulled by |
|---|---|---|
| **T2.1 Grounding corrections — COMPLETE; still unwired** | The three prerequisite corrections are complete: forced recursive transitions, witness-bearing refutation, and the behavioural-judgment header correction. Wiring remains consumer-gated; do not wire merely because the implementation exists. | T1.3, A-NEG |
| **T2.2 AP-30 + `refute` — COMPLETE 2026-08-01** | Expression completion carries structured evidence; bounded Pure-call realization mints `ApplicationWitness` only on actual `CompletedWithoutValue`; Match preserves selected-arm outcomes for the enclosing consumer; completion claims use the row partition. Blocker 3 is live. | T1.2 (seat demands), T1.4 |
| **T2.3 Application path unification — COMPLETE 2026-08-01** | `drive_application` owns live-alternative traversal, projection weakening, and outcome joining. `analyze_apply` is the expression/fact adapter; its parallel callee loop is deleted and mechanically forbidden. The bridge intentionally keeps erased arguments opaque: propagating annotated source correlation remains a separate owed feature, not a false T2.3 claim. | T1.2 |
| **T2.4 Recursive source contracts → `RecGroup`** | Nothing live constructs `Contract::Ref`, so `contract::recursive` (and via it `length`) is dead. Building named recursive *source* contracts gives it its first real consumer. | T1.1 (`where`/named contracts) |
| **T2.5 String-length contract form** | Tuple-family §5 lift. No string-length contract exists — this is what F0's `Add(String,String)` length lift is blocked on, and it gives `contract::length` + `grapheme` their consumer. | F0 residual |

---

## TIER 3 — Complete the specified-but-partial features

- **T3.1 Region table:** cases (b)/(c) over captures; **§5 multi-parameter projection** (attempted
  and reverted 2026-07-30 — resolution recorded: fold a position into its row region only when it
  grows); the guards' own path demands; the **annotated-tuple instance cache** (C§13.4, RT-09);
  RT-01…RT-14 as conformance rows.
- **T3.2 Grounding completion:** point-base/Ackermann (GR-18), peel-k grid, `restrict_len` facts
  (GR-08), nonlinear measures, oscillator composition, closed-orbit refutation (GR-11), §4
  exact-singleton chains, **§8 WorldDecided classifier**, multi-param mutual; **Phase GR
  GR-01…GR-30 tests (currently zero exist)**.
- **T3.3 μ §5/§6 canonicalizer:** universal interning at construction + group construction windows.
  Un-ignores **MU-18** and retires the PENDING-§5 register (FE-03/04/05/06, H-05).
- **T3.4 Module system (E12):** linking, module-file top-level world, store modules, duplicate-module
  error. Un-ignores **5** conformance rows (P-27b, MOD-01/03/04/05).
- **T3.5 Program-level fuel harness:** bounded `run_module` → **M-04** `DIVERGES`.
- **T3.6 Lint tier:** goes-nowhere, discarded effect result, identity slice, redundant `?.`/`~`,
  `||`-non-Boolean, leading-minus continuation, self-prefix (A-LNT).
- **T3.7 C§13.4 caches:** template / instance / evaluation (`EvaluationCore`) / subcontract /
  proven-return-fact, under the semantics+kernel namespace.

---

## TIER 4 — Consolidate (only safe once the live path is settled)

Deduplicate the remaining parallel implementations the scan named — the retired body-summary fork
is already gone; next reconcile the four verdict
enums, the two row-selection walks, the three `intersect` copies, the two completion tri-states.
Delete the Phase-3 superseded set (`accepted_domain`, `summarize_instance`'s per-call role,
residual `kind_abstraction`). **Nothing is deleted until its replacement passes what the current
tests encode.**

---

## TIER 5 — Discharge (C§16 proofs)

Per-rule soundness for the operation rules; grounding §13's four obligations (exact-chain bound
theorem, lex joint-settlement, multigraph decomposition lemma, per-rule soundness); the
application package's four γ obligations as a sampled joint-operand battery per world; tuple-family
and recursive-contract discharge; μ obligations; the semantics theorem (*every evaluated reference
is bound*); **A-SND** as the executable soundness harness.

---

## Policy gates (author-only; they change *what* gets built, not just when)

- **P-1 / Principle 9** — unproven grounding: warn-and-compile (current law) vs **reject** (heavily
  leaning). Blocker (4) satisfied; **(2) hard-vs-acknowledgeable and (3) the [permanent] gray
  family remain open.** *Gates Phase GR's expected-verdict polarity* — GRAY vs REJECT rides the P-1
  status, not test edits.
- **R8's ruling — SETTLED 2026-08-01:** `Numeric = Number ∪ Indeterminate`, with specific
  `DivZero(a)` / `ModZero(a)` forms, is recorded in manifest-governed Part XII and implemented.
- **Uncalled proven-unsafe body** — definition-site diagnostic: error / lint / silent. Unruled.
- **F0 draft Q1** — `Union` distribution vs interval hull (hull implemented).
- Literal parameter patterns; mutator returns; module dot-nesting; modules in value seats;
  shadowing policy; `String.units` element representation.

## Explicitly out of scope (recorded so absence is deliberate)

**Permanent walls** (relations outside the algebra, cross-orbit Diophantine, hypothesis
strengthening, data-decided structure, Rice/halting, graphs-are-gray, sortedness, …) ·
**Fenced** (reactive layer, concurrency, UI, dynamic import, composeAll, Part D slice 2) ·
**Parked** (the act/`@` session's statutes and spellings) · **Grounding §14's killed list** (fuel of
any kind, tier-0 evaluation-as-grounding, constructed witnesses, supplied measures, invariant
synthesis — *may not be resurrected by any reading*) · **Part D** (candidate, not adopted).

---

## Acceptance map — current `#[ignore]`s by feature

| Ignored tests | Count | Released by |
|---|---|---|
| Blocker 1b exact-singleton chain (lib) | 1 | **T3.2** |
| Phase A (A-VER, A-ACC, A-SND, verdicts, A-LNT, A-WRK) | 6 | **T1.1** (+ T3.6 for lints, T5 for A-SND) |
| MOD-03/04/05, P-27b | 4 | **T3.4** |
| MU-18 | 1 | **T3.3** |
| M-04 | 1 | **T3.5** |

---

## Recommended immediate order

1. Make the existing `where` return demand consume `check_return_claim`, preserving realized
   Refuted evidence instead of collapsing it into generic Unproven.
2. Carry `AnalysisContract` through source bindings/accesses so the now-live driver receives the
   normative joint operand rather than the legal-but-projecting erased bridge.
3. Then select the next consumer-led Phase-A slice; do not wire grounding merely because it exists.

*The remaining T1.2 breadth is pulled by these consumers; it is not a licence for a standalone
backward-analysis rebuild.*
