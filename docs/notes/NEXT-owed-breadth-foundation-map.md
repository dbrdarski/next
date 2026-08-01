> ## ⛔ STATUS: **SUPERSEDED**
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Two things in this
> file are **not** to be followed: its **F0-before-demand-core ordering** (it rested on the
> assumption that an incomplete operation table forces invention — imprecision correctly yields
> *unproven*), and its **"replace-and-rebuild"** framing for the induction pipeline (no such project
> is authorized). Its diagnosis of the missing foundation stands as history. Left unedited.

# NEXT — Owed-Breadth Foundation Map (body-safety substrate)

**Date:** 2026-07-31. **Status:** planning document (maintainer file, not spec). Produced after a
session in which the four pinned Archive-11 body-safety blockers (1b/2a/2b/3) were "closed" by an
**imported** forward reaching-domain fixpoint + Kind-collapse widening (`analyzer/summary.rs`),
then **reverted** on the author's instruction. The blockers are re-pinned `#[ignore]` naming this
document. This map records *why* the imports happened — a **skipped foundation** — and the
dependency-ordered plan to build that foundation so the native body check needs no imports.

**The one-line finding.** The body-safety check has been built **ahead of its foundation**. The
recovery order is *demand core → summary template → region table → call-site body check*; the
region table and body check exist, **the demand core (step 1) was never built**. With no
demand-and-fact substrate underneath, every time the check cannot close a recursion or hold a
parameter's contract natively, the implementation reaches for a **forward-solve** mechanism
(accumulate reaching values, then widen). That is the imported abstract-interpretation shape NEXT
rejects (Principle 7; late-resolution law; the "widening is foreign" stance). **Green tests then
mask the missing foundation.**

---

## 1. Evidence (code audit, 2026-07-31)

Three foundational pieces the native check depends on are **absent**:

1. **No demand core (C§13.1).** The only `demand` in the tree is `analyzer/mod.rs`'s local
   expecting-seat helper and `application.rs::seat_demand`. `analyze(expr, env)` runs strictly
   **forward / bottom-up**; there is **no backward-demand subscription channel, no forward
   resolution through the operation rules keyed to a demand, and no three-valued adjudication at a
   demand origin.** C§13.1's substrate does not exist.
2. **Operations don't carry the demand/completion shape (C§7 upgrade / C§16 obl.3, patch 1.0.7).**
   `contract/operation.rs::analyze_operation` returns the pre-upgrade `OpResult { safety, output }`,
   not `OperationOutcome { safety, produced, completion }`. (`OwedItems.md §2` registered drift.)
3. **Return facts exist; safety facts do not.** `induction.rs` has `infer_return_fact` and a
   `Hypothesis { callee, input, contract }` keyed to (instance, input-domain) → **return** contract.
   There is **no** `BodySafe(instance, I)` fact — the safety analogue that C§13.2a's fact-node shape
   `(instance, row-set I, demanded C)` implies. So a recursive body-safety question has **nothing to
   close on by induction** — which is precisely why the implementation unfolds/accumulates instead.

---

## 2. The imports, and the foundation each substitutes for

Every "clever" mechanism the body check grew is a prosthetic for one of the three missing pieces.

| Imported mechanism (reverted / to remove) | The missing foundation it stands in for |
|---|---|
| the **reaching-domain fixpoint** — forward accumulation of the contracts that reach each `(member,row)` across recursion depths (`summary.rs`, and the single-param `bodycheck::check_recursive_body`) | **domain-indexed safety facts** — with `BodySafe(instance, I)` settled by induction, a recursive call *closes on the fact*; there is nothing to accumulate across depths |
| the **Kind-collapse "swap" / widening** (`grow_pos`) | the domain being **one contract**, not a growing union — the union only grows because there is no fact to close on, so its growth had to be bounded |
| the **cargo/drift multi-position reaching** (track which value reaches each slot) | the **demand core** — `total + n` *demands* `total : Number`; under a demand model that contract is **registered at the parameter and checked against every provider**, not reconstructed by watching values flow forward |

**What is NOT an import and stays:** the **region table** + **single-domain row selection**
(`region.rs`) — that is C§13.2's *"obtain the region table, perform the ordered remainder walk,"*
i.e. reachability of a branch for **one** input contract. Reachability is a single-domain contract
question, not cross-depth accumulation. The line to hold: **branch reachability = region table
(keep); recursion closure = safety facts + induction (build), never a forward reaching fixpoint.**

---

## 3. The foundations (spec anchor · what exists · what's needed · what it unblocks)

> **Revision [2026-07-31, after two more reverted patch-shaped attempts].** F1 as first written
> ("reshape the return type") was **too small and the wrong shape**. Two corrections, both learned by
> doing it wrong:
>
> 1. **The operation rulebook itself is a foundation — call it F0 — and it is the *first* one.**
>    C§13.1's resolution runs *"forward through the operation rules"*, so the demand core **executes**
>    the C§7 table. A half-built table loses information exactly when a demand resolves, and something
>    downstream gets invented to compensate. F2 on a half-built rulebook imports for the same reason
>    the body check did.
> 2. **Build each foundation as a COMPLETE FEATURE SET, never per-failing-case.** The reverted
>    attempts were: fix `+`/`−` over half-lines (leaving `*`, `/`, `**`, `Mod`, `Geo`), and extract a
>    return type without its function. Both went green; both were patches. The rule for the rest of
>    this rebuild: *build the whole specified feature, then see what passes* — a failing case may
>    **scope** the feature, but must never **define** the increment.
>
> Revised order: **F0 (complete C§7 rulebook) → F1 (`analyzeOperation` + `OperationOutcome`, the real
> analyzer-level function) → F2 (demand core) → F3 (safety facts) → native body check.**

### F0 — The complete operation rulebook (C§7 + C§17's per-pair tables) — **build whole**
- **Spec:** C§7 (Range/Mod/Geo arithmetic and scaling; division total; Indeterminate propagation);
  C§17 **Owed**: per-pair tables (`Geo`, `Difference`/emptiness, finite-interval coverage) honoring
  the no-flattening rule; boolean-DNF; the remaining per-operation `analyzeOperation` tables;
  Indeterminate enumerations; division/NF coupling; Union/Intersection completeness *or documented
  incompleteness*.
- **Exists:** `contract/operation.rs` — safety verdicts (sound, brute-tested against the oracle) and
  image bounds, but the image side is **closed-`Range`-only** for arithmetic. Verified gaps:
  half-lines do not compose (`GreaterEq(8) + GreaterEq(10)` → `Kind(Number)`; the algebra has **no
  infinity**, so half-lines *are* the unbounded form and every unbounded domain hits this);
  `Mod`/`Geo` arithmetic absent; `Intersection`/`Union` not read through. Also
  `region.rs` regionalizes only `param OP const` on a bare-parameter scrutinee, so a **compound
  scrutinee** (`(a + b) :: { … }`) is opaque — the same rulebook gap seen from the control side.
- **Needed:** the table, **complete** — every operation × every contract form, with the documented
  incompleteness where a pair is deliberately unproven. Reuse `subcontract.rs:129-162`'s existing
  `Interval`/`Bound`/`interval_of`/`meet` rather than a parallel encoding; keep **two** conversions
  (image over-approximation may widen; subset testing may not — `GreaterEq(0) ⊑ Mod(1,0)` must not
  come out Proven). The existing `operation_soundness_sweep` is the net; extend its grid with the
  half-line and `Intersection` forms.
- **Unblocks:** everything downstream — a demand resolves *through* these rules, and a region/branch
  decision is taken *against* their output.

### F1 — `analyzeOperation` + `OperationOutcome` (the analyzer-level rule interface)
- **Spec:** C§7 (upgraded interface, 1.0.7): `analyzeOperation(op, jointOperands, seatContext) →
  OperationOutcome { safety: proven|refuted(witness)|unproven; produced: AnalysisContract;
  completion }`. C§16 obligation 3. Ordinary operations use the **degenerate** form at zero cost.
- **Exists:** `analyze_operation → OpResult { safety, output }` (`operation.rs`). Safety verdicts
  and output contracts are computed and brute-tested against the oracle (sound).
- **Needed — the *function*, not just the type [corrected 2026-07-31].** The spec's inputs are
  analyzer-level too (`Correlated<AnalysisContract>` + `seatContext`), so this is an **analyzer-level
  `analyzeOperation`** wrapping F0's contract-layer kernel — with `OperationOutcome` as its return
  type, living beside `ApplicationOutcome` (C§16: the application case **is** "obligation 3's
  application instance"), not in a separate module. Extracting the return type alone was tried and
  reverted: a noun without its verb, no genuine consumer. Land the type **with** the function, and
  fold the application path onto it so there is one operation interface, not two.
- **Unblocks:** the vocabulary the demand core and the facts speak. Without it the demand core has
  no uniform per-operation carrier for *safety + produced + completion*.

### F2 — Demand core (C§13.1)
- **Spec:** C§13.1 *"Demands propagate backward untransformed as subscriptions; resolution is
  forward through the operation rules (each carrying its C§7 safety verdict); adjudication where the
  demand was asked, three-valued. … Eager preimage transformation is an optimization."* The
  late-resolution law (`next-late-resolution-v0-5.md`): demand-triggered, dependency-complete.
- **Exists:** nothing. `analyze` is forward-only, no subscription/adjudication layer.
- **Needed:** the subscription + origin-adjudication layer over forward resolution. An operation
  registers a **demand** (a contract) on each operand **at the operand's origin**; the origin
  adjudicates three-valued (proven / refuted-with-witness / unproven). For a **parameter** origin,
  the demand becomes an obligation on **every provider of that parameter** — the base call and each
  recursive call — which is where induction (F3) enters. This is the piece that lets `total : Number`
  be *derived from the demand and checked against providers*, never reconstructed forward.
- **Unblocks:** the whole demand-driven shape — including the ability to state a parameter's
  demanded contract and discharge it by provider-checking + induction instead of reaching.

### F3 — Domain-indexed safety facts (C§13.2a)
- **Spec:** C§13.2a *"Fact nodes are (analysis instance, row-set I, demanded C)"*; C§13.2
  *"recursive references never unfold; they resolve through proven … facts — (instance, I, C)"*;
  §10.6 domain-indexed, instance-scoped, settled **jointly** by the SCC/vector pass. E-8: `where` is
  `BodySafe(instance, DeclaredInput) = proven`. The **safety** flavour is `BodySafe(instance, I)`.
- **Exists:** the **induction engine** — `joint_vector_pass`, the multi-SCC driver, `Hypothesis`
  keyed by (instance, input-domain) — but wired only to **return** facts (`infer_return_fact`). This
  is the *keep-set* the recovery preserved.
- **Needed:** a **safety** fact `BodySafe(instance, I)` established by the **same** machinery:
  assume `BodySafe(instance, I)` as the hypothesis, check the body under `I` (region table selects
  branches; F1/F2 discharge each operation's demand), resolve recursive/mutual calls through the
  hypothesis (SCC-vector, jointly), refute only with a jointly-represented witness (RT-14). The
  domain `I` ranges over the **region partition** (GR-03's finite row-set lattice) — and later,
  grounding's A-NEG derived basin for tighter domains. **No forward reaching, no widening:** the
  fact's domain is a contract from the start; the finite bound is the fact lattice + §4a cutoff.
- **Unblocks:** recursive/mutual body-safety closes on a fact (2b: the SCC spans functions because
  the vector pass already does; 1b/2a: the domain is a contract checked once per region, not an
  accumulated union; 3: completion rides the same fact — `OperationOutcome.completion` through the
  induction). This is the native replacement for `summary.rs` and `check_recursive_body`.

---

## 4. Keep / delete, precisely

**Keep (native, reused):**
- `region.rs` region table + `select` — branch reachability for one input contract (C§13.2).
- `reachable_closures` / `inventory.rs` §4a shape-cutoff closure — the SCC/instance bound.
- `induction.rs` `joint_vector_pass` / multi-SCC driver / `Hypothesis` (instance+domain key) — the
  induction engine, to be **extended** from return-only to safety facts.
- `analyze_match` dead-arm/path narrowing; `prove_subcontract_a`; the `AnalysisContract` domain.

**Delete when F3 lands (the imported forward-solve):**
- `analyzer/summary.rs` — already reverted; do not re-add.
- `bodycheck::check_recursive_body` + `reachable_rows` + `grow`/`intersect` reaching accumulation —
  the single-param forward reaching fixpoint (07-30). Replaced by safety-fact induction.
- any `kind_abstraction`-as-domain-widener use (already retired for the domain role).

---

## 5. Build order

Dependency-correct order (note: this **reorders** the author's stated "demand core → OperationOutcome
→ safety facts" — `OperationOutcome` is the vocabulary the core routes through, so it comes first;
flag for author confirmation):

```
F0  Complete C§7 operation rulebook  (+ C§17 per-pair tables)  — BUILD WHOLE, not per-case
      │                                                          the table demands resolve through
F1  analyzeOperation + OperationOutcome  (C§7 1.0.7 / C§16 obl.3)
      │                                   the analyzer-level rule interface (function, not just type)
F2  Demand core                     (C§13.1)   — demands to origins, three-valued adjudication
      │
F3  Domain-indexed safety facts     (C§13.2a)  — BodySafe(instance,I) via joint_vector_pass
      │
R   Rewrite the body check native → delete the forward reaching engine
      │
✔   Un-ignore 1b/2a/2b/3 — they must pass with NO reaching fixpoint and NO widening present
```

**The standing rule for every step above:** build the **complete specified feature set**, then see
what passes. A failing case may *scope* a feature; it must never *define* an increment. Three
attempts on 2026-07-31 violated this (the SCC engine, the `+`/`−` interval patch, the bare
`OperationOutcome` type) and all three were reverted.

**On the "minimal F3-first" staging — RETRACTED [author, 2026-07-31].** An earlier draft suggested
building F3 on today's induction *before* F2, to delete the reaching fixpoint sooner. That is wrong:
**F2 is load-bearing for F3.** A safety fact is *"for inputs ⊑ I, the body is safe"* — its whole
content is the domain `I`. In the demand model `I` is **derived** (the operation *demands* a
contract on its operand — `total + n` demands `total : Number`, so `Number` **is** `I` for that
parameter; induction checks the recursive provider preserves it). Without F2 the fact still has a
shape but `I` has **no principled source**, so F3-first must **guess/generalize** `I`
(kind-abstract the argument, widen to a region). **That guess is the import in another hat** —
kind-collapse/widening was exactly "pick a coarse domain because the right one can't be derived." So
F3-without-F2 does not remove the import; it relocates it from the reaching fixpoint into
domain-selection. **Recommended staging: F1 → F2 → F3, full native, no shortcut.** (Open question §7.2
is thereby resolved toward full-native; F1-vs-F2 order in §7.1 still open.)

---

## 6. Verification gates (so green cannot lie again)

- The four blockers (`bodycheck.rs` tests, re-pinned) are the acceptance test. They may be
  un-ignored **only** when they pass with the region table + safety-fact induction and **no forward
  reaching fixpoint and no domain widening exist in the tree.** A grep gate (`summary.rs` absent;
  `check_recursive_body`/`reachable_rows`/`grow_pos` absent) is part of "done."
- No new `#[ignore]`→green transition on a body-safety test without the fact/demand mechanism behind
  it. If a case cannot be closed natively, it stays pinned with the blocking foundation named.
- Existing green stays green (371 lib / 111 conformance / 13 ignored); clippy clean.
- Property: analysis terminates on divergent programs **without execution** (the `loop()` gate),
  established by the §4a cutoff + fact lattice, not by fuel.

---

## 7. Open questions for the author

1. **Build order:** F1 before F2 (dependency-correct) vs your stated F2-first — confirm.
2. **Staging:** full-native (F1→F2→F3) vs minimal-first (F3 on today's induction to delete the
   import sooner, then F1/F2 to clean it) — pick.
3. **Safety-fact domain lattice:** region partition alone for v1, or wire grounding's **A-NEG
   derived basin** in as the domain source at the same time (C§10; grounding is built but unwired)?
4. **`where` safety:** E-8 makes `where` = `BodySafe(instance, DeclaredInput)`; do we land the
   `where`-driven safety fact as the first consumer (a real demand origin), or start with the
   call-site body check? (`where` gives a clean, source-authored demand to build against.)

---

*This document is the "how much breadth is owed" audit, done properly. No further body-safety
machinery should be built until F1–F3 are planned/built; the reverted import is the cautionary
instance. See `DECISIONS.md` (2026-07-31 revert entry), `OwedItems.md §0.1`.*
