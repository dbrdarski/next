# OwedItems.md — CLOSED (2026-07-18)

All four items resolved; this registry is retired. Resolutions below, each with its
normative home. New normative gaps found during implementation open a fresh registry.

## 1. Tuple-length / concatenation contract family — **CLOSED [shipped, design-closed]**
Specified as `next-tuple-length-family-specification-v0-3.md` (+ patch 0.3.1);
three external review rounds; **C§17 discharge confirmed round three.**
Implementation notes: `Concat` joins the algebra (positive per segment); `Repeat`
derived via C§9; lengths are stamped `(NumberContract, Exact | Approx)` under
Λ-semantics; the weighted-graph SCC solver with closed-walk periods; segment
alignment with `ElementRefutation` witnesses; `LengthRestricted(T, D)`; the
compositional grapheme transition summary. Replace the analyzer's Top-for-spread
with the derived shapes; suite TL-01a…TL-22.

## 2. Print doctrine for structure interpolation — **CLOSED [ruled: user, 2026-07-18]**
**Interpolation is total; the `unprintable-interpolation` trap is deleted** (13 trap
classes remain). Renderings: Tuple/Record as canonical literal forms (sorted-key
records, B2 numbers, quoted-and-escaped inner strings); `<Function>`;
`<Indeterminate _/0>` / `<Indeterminate 0/0>` — the form, never operands.
`parse ∘ print = identity` on the literal fragment is a harness law. Move the
accept/reject boundary out of `analyze_template` entirely; update `stringify`;
suite PR-01…05. Normative home: semantics companion §Template + Compendium E1.

## 3. `analyzeOperation` application table + interprocedural return induction — **CLOSED [shipped, design-closed]**
Specified as `next-application-induction-specification-v0-8.md` (+ patch 0.8.1);
eight external review rounds. The seven-step application rule over joint correlated
`AnalysisContract` operands; γ-concretization with the Known/Unknown lattice and
certified-only `intersectA`; the traversal-free instance inventory and the
environment-qualified cutoff ladder; per-row-grounded domain-indexed facts; the
deterministic candidate closure with one-pass SCC vector induction; `ApplicationOutcome`
with three-valued completion evidence; the seat/world-independent `EvaluationCore`
cache value (Compendium 1.0.8). Lifts the deferred behaviors: open-call returns,
unknown-callee admission, non-mutator completion. Suite AP-01…30.

## 4. First-class function-shape (arrow) contract — **CLOSED [dissolved, user-confirmed]**
Not a gap: the algebra has **no arrow constructor by design** (Compendium C§4).
Higher-order precision flows through analysis-instance metadata under Transparent
modularity — per-call-site obligations and refinements strictly tighter than any
declared arrow. The residue Claude Code needed is item 3's coarsening row: instance
metadata unrecoverable at a seat ⇒ **unproven there**, never a synthesized arrow.
Traded away, knowingly: declaration-as-documentation for HOF parameters (doc
comments carry it). A boundary-interface arrow could re-enter only with C§14's
contracted-boundaries opt-in.

## Related author-flagged opens — status at closure
Open-value group identity: **ruled** (strict openness; contagious; observation of
open values is a compile error — Compendium B4, μ package). Record openness:
**ruled** (`Record(fields, Exact | Open)`; exact everywhere users write; open =
derived demands only; `HasField(k)` ≡ `Record({k: Top}, Open)`). Mutator returns:
return-nothing law stands; the returns-leaning remains a tagged extension point.
Module in a value seat: clear error, unchanged.

*Registry closed against Compendium v1.0 patch 1.0.8 (frozen). The arc's event log:
Appendix M; the review rounds: the session transcripts.*
