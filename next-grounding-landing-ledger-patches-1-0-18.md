# NEXT — Grounding Landing: Ledger Patch Bundle (compendium 1.0.18 + satellites)

**Date:** 2026-07-30 · **Trigger:** the author's stamp on Grounding Specification v0.5 (patch 0.5.1, hash `195dd2b92cdbae1ebe5d1fb001bccd5adadfe280d0574d9529e688e7249bfc94`) — four hostile rounds (10 → 9 → 4 → 2 findings), final ACCEPTED with two remarks applied. This bundle contains the four flagged LEDGER CHANGES exactly as registered in the spec's §16; apply each to its file, then re-hash the four files into `MANIFEST_sha256.txt` alongside the spec's hash above. No rule content changes anywhere — status, pointers, one seat row, and one test phase.

---

## Patch 1 — `next-design-compendium-v1-0.md` → patch level 1.0.18

**(1a) Header:** change `current patch level 1.0.17 (2026-07-29; supersedes 1.0.16)` → `current patch level 1.0.18 (2026-07-30; supersedes 1.0.17)`, and append to the header's patch summaries:

> **Patch 1.0.18 (2026-07-30, status/sync — no rules changed):** Grounding Specification v1 DESIGN-CLOSED — `next-grounding-specification-v0-5.md` (patch 0.5.1; rounds one–four: hostile, hostile, substantively-accepted, ACCEPTED-with-remarks; author rulings 2026-07-30 recorded in its Appendix R1 addendum: demand-path recursion discovery, full dependency-graph and all-round-trips rules, GR-14 granularity confirmed, forwarder-collapse declined). C§17/J3 moved from owed to specified; Principle 9 stamp-blocker (4) SATISFIED; the application-spec seat row lands as patch 0.8.2; the test suite gains Phase GR.

**(1b) C§17 (the grounding block at "Grounding Specification v1 — design/specification owed…"):** change the block heading

> `**Grounding Specification v1 — design/specification owed [registered 1.0.10; inventory synchronized 1.0.11–1.0.16]**, sourced`

to

> `**Grounding Specification v1 — DESIGN-CLOSED [1.0.18]: `next-grounding-specification-v0-5.md` (patch 0.5.1) — implementation and §16 discharge owed**, sourced`

and append at the end of that block:

> **Landing [1.0.18]:** thirty rules GR-01–GR-30 over the eight-item package; the sound WorldDecided classifier specified (universal per-region seeding and propagation; SCC-scoped Layer-2 certificates; the whole-call label minted only by GR-26's four-stage aggregation); the exact dependency graph with orbit-prefix witness discipline; ProgressRange composition over the domain-indexed call-site multigraph with the stated Σ [N!/(N−k)!]·T^k bound; the program-expression read path with the closed operator inventory; thirty specimens seeded to Phase GR. §16 discharge obligations enumerated in the spec's §13; deferred-by-ruling items (basin derivation; finite-product chains; async) and P-1's open policy picks unchanged.

**(1c) J3** — replace the line

> `**Grounding specification v1 — owed [registered 1.0.10; synchronized through 1.0.16]:** the termination-decisions v4 package (see C§17's registration for the full inventory).`

with

> `**Grounding specification v1 — DESIGN-CLOSED [1.0.18]; implementation and §16 discharge owed:** `next-grounding-specification-v0-5.md` (patch 0.5.1; four rounds + acceptance; see C§17's landing note). Owed from it: the GR implementation with Phase GR; the §13 discharge list (exact-chain bound theorem; lex joint-settlement; multigraph decomposition lemma; per-rule soundness); the GR-27 executable preservation check.`

**(1d) Principle 9 annotation** — at stamp-blocker (4), after `…must be specified before stamping, since under rejection its coverage determines what compiles.` append:

> **SATISFIED [1.0.18]** — the package is specified and design-closed. Blockers (2) and (3) remain the open policy picks; blocker (1) closed at 1.0.14 with the classifier now specified. Current law (warn-and-compile) remains in force until the author stamps P-1 itself.

**(1e) Appendix M** — append the 1.0.18 entry (same text as 1a's summary, in the appendix's chronological format).

---

## Patch 2 — `next-application-induction-specification-v0-8.md` → patch 0.8.2

**(2a) Header:** prepend to the patch history:

> **Patch 0.8.2 (2026-07-30 — the flagged grounding-landing amendment, riding Grounding Specification v0.5 §16; one row + one aggregation note; no other rule touched):**

**(2b) Seat judgment (insert as an additional row/paragraph in step 6's completion demand):**

> **Effect-world completion evidence [GR-26; 0.8.2].** At an effect-world seat, completion evidence `WorldDecided(callee instance, I′)` (I′ covering the seat's represented callees over the seat's argument domain) is **admissible**, with the downstream-conditioning consequence: subsequent statements are world-conditioned by ordinary sequencing; no contract-side change. **The row consumes a classification — it never establishes one.** At pure- and mutation-world seats the evidence is **inadmissible** (by B5's matrix such callees cannot legally arrive; coarsened metadata presenting the possibility yields unproven — evidence is never invented). The whole-call completion result itself is established by the four-stage EvaluationCore aggregation of Grounding Spec GR-26 — witnessed-refutation precedence; the all-Grounded ordinary-completion case (no label minted); the mixed case minting `WorldDecided` only with at least one SCC-world-decided certificate; residual unproven — this row only consumes its output at the seat.

---

## Patch 3 — `next-test-suite-specification-v0-1.md` → add Phase GR

Insert after Phase A (same conventions: stable IDs, `#[ignore]`d stubs until the analyzer phase opens; verdict vocabulary ACCEPT/REJECT(witness)/GRAY per the header, with GRAY carrying Principle 9's current law):

> ## Phase GR — Grounding verdict suite (specified 2026-07-30; Grounding Specification v0.5 §15; runs when the analyzer phase opens)
>
> One test per spec-§15 specimen, IDs `GR-01`–`GR-26` and `GR-22b`, `GR-27`–`GR-30` mapping to specimen numbers 1–30 (22b keeps its letter). Expected verdicts are the spec's table verbatim — proven → ACCEPT; refuted → REJECT(witness as stated); unproven → GRAY under current law (flips to REJECT if P-1 stamps rejection; the tag rides the P-1 status, not the test). Highlights: `GR-03a` REJECT(witness `[3,7,2]`); `GR-12` REJECT(witness `1`, grid); `GR-22b` REJECT(witness `[7]`, dependency cycle with proven prefix); `GR-29` GRAY (no false cycle refutation); `GR-30` ACCEPT with ordinary completion, **no** WorldDecided label; `GR-14`/`GR-15` the classifier pair (broad GRAY, narrowed ACCEPT).
>
> **GR-EX-01 [executable at tuple-procedure time, before the analyzer]:** the GR-27 preservation check — `Repeat(NotEquals(v))` closed under element projection, `rest`/suffix, and slice per the tuple-family and subcontract procedures; derived length `GE(0) ∧ Mod(1,0)` with peel drift −1. This is the standing Claude Code verification task registered by the handover.

---

## Patch 4 — `next-termination-decisions-v4.md` — footer pointer

Append to the footer:

> *Discharged: the grounding specification drafted from this note is `next-grounding-specification-v0-5.md` (patch 0.5.1) — DESIGN-CLOSED 2026-07-30 after four rounds (dispositions in its Appendices R1–R4); compendium 1.0.18 registers the landing.*

---

## Manifest additions

After applying, append/refresh in `MANIFEST_sha256.txt`:

```
195dd2b92cdbae1ebe5d1fb001bccd5adadfe280d0574d9529e688e7249bfc94  next-grounding-specification-v0-5.md
<re-hash after patch>  next-design-compendium-v1-0.md
<re-hash after patch>  next-application-induction-specification-v0-8.md
<re-hash after patch>  next-test-suite-specification-v0-1.md
<re-hash after patch>  next-termination-decisions-v4.md
```

*End of bundle. Four patches, zero rule changes; the author applies and re-hashes.*
