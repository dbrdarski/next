# Technical debt

Implementation defects **I own** — waste, redundancy, and cost profiles that are not
mandated by any specification and that no design ruling is waiting on. Distinct from:

- `OPEN-DECISIONS-*.md` — decisions waiting on the author.
- `OwedItems.md` / the normative ledgers — design-owed work.
- `DECISIONS.md` — the chronological implementation record.

Nothing here changes behavior or verdicts. Each entry states what was **measured**, not
what is suspected.

---

## TD-1 — The body is analyzed three times per `where` (and three times per call seat)

**What.** `analyze_where` (`src/analyzer/program.rs`) raises three separate judgments over
the same function body and the same declared domain, and each one re-walks the whole body
from scratch:

1. `safety::prove(callee, &args, …)` — body safety,
2. `safety::completes(callee, &args, …)` — the E10 completion half,
3. `demand::returns(…)` → `check_return_claim` → `prove_claim(…, Claim::Return(…))` — the
   declared return.

The ordinary call seat does the same: its safety, completion, and produced-contract
judgments each walk the body independently.

**Measured (2026-08-05).** Temporary trace on every block binding, run over
`pricing2.next` (a five-parameter function, six-step body):

- with `where (Plan, Size, Boolean, Boolean, Boolean) => Number` — **4 walks** of the body:
  **3** over the declared domain (the three judgments above) plus **1** at the concrete
  call site;
- with the `where` line deleted — **3 walks**, all at the call site.

So the `where` costs three full body analyses, and each call seat costs three more (the
with-`where` case shows only one call-site walk because the earlier declared-domain passes
have already warmed the fact cache — evidence that the redundancy is *partly* absorbed by
memoization at some seats and not at others).

**Why it is debt, not architecture.** E11 mandates the *content* — "the assertion holds iff
running the ordinary body check under the whole declared input proves every body demand
safe" — and says nothing about running that check once per judgment. One walk already
produces all three answers: `Analysis` carries `contract`, `annotated`, `findings`,
`safety_demands`, **and** `completion` together. The three judgments are three readings of
one result, not three analyses.

**Cost shape.** Linear in body size × number of judgments, and it multiplies against
whatever the operation rulebook costs per node — so it is worst exactly where analysis is
already most expensive (wide declared domains, deep bodies).

**Fix shape, and the caution that goes with it.** Analyze the body once per `(instance,
domain)` and adjudicate all three judgments from that single `Analysis`. The merge is *not*
purely mechanical: `safety::prove` runs the partition machinery under the induction
hypothesis stack, while `prove_claim` enters with `Claim::Return(…)`; the fact-cache and
hypothesis interactions must be checked before collapsing them, or a settlement could
publish under an ambient hypothesis it should not (the taint rule in
`factcache::finish`). Any such change needs the full suite plus the hypothesis-taint pins.

**Status:** open, unscheduled. No correctness consequence — the verdicts agree; this is
pure waste.
