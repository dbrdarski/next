# DRAFT — Branch sets and routing (v0.1)

**Status: DRAFT, not adopted, no author stamp.** Written 2026-08-07 to be attacked. It
formalizes what survived a working session on A6 (hull vs distribution); several
mechanisms proposed during that session are **killed here on purpose** (§10), because they
answered questions the language never asks.

**Provenance tags.** `[author]` — the author's ruling, given in session. `[measured]` —
observed by running the implementation or a prototype; the program is cited.
`[drafted]` — systematization by the drafter, unratified. `[open]` — undecided.

**What it is for.** Today an operation over a multi-member domain widens its operands to
an interval (the "hull"). That is sound but imprecise, and under reject-on-unproven the
imprecision becomes a **rejection of correct programs** — measured: `hull.next`, a total
function, rejected over its own declared domain. This draft describes the alternative that
survived scrutiny.

---

## 1. The object

**BR-01 — Class [drafted].** A **branch set** is analyzer-side metadata. It is **not** a
contract, is never interned, and never rides on a value. Contracts are interned with
pointer equality by constitution (B1); a branch set carries conditions on source variables
and therefore cannot enter the value domain. Its natural home is beside instance metadata
in `AnalysisContract`. **[open]** — exact representation.

**BR-02 — Origin [measured].** Branch sets arise from **one** place: a match whose
scrutinee domain has more than one member, where more than one row survives the remainder
walk. Program `pricing3.next` (no `where`) versus `pricing2.next` (with one): without a
declared domain every argument at every seat is a singleton, every match selects exactly
one row, and **no branch set ever exists**. Traced 2026-08-05.

**BR-03 — Cells and the cell index [drafted].** Every node has a **cell index**: the tuple
of *sources* it transitively depends on. A **cell** is one assignment of those sources; the
node has one value per cell. `rate` over `plan` has 3 cells; `monthly = rate * seats` has
index `(plan, size)` and 6 cells; a node built from `rate` twice still has index `(plan)`
and 3 cells.

**BR-04 — Correlation is structural, not a rule [drafted].** BR-03 makes correlation
automatic: within a cell every source has exactly one assignment, so both operands of an
operation are read at the same assignment. `rate + rate` over `rate ∈ {0,5,20}` has cells
`{0, 10, 40}`, never the cross-product `{0,5,10,20,25,40}`. **This is strictly more precise
than eager union distribution**, which discards the provenance and must admit `0+20`.

**BR-05 — Laziness [drafted].** A node's cells are **not** evaluated at its defining line.
The node records its operation and operand nodes. Nothing is computed until §4 demands it.

---

## 2. What is asked of a branch set

**BR-06 — Routing is the only question [author].** A match asks a branch set exactly one
thing: **for each arriving branch, which arm does it select?** Everything else is an
aggregate of that answer —

- *exhaustive?* = every arriving branch selected some arm;
- *arm dead?* = no arriving branch selected that arm.

**BR-07 — Nothing else is asked [author, corrective].** In particular the seat does **not**
ask "can this node ever be *X*?" as a primitive. That question was prototyped, measured,
and **killed** (§10.2): it is an aggregate of routing, not an input to it.

---

## 3. Routing

**BR-08 — Routing demand [drafted].** A branch is routed only when some arm's analysis
depends on *which* branches arrive at it. An arm whose body is source-independent (a
literal, a closed expression) needs only its **reachability**, not its arriving set. This is
the rule that keeps routing off the hot path for ordinary code.

**BR-09 — Narrowing by arrival [measured].** Within an arm, the live branch set is the
arriving subset, and **every source and every derived node narrows to its cells on that
subset simultaneously**. In

```
rate = p :: { "pro" => 20  _ => 0 }
d    = rate * 2
=> d :: { 40 => rate   _ => 20 }
```

the row `Equals(40)` is reached only by the `pro` branch, so inside that arm `p = "pro"`,
`rate = 20`, `d = 40` — all at once, with no inversion. Compare the measured baseline:
`direct = (n) => n :: { 2 => n … }` proves `⊑ Equals(2)` today (the region table narrows a
direct guard), while the version through an operation does not.

**BR-10 — Lookup strategy [author].** Given the arriving branches and the arm list, a
branch finds its arm either

- **by key** — when arms are literal values, they form a lookup table and a branch's value
  indexes straight to its arm, one step, exactly like a record property access; or
- **iteratively** — walking arms in source order and testing each.

**BR-11 — First-match is preserved [drafted].** Keying is available only where it cannot
disturb source order. A literal arm may be shadowed by an *earlier* non-literal arm
(`{ Number => a  4 => b }` sends `4` to the first arm). Therefore: arms form a keyed table
only from the position after the last preceding non-literal arm; anything earlier is
scanned in order first. **[open]** — whether to also key contract arms by kind.

---

## 4. The hull, retained as an accelerator

**BR-12 — The hull stays [author].** The interval (with whatever congruence the rulebook
already carries) is retained — **not** as the value a consumer reads, but as a free
pre-routing filter.

**BR-13 — Its two sanctioned uses [drafted, from the over-approximation law].** The hull
over-approximates: `true ⊆ hull`. Therefore it may

1. **eliminate an arm before any routing** — `armValue ∉ hull` ⇒ no branch can reach it ⇒
   the arm is dead. *(refuting an existential — sound)*
2. **prove exhaustiveness before any routing** — `hull ⊆ arms` ⇒ `true ⊆ arms` ⇒ every
   branch lands. *(proving a universal — sound)*

**BR-14 — Its two forbidden uses [drafted].** It may **not** refute exhaustiveness
(`hull ⊄ arms` says nothing about the truth — this is the current false-rejection bug), and
it may **not** establish an arm reachable (`armValue ∈ hull` says nothing). Under
reject-on-unproven the first is indistinguishable from an unsound claim at the seat, which
is why the hull may never be the last word.

---

## 5. Collapse

**BR-15 — Collapse points [drafted, open in detail].** A branch set's conditions are
meaningful only where its sources are in scope. It collapses to an ordinary contract — the
join of its cells — when the value escapes: returned across a function boundary, stored in
a structure, or reaching a **recursive** boundary, where resolution goes through a *fact*
and a fact is a contract. Recursion is therefore not a separate mechanism; it is a collapse
site. **[open]** — the precise inventory of escape sites and whether a collapsed set may
retain any summary.

---

## 6. Cost, stated honestly

**BR-16 — What is saved, and what is not [measured + drafted].**

- A value **no match routes** — consumed only by a coarse demand such as `⊑ Number` — costs
  **zero**: no cell is ever evaluated. Eager distribution pays the whole chain regardless
  (146 rule applications on the six-line pricing chain).
- A value **a match routes**, whose arm bodies depend on sources (BR-08), costs its **cell
  count**. There is no cleverness that avoids this: routing is the work.
- Between them sit the hull's two shortcuts (BR-13), which can settle exhaustiveness or kill
  an arm with **no** routing at all.

So the saving is not asymptotic. It is: *pay nothing unless a match actually needs to route,
and let the hull settle what it soundly can before routing begins.*

---

## 7. Worked examples

**E1 — the flagship, rejected today.** `rate ∈ {2,1}`, `doubled = rate * 2`,
`doubled :: { 2 => 10  4 => 20 }`. Cells of `doubled`: `{4, 2}`. Both route; both arms hit;
exhaustive. Today: the hull yields `Range(2,4) ∧ Mod(2,0)`, the remainder walk cannot prove
the leftover empty, and a **total function is rejected** (`hull.next`, measured).

**E2 — the narrowing case.** §3's `d :: { 40 => rate }`. Arrival narrows `rate` to `20`
with no inversion. Rejected today (`branchy.next`, measured).

**E3 — correlation.** `rate + rate` over `{0,5,20}` has cells `{0,10,40}` by BR-03/BR-04.
Eager distribution gives `{0,5,10,20,25,40}` — sound but wrong-in-spirit, admitting sums no
execution produces.

**E4 — the hull earning its keep.** `perms ∈ [0, 8191]` (13 flags) with an arm `9000`:
BR-13(1) kills the arm in one comparison, **no branch routed**. With an arm `4095` the hull
is inconclusive and routing decides.

---

## 8. Relation to A6

This draft is a candidate answer to A6 (`OwedItems` Thread D). It **removes the hull as the
answer-producing rule** (BR-14) and **keeps it as an accelerator** (BR-12) — the author's
stated position — and replaces eager union distribution with branch sets that are more
precise (BR-04) and cheaper when unrouted (BR-16).

---

## 9. Obligations a discharge would owe

1. A concretization γ for branch sets, and soundness of BR-09's narrowing over it.
2. Soundness of BR-13's two uses and a proof that BR-14's two are excluded.
3. Order-independence: routing results identical regardless of demand order and cache warmth
   (AP-10's discipline).
4. Termination **without a budget**: routing is bounded by the finite cell count; collapse
   at recursive boundaries is what keeps that finite. To be proved, not asserted.
5. Interaction with fact keys: a node routed at one seat and coarse at another must not key
   inconsistently. This is the failure mode that has already occurred once in this project.

---

## 10. Killed — do not reintroduce

**10.1 Preimage / backward inversion.** Pulling an arm's region back through an operation to
narrow a source. **Killed [author]:** BR-09 gives the same narrowing for free, and gives it
for *every* variable at once, where preimage narrows one per inversion and needs a rule per
operation, a fence for two-varying operands, and a widening story for non-invertibles. The
example that motivated it (`n : Number`, no branches) was outside the model.

**10.2 The backward existential search.** Answering "can this node be *X*?" by pushing the
target through the operation with hull pruning. Prototyped and measured — 17 operations
against eager's 131,068 at 65,536 combinations — and **killed anyway [author]:** no seat asks
that question. Routing must visit every branch a body depends on (BR-08), so a search that
avoids visiting them answers nothing the match needs. The measurement stands; the customer
does not exist.

**10.3 Eager union distribution as the operation rule.** Superseded by BR-03/BR-04, which are
more precise.

**10.4 Fuel, budgets, and search over unknowns.** Nothing here searches. Routing enumerates a
finite, structurally-determined set.

---

## 11. Open

- **BR-01** representation and where branch sets live.
- **BR-11** whether contract arms can be keyed by kind.
- **BR-15** the escape-site inventory.
- Cost at large cell counts when BR-08 *does* demand routing — the honest residual problem,
  with no mechanism proposed here.
- Whether the union-emptiness gap (three exact point arms over a three-member union are not
  proven exhaustive — measured 2026-08-06) is subsumed by BR-13(2) or needs its own fix.
