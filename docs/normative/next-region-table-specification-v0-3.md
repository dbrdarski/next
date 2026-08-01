# NEXT — Region-Table Computation Specification v0.3 (patch 0.3.1)

**Date:** 2026-07-24. **Patch 0.3.2 (confirmatory review round four — architecture ACCEPTED, “architecturally closed”; four editorial/precision edits, no mechanism change):** direct `!= constant` spelled in the case-(a) inventory; negated-unsupported-leaf fallback to case (d) made explicit; “genuinely possible” → “conservatively possible (not proven impossible)” to match the witness bridge; lineage corrected (0.3.1 supersedes v0.3, which superseded v0.2). **Patch 0.3.1 (hostile review round three — architecture confirmed “architecturally settled”):** one soundness blocker — a **non-singleton pin** is relational and must not be marked exact merely for being a pattern (it is the pattern analogue of a two-variable guard) — fixed by routing pattern regionalization through the same `(region, exact)` bit; plus three no-new-mechanism corrections — the selection/witness bridge to C§13.2, case (b)'s finite operator transfer table, and compound-negation De Morgan normalization. No redesign. **Supersedes v0.3** (which superseded v0.2 after review round two). The forward-reading core of v0.2 was
endorsed (the previous review's two-sided `{mayTrue, mayFalse}` proposal was formally withdrawn — one forward
may-reach region per arm is enough). Round two found the residual flaws, and every one of them makes v0.3
**smaller** than v0.2:

- **Blocker (selection):** v0.2 let an *exact argument* resolve first-match into an *uncertain* row's
  may-region — unsound (`check(50)` with `cap ⊑ LE(100)` could pick `accept` though `cap` might be `5`). Fixed
  by one **`exact` bit** per row and an ordered remainder walk in which **only exact rows consume**.
- **Blocker (§6):** v0.2's accepted-domain law `Difference(demand, guaranteeOf(region))` was **algebraically
  false** under NEXT's `Difference` (`Difference(A,A) = Bottom`, not `Top`) — it invented a second meaning for
  the set-exclusion constructor. **Deleted.** Accepted-domain is the separate spec's job; this document does
  not compute it and carries no scaffolding for it.
- The per-row **`demand` slot** and the `liftConstraint` named procedure are removed as premature/over-
  specified; the wildcard special case is removed (it falls out of the walk); guard-demand existence is
  restated as **settled** (E10 + C§7), not open; "disjoint from one call" is separated from "statically
  unreachable branch"; the cache rule is stated on the **annotated** tuple; case (a) is tightened; two typos
  fixed.

**Scope.** This document computes **branch reachability** — *where an input may go* — as an ordered table of
`(region, exact, resultExpr)` rows, plus the selection walk that consumes them. It does **not** compute
`InferredAcceptedDomain` (*which inputs are safe*); that is a separate, deliberately small specification which
**consumes this table** together with the ordinary operation demands of guards and bodies (§6). The two share
control-flow information and need no cross-layer algebra.

---

## 1. What a region table is, and why it waits for instantiation

A lambda body's control flow — its `::`/`?:` arms, guarded exits — sorts the parameter's possible values into
regions, each with a result expression. When every guard mentions only the parameter and constants, the sort
is computable at **shape** time (compile time, once per lambda text). When a guard mentions a **captured**
name, it cannot finish until the closure is built, so the shape holds the guard **symbolically** and the sort
completes at **instantiation**, when the capture contracts arrive (C§12.3 layer 3). The completed sort is the
**region table**, cached per C§13.4.

```
makeCounter = (limit) => (n) => n <= limit ? count(n) : done
c = makeCounter(5)          // limit = Equals(5)
    row 1:  region LE(5)  exact  →  count(n)
    row 2:  region GT(5)  exact  →  done       (from !(n<=5) read forward)
```

This is §E9's match/remainder behavior, run **after** capture substitution, with the forward construction (§2)
that keeps it sound when a substituted guard is uncertain, and the `exact` bit (§3) that keeps selection sound.

## 2. Construction — read each guard forward, one may-reach region per arm

**The rule:** a row's region is its own guard, substituted and read forward as a constraint on the parameter,
intersected with the row's pattern region (§4). Rows are in source order. **No row is built by subtracting
earlier rows.** Rows may overlap; overlap is the honest statement that, for those inputs, more than one branch
is **conservatively possible (not proven impossible — matching the §3 witness bridge, not a realizability claim)** [0.3.2]; the ordered walk (§3), not the table, resolves which one runs.

Reading a substituted guard forward has these cases — the whole of *"the regionalization law"* — each also
determining the row's `exact` bit (§3):

**(a) A supported comparison of a parameter projection against a constant — exact.** After substitution the
captured operand is a singleton `Equals(v)`, and the comparison is one of the **fixed regionalizable forms**
(`n <= v`, `n == v`, `n < v`, ` n >= v`, `n > v`, the direct projections the inventory lists, and **`n != v` → `NotEquals(v)`, exact** [0.3.2 — or, equivalently, source `!=` normalizes to `!(==)` before regionalization]) against that constant. `n <= limit` with `limit = Equals(5)` → `LE(5)`, **exact**. This is C§12.3's constant-parameter
extraction; it loses nothing and is the common case. *Only supported direct forms qualify* — see (d) for the
rest.

**(b) A supported comparison of the parameter against a non-singleton capture — may-reach, not exact.** The
captured contract is a range/half-line. `n <= limit` with `limit ⊑ LE(100)` reads forward to `LE(100)`: the
branch *may* run only where `n ≤ 100`. This is a sound over-approximation of "may run," **not** "does run," so
its `exact` bit is **false** — and because uncertain regions are never subtracted or used to resolve
first-match (§3), that is all the caution needed. **The finite operator transfer [0.3.1 — not left to intuition],
for capture `≤/≥/Range` contracts** (a fixed lookup, not a solver): `n < limit` → governed by the capture's
**upper** endpoint (`limit ⊑ LE(U)` or `Range(L,U)` → `LT(U)`; unbounded above → `Top`); `n <= limit` → upper
endpoint, closed (`→ LE(U)`); `n > limit` → **lower** endpoint (`limit ⊑ GE(L)` or `Range(L,U)` → `GT(L)`;
unbounded below → `Top`); `n >= limit` → lower endpoint, closed (`→ GE(L)`); `n == limit` → the capture's own
possible-value contract projected onto `n` (`Range(L,U) → Range(L,U)`); `n != limit` → `Top` (for any `n` some
represented `limit` may differ). All non-exact. Any capture contract or operator outside this table falls to case
(d). (If a broader per-operator table is later centralized — the C§17 per-pair tables — this delegates to it.)

**(c) The parameter related to another unbounded value — opaque, not exact.** Two unbounded operands: an
unbounded capture, or **another parameter** (`(n, limit) => n <= limit ? …` — opaque *even with zero
captures*). No unary bound reads out; region `Top`, `exact` false. The relation is real but not a unary
contract (C§5: relations are outside the algebra). §7 records a non-adopted refinement.

**(d) Anything else — the total fallback, not exact.** Any guard leaf outside the fixed regionalizable
inventory — a non-trivial expression on the tested side (`n * n <= 5`, `foo(n) <= 5`, `n.field <= 5`), an
unsupported predicate — reads to region `Top`, `exact` false. Constant substitution does **not** by itself give
an exact preimage; only the listed direct forms of (a) are exact. This makes the construction **total**: every
guard yields some region, never a stuck state, and `Top`/non-exact is always sound.

**Compound guards** combine leaf regions by the ordinary algebra — `&&` → Intersection, `||` → Union, `!` →
the forward-read negation (§3a) — and are **exact iff every contributing leaf is exact** (a conservative rule;
more precision is recoverable later if simplification proves it, but is not needed for soundness). An opaque
leaf contributes `Top` and makes the compound non-exact.

### 3a. Negation — read the flipped comparison

**Compound negation normalizes structurally first [0.3.1]:** the symbolic template pushes Boolean negation inward by De Morgan — `!(A && B) → !A || !B`, `!(A || B) → !A && !B`, `!!A → A` — until negation sits on comparison leaves, then each leaf is forward-read. **After normalization, a negated leaf that is not an invertible supported comparison falls to case (d): `Top`, non-exact [0.3.2 — totality made explicit]** (e.g. `!pred(n)` for an unsupported `pred`). So `!(n <= limit)` is the forward-read of `n > limit`, **never** `Difference(Top, region-of(n <= limit))`; So an
opaque guard's negation is `n > limit` read forward — also opaque (`Top`), never `Difference(Top, Top) =
Bottom`. An exact guard's negation is its exact complement (`!(n <= 5)` → `GT(5)`, exact). **Invariant:** no
boolean operator turns an unknown-either-way guard into a proof; opacity is preserved through `!`, `&&`, `||`.

## 3. Selection — the ordered remainder walk (exact rows consume, uncertain rows do not)

First-match is a property of the **walk at selection**, not baked into the table. The walk carries a
`remaining` domain and, crucially, **only exact rows subtract from it**:

```
remaining = argumentDomain
for row in source order:
    candidate = remaining ∩ row.region
    if candidate is not proven empty:
        select / evaluate row on candidate
    if row.exact:
        remaining = Difference(remaining, row.region)
    // uncertain rows consume nothing
```

The reasoning: an **exact** row's region *exactly* characterizes its match, so inputs in it are definitely
consumed if execution reaches the row — subtract them. An **uncertain** row's region says only *may*, so it
consumes nothing abstractly — leave `remaining` unchanged. This is E9's "opaque guards do not consume,"
generalized from fully-opaque guards to *every* non-exact forward region. It is the single fix for v0.2's
blocker:

> **The v0.2 blocker.** `check = makeCheck(cap)`, `cap ⊑ LE(100)`; rows `[LE(100) accept, Top reject]`;
> call `check(50)`. `50 ∈ LE(100)`, so v0.2's "exact argument picks earliest containing row" fired **accept**.
> But `cap` might be `5`, making `50 <= 5` false and **reject** run. The argument's exactness cannot repair the
> capture's uncertainty. Under the walk above, row 1 (accept) is uncertain (`exact=false`, case (b)), so it is
> *selected* (candidate non-empty) but **consumes nothing**; `remaining` stays `Top`; row 2 (reject) is also
> selected. Both branches are carried — the honest answer — and the ApplicationOutcome join (C§13.2) unions
> them. No branch is falsely resolved.

**Selection is possible reachability, not an execution witness [0.3.1 — bridge to C§13.2].** `candidate ≠ Bottom`
establishes only that the row *may* execute — and this holds even for an *exact* row when an earlier non-exact row
is still live (for some represented environments the earlier row matches first, so the later never runs). A selected
candidate is therefore valid for **produced-value over-approximation**, but is **not by itself** evidence for
safety refutation, completion `ProvenPresent`, or any other existential-execution claim: those remain governed by
C§13.2's **jointly represented witness** requirement (analyzing a selected row's body over its conservative
candidate and finding an invalid operation does **not** authorize `Refuted` — that is the “projection invents a
witness” error the application package already forbids). No region-table witness plumbing is added; the existing
rule is cited. — Uncertainty **widens** selection (an uncertain or overlapping row stays selectable), never narrows
it; no region can *exclude* a value. When several rows are selected and the exact runtime value is known at compile
time *and the selected rows are exact*, the walk resolves to the earliest satisfied one; when uncertainty is
present, the selected rows are carried and their results joined.

**No wildcard special case.** An unconditional final arm is `region = Top, exact = true`. After earlier exact
rows have subtracted their regions, its `candidate = remaining ∩ Top = remaining` — exactly "everything not yet
claimed." If earlier rows were uncertain (consumed nothing), the wildcard stays conservatively live, which is
correct. v0.2's special `Difference(Top, prior exact regions)` for the wildcard is therefore **deleted** — the
walk already produces it.

## 4. Patterns — every row is pattern ∩ guard; and per-call vs source-unreachable

An arm has a **pattern** and an **optional guard**. **Pattern regionalization yields the same `(region, exact)`
distinction as guard regionalization [0.3.1 — patterns are NOT universally analyzer-exact]:** pattern matching
is exact *at runtime*, but its *contract regionalization* is approximate exactly when a pattern depends
**relationally on another non-singleton binding** — the pin. Literal, wildcard, structural (tuple/record), and
contract patterns are exact under their ordinary contract translation. A **pin** `^name` is the pattern
analogue of a two-variable guard: **singleton binding** (`name = Equals(v)`) → `region Equals(v)`, **exact**;
**non-singleton binding** (`name ⊑ C`, C not a singleton, e.g. `name : Number`) → the relation `x == name`
cannot be a unary contract on `x` (C§5) → `region Top` (or a tighter derivable may-region), **not exact**.
**Pattern alternatives** `p₁ | p₂ | …` (E9): `region = Union(region(pᵢ))`, `exact = ⋀ exact(pᵢ)` (conservative —
precision loss only, sound and finite). The row's region is **`patternRegion ∩ guardRegion`** (both forward-read,
on the argument tuple, §5), and its `exact` bit is **`pattern.exact && guard.exact`** — the formula v0.3 already
anticipated, now with the correct pattern definition. Unguarded arm → guard region `Top`, exact, so the pattern's
own `(region, exact)` rules. **Why this matters [the 0.3.1 blocker]:** were a non-singleton pin marked
`region Top, exact true`, the walk would let it consume the whole remaining domain and kill later arms — but at
runtime `x != name` must reach the else arm. Marking it non-exact makes it consume nothing, exactly as E9's pin
rule already implies (singleton contracts consume their point; runtime/non-singleton values consume nothing
provable). No new pattern abstraction — the existing `exact` bit carries it.

**"Disjoint from this call" is NOT "statically unreachable branch" [review].** A row whose region is disjoint
from *a particular call's argument* is simply **not selected by that call** — ordinary non-selection, no error.
The §E9 unreachable-branch diagnostic applies only when the branch's **remaining source domain** is proven
empty *after first-match consumption over the function's whole parameter domain* — a property of the function,
not of one caller. For `f = x => x :: { Number => 1  String => 2 }`, the call `f(5)` leaves the `String` row
unselected (fine); the `String` branch is *not* unreachable, because *some* input reaches it. The two must be
kept distinct: **source-domain-empty after consumption → unreachable-branch error; disjoint from one call's
argument → non-selection.**

## 5. Argument-tuple representation

Guards and patterns are written over **named parameters**; selection is against the **argument-tuple** contract
(C§E3 — one contract over the complete argument tuple, correlated alternatives never flattened). The template
knows how each bound name corresponds to a position in the argument tuple through its parameter pattern
(including destructuring — `([first, ...rest]) =>` binds `first` at the head of the first argument). **The
normative requirement:** every regionalized parameter constraint is represented on the complete argument-tuple
contract using that existing parameter-pattern binding projection — a constraint on a bound name becomes a
contract at its position, `Top` elsewhere. (This is ordinary projection; it needs no separately named procedure
in this specification.)

## 6. The boundary — accepted-domain is a separate specification

**This document computes reachability only.** `InferredAcceptedDomain` — which inputs are *safe* — is derived
by a separate, deliberately small specification that **consumes this table** (the ordered rows, their regions,
their `exact` bits, the selection walk) together with the ordinary operation demands of guards and bodies
(C§7). It is not computed here, and this document carries no field or law for it. The two specifications share
control-flow information; they need no cross-layer algebra. (v0.2's §6 law and per-row `demand` slot are
deleted — the law was algebraically unsound under NEXT's `Difference`, and the slot was premature scaffolding.)

Two facts fix the boundary so the separate spec is not mis-scoped:

- **Guards impose demands — settled, not open [E10 + C§7].** Evaluating a guard is an ordinary computation with
  ordinary safety demands: `x.field > limit` demands `x` admit field access, the comparison operands satisfy
  comparison requirements, and the result satisfy Boolean testedness (E10: guards are strict Boolean-tested
  seats). *That guards impose demands is settled.* What remains for the accepted-domain spec is only **how those
  demands project back to the complete input tuple**, and that guard demands apply *on the path that reaches the
  guard* — before either branch is selected — so they are **not** attributable to any one arm's result (a
  further reason no per-result `demand` slot belongs here).

## 7. Termination and caching

Finite and non-iterative. A shape has finitely many arms (bounded by program text); reading each guard/pattern
forward is one pass; the algebra operations terminate. No fixpoint, no search (Principle 7, C§13.3). The
**template** carries the symbolic arms, their parameter-tuple positions, and the pre-analysis of each leaf's
case (a)/(b)/(c)/(d) and exactness; **instantiation** is finite substitution plus fixed local transfer. The
result caches in the **instance cache** (C§13.4).

**Cache identity [review — annotated, not plain].** The key is `(shape, annotated captured-environment
AnalysisContract tuple)`. **Same shape + same *annotated* tuple → one entry.** It is *not* sufficient that the
coarse contracts match: two captures may share a coarse `Kind(Function)` while carrying different
analysis-instance metadata, and the annotated tuple is part of the key precisely so those states are not
conflated. (Stating it on plain contracts has caused bugs elsewhere; the rule is the annotated tuple.)

## 8. Future refinement — the held-relation suspension (NON-NORMATIVE, believed sound, NOT ADOPTED)

> Records a refinement of case (c) explored 2026-07-24, believed sound under the stated boundary, deliberately
> deferred; parked so the boundary that keeps it safe is not lost. Absent it, case (c) is opaque, full stop.

Case (c) throws the relation away, but `n <= limit` is a *suspended computation* that would force to a unary
contract the moment either operand gains a constant bound. A lazy analyzer could **hold** it as a branch-local
assumption and force it if a bound arrives later in the same arm (the recursion move: analyze the suspension,
don't expand it). If ever adopted: assumptions are arm-scoped, **never enter the contract algebra or ride on
any interned value** (so canonicalization is untouched — these are arm-context assumptions, not value-borne
contracts, so the permanent exclusion of relational *contracts* is not violated), consulted **only by
comparison guards, never arithmetic** (so they cannot breed), and — the whole safety boundary — **a suspension
forces against *forced* facts only, never another suspension** (transitivity through a forced bound: yes;
chaining suspensions: no — that rebuilds polyhedra). The single benefit is **deferral, not solving**. It is a
*precision* refinement, not a correctness requirement of the committed table; parked pending evidence real code
hits it.

## 9. Worked examples

**W-1 — singleton capture (a), exact complements.** `makeCounter(5)`: row 1 `LE(5)` exact → `count(n)`; row 2
`GT(5)` exact → `done` (from `!(n<=5)` forward). Disjoint by exactness. Walk: exact rows consume; a concrete
`n=2` selects row 1 and consumes `LE(5)`; `n=9` falls to row 2.

**W-2 — bounded-range capture (b), overlap, uncertain rows consume nothing.** `makeCheck(cap)`, `cap ⊑ LE(100)`,
inner `n <= cap`: row accept `LE(100)` **not exact**; row reject `Top` (from `n > cap`, `cap` unbounded below)
not exact. They overlap on **`LE(100)`** (the whole of accept's region). `check(50)`: accept selected (candidate
non-empty) but consumes nothing (uncertain), reject selected; both carried, results joined — the honest answer,
and the v0.2 blocker fixed. `check(200)`: accept's candidate `Equals(200) ∩ LE(100) = Bottom` → accept not
selected; reject selected. Correct.

**W-3 — two parameters (c), opaque, zero captures.** `(n, limit) => n <= limit ? A : B`: both rows `Top`, not
exact; both always selected; results joined. Closes v0.2's totality gap.

**W-4 — compound guard, mixed leaves.** `(n) => n > lo && n < hi ? A : B`, `lo = Equals(0)` (a), `hi ⊑ Top`
(c): true row `GT(0) ∩ Top = GT(0)`, **not exact** (an opaque leaf is present); the known lower bound narrows
the region, the unknown upper neither excludes nor refutes; other arm from the forward negation. Because the
row is non-exact it consumes nothing in the walk — so the else arm stays live, correctly.

**W-5 — ladder; the walk derives the rational regions, no pre-carving.** `(n) => n <= 3 ? P : n <= 7 ? Q : R`,
`a=Equals(3)`, `b=Equals(7)`. Raw rows: `LE(3)` exact; **`LE(7)`** exact (its *own* guard — not `Range(4,7)`,
v0.2's rationals bug); `Top` exact (the unconditional arm). The walk over `remaining = Top`: row 1 candidate
`LE(3)`, then `remaining = GT(3)`; row 2 candidate `GT(3) ∩ LE(7) = Intersection(GreaterThan(3),
LessOrEqual(7))` (the half-open interval — `3.5` correctly lands here), then `remaining = GT(7)`; row 3
candidate `GT(7)`. First-match is the walk itself: `n=2` → row 1 consumes it, done; `n=5` → row 1 empty, row 2
consumes it. Correct rational regions with no complement pre-computation.

**W-6b — non-singleton pin (the 0.3.1 blocker).** `f = (x, y) => x :: { ^y => A  _ => B }` with `y : Number`:
pin row `region Top, exact false` (relational, unrepresentable as unary on `x`); wildcard `region Top, exact true`.
Walk: pin selected but **consumes nothing** (non-exact); wildcard stays live — `x != y` correctly reaches B. With
`y = Equals(5)` instead: pin `Equals(5), exact` consumes its point; `5 → A`, anything else `→ B`. **W-6 — negation opacity.** `(n, limit) => !(n <= limit) ? A : B`: `!(n<=limit)` reads `n > limit`, opaque
(`Top`); the other arm reads `n <= limit`, opaque (`Top`). Both `Top`, both selected, never `Bottom`. The v0.2
degeneracy is structurally impossible.

## 10. Suite obligations

**RT-01** singleton capture → exact complements via forward negation; walk consumes exact rows (W-1). **RT-02**
[the v0.2 selection-blocker regression guard] bounded-range capture, `check(50)` → accept **not exact**, selected
but consumes nothing, reject also selected, results joined; assert accept did **not** resolve first-match.
**RT-03** two-parameter guard, zero captures → opaque, both selected (W-3; totality). **RT-04** compound guard
with an opaque leaf → non-exact, narrows by the known leaf, consumes nothing so the else arm stays live (W-4).
**RT-05** [rationals regression guard] ladder → each row its own forward region, `3.5` lands in row 2 via the
walk's `Intersection(GreaterThan(3), LessOrEqual(7))` (W-5). **RT-06** [negation regression guard] `!opaque` →
`Top`, never `Bottom` (W-6). **RT-07** pattern-only arm → pattern region rules; guarded arm → pattern ∩ guard;
exactness = pattern-exact && guard-exact. **RT-08** parameter-pattern projection places a constraint at the
right argument-tuple position, `Top` elsewhere, through a destructuring pattern. **RT-09** [annotated-key
regression guard] same shape + same **annotated** tuple → one entry; same shape + same coarse contract but
**different instance metadata** → **distinct** tables (not conflated). **RT-10** [per-call vs source guard]
`f = x => x :: {Number=>1 String=>2}`, `f(5)`: String row **not selected** (no error); a genuinely
source-empty-after-consumption branch → unreachable-branch error. The two outcomes are distinct. **RT-12** [pin blocker regression guard] non-singleton pin (`y : Number`) → `region Top, exact false`, consumes nothing, wildcard stays selectable; assert the pin did **not** consume the else arm. **RT-13** singleton pin (`y = Equals(5)`) → `Equals(5), exact`, consumes its point; `5 →` pin, else `→` wildcard. **RT-14** [witness bridge] a non-exact row selected via an over-approximate candidate does **not** by itself authorize `Refuted(witness)` or completion `ProvenPresent` — those require C§13.2's jointly represented witness. **RT-11** [§8 non-normative] no test asserts suspension behavior; a test asserts case (c) is *opaque* (not held).

## 11. What this document is and is not

**Is:** the procedure turning a symbolic summary template + capture contracts into an ordered table of
`(region, exact, resultExpr)` rows by reading each guard/pattern forward, plus the ordered remainder walk in
which exact rows consume and uncertain rows do not — reachability, sound under uncertainty, total,
non-iterative, cached.

**Is not:** the accepted-domain procedure. It computes *where inputs may go*; *which inputs are safe* is a
separate small specification (§6) that consumes this table and the ordinary operation demands of guards and
bodies. They share control-flow information and need no cross-layer algebra.

*End of Region-Table Computation Specification v0.3 (patches 0.3.1–0.3.2 — architecturally closed; Ask 1 / C§17 region-table item discharged).*
