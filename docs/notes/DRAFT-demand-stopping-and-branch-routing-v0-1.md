# NEXT — Demand-Stopping Contract Resolution and Lazy Branch Routing

**Status:** Draft for review
**Scope:** Result-contract resolution, arithmetic producer mappings, match-local substitution, and interaction with lazy branch routing.

> **Editorial note (fold, 2026-08-07).** §§1–11 are the author's document, reproduced
> unchanged. §§12–14 fold in `DRAFT-branch-routing-v0-1.md` (drafter, superseded and
> deleted), keeping only what survives this document and **correcting two rules it got
> wrong** — see §12.0. §15 records what is implemented today.

---

## 1. Purpose

This specification defines how a contract demand is resolved through an expression.

Its central rule is:

> A contract demand propagates only until it reaches a producer that establishes the demanded contract. Once the demand is satisfied, resolution stops and does not continue into the producer's operands or earlier dependencies.

This specification also separates three distinct judgments:

1. **Result-contract judgment** — determines whether every value actually produced by a completing expression satisfies a demanded contract.
2. **Operation-safety judgment** — determines whether an operation's operands satisfy the operation's input requirements.
3. **Completion judgment** — determines whether every represented execution path produces a result.

These judgments may inspect the same expression, but they must not be collapsed into one unrestricted backward traversal.

---

## 2. Numeric contracts

### DR-01 — Numeric hierarchy

```text
Numeric = Number ∪ Indeterminate

Indeterminate =
    DivisionByZero
  ∪ ModuloByZero
```

`Number` contains ordinary numeric values.

`DivisionByZero` and `ModuloByZero` are numeric indeterminate values. They are members of `Numeric`, but not members of `Number`.

```text
Number ⊑ Numeric
Indeterminate ⊑ Numeric
```

---

## 3. Operation producer mappings

Every operation declares two independent pieces of information:

1. its **operand demands**;
2. its **result mapping**.

The operand demands are used by operation-safety analysis.
The result mapping is used by result-contract resolution.

### DR-02 — Arithmetic operations produce Numeric

Every valid arithmetic operation produces a value within `Numeric`.

```text
Result(op(...)) ⊑ Numeric
```

When the demanded result contract is `Numeric`, the demand stops at the operation node. The result-contract judgment does not continue into the operands merely to prove `Numeric`.

### DR-03 — Addition, subtraction, and multiplication

```text
Number + Number → Number
Number - Number → Number
Number * Number → Number
```

When an indeterminate participates:

```text
Indeterminate + Numeric → Indeterminate
Numeric + Indeterminate → Indeterminate

Indeterminate - Numeric → Indeterminate
Numeric - Indeterminate → Indeterminate

Indeterminate * Numeric → Indeterminate
Numeric * Indeterminate → Indeterminate
```

At the broader level:

```text
Numeric + Numeric → Numeric
Numeric - Numeric → Numeric
Numeric * Numeric → Numeric
```

Only division and modulo can create a new indeterminate from two ordinary `Number` operands.

### DR-04 — Division

```text
Number / NonZeroNumber → Number
Number / Zero          → DivisionByZero
```

When zero is not excluded:

```text
Number / Number
    → Number ∪ DivisionByZero
    ⊑ Numeric
```

Therefore:
- a `Numeric` result demand stops at division;
- a `Number` result demand requires proof that the divisor cannot be zero.

### DR-05 — Modulo

```text
Number % NonZeroNumber → Number
Number % Zero          → ModuloByZero
```

When zero is not excluded:

```text
Number % Number
    → Number ∪ ModuloByZero
    ⊑ Numeric
```

Therefore:
- a `Numeric` result demand stops at modulo;
- a `Number` result demand requires proof that the divisor cannot be zero.

### DR-06 — Indeterminate propagation remains closed

Arithmetic over an existing indeterminate does not return to `Number`; it remains within `Indeterminate`, and therefore within `Numeric`.

The exact identity rule when different indeterminate kinds interact is not settled here. Until settled, the sound result contract is:

```text
Indeterminate
```

---

## 4. Demand-stopping resolution

### DR-07 — Immediate producer contract

Let `D` be the demanded result contract, `e` the expression receiving the demand, and `P(e)` the result contract established by the immediate producer of `e`.

If:

```text
P(e) ⊑ D
```

then the demand is proven at `e` and resolution stops.

The demand must not continue into:
- the operands of `e`;
- bindings used by those operands;
- earlier expressions from which those bindings were derived.

### DR-08 — Demand resolution procedure

```text
Resolve(environment, expression, demand):

1. Apply branch-local match refinement or substitution.

2. Determine the immediate producer result contract P(expression).

3. If P(expression) ⊑ demand:
       return Proven

4. If expression is a reference:
       resolve the reference under the same demand

5. If the producer has a more precise result rule whose premises
   could establish the demand:
       generate only those necessary premises

6. Otherwise:
       return Unproven or Refuted according to the ordinary
       contract judgment
```

For example:

```text
Demand: Numeric
Expression: a / b
```

Division already establishes `Numeric`, so no further result demand is generated.

But:

```text
Demand: Number
Expression: a / b
```

requires:

```text
b ⊑ NonZeroNumber
```

### DR-09 — Satisfied demands do not propagate

```text
Demand Numeric
    → arithmetic operator
    → Numeric established
    → stop
```

It is incorrect to continue propagating `Numeric` into the operands as part of the result-contract judgment. Operand requirements belong to operation-safety analysis.

---

## 5. Match result contracts

### DR-10 — A match result is produced by its selected arm

For:

```next
scrutinee :: {
    pattern₁ => result₁
    pattern₂ => result₂
    ...
}
```

the selected arm body produces the result. A result demand on the match is therefore checked against the arm result expressions.

### DR-11 — Result contract does not imply exhaustiveness

The result-contract claim is:

> Every value actually returned by a completing arm satisfies the demanded contract.

The completion claim is:

> Every represented arriving value selects a completing arm.

These are independent.

An unmatched value causes a completion failure. It does not create a returned value that violates the result contract.

---

## 6. Match-local substitution

### DR-12 — Exact-arm refinement

Inside an exact-value match arm:

```next
scrutinee :: {
    value => body
}
```

the arm environment establishes:

```text
scrutinee = value
```

or equivalently:

```text
scrutinee ⊑ Equals(value)
```

Within that arm, result-contract resolution may substitute references to the scrutinee with the exact matched value.

This is an analyzer judgment. Physical AST rewriting is not required.

### DR-13 — Exact substitution precedes reference propagation

Given:

```next
20 => subtotal
```

inside a match on `subtotal`, analysis resolves the arm as:

```next
20 => 20
```

Therefore:

```text
20 ⊑ Number ⊑ Numeric
```

The demand is discharged locally. The analyzer must not follow `subtotal` back to its earlier producer.

### DR-14 — Substitution inside compound expressions

```next
6  => subtotal - rate
12 => subtotal + seats
```

are analysed locally as:

```next
6  => 6 - rate
12 => 12 + seats
```

The operation producer then establishes `Numeric`, so a `Numeric` result demand stops at the operation.

### DR-15 — Non-singleton arms narrow but do not substitute a literal

For a contract arm:

```next
Number => body
```

the scrutinee narrows to `Number`, but cannot be replaced by one literal.

For a default arm:

```next
_ => body
```

the scrutinee narrows to the remainder after earlier arms.

Literal substitution is authorized only when the admitted arm region is represented exactly by one value.

---

## 7. Worked example

```next
Plan = Union(
    Equals("basic"),
    Equals("pro"),
    Equals("enterprise")
)

Size = Union(
    Equals("small"),
    Equals("large")
)

price where (Plan, Size) => Numeric

price = (plan, size) => {
    rate = plan :: {
        "basic"      => 1
        "pro"        => 3
        "enterprise" => 5
    }

    seats = size :: {
        "small" => 2
        "large" => 4
    }

    subtotal = rate * seats

    => subtotal :: {
        2  => rate + seats
        4  => seats * 10
        6  => subtotal - rate
        10 => rate * 2
        12 => subtotal + seats
        20 => subtotal
    }
}
```

The declared result demand is:

```text
result ⊑ Numeric
```

After match-local substitution:

```next
2  => rate + seats
4  => seats * 10
6  => 6 - rate
10 => rate * 2
12 => 12 + seats
20 => 20
```

| Arm | Immediate producer | Established result |
|---|---|---|
| `2` | addition | `Numeric` |
| `4` | multiplication | `Numeric` |
| `6` | subtraction | `Numeric` |
| `10` | multiplication | `Numeric` |
| `12` | addition | `Numeric` |
| `20` | literal `20` | `Number ⊑ Numeric` |

Therefore the `Numeric` return contract is proven entirely within the final match.

No result demand propagates to `subtotal = rate * seats`, the earlier `rate` match, or the earlier `seats` match. Those expressions remain subject to their own operation-safety and completion judgments.

---

## 8. Interaction with lazy operation resolution

### DR-16 — Result demands do not force exact branch computation unnecessarily

A lazy operation image must not be forced when the current result demand has already been discharged by the producer mapping.

Example:

```text
Demand: Numeric
Expression: rate * seats
```

Multiplication establishes `Numeric`. The exact distributed result is irrelevant to that result-contract judgment.

### DR-17 — Exact resolution belongs to routing and completion

Exact branch-sensitive computation may still be required by another judgment:

```text
For each arriving branch, which match arm does it select?
```

This routing question is used to establish:
- match exhaustiveness;
- arm reachability;
- branch-local narrowing;
- whole-function completion.

If the coarse hull cannot prove completion, the analyzer may force the held branch-sensitive computation for routing.

### DR-18 — Hull authority is asymmetric

A coarse hull is an over-approximation of the exact branch result.

A positive proof may stand:

```text
hull ⊑ demanded
    ⇒ exact result ⊑ demanded
```

But failure of the hull to prove an exact routing or completion property may not be used as the final rejection when a held exact branch computation exists.

```text
coarse routing result = Unproven or apparent remainder
    → force exact branch computation
    → repeat routing judgment
```

---

## 9. Separation of judgments

### Result contract

```text
What kind of value does this producer return?
```

Example:

```text
a / b → Numeric
```

### Operation safety

```text
Do the operands satisfy the operation's input requirements?
```

Example:

```text
a ⊑ Numeric
b ⊑ Numeric
```

### Completion

```text
Does every represented path reach and complete the expression?
```

For a match, this may require exact branch routing.

A proof in one judgment must not silently substitute for a proof in another.

---

## 10. Binding principles

1. Every operation has an explicit operand-demand mapping and result mapping.
2. Only division by zero and modulo by zero currently create new indeterminate values from ordinary number operands.
3. Addition, subtraction, and multiplication map ordinary number operands to `Number`.
4. Existing indeterminate values remain indeterminate through arithmetic.
5. `Numeric` result demands stop at any arithmetic operator.
6. More specific demands, such as `Number`, propagate only when the immediate result mapping does not already establish them.
7. Exact match arms substitute the matched value for references to the scrutinee within the arm.
8. Match-local substitution occurs before reference propagation.
9. Return-contract correctness does not imply match exhaustiveness or function completion.
10. Lazy exact computation is forced by routing or completion needs, not by a result demand that has already been satisfied.
11. Once a demand is satisfied, it must not propagate indefinitely into earlier expressions.

---

## 11. Open items

This specification does not settle:

1. the precise identity produced when multiple different indeterminate kinds interact;
2. the physical representation of lazy operation images;
3. the cache-key treatment of forced versus unforced branch computations;
4. the complete set of consumers authorized to force an exact branch image;
5. whether some non-singleton match regions admit stronger substitution than ordinary narrowing;
6. the exact diagnostic relationship between a proven result contract and separately failed completion or operation safety.

These questions must not be answered by importing general symbolic execution, backward inversion, widening, search budgets, or unrestricted expression propagation.

---
---

## 12. Branch sets and routing *(folded from `DRAFT-branch-routing-v0-1.md`)*

### 12.0 — What the fold corrects

The superseded draft asserted two rules this document refutes. Recorded so they are not
re-imported:

- **BR-06 as written ("routing is the *only* question a branch set is asked") is wrong.**
  §4/DR-09 shows the result-contract judgment asks nothing of a branch set at all: it stops
  at the producer's result mapping. Routing is the question **completion** asks. The corrected
  form is BR-06′ below.
- **BR-07 ("nothing else is asked") is wrong for the same reason**, and its consequence — the
  claim that the backward existential search has *no* customer — was right by accident. It has
  no customer because completion routes every branch anyway (BR-08), not because seats ask
  nothing.

### 12.1 — The object

**BR-01 — Class [drafted].** A **branch set** is analyzer-side metadata. It is not a
contract, is never interned, and never rides on a value; contracts are interned with pointer
equality by constitution (B1), and a branch set carries conditions on source variables.
**[open]** — exact representation. This is §11's open item 2.

**BR-02 — Origin [measured].** Branch sets arise from **one** place: a match whose scrutinee
domain has more than one member, where more than one row survives the remainder walk.
Without a declared domain, every argument at every seat is a singleton, every match selects
exactly one row, and **no branch set ever exists** (traced 2026-08-05, `pricing3.next` vs
`pricing2.next`).

**BR-03 — Cells and the cell index [drafted].** Every node has a **cell index**: the tuple of
*sources* it transitively depends on. A **cell** is one assignment of those sources. `rate`
over `plan` has 3 cells; `subtotal = rate * seats` has index `(plan, size)` and 6 cells; a
node built from `rate` twice still has index `(plan)` and 3 cells.

**BR-04 — Correlation is structural, not a rule [drafted].** BR-03 makes correlation
automatic: within a cell every source has exactly one assignment, so both operands are read
at the same assignment. `rate + rate` over `{0,5,20}` has cells `{0,10,40}`, never the
cross-product `{0,5,10,20,25,40}`. **This is strictly more precise than eager union
distribution**, which discards provenance and must admit `0+20`.

### 12.2 — Routing

**BR-06′ — Routing is the question *completion* asks [author, corrected].** The completion
judgment (§9) asks a branch set exactly one thing: **for each arriving branch, which arm does
it select?** Exhaustiveness and arm-reachability are aggregates of that answer. The
result-contract judgment asks it nothing (DR-09).

**BR-08 — Routing demand [drafted].** A branch is routed only when some arm's analysis
depends on *which* branches arrive at it. An arm whose body is source-independent needs only
its reachability, not its arriving set.

**BR-09 — Narrowing by arrival [measured].** Within an arm, the live branch set is the
arriving subset, and **every source and derived node narrows to its cells on that subset
simultaneously** — with no inversion. This is the branch-set generalization of DR-12/DR-13:
where those substitute the *scrutinee's* matched value, BR-09 narrows every variable the
surviving branches pin. In
`rate = p :: { "pro" => 20  _ => 0 }`, `d = rate * 2`, `d :: { 40 => rate }`, the `40` row is
reached only by the `pro` branch, so inside it `p = "pro"`, `rate = 20`, `d = 40` at once.

**BR-10 — Lookup strategy [author].** A branch finds its arm either **by key** — when arms
are literal values they form a lookup table and a branch's value indexes straight to its arm,
exactly like a record property access — or **iteratively**, walking arms in source order.

**BR-11 — First-match is preserved [drafted].** Keying is available only where it cannot
disturb source order: a literal arm may be shadowed by an *earlier* non-literal arm
(`{ Number => a  4 => b }` sends `4` to the first). Arms form a keyed table only from the
position after the last preceding non-literal arm. **[open]** — whether contract arms can be
keyed by kind.

### 12.3 — The hull's authority, itemized

DR-18 states the asymmetry; these are its four cases, with the two that are forbidden.

**BR-13 — Sanctioned [drafted].** Since `true ⊆ hull`, the hull may

1. **eliminate an arm before any routing** — `armValue ∉ hull` ⇒ no branch reaches it ⇒ dead.
   *(refuting an existential)*
2. **prove exhaustiveness before any routing** — `hull ⊆ arms` ⇒ `true ⊆ arms`.
   *(proving a universal)*

**BR-14 — Forbidden [drafted].** It may **not** refute exhaustiveness (`hull ⊄ arms` says
nothing about the truth — this was the false-rejection bug), and it may **not** establish an
arm reachable (`armValue ∈ hull` says nothing). This is DR-18's second half stated as a
prohibition.

### 12.4 — Collapse

**BR-15 — Collapse points [drafted, open in detail].** A branch set's conditions are
meaningful only where its sources are in scope. It collapses to an ordinary contract — the
join of its cells — when the value escapes: returned across a function boundary, stored in a
structure, or reaching a **recursive** boundary, where resolution goes through a *fact* and a
fact is a contract. Recursion is therefore not a separate mechanism but a collapse site.
**[open]** — the escape-site inventory.

### 12.5 — Cost

**BR-16 — What is saved, and what is not [measured + drafted].** A value **no match routes**
— consumed only by a result demand — costs nothing, because DR-16 forbids forcing it. A value
**a match routes**, whose arm bodies depend on sources (BR-08), costs its cell count; routing
is the work and no cleverness avoids it. Between them sit BR-13's two shortcuts, which can
settle exhaustiveness or kill an arm with no routing at all.

---

## 13. Killed — do not reintroduce

§11's closing sentence names the categories. This records the specific mechanisms that were
proposed, built or measured during the session that produced this document, and why each was
rejected — so the same ground is not retaken.

**13.1 Preimage / backward inversion.** Pulling an arm's region back through an operation to
narrow a source. **Killed [author]:** BR-09 gives the same narrowing for free and gives it for
*every* variable at once, where preimage narrows one per inversion and needs a rule per
operation, a fence for two-varying operands, and a widening story for non-invertibles. The
example that motivated it had an open `Number` domain with no branches — outside the model.

**13.2 The backward existential search.** Answering "can this node be *X*?" by pushing the
target through the operation with hull pruning. Prototyped and measured — 17 operations
against eager's 131,068 at 65,536 combinations — and **killed anyway [author]:** completion
routes every branch an arm body depends on (BR-08), so a search that avoids visiting them
answers nothing the judgment needs. The measurement stands; the customer does not exist.

**13.3 Eager union distribution as the operation rule.** Superseded by BR-03/BR-04 (more
precise) and by §15's routing-forced exact image (cheaper when unrouted).

**13.4 The interval hull as an answer-producing rule.** Retained only in BR-13's two
sanctioned directions.

**13.5 Fuel, budgets, and search over unknowns.** Nothing here searches. Routing enumerates a
finite, structurally-determined set; §15's exact image applies a leaf rule to a bounded
number of combinations.

---

## 14. Obligations a discharge would owe

1. A concretization γ for branch sets, and soundness of BR-09's narrowing over it.
2. Soundness of BR-13's two uses and a proof that BR-14's two are excluded.
3. Order-independence: routing results identical regardless of demand order and cache warmth
   (AP-10's discipline).
4. Termination **without a budget**: routing is bounded by the finite cell count; collapse at
   recursive boundaries (BR-15) is what keeps that finite. To be proved, not asserted.
5. Per-rule soundness of the exact image (§15) against the leaf rules it composes.

---

## 15. Implementation status (2026-08-07)

**Already true, measured.**

- **DR-02 / DR-09 hold today.** A `⊑ Numeric` return demand on the §7 example discharges at
  the arithmetic producers; no error is raised for the return contract, and no demand
  propagates to `subtotal`, `rate` or `seats`.
- **DR-11's separation is visible in the diagnostics.** Adding a wildcard arm removes the
  completion error and leaves the result contract untouched — two judgments failing
  independently.
- **The union-remainder algebra is fixed** (2026-08-07): `difference` distributes over union
  arms, `Equals(v) ∖ Z` reduces to `Bottom` by membership, `union` drops `Bottom`. *n* exact
  point arms now consume an *n*-member union; previously three failed where two succeeded.
- **DR-17/DR-18's first slice is built** (2026-08-07): completion is judged coarsely, and
  **only if that fails** the same judgment re-runs with the rulebook distributing over finite
  point operands. The mode is part of the memo key, so a cached coarse `Unproven` cannot
  short-circuit the retry — that is §11's open item 3, answered for this slice. Capped at 256
  combinations; beyond the cap the coarse verdict stands. §7's worked example checks `ok` and
  runs to `16`; removing one arm is still refused.

**Not built, deliberately.** Chaining, shared-versus-independent provenance, deeper operation
graphs, the general lazy-image representation (§11 item 2), BR-10/BR-11's keyed lookup,
BR-15's collapse inventory, and DR-12/DR-14's substitution as a *distinct* mechanism (today's
narrowing comes from the region walk, not from substitution).

**Editorial nit on §7.** `Union` is binary in the grammar, so the example's three-argument
`Union(a, b, c)` must be written nested — `Union(a, Union(b, c))` — to parse. The verified
program is otherwise identical to the one above.
