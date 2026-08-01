> ## 📗 STATUS: **HISTORICAL** — design record for a feature that is now built
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. This draft was the
> author-reviewed design for the C§7 operation rulebook, which is implemented
> (`src/contract/numeric.rs`, `src/contract/operation.rs`). Left unedited.

# F0 — The complete operation rulebook: draft table

**Date:** 2026-07-31. **Status:** DRAFT FOR AUTHOR REVIEW — no code written. Derived from C§7 +
C§17's owed per-pair tables, and checked line-by-line against the truth source
(`oracle::eval::apply_prim`). Per `NEXT-owed-breadth-foundation-map.md`, F0 is built **whole** —
this table is the feature set; a failing case may scope it, never define it.

Two halves per rule (C§7 / C§16 obligation 3): **safety** (the operation's own demand,
three-valued with an n-ary witness) and **image** (an over-approximation of
`{ op(v₁…vₙ) : vᵢ ∈ ⟦Cᵢ⟧ }`).

---

## Part 1 — Safety demands (complete; 13 operations)

Read off `apply_prim`. **The Indeterminate rule is the load-bearing subtlety**: arithmetic checks
Indeterminate *first* and propagates it (no trap); ordering comparisons check it first and *trap*.

| Operation | Safe exactly when | Trap class otherwise |
|---|---|---|
| `Eq`, `Ne` | **always** (total — any values, Indeterminate included) | — |
| `Neg` | operand ⊑ `Number ∪ Indeterminate` | OperationSafety |
| `Add` | `(Number,Number)` ∪ `(String,String)` ∪ **either operand Indeterminate** | OperationSafety |
| `Sub`, `Mul` | `(Number,Number)` ∪ either Indeterminate | OperationSafety |
| `Div`, `Rem` | `(Number,Number)` ∪ either Indeterminate — **zero divisor is total**, not a trap | OperationSafety |
| `Pow` | `(Number,Number)` ∪ either Indeterminate, **and** exponent ⊑ integers, **and** ¬(base ∋ 0 ∧ exponent ∋ negative) | OperationSafety |
| `Lt`,`Le`,`Gt`,`Ge` | `(Number,Number)` **strictly** — Indeterminate is *not* admitted | **UndischargedIndeterminate** if an operand is Indeterminate; else OperationSafety |

**Gap this closes vs. today:** the current `demand_proven` has no Indeterminate clause, so
`Indeterminate + Number` comes out **Unproven** when it is provably **safe** (it propagates). And
`Pow`'s "0 to a negative power" and non-integer exponent are present but the Indeterminate
interaction is not.

---

## Part 2 — The numeric abstraction

One shared representation, since every numeric contract form is a facet of the same thing:

```
NumAbs { iv: Interval, cong: Option<Congruence> }
Interval { lo: Bound, hi: Bound }        Bound = Unbounded | Incl(q) | Excl(q)
Congruence { n: BigInt, r: BigInt }      // x ≡ r (mod n), n > 0
```

`Interval`/`Bound` **already exist** in `subcontract.rs:129-162` — extract and share, do not
re-encode.

### 2a. Reading a contract into `NumAbs` (image direction — may widen)

| Contract | interval | congruence |
|---|---|---|
| `Kind(Number)` | (−∞,∞) | — |
| `Range(l,h)` | [l,h] | — |
| `Greater(m)` / `GreaterEq(m)` | (m,∞) / [m,∞) | — |
| `Less(m)` / `LessEq(m)` | (−∞,m) / (−∞,m] | — |
| `Equals(v)`, v numeric | [v,v] | exact |
| `Mod{n,r}` | (−∞,∞) | (n,r) |
| `Geo{b,r}`, b>0 | [b,∞) | — |
| `Geo{b,r}`, b<0 | (−∞,b] | — |
| `Intersection(A,B)` | meet | CRT meet (⊥ if incompatible ⇒ `Bottom`) |
| `Union(A,B)` | hull | congruence join (gcd) |
| `Difference(A,B)` | A's (drop the exclusion) | A's |
| `Bottom` | empty | — |
| anything else | **not numeric** → `None` |

> **DIRECTION ASYMMETRY — normative.** This conversion **over-approximates**, which is sound for an
> *image* (widening the input widens the image) but **unsound for subset testing** (widening the RHS
> makes `⊑` wrongly true — `GreaterEq(0) ⊑ Mod(1,0)` would come out Proven, which is false). The
> exact conversion in `subcontract.rs` stays separate. **Two conversions, documented.**

### 2b. Rendering `NumAbs` back to a contract

Half-line where one side is unbounded · closed `Range` when both endpoints are inclusive ·
`Intersection` of two half-lines for mixed strictness (the half-open form the region walk already
produces) · `Bottom` when bounds cross · `∧ Mod{n,r}` conjunct when a congruence survives ·
`Kind(Number)` when nothing is known.

---

## Part 3 — Image rules, per operation

### Interval transfer

| op | rule |
|---|---|
| `+` | `[a,b] + [c,d] = [a+c, b+d]` |
| `−` | `[a,b] − [c,d] = [a−d, b−c]` (each bound pairs with the subtrahend's **opposite**) |
| unary `−` | `−[a,b] = [−b, −a]` |
| `×` | the four corner products under **extended (±∞) arithmetic**, taking min/max; `0·∞ = 0` since 0 is exact. Sign cases fall out of the corner rule — no separate case analysis. |
| `/` | divisor excludes 0 → corner quotients; divisor **may** be 0 → interval unbounded **and** the image gains the Indeterminate forms (below) |
| `%` | `\|r\| < \|y\|` and **sign follows the dividend** (truncation toward zero, per `eval_rem`): result ⊆ `(−maxAbs(divisor), maxAbs(divisor))`, intersected with the dividend's sign half |
| `**` | exponent a nonneg even singleton → result ≥ 0; base ≥ 0 → result ≥ 0; base and exponent both singleton → exact (already constant-folded upstream); otherwise `Kind(Number)` |

Endpoint strictness: **inclusive only when both contributing endpoints are.**

### Congruence transfer

| op | rule |
|---|---|
| `+` / `−` | `(n₁,r₁) ± (n₂,r₂) → (gcd(n₁,n₂), r₁±r₂ mod gcd)` |
| unary `−` | `(n, −r mod n)` |
| `×` by an **exact** constant c | `(n,r) → (c·n, c·r)` — this is C§7's *scaling* |
| `×` otherwise, `/`, `%`, `**` | dropped (no congruence) |

### Non-numeric images

| case | image |
|---|---|
| `Add` on `(String,String)` | `Kind(String)` — *the length-contract lift is owed (§5, tuple family); a string-length contract form does not exist yet* |
| `Lt`,`Le`,`Gt`,`Ge` | `Kind(Boolean)` — **but decide it when the intervals decide it**: `Range(0,5) < GreaterEq(10)` → `Equals(true)`. This is the *precise* image, not an invention, and it is what lets a guard resolve. |
| `Eq`,`Ne` | `Kind(Boolean)`; `Equals(true)`/`Equals(false)` when the operands are proven equal singletons or proven disjoint |
| any arithmetic with a possibly-Indeterminate operand | image ∪ the possible `Indeterminate` forms (union over operands — sound over-approximation of the left-most rule) |
| `Div`,`Rem` with `0` possibly in the divisor | image ∪ `Indeterminate(DivByZero)` ∪ `Indeterminate(ZeroOverZero)` (the latter only if the dividend may be 0) |
| `Bottom` operand | `Bottom` (no values ⇒ no image) |

### Composite operand forms

- **`Union(A,B)` → distribute**: `op(A,C) ∪ op(B,C)`, per-alternative, never flattened (the
  no-flattening precision rule). Bounded: distribute up to *k* alternatives, else fall back to the
  hull. **[ask-author: k, or always distribute?]**
- **`Intersection`** → meet inside `NumAbs` (CRT for congruences).
- **`Difference(A,B)`** → use A; additionally, when B is a singleton at an endpoint of A's interval,
  tighten that endpoint to strict.
- **`Top`** → not provably numeric: safety is refuted-or-unproven, image `Top`.

---

## Part 4 — Deliberately unproven (documented incompleteness, per C§17)

Each of these returns a *sound coarse* answer and is **recorded**, not silently missed:

1. `Geo` arithmetic beyond scaling — `Geo + Geo`, `Geo + Range` are not `Geo`; project to interval.
2. `Mod` through `×` by a non-constant; through `/`, `%`, `**` — dropped.
3. `**` with non-singleton base *and* exponent — `Kind(Number)` (plus sign facts where derivable).
4. String **length** contracts through `+` — needs the tuple-family §5 lift; owed there, not here.
5. `Difference` with a non-singleton exclusion — the exclusion is dropped.
6. Non-numeric structural forms (`Tuple`, `Record`, `Concat`, `LengthRestricted`, `Ref`) in
   arithmetic — safety refutes or is unproven; no image rule needed.
7. Cross-form emptiness beyond CRT + interval crossing (C§6's per-pair emptiness tables).

---

## Part 5 — Implementation plan

**New/changed files**
- `contract/numeric.rs` **(new)** — `Interval`/`Bound` (moved from `subcontract.rs`), `Congruence`,
  `NumAbs`, the two conversions (image-over-approximating vs. exact-for-subset), the renderer, and
  the interval/congruence transfer functions.
- `contract/subcontract.rs` — use the shared `Interval`/`Bound`; **behaviour unchanged** (keeps its
  own exact conversion).
- `contract/operation.rs` — `analyze_safety` rewritten to the Part-1 table; `analyze_output`
  rewritten to dispatch through `NumAbs` per Part 3.

**Order (each step ends green; no step is scoped by a failing case)**

1. **Extract** `Interval`/`Bound` into `contract/numeric.rs`, `subcontract.rs` uses it. Pure
   refactor — suite must be byte-identical green.
2. **Build `NumAbs`**: congruence + both conversions + renderer, with direct unit tests (no operation
   wiring yet).
3. **Safety table** (Part 1) — complete, including the Indeterminate clauses. Verify against the
   sweep.
4. **Image rules** (Part 3) — complete, all 13 operations, through `NumAbs`.
5. **Extend `operation_soundness_sweep`'s grid** to every contract form in Part 2a × every operation
   — this is the net that proves the table sound against the oracle. Add a separate *precision*
   test asserting the exact expected output for each table row.
6. **Document** the Part-4 incompleteness in the module doc and `OwedItems`.

**Not in F0** (named so scope stays fixed): the analyzer-level `analyzeOperation` +
`OperationOutcome` (that is F1); the demand core (F2); anything in `analyzer/`.

**A correction to an earlier claim.** I previously called the compound scrutinee
`(a + b) :: { … }` a *gap*. It is not: region-table §2 case (d) **specifies** a compound tested
expression as opaque (`Top`, non-exact). What actually improves it is exactly this table — with a
real image for `a + b`, `analyze_match` narrows arms against the scrutinee's contract, and the
comparison-decision rule above lets a guard resolve when the bounds decide it. No separate item.

---

## Open questions for the author

1. **`Union` distribution bound** — distribute over all alternatives, or cap at *k* and fall back to
   the interval hull?
2. **Comparison decision** — confirm that producing `Equals(true)`/`Equals(false)` when the bounds
   decide a comparison is wanted here (it is the precise image, and it is what makes guards
   resolvable), rather than always `Kind(Boolean)`.
3. **`Geo` scope** — is scaling (`Geo × exact constant`) the intended extent for v1, with everything
   else projected to an interval?
4. **`Rem` precision** — is the sign-follows-dividend bound worth carrying, or is
   `(−|d|, |d|)` enough for v1?
