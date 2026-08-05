# Handover — hull vs distribution in the operation rulebook (A6 / F0 draft Q1)

**Status: OPEN. No ruling exists. Nothing in the implementation was changed by this
investigation** — the two experiments described under "How to reproduce" were temporary,
env-gated, and reverted; suites green at 467 lib / 176 conformance / 10 machinery.

**Provenance discipline used below.** Every claim is tagged **[observed]** (produced by
running the implementation) or **[derived]** (arithmetic or reasoning by the author of this
note). An earlier round of this discussion mixed the two silently and produced several
wrong claims; those are listed under "Corrections" so they are not re-imported.

---

## 1. The question

When an operand of a primitive operation is a union, the transfer rule must produce an
output contract. Two candidate rules:

- **Hull (implemented today).** Flatten each operand to its numeric envelope, apply the
  rule to the envelopes. `Union(2,1) * 2` → `Range(1,2) * 2` → `Range(2,4)` (with parity
  retained — see §5).
- **Distribution.** Apply the rule to every combination of operand alternatives and join
  the results. `Union(2,1) * 2` → `{2*2, 1*2}` → `Union(4,2)`.

---

## 2. Where unions come from at all [observed]

Traced with temporary instrumentation on every block binding:

- **Without a `where`**, analysis is point-valued end to end. Every argument at every call
  seat is a singleton, every match selects exactly one row (the first exact row containing
  the point consumes it and the walk stops), and every operation sees singleton operands.
  **No union and no hull ever arises**, so this question is invisible to such code.
- **With a `where`**, the body is *additionally* analyzed over the declared domain — E11's
  stated mechanism: *"the assertion holds iff running the ordinary body check under the
  whole declared input proves every body demand safe."* That analysis is the only place a
  union appears, because a domain with several members leaves several rows selected and the
  match join unions their results.

The call site is **unaffected** by the presence of a `where`: same env, same contracts. The
declared-domain passes are additional work at the declaration, not a change to how calls
are analyzed.

---

## 3. The decisive case — same file, both rules [observed]

`hull.next`:

```
Plan = Union(Equals("free"), Equals("pro"))

f where (Plan) => Number
f = (p) => {
  rate = p :: { "pro" => 2
    _ => 1 }
  doubled = rate * 2
  => doubled :: { 2 => 10
    4 => 20 }
}

a = f("pro")
b = f("free")
b
```

The program is **total over `Plan`** and runs: `f("pro")` → 20, `f("free")` → 10, output
`=> 10`.

| | `rate` | `doubled` | `--check` |
|---|---|---|---|
| **hull** | `Union(Equals(2), Equals(1))` | `Intersection(Range(2,4), Mod{n:2,r:0})` | **error** — `where f` … cannot be proven to produce a value on every path (E10 completion) |
| **distribution** | `Union(Equals(2), Equals(1))` | `Union(Equals(4), Equals(2))` | **ok** |

At the call seat both rules are identical: `rate = Equals(2)`, `doubled = Equals(4)` —
distribution over singletons *is* the exact image.

**So the hull rejects a correct, total program over its own declared domain, and
distribution accepts it.** This is the entire practical stake of A6.

For contrast, `pricing2.next` (a six-step chain with a four-member and a three-member enum
plus three Booleans) checks **ok under both rules** [observed] — on that program the choice
changes nothing.

---

## 4. The mechanism, and why the failure is categorical

One step differs. Everything before it (the region walk) and everything at the call site is
identical under both rules.

**Under distribution:** the rulebook forms the operand pairs `(2,2)` and `(1,2)`, applies
`Mul` to each, joins → `Union(4,2)`. The exit match's two exact point rows then consume the
two members and the remainder is **empty** → E10 completion proven.

**Under the hull:** `{1,2}` is replaced by an interval. The exit match's rows subtract
`Equals(2)` and `Equals(4)` from it, and the remainder is **not** empty.

The reason it is not empty is structural, not marginal: **NEXT numbers are exact
rationals, so an interval is dense.** `Range(2,4)` minus two points still holds 2.5, 3,
3.7, 2.0001. No finite number of point rows can ever consume an interval. Once a finite set
becomes an interval, any body that dispatches on its values is unprovable.

---

## 5. The parity nuance [observed] — the hull is better than "Range" and still fails

The hull does **not** produce a bare `Range(2,4)`. It produces
`Intersection(Range(2,4), Mod{n:2,r:0})` — it carries the parity through. That contract
denotes exactly `{2,4}`; a human reads it off immediately.

It still fails, because the *emptiness check* has no rule that
`(even ∧ [2,4]) ∖ {2} ∖ {4}` is uninhabited. So the rejection is not the hull losing the
information — it is the hull moving the information into a form the remainder walk cannot
discharge.

---

## 6. Could the emptiness check be fixed instead? [derived]

Partly, and it is worth having on its own — but it does **not** substitute for the rule
choice.

**What is decidable.** `Range(lo,hi) ∧ Mod(n,r)` over exact rationals is a bounded
arithmetic progression; its member count is computable in closed form, so the contract
denotes an enumerable finite set. Normalizing such a contract to a union of its points
makes difference, emptiness and exhaustiveness fall out of existing machinery.

**What would be needed.** A predicate distinct from today's `Contract::proven_members`,
which is a *sampler* (sound one-way: "these are members", never "these are all"). The new
one is `denotes_exactly(finite set)` — provable for `Equals`, bounded `Range ∧ Mod` with an
integer-implying modulus, `Geo` within bounds, and finite unions of those. It needs a
cardinality cap (`Range(0,10⁹) ∧ Mod(1,0)` is a billion points), and **the cap's failure
mode is graceful** — exceed it and you fall back to today's unproven verdict, never to
invented values.

**Independent value.** `Intersection(Range(0,5), Mod(1,0))` — "an integer 0..5", the
bounded sibling of the suite's `Nat` — should make a match on arms `0…5` provably
exhaustive. Today it does not, for exactly the same reason.

**The limit.** Enumeration only recovers the truth where the hull was *accidentally* exact.
`{1,2}` is a contiguous integer run, so doubling gives a contiguous even run and
`Range(2,4) ∧ Mod(2,0)` happens to equal `{2,4}`. Change the input to `{1,2,5}`: the true
product set is `{2,4,10}`, but the hull gives `Range(2,10) ∧ Mod(2,0)`, which enumerates to
`{2,4,6,8,10}` — a strict superset. A match on `2`, `4`, `10` still leaves `{6,8}`
unconsumed and is still rejected. The information was genuinely destroyed at the multiply,
and no downstream check can recover it.

---

## 7. Cost

**Arm growth is the product of the choice counts along a chain** [derived]. On
`pricing2.next` under distribution: 4, 3, then 10, 19, 38, ~72 arms, and 146 rule
applications in one body walk versus 4 under the hull — ×3, since three declared-domain
passes each rebuild them (see TD-1). Both rules accept; the cost buys no verdict change on
that program.

**Algebra cost at a given union width** [observed] — built as a left-leaning spine of
distinct integer points:

| arms | build | `contains` | one `subcontract` |
|---|---|---|---|
| 1,024 | 11 ms | 0.3 ms | 6.9 ms |
| 2,048 | 21 ms | 0.6 ms | 32 ms |
| 4,096 | 40 ms | 0.5 ms | 143 ms |
| 8,192 | 81 ms | 1.1 ms | 669 ms |
| 16,384 | 164 ms | 3.8 ms | **4.8 s** |
| 32,768 | 348 ms | 6.5 ms | **45 s** |

Construction is linear and cheap; membership is cheap; **`subcontract` is ~O(n^2.2)** and
it is the analyzer's most-called primitive. On an ordinary test thread the recursive walks
**overflow the stack at n ≈ 8192** (the table above was produced on a 512 MB stack).

**Caveats, explicit.** This measures the algebra's cost on unions of a given size, not
distribution itself. The spine was left-leaning, so the stack limit is partly a
construction-shape artifact; a balanced tree would move it without touching the
`subcontract` curve. And that curve may itself be an implementation defect — `Union ⊑ X`
ought to be linear in arms — which means **the affordable arm budget and the rule choice
are not independent**: fix the quadratic and the tradeoff shifts by an order of magnitude.

---

## 8. Decision space

1. **Keep the hull.** Accept that bodies computing a small set and dispatching on it are
   unprovable over a declared domain.
2. **Distribution.** Exact; cost is the running product of choice counts along a chain.
3. **Distribution up to N alternatives, hull beyond.** Needs N chosen — and needs a ruling
   on *what* the fallback widening is, since a bare `Range` loses the parity the current
   hull keeps.
4. **Finite-enumeration emptiness (§6).** Orthogonal and additive — it helps user-written
   bounded integer contracts regardless of which rule wins, and partially masks the hull's
   damage where the hull was accidentally exact.

---

## 9. How to reproduce

Both experiments were temporary and are **not** in the tree.

- **Binding trace.** In `src/analyzer/mod.rs`, the `MatchItem::Bind` arm of the match
  analysis, after `analyze_in_world`: `eprintln!` the bind target name and `a.contract`,
  gated on an env var. Optionally add pass markers in `analyze_where`
  (`src/analyzer/program.rs`) before `safety::prove`, before `safety::completes`, and
  before `demand::returns`.
- **Distribution.** In `src/contract/operation.rs`, at the head of `analyze_operation`,
  gate on an env var: flatten each input's `Union` spine into alternatives, take the
  cartesian product, recurse per tuple, join outputs with `Contract::union`, and combine
  safety verdicts (any `Refuted` dominates, then any `Unproven`). Bail out when the product
  is 1 (nothing to distribute) or above a few thousand (experiment guard).
- Run `cargo run -- --check <file>` with and without the env vars. `git checkout` both
  files afterwards.

---

## 10. Corrections to earlier claims in this thread

Recorded so they are not re-imported from the conversation:

- **"Distribution explodes on this pricing chain."** False. ~72 arms, ~1 ms. The chain has
  four choice points; nothing runs away.
- **"The wall is thousands of alternatives on every expression."** Unsupported as stated.
  The measured wall is the algebra's `subcontract` cost above ~4k arms, and it may be a
  fixable quadratic rather than an intrinsic bound.
- **"A6 is a precision/cost dial."** Wrong in the direction that matters. The hull
  manufactures values the program cannot produce and then rejects the program for not
  handling them. **The A6 entry in `OPEN-DECISIONS-2026-08-05.md` still carries the old
  framing and is owed a correction.**
- **"The union buys exhaustiveness over `{1,2}` and not over anything coarser — that's the
  whole of it."** Incomplete framing. The join's union is not an addition needing
  justification; it *is* the result of the selected arms. The hull is the added step.
- **A `where (Range(1,2))` demonstration** was used at one point to argue the hull's cost.
  It proves nothing: that function is genuinely partial, so the rejection is correct and
  `Number` fails identically. Discard it.
- **A "variant B" program** (doubling folded into the match arms) was used as a stand-in
  for distribution. It is a *different program*; the same-file experiment in §3 supersedes
  it.

---

## 11. Related items

- **TD-1** (`TECHNICAL-DEBT.md`) — the body is analyzed three times per `where` and three
  times per call seat. Multiplies whatever the rulebook costs. Independent of A6.
- **E11** — the declared-domain body check is the mechanism that makes unions exist at all.
  Confirmed as spec-mandated during this discussion; the author questioned it and it was
  defended from the text, not changed.
- **GR-10(3)** — the finite-product exact-chain extension, deferred by ruling. Adjacent
  (finite numeric state spaces) but a *termination* question, not an emptiness one.
- **Handover Thread C** mentions a "closed-enumeration narrowing" among the unratified
  equality-freeze exclusions. Whether that is the same notion as §6's `denotes_exactly` was
  **not** checked; someone continuing this should read it before assuming either way.
