> ## 📌 STATUS: **RULED [user, 2026-08-03] — option 2: the deferral stands; retained as record**
> The author kept grounding §14's deferral. The pin is re-expected to the v1-honest
> verdict (reject-as-Unproven, never Refuted, live and green), with an `#[ignore]`d
> acceptance twin tagged to the deferred finite-product extension. Recorded in
> `DECISIONS.md` (2026-08-03) and `IMPLEMENTATION-STATUS.md` §4.

# Finding: blocker 1b's acceptance is outside grounding v1's chain license

**Date:** 2026-08-03. **Found while:** starting the authorized slice "pull grounding from the
exact-singleton-chain pin" (completion plan, recommended immediate order step 3).

## The pin as recorded

`analyzer::tests::recursive_domains::a_widened_domain_trap_does_not_refute_the_narrower_call`
(the one `#[ignore]` in the library suite) expects **acceptance** of:

```next
f = (x) => x == 0 ? f(1) : (x == 1 ? 1 : 1 + "x")
f(0)
```

with the reason "proving this call requires grounding §4's exact-singleton fact-chain
mechanism." `IMPLEMENTATION-STATUS.md` §4 and the completion plan (T3.2; recommended order
step 3) carry the same attribution.

## What §4 actually licenses in v1

The chain for `f(0)` walks represented-exact states `Equals(0) → Equals(1) → base` — a
**varying numeric argument**. The manifest-governed grounding specification scopes the v1
license against exactly this shape:

- **GR-10(3) (complete varying call state):** "Every recursively *varying* argument is a
  flat sequence under (1)–(2); every other argument **proven constant** across the
  recursive edges … The finite-product extension (non-sequence varying components over
  proven-finite exact domains) is **recorded, deferred — not v1** [user]."
- **§14 (deferred by ruling [user]):** "the finite-product exact-chain extension
  (GR-10(3)) — **covers numeric finite-state walking** (specimens 11, 22)." §14's header:
  nothing there "may be resurrected by any reading of §§1–13."
- **Specimen 22** (`f = n => n == 0 ? 0 : f(n − 1) + f(n)` at `f(1)`): expected v1 verdict
  "unproven — **numeric exact walking not admitted**." Specimen 11 likewise.

The 1b chain is a non-sequence varying component over a proven-finite exact domain
({0, 1}) — verbatim the deferred extension.

## No other admitted v1 route proves it (checked, not assumed)

- **GR-05 descent:** inapplicable — the recursive edge drifts +1 (ascending); the chain
  terminates by *landing on a base*, not by a well-founded measure.
- **Domain-indexed row facts:** `Equals(1)` is not a row of `f`'s region table. The
  implemented and specified table nests the else-arm ternary ("a `?:` chain nests, so its
  else-arm result is a `Match` the body check recurses into rather than a flattened row" —
  `analyzer/region.rs` header, per region-table v0.3). The top-level rows are
  `(Equals(0), exact)` and the remainder — and a fact over the remainder row correctly
  refuses to prove, since that row also contains trapping inputs (`x = 2`).
- **Generalized facts:** the `Number`-wide fact meets the same trapping inputs; it can
  never prove this call, and refuting it at `f(0)` would manufacture an unrepresented
  witness — the exact false-refutation the pin's *name* guards against.

## Measured current behavior (2026-08-03)

The pinned program **rejects as Unproven** — two advisory warnings plus the seat's
unsuppressible error; **no refutation is minted**. The pin's adversarial half ("the
widened-domain trap must not refute the narrower call") already holds; only the
*acceptance* half awaits a mechanism, and that mechanism is deferred by ruling.

## The options (author's pick; none taken unilaterally)

1. **Stamp the finite-product extension into v1 scope.** A design action on the
   manifest-governed grounding spec (its §14 and GR-10(3), plus the specimen-11/22
   verdicts). Then GR-09/10/11 are implemented with numeric finite-state walking and the
   pin flips green as written.
2. **Keep the deferral; re-expect the pin.** The v1-honest verdict for the pinned program
   is *reject-as-Unproven, never Refuted*. The live test asserts that voice (preserving
   the adversarial content); the acceptance expectation moves to an `#[ignore]`d twin
   tagged to the deferred extension. No design change; the maintainer docs' §4-chain
   attribution for 1b is corrected to "deferred finite-product extension."
3. **A narrower license** the author formulates (a new design round under the
   late-resolution checklist); not sketched here — mechanism formation is not an
   implementation call.

Until one of these is picked, blocker 1b stays pinned exactly as it is, and grounding
remains unwired — no consumer currently licenses it.
