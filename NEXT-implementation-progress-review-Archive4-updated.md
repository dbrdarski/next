# NEXT Implementation Progress Review — Archive(4)

**Review focus:** application/induction tail progress, analyzer soundness boundaries, oracle separation, and remaining implementation risks.

## Executive verdict

This snapshot represents a **major implementation jump**. The application/induction tail has progressed through real recursive return inference, `analyze_apply` rewiring, completion tri-state handling, and realized-witness support.

However, one issue is important enough to treat as a **soundness blocker before calling the induction tail complete**:

> **Active induction hypotheses are still keyed only by `Lambda` shape.**

The v0.8.1 application/induction specification explicitly requires facts to be indexed by the **actual instance/environment and input domain**. Shape alone is insufficient.

In addition, this review identified two cleanup/design issues around the use of the word and mechanism of **fuel**:

1. `REFUTE_FUEL / OutOfFuel` is acceptable only as an **external bounded concrete-witness harness**. Arbitrary execution effort must not become part of the normative analyzer verdict.
2. `segment_nullable(..., 8)` is a genuine hard-coded analyzer depth cap and should be replaced with an **advance-bounded finite algorithm** derived from the recursive-contract graph.

The overall direction remains strong, but these boundaries should be corrected before the analyzer is considered normatively complete.

---

# 1. Progress since the previous snapshot

The previous repository reported:

| Metric | Previous | Current |
|---|---:|---:|
| Library tests | 269 | **302** |
| Passing conformance tests | 111 | **111** |
| Ignored conformance tests | 13 | **13** |
| Rust LOC (`src` + `tests`) | — | **20,409** |

This iteration therefore added **33 library tests**, primarily around the application/induction tail.

The canonical manifest was also checked: **14/14 hashes match**.

The conformance total has not yet moved because Phase A remains staged. Most of the progress is currently below the program-level battery.

---

# 2. What genuinely landed

The induction work is no longer scaffolding. The implementation now contains a substantial chain:

```text
μ/current-closure body walk
        ↓
accepted-domain derivation
        ↓
per-instance outcome summary
        ↓
joint vector induction
        ↓
multi-SCC dependency driver
        ↓
autonomous return-fact proposal
        ↓
analyze_apply consumes inferred return
        ↓
completion tri-state
        ↓
realized-witness refutation
        +
bounded oracle harness
```

Several of these are important milestones.

The recursive return machinery now performs real inference such as:

```text
factorial(Number) → Number
even(Number)      → Boolean
```

rather than merely exposing a standalone induction API.

The completion work is also materially better. A partial pure callee can now produce an expecting-seat error, while uncertain guarded fall-through remains `Unproven` rather than becoming a false rejection.

The realized-witness work is also structurally useful: concrete completing executions can validate a refutation witness, while trapping, non-completing, or bounded-out runs are not treated as counterexamples.

---

# 3. Main soundness issue: hypotheses are keyed by shape only

The current implementation contains an active hypothesis table equivalent to:

```rust
static HYPOTHESES: RefCell<Vec<(Lambda, Contract)>>
```

with lookup conceptually equivalent to:

```rust
hypothesis_for(shape: &Lambda)
```

A candidate itself contains richer information:

```text
callee
args
contract
```

but when the candidate becomes an active induction hypothesis, both the concrete closure instance/environment and the input domain disappear.

This conflicts directly with the v0.8.1 rule that a hypothesis must be indexed by the demanded:

```text
(shape, annotated environment, input domain)
```

and that:

> **shape alone never suffices**

This is now a soundness issue because `analyze_apply` consumes the resulting inferred facts.

---

## 3.1 Same shape, different captured environment

Consider:

```text
make = (v) => () => v

a = make(1)
b = make("s")
```

Both closures have the same lambda shape, but different captured environments:

```text
a → Number
b → String
```

The candidate graph can distinguish the two concrete closure values.

But if the active hypothesis table stores only:

```text
shape S → Number
shape S → String
```

then a lookup by `shape S` can return the wrong fact depending on insertion order.

A call to `b()` could therefore reuse the return fact proved for `a()`.

That is precisely the class of aliasing that instance-indexing is meant to prevent.

A useful adversarial test is:

```text
make = (v) => () => v

a = make(1)
b = make("s")

h = (c, d) =>
    c ? 0 :
    d ? a() :
        b()
```

If the numeric closure fact is accidentally reused for `b`, then a false `h : Number` candidate can potentially close even though:

```text
h(false, false) → "s"
```

This review did not execute the test because no Rust toolchain was available in the environment, so this is a source-derived counterexample class rather than an observed failing test.

---

## 3.2 Same instance, wrong argument domain

The second aliasing problem exists even without multiple captured environments.

Suppose the analyzer proves:

```text
f : I_Number → C
```

A recursive call:

```text
f(String)
```

must not be allowed to reuse that fact unless the new call's input domain is proved to be contained within `I_Number`.

The current shape-only lookup does not encode this requirement.

The normative rule should be:

```text
hypothesis usable
iff
exact instance matches
AND
call input ⊆ fact input domain
```

This is exactly why the specification uses **domain-indexed facts**.

---

# 4. Required correction: instance + domain indexed facts

The current status should not treat domain-indexed facts as a later precision enhancement.

They are a **soundness completion of the already-live induction path**.

The current conceptual representation:

```text
Hypothesis =
    shape
    → return contract
```

needs to become equivalent to:

```text
Hypothesis =
    instance
    × input domain
    → return contract
```

An implementation-level interim representation could use:

```text
callee ValueRef
+ argument/input contract
+ return contract
```

The final spec-oriented form naturally becomes:

```text
shape
+ annotated captured environment
+ input domain I
+ return contract C
```

Then a call may consume a fact only after proving:

```text
callee realizes the same instance

AND

actual argument domain ⊆ fact input domain
```

Otherwise the analyzer must continue through the normal candidate/generalization ladder or return `Unproven`/`Top`.

---

# 5. Recommended adversarial tests

Before further optimization or caching, add tests for the exact fact-identity boundary.

## 5.1 Same shape, different captures

```text
make(1)
make("s")
```

must retain distinct return facts.

## 5.2 Candidate-order independence

Reverse the order in which the same-shape/different-environment candidates are installed.

The inferred result must not change.

## 5.3 Recursive domain escape

Prove a return fact over some input domain `I`, then perform a recursive call whose input is not proved to satisfy `⊑ I`.

The existing hypothesis must not apply.

## 5.4 Same shape + different environment + dependency

A dependent function that calls both closures should be used to test the carried-fact path through the real SCC/vector induction machinery.

---

# 6. AP-30 remains honestly incomplete

The repository no longer appears to overclaim AP-30.

The current outcome summarization conservatively maps uncertain or projected fall-through to:

```text
UnprovenPossible
```

rather than manufacturing a fake concrete witness.

That is acceptable while incomplete.

The eventual AP-30 implementation still needs to preserve the bridge discipline:

```text
fall-through supported only by projected cross-pair
    → UnprovenPossible

fall-through supported by represented R_alt execution
    → ProvenPresent(ApplicationWitness)
```

This naturally belongs in the row-selection/outcome-contribution portion of the tail.

---

# 7. `may_not_complete` is still incomplete

The current outcome summarization still effectively hard-codes:

```text
may_not_complete = false
```

in cases where the specification requires a gray recursive/non-completion possibility.

This does not currently appear to manufacture false safety rejections, but it means the full application-outcome semantics are not yet conformant.

It should be treated as incomplete semantics rather than as a final implementation.

---

# 8. μ-aware body walk: valid now, likely integration debt later

The current body walk resolves recursive/captured callees through the present closure representation:

```text
@capᵢ
→ free_vars[i]
→ closure.env
→ captured closure
```

This is reasonable against the current runtime model.

However, the final μ architecture intends same-group references to live in the μ/GroupTemplate structure rather than as ordinary external captures.

Therefore this should be described as:

> **μ-compatible body walk for the current closure representation**

rather than assumed to be the final body-walk mechanism after universal μ interning is implemented.

That is integration debt, not a present semantic flaw.

---

# 9. Oracle boundary: keep it outside the normative language/analyzer

The oracle should remain a **reference interpreter / validation system**, not a required part of NEXT runtime or normative static analysis.

The intended architecture should remain:

```text
NEXT source
   │
   ├── real compiler/runtime/analyzer
   │
   └── oracle/reference interpreter
```

The oracle is appropriate for:

- implementation validation;
- conformance testing;
- property/fuzz testing;
- checking that concrete analyzer witnesses really execute as claimed;
- optional developer diagnostics.

It should **not** become required for:

- executing NEXT programs;
- canonicalization;
- equality;
- contract proof;
- analyzer termination;
- normative analyzer verdicts.

The preferred direction is:

```text
analyzer derives witness
        ↓
oracle may confirm witness in tests
```

not:

```text
oracle happens to discover witness
        ↓
normative analyzer verdict changes
```

unless a deliberately non-normative diagnostic layer is introduced.

---

# 10. Cleanup/design point 1 — `REFUTE_FUEL / OutOfFuel`

The repository now includes a bounded oracle execution helper with an outcome similar to:

```text
Produced(v)
CompletedWithoutValue
Trapped
OutOfFuel
```

The normal oracle remains unlimited. `OutOfFuel` belongs only to a bounded auxiliary execution harness.

That is acceptable **only if its role remains external concrete-witness search / testing infrastructure**.

The important rule is:

> Arbitrary execution effort must not become part of the normative analyzer verdict.

A hard-coded value such as:

```text
REFUTE_FUEL = 200_000
```

means a larger search budget could potentially discover a concrete witness that a smaller budget misses.

That does **not** create an unsound refutation if only genuine completed counterexamples are accepted.

But it can create effort-dependent behavior:

```text
smaller search budget  → Unproven
larger search budget   → Refuted(witness)
```

That is in tension with NEXT's stronger analyzer principle that verdicts should not depend on arbitrary effort limits.

Therefore the recommended classification is:

```text
normative analyzer
    → structurally finite
    → no arbitrary fuel
    → verdict independent of "try harder"

optional concrete witness search / diagnostics
    → may be bounded
    → OutOfFuel means only "search stopped"
    → never semantic evidence
```

If concrete witness discovery ever becomes part of the normative `Refuted` path, its search bound should instead be derived from the finite analysis structure, not from an arbitrary `REFUTE_FUEL` constant.

The specification requirement that a non-completing execution is not a witness is normative.

The use of an arbitrary execution fuel counter is merely one implementation technique for avoiding a hanging auxiliary run.

---

# 11. Cleanup/design point 2 — `segment_nullable(..., 8)`

A separate and more concerning fuel-like mechanism exists in recursive contract nullability.

The implementation contains logic equivalent to:

```rust
fn segment_nullable(group: &RecGroup, s: &Contract) -> bool {
    fn go(group: &RecGroup, s: &Contract, fuel: usize) -> bool {
        if fuel == 0 {
            return false;
        }

        ...
    }

    go(group, s, 8)
}
```

This is unrelated to the bounded oracle harness.

It is a hard-coded recursive analysis depth:

```text
fuel = 8
```

When the depth is exhausted, the routine returns `false`.

That appears conservative—it does not manufacture a false nullability proof—but it means analyzer precision can depend on an arbitrary magic number.

A recursive structure requiring more than eight unfoldings can be treated differently merely because the implementation happens to contain:

```text
go(..., 8)
```

That is contrary to the project's Principle 7 direction.

Recursive-contract procedures should use:

- graph-theoretic finite state;
- visited-state/SCC algorithms;
- precomputed structural bounds;
- or another bound derived from the recursive contract graph.

They should not use a magic recursion budget.

Therefore:

> **Remove `segment_nullable(..., 8)` and replace it with an advance-bounded finite algorithm whose termination follows from the `RecGroup` structure.**

This is not the same category as `OutOfFuel`.

`OutOfFuel` can remain harmless external harness machinery.

`segment_nullable(..., 8)` is inside analyzer reasoning and deserves actual correction.

---

# 12. Why the fuel review mattered

The word `OutOfFuel` initially looked alarming because NEXT's analyzer architecture explicitly rejects fuel-dependent proof search.

Tracing it exposed two distinct mechanisms:

```text
A. bounded oracle execution
   → acceptable as external/test/diagnostic machinery
   → must not define normative semantics

B. segment_nullable recursion fuel = 8
   → analyzer implementation shortcut
   → should be removed
```

So the concern was useful.

One fuel use is mostly a naming/architectural-boundary issue.

The other is an actual implementation cleanup item.

---

# 13. Realized witness checking does not repair the hypothesis-key problem

The new concrete-witness machinery should not be relied on to compensate for an unsound induction proof.

A bounded concrete execution can only discover some counterexamples.

Sampling or bounded execution is incomplete by construction.

Therefore:

```text
inductive proof
```

must already be sound.

The oracle can validate or supplement diagnostics, but it cannot be the foundation that makes an otherwise incorrectly keyed fact system safe.

---

# 14. Phase A remains the next qualitative milestone

The six Phase-A tests are still ignored.

That gives a useful maturity distinction:

```text
before:
    analyzer infrastructure

current:
    real recursive inference machinery

next:
    end-to-end program-level analyzer judgments
```

Once the instance/domain hypothesis identity is fixed, the remaining outcome details are integrated, and Phase A starts turning green, the implementation will cross another meaningful threshold.

At that point NEXT's unusual analyzer architecture will be participating in complete program judgments rather than existing primarily as individually tested subsystems.

---

# 15. Updated assessment

| Area | Assessment |
|---|---:|
| Breadth of implemented architecture | **9.1 / 10** |
| Analyzer machinery | **9.0 / 10** |
| Recursive contract machinery | **9.3 / 10** |
| Application/induction implementation depth | **8.8 / 10** |
| Current induction soundness confidence | **8.1 / 10** |
| Spec integration | **8.6 / 10** |
| Overall implementation maturity | **8.8 / 10** |

The score still increases relative to the previous checkpoint because a large amount of difficult machinery has genuinely landed.

It does not yet move above 9 overall because the missing instance/domain key sits exactly where a provisional recursive assumption becomes a reusable proof fact.

That is too central to treat as polish.

---

# 16. Recommended next order

The next work should prioritize soundness boundaries before caching or cleanup:

```text
1. full instance + domain-indexed hypothesis key
2. adversarial same-shape / different-environment tests
3. recursive domain-escape tests
4. remove segment_nullable(..., 8) magic fuel
5. keep REFUTE_FUEL strictly outside normative analyzer semantics
6. complete AP-30 represented fall-through
7. complete may_not_complete semantics
8. sampled γ / soundness battery
9. activate A-ACC / A-SND
10. evaluation cache
11. program-level M-04
```

The cache should come only after fact identity is correct.

Otherwise the implementation would merely cache an incorrectly identified proof fact more efficiently.

---

# Final verdict

This is one of the strongest implementation jumps in the project so far.

The important positive change is that the application/induction design is now becoming **real analyzer machinery**, not merely a specification or isolated set of helper algorithms.

The important caution is equally specific:

> **Do not treat the current shape-only active hypothesis map as final. Facts must be indexed by the actual closure instance/environment and the input domain over which they were proved.**

And the fuel audit adds two concrete cleanup/design conclusions:

> **`REFUTE_FUEL / OutOfFuel` is acceptable only as external bounded witness-search infrastructure and must not make normative analyzer verdicts effort-dependent.**

> **`segment_nullable(..., 8)` should be removed and replaced by an advance-bounded finite algorithm derived from recursive-contract structure.**

With those boundaries corrected, the remaining induction work can continue on a much firmer foundation.
