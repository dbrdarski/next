# NEXT Implementation Review — Archive(5)

**Review focus:** verification of the Archive(4 soundness fixes, induction hypothesis identity, recursive-contract termination cleanup, and the oracle/analyzer boundary.

## Executive verdict

The two main corrections requested after the Archive(4 review are genuinely present in the current source:

1. **The shape-only induction hypothesis bug is fixed.**
2. **The hard-coded `segment_nullable(..., 8)` recursion fuel is removed and replaced with structural cycle detection.**

I would sign off on both fixes.

However, this review found two important qualifications before considering the induction foundation fully settled:

- the wrong-domain hypothesis guard is implemented correctly, but the claimed indirect regression no longer actually tests rejection after the new same-arity domain propagation;
- the analyzer already contains older direct dependencies on the oracle for constant folding and primitive evaluation, including a closed-call path that can execute a diverging user function during static analysis.

The first is mainly a testing/provenance issue.

The second is an architectural implementation-debt issue and should be corrected if the intended NEXT architecture keeps the oracle strictly as validation/reference infrastructure rather than normative analyzer machinery.

---

# 1. The main soundness blocker is fixed

The active induction hypothesis is no longer keyed only by `Lambda` shape.

It now has the conceptual form:

```rust
struct Hypothesis {
    callee: ValueRef,
    input: Vec<Contract>,
    contract: Contract,
}
```

Hypothesis lookup requires both:

```text
same concrete callee instance
AND
actual args ⊑ hypothesis input domain
```

The application analyzer now passes the actual closure value and actual argument contracts into hypothesis lookup rather than only a Lambda shape.

This closes both aliasing classes identified in the Archive(4 review:

```text
same shape + different captured environment
```

and:

```text
same instance + incompatible input domain
```

## Verdict

**Fixed.**

---

# 2. Same-shape/different-captures regression is good

The adversarial regression requested in the previous review is now present.

It constructs the equivalent of:

```text
make = (v) => () => v

a = make(1)
b = make("s")
```

Both closures have the same Lambda shape, but distinct captured environments.

The test verifies that:

```text
a → Number
b → String
```

remain distinct facts.

It also checks a dependent caller conceptually equivalent to:

```text
h = (c, d) =>
    c ? 0 :
    d ? a() :
        b()
```

and confirms that the analyzer does not falsely close `h` as `Number`.

This directly exercises the aliasing bug from the prior review.

## Verdict

**Good regression coverage.**

---

# 3. Input-domain containment is implemented correctly

The hypothesis lookup now checks that the actual argument contracts are covered by the hypothesis input domain.

Conceptually:

```text
hypothesis usable
iff
callee == hypothesis.callee
AND
actual args ⊑ hypothesis.input
```

So a fact such as:

```text
f : [Number] → Boolean
```

must not be reused for:

```text
f(String)
```

or for an input domain broader than the fact's proven domain.

The implementation contains the correct guard.

## Verdict

**Implemented correctly.**

---

# 4. But the explicit wrong-domain regression is still missing

The progress report says the even/odd mutual-recursion test now covers the domain-rejection rule implicitly.

It no longer really does.

The earlier failing situation was:

```text
root even analyzed over [Number]

odd analyzed over [Top]

odd calls even(n - 1)

derived argument domain:
    Number ∪ Indeterminate

not ⊑ Number

therefore the hypothesis correctly declines
```

But the implementation was subsequently changed so that the root call-site domain is propagated to same-arity mutual/reachable partners.

That means `odd` is now analyzed over `[Number]`, so the previous out-of-domain lookup is no longer generated.

Therefore the test does not directly exercise:

```text
hypothesis_for(f, [String]) → None
```

even though the implementation should behave that way.

## Recommended direct unit test

The cleanest regression should target the hypothesis machinery itself:

```text
install:
    f : [Number] → Boolean

query:
    hypothesis_for(f, [Number])      → Boolean
    hypothesis_for(f, [Equals(1)])   → Boolean
    hypothesis_for(f, [String])      → None
    hypothesis_for(f, [Top])         → None
```

This locks the law directly without involving execution, recursion, or the oracle.

## Verdict

**Implementation correct; direct regression still owed.**

---

# 5. Same-arity domain propagation should remain explicitly provisional

The fix that restored mutual recursive inference propagates the root call-site input domain to reachable same-arity closures.

Conceptually:

```text
if reachable callee arity == root arity:
    use root call-site domain
else:
    use callee-derived domain
```

This is useful for the current even/odd-style mutual recursion.

However, it is broader than the final application/induction design.

It does not mean:

```text
members of the same recursive SCC
```

It means approximately:

```text
reachable closures with matching arity
```

That can include ordinary downstream helpers.

Example:

```text
root(Number)
   ↓
helper(String)
```

If both have one parameter, the current mechanism may initially propose `helper` over the root's `Number` domain.

The new hypothesis-domain guard prevents a mismatching actual call from consuming the wrong fact, so no false-proof counterexample was established from this.

But it is not the final §5/§6 domain construction.

The specification's more principled mechanism is:

```text
symbolic body verification
        ↓
actual call edge
        ↓
actual demanded callee instance
+
actual demanded input domain
        ↓
candidate fact
```

rather than:

```text
same arity
        ↓
share root domain
```

## Recommendation

Treat the current propagation as:

> **an interim precision mechanism**

not as the final domain-indexed candidate semantics.

If retained temporarily, restricting it to the relevant recursive SCC would make its meaning cleaner than applying it to every reachable same-arity closure.

## Verdict

**Safe-looking interim heuristic; not the final §5 mechanism.**

---

# 6. `segment_nullable(..., 8)` is properly removed

The previous implementation used a hard-coded recursive depth:

```rust
go(group, s, 8)
```

That is gone.

It has been replaced by path-based cycle detection over recursive-contract member names.

Conceptually:

```text
if Ref(name) is already on active path:
    cut this back-edge

otherwise:
    push name
    recurse
    pop name
```

The termination argument is now structural:

```text
each RecGroup member appears at most once on the active path
        ↓
maximum path length ≤ number of RecGroup members
```

This is exactly the Principle-7-compatible shape requested in the prior review.

It also improves precision:

```text
non-cyclic depth > 8
```

is now followed correctly, while only genuine cycles are cut.

## Verdict

**Approved.**

---

# 7. `REFUTE_FUEL / OutOfFuel` remains contained

The bounded witness-search mechanism still exists.

It produces outcomes conceptually like:

```text
Produced(v)
CompletedWithoutValue
Trapped
OutOfFuel
```

The important current fact is:

> `REFUTE_FUEL` is not presently on the normal `analyze_apply` verdict path.

The bounded witness machinery is used from `check_return_claim` / realized-refutation support and tests, not by the current normative analyzer flow.

Therefore today:

```text
REFUTE_FUEL
```

does not decide a normal compiler judgment.

This matches the boundary requested in the previous review.

## Standing rule

It should remain:

```text
optional / external concrete-witness search
```

rather than:

```text
normative analyzer proof procedure
```

A found concrete witness can of course be genuine evidence.

But whether the search happens to find that witness must not make analyzer semantics depend on an arbitrary constant such as:

```text
REFUTE_FUEL = 200_000
```

## Verdict

**Currently contained correctly. Keep it that way.**

---

# 8. Important correction: the analyzer already depends on the oracle elsewhere

This is the biggest new architectural finding in Archive(5).

The intended architecture is:

```text
NEXT source
   │
   ├── real runtime / compiler / analyzer
   │
   └── oracle reference interpreter
```

with the oracle used for:

- conformance;
- testing;
- implementation validation;
- property/fuzz checking;
- optional diagnostics.

However, the current analyzer already imports and uses oracle functionality directly.

Examples include:

```text
eval_prim(...)
```

for primitive operation folding, and:

```text
eval_expr(...)
```

for closed access expressions and fully-known function applications.

The important closed-call path is conceptually:

```text
if callee and args are fully known:
    execute the entire call through eval_expr
    use its result as analyzer folding
```

This creates a direct semantic/termination dependency:

```text
closed recursive call
        ↓
analyzer tries to constant-fold it
        ↓
oracle executes user function
        ↓
user function diverges
        ↓
analyzer hangs / overflows
```

This is exactly what surfaced when a direct domain-escape test attempted a closed diverging call.

The repository has correctly registered the divergence issue, but the architectural problem is broader than merely:

> `eval_expr` is unbounded.

It is:

> **The normative static analyzer should not require execution by the reference oracle to establish its normal judgments.**

---

# 9. Recommended oracle separation

The analyzer should not depend on the complete reference interpreter.

Instead, shared finite semantic laws should be extracted into neutral implementation components.

## Primitive operations

If both analyzer and oracle need exact primitive semantics:

```text
semantics::primitive
        ↑          ↑
     oracle     analyzer
```

That is not the analyzer "asking the oracle."

Both systems are using the same semantic kernel.

## Closed field/index operations

Likewise, finite canonical-value access operations can live in a neutral semantic helper.

## Closed function applications

This is different.

The analyzer should not do:

```text
analyzer
    ↓
eval_expr(full user call)
```

for normal proof/folding.

Instead it should stay inside the analyzer:

```text
input obligation
        ↓
completion reasoning
        ↓
return fact / induction
        ↓
static result
```

If exact constant folding cannot be established structurally, returning a less precise result is preferable to making analyzer termination depend on executing the user's function.

## Recommendation

Remove the full-function `eval_expr` dependency from normative analyzer paths.

## Verdict

**Current implementation debt; should be raised in priority.**

---

# 10. Oracle directionality should remain one-way

The preferred relationship is:

```text
analyzer derives a proof or witness
        ↓
oracle verifies it in tests
```

not:

```text
oracle executes/searches
        ↓
normative analyzer obtains its semantic verdict
```

The oracle is extremely valuable as an independent executable semantic reference.

That value is strongest when it remains independent.

Making the analyzer depend on it weakens both the architectural separation and the ability to use the oracle as a truly external concordance check.

---

# 11. AP-30 remains owed

The current implementation still conservatively represents uncertain/projected fall-through without manufacturing a false structural witness.

The eventual rule remains:

```text
fall-through supported only by projected cross-pair
    → UnprovenPossible

fall-through supported by represented R_alt execution
    → ProvenPresent(ApplicationWitness)
```

This remains legitimate tail work.

## Verdict

**Still owed.**

---

# 12. `may_not_complete` remains owed

The application outcome still does not fully model all specification-required possible non-completion cases.

This does not currently appear to manufacture false rejections, but it means the complete application-outcome semantics are not yet finished.

## Verdict

**Still owed.**

---

# 13. Updated checkpoint table

| Item | Verdict |
|---|---|
| Shape-only hypothesis aliasing | **✅ fixed** |
| Instance-keyed hypothesis | **✅** |
| Input-domain containment guard | **✅ implemented** |
| Direct out-of-domain regression | **⚠️ still missing** |
| Same-shape/different-captures regression | **✅ good** |
| Same-arity domain propagation | **🟡 safe-looking interim heuristic, not final §5 mechanism** |
| `segment_nullable(..., 8)` | **✅ properly removed** |
| Structural nullability termination | **✅ advance-bounded** |
| `REFUTE_FUEL` affecting normal verdicts | **✅ currently no** |
| Oracle used by normative analyzer generally | **⚠️ yes, already** |
| Closed-call oracle divergence | **⚠️ real current issue** |
| AP-30 | **⬜ owed** |
| `may_not_complete` | **⬜ owed** |

---

# 14. Recommended next order

Given the current state, the recommended priority changes slightly.

```text
1. add direct out-of-domain hypothesis regression
2. remove full eval_expr dependency from normative analyzer paths
3. keep same-arity domain propagation explicitly provisional
4. replace it eventually with actual call-edge/domain-derived candidates
5. complete AP-30 represented fall-through
6. complete may_not_complete semantics
7. γ / soundness battery
8. activate A-ACC / A-SND
9. evaluation cache
10. program-level M-04
```

Primitive/shared finite semantic helpers can remain shared if extracted from the oracle into neutral semantic code.

The important boundary is specifically:

```text
static analyzer must not execute arbitrary user functions
through the reference interpreter
to obtain normal static judgments
```

---

# Final verdict

The Archive(4 soundness blocker has been repaired correctly.

The strongest positive result is:

> **Induction facts are now keyed by the actual closure instance plus the input domain over which they were proved, and same-shape/different-capture aliasing has a concrete adversarial regression.**

The recursive-contract fuel cleanup is also exactly right:

> **`segment_nullable(..., 8)` is gone and replaced with structural path-bounded cycle detection.**

Two follow-ups remain important:

> **Add a direct regression proving that out-of-domain hypothesis lookup is rejected.**

and, more significantly:

> **Remove the analyzer's dependency on full oracle execution for closed user-function constant folding. The oracle should remain reference/validation infrastructure, not normative analyzer machinery.**

The current same-arity domain propagation appears safe as an interim mechanism because the new domain guard prevents mismatched facts from being consumed, but it should not be mistaken for the final call-edge/domain-indexed candidate construction required by the application/induction design.
