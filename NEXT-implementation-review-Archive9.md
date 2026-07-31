> ## 📗 STATUS: **HISTORICAL** — record of a past review/audit; not current guidance
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Left unedited.

# NEXT Implementation Review — Archive(9)

**Review focus:** verification of the `InstanceBodySummary` unification, `(instance, input-domain)` recursion identity, multi-callee enumeration, recursive-domain generalization, termination guarantees, and readiness to proceed to AP-30.

## Executive verdict

Archive(9 makes a strong architectural improvement.

The new:

```text
instance_body_summary(callee, args)
    → {
        produced,
        completion,
        findings
      }
```

does successfully unify several previously separate mechanisms around the correct semantic unit:

```text
(concrete instance, demanded input domain)
```

The four Archive(8) adversarial gates are represented in the implementation and the design now correctly distinguishes:

- same Lambda shape but different captured environments;
- the same closure instance under different demanded input domains;
- multiple concrete callee alternatives;
- exact non-recursive return information such as `Equals(true)`.

However, I would **not sign off on AP-30 yet**.

Three issues remain important:

1. **Recursive-domain widening can propagate a trap discovered only in a broader domain back into a narrower call.** This can manufacture a false rejection.
2. **`callee_alternatives` silently drops non-singleton or non-function alternatives when at least one known concrete function is present.** This can manufacture a false acceptance.
3. **The new dynamic domain-generalization rule does not guarantee Principle-7 termination for arbitrary contract domains.** `Range`, relational contracts, tuples, records, etc. can form an unbounded sequence of distinct abstract states.

The unification itself is the right direction.

The current **domain closure and alternative enumeration** are not yet sufficient to make that unified mechanism normatively sound.

---

# 1. What the unification gets right

The new design replaces several overlapping mechanisms with a single body-summary concept:

```text
(instance, demanded input domain)
        ↓
InstanceBodySummary
        ├── produced
        ├── completion
        └── findings
```

This is a significant improvement over the previous split between:

```text
return inference
body_safety
completion
```

The semantic identity is also much stronger than the earlier Lambda-shape cutoff.

## Good consequences

The implementation now correctly handles:

```text
same shape
+
different captures
```

as distinct states.

It also distinguishes:

```text
same closure instance
+
different demanded input domains
```

and can propagate exact non-recursive returns such as:

```text
always() → Equals(true)
```

instead of immediately coarsening them to `Boolean` or `Top`.

## Verdict

**Architecturally correct direction.**

---

# 2. Archive(8 gate A — same shape, different captures

The previous counterexample was:

```next
bad = () => 1 + "x"

make = (f) => () => f()

b = make(bad)
c = make(b)

c()
```

`b` and `c` share the same Lambda shape but have different captured environments.

The new `(instance, input-domain)` identity keeps them separate.

That prevents the previous shape-cutoff bug where analysis of `b` could be skipped merely because `c` had the same Lambda shape.

## Verdict

**Fixed.**

---

# 3. Archive(8 gate B — same instance, changed demanded domain

The previous recursive-domain counterexample was:

```next
f = (x) =>
    x == 0 ? f("x") : x + 1

f(0)
```

The nested recursive call is:

```text
same closure instance
+
String input domain
```

rather than:

```text
same closure instance
+
Equals(0)
```

The new body-summary identity recognizes that distinction and analyzes the nested state accordingly.

## Verdict

**Fixed for this class of singleton-domain transition.**

---

# 4. Archive(8 gate C — multiple concrete callees

The implementation now handles a union of concrete singleton function values such as:

```next
bad = () => 1 + "x"
good = () => 1

root = (b) =>
    (b ? bad : good)()
```

Both:

```text
Equals(bad)
```

and:

```text
Equals(good)
```

can be enumerated and inspected.

That closes the previous singleton-only body-safety gap for this concrete-union case.

## Verdict

**Improved and correct for unions consisting entirely of concrete function singletons.**

---

# 5. Archive(8 gate D — exact non-recursive return

The new summary preserves the exact non-recursive body contract.

For:

```next
always = () => true
```

the summary can retain:

```text
Equals(true)
```

so:

```next
root = () =>
    always() ? 1 : 1 + "x"
```

can eliminate the false branch and avoid a false trap.

This is a meaningful precision improvement and shows why combining body safety with return information is the correct architectural direction.

## Verdict

**Good.**

---

# 6. Soundness blocker: widened-domain trap can refute a narrower call

The new recursive cycle handling dynamically generalizes a recursive call's domain.

Conceptually:

```text
Equals(1)
    ↓
Number
```

when the same instance re-enters under a different domain.

The problem is not that generalization exists.

The problem is that **Error findings discovered under the broader domain can then be propagated back to the narrower call**.

That is not sound.

---

## 6.1 Concrete false-rejection counterexample

Consider:

```next
f = (x) =>
    x == 0
        ? f(1)
        : x == 1
            ? 1
            : 1 + "x"

f(0)
```

Concrete execution is safe:

```text
f(0)
→ f(1)
→ 1
```

But the recursive summary can proceed approximately as:

```text
f(0)
    ↓
f(1)
    ↓
same instance re-entered
    ↓
generalize Equals(1) → Number
    ↓
analyze f(Number)
```

Under:

```text
x : Number
```

the branch:

```next
1 + "x"
```

is reachable for numbers other than `0` and `1`.

So the generalized analysis can produce a proven operation-safety `Error`.

If that `Error` is then propagated back to:

```text
f(1)
```

and ultimately:

```text
f(0)
```

the analyzer rejects a call whose represented executions never reach the trap.

That violates the required witness direction.

---

# 7. Why this violates the application witness discipline

Generalization can safely support a universal proof:

```text
broad domain is safe
        ↓
narrower domain is safe
```

For example:

```text
Number proven safe
⇒ Equals(1) safe
```

But refutation does not move downward automatically.

This is invalid:

```text
there exists a trap in Number
        ↓
therefore Equals(1) traps
```

unless the trap witness is actually represented inside:

```text
Equals(1)
```

So:

```text
trap in generalized domain
```

must not become:

```text
Refuted narrower call
```

without a represented witness.

This is conceptually the same discipline behind AP-29/AP-30.

## Required rule

A generalized summary may safely contribute conservative positive information.

But a narrower call can be refuted only by:

```text
ApplicationWitness
```

whose execution belongs to that narrower call's represented relation.

---

# 8. Recommended safety-summary shape

The current summary transports `findings`.

For cross-domain use, a stronger representation would be something like:

```text
InstanceBodySummary {
    produced,
    completion,
    may_not_complete,

    safety:
        ProvenSafe
      | Refuted(ApplicationWitness)
      | Unproven
}
```

Then domain generalization has a clear variance rule:

```text
ProvenSafe(broad)
    → can establish ProvenSafe(narrow)
```

while:

```text
Refuted(broadWitness)
```

can refute the narrow state only if:

```text
broadWitness ∈ narrow represented domain
```

Otherwise:

```text
Unproven
```

is the correct result.

---

# 9. Soundness blocker: mixed callee alternatives can be silently dropped

The new `callee_alternatives` logic recursively extracts concrete function singleton leaves:

```text
Equals(function)
```

from unions.

But other leaves contribute nothing.

Conceptually:

```rust
match contract {
    Equals(v) if v.is_function() => add(v),
    Union(a, b) => recurse(a); recurse(b),
    _ => {}
}
```

This is not always conservative.

If **no** known function alternative is found, the caller may coarsen to `Top`.

But when a union contains:

```text
known concrete function
+
unknown or non-function alternative
```

the known function is analyzed while the other live alternative silently disappears.

That can create a false acceptance.

---

# 10. Counterexample — function + non-function

Consider:

```next
good = () => 1

root = (b) =>
    (b ? good : 1)()
```

For:

```text
b : Boolean
```

the callee contract can represent:

```text
Equals(good) ∪ Equals(1)
```

The whole union is not disjoint from `Function`, so a coarse top-level "not callable" check cannot reject it outright.

Then the concrete-function extractor finds:

```text
good
```

and drops:

```text
1
```

The known function path is safe.

But the represented execution:

```text
b = false
→ 1()
```

is an operation-safety trap.

If that alternative disappears from the application outcome, the analyzer can incorrectly accept the call.

## Classification

**False-acceptance soundness gap.**

---

# 11. Counterexample — known function + unknown function

Consider:

```next
good = () => 1

root = (b, f) =>
    (b ? good : f)() + 1
```

with:

```text
f : Function
```

The abstract callee can contain:

```text
Equals(good) ∪ Function
```

The implementation can inspect `good` but has no concrete instance for the unknown `Function` alternative.

If the unknown alternative is simply dropped, the application can appear to return exactly:

```text
Equals(1)
```

making:

```text
+ 1
```

look proven safe.

But the unknown function may:

- return a String;
- complete without a value;
- trap internally;
- return another incompatible value.

The correct combined result therefore cannot be derived solely from the known `good` branch.

The unknown alternative must contribute a conservative outcome such as:

```text
produced      → Top / unknown
completion    → unknown contribution
safety        → Unproven
```

rather than disappearing.

## Classification

**Soundness gap.**

---

# 12. The full correlated application driver is still not the normal path

NEXT already has machinery for analyzing a joint operand:

```text
[callee, ...arguments]
```

per live correlated alternative.

That architecture exists specifically to avoid losing the relationship between:

```text
which callee
```

and:

```text
which arguments
```

Normal `analyze_apply`, however, is still substantially driven from:

```text
callee contract
+
separate argument contracts
```

and then concrete singleton extraction from the callee contract.

Therefore the phrase:

> "enumerates every live callee alternative"

is currently too strong.

It enumerates every **extractable concrete function singleton** from the projected callee contract.

It does not yet process the complete joint live-alternative relation required by v0.8.1.

## Verdict

**Integration gap remains.**

---

# 13. Principle-7 blocker: dynamic generalization is not guaranteed to terminate

The current recursive-domain strategy relies on the idea that a different recursive domain can be generalized and eventually stabilize.

However, `Contract::generalize()` only meaningfully widens certain contract forms, especially singleton equality and unions containing them.

Conceptually:

```text
Equals(v)
    → Kind(v)
```

But many contract forms remain structurally unchanged, including important classes such as:

```text
Range
Greater
Less
Mod
Geo
Tuple
Record
LengthRestricted
...
```

Therefore a recursive program can generate an unbounded sequence of distinct input-domain contracts for the same closure instance.

---

# 14. Concrete infinite abstract-domain chain

Consider conceptually:

```next
f = (x, y) => f(x + y, y)
```

Analyze with:

```text
x : Range(0, 1)
y : Range(1, 2)
```

If arithmetic transfer preserves range information:

```text
Range(a,b) + Range(c,d)
→ Range(a+c, b+d)
```

then recursive states can become:

```text
f(Range(0,1), Range(1,2))
↓
f(Range(1,3), Range(1,2))
↓
f(Range(2,5), Range(1,2))
↓
f(Range(3,7), Range(1,2))
↓
...
```

For each:

```text
generalize(Range(...))
=
Range(...)
```

So the "generalized" domain is identical to the incoming domain.

No finite stabilization occurs.

Every state has:

```text
same closure instance
+
new input domain
```

and therefore creates another body-summary state.

This violates the required Principle-7 guarantee.

## Classification

**Termination blocker.**

---

# 15. Why patching `Contract::generalize()` is not the right final solution

One possible response would be to add more widening cases:

```text
Range → Number
Greater → Number
Tuple components → kinds
...
```

That may help particular examples.

But it remains a dynamic widening strategy:

```text
keep inventing domains
until they stabilize
```

That is weaker than NEXT's stated analyzer architecture.

The application/induction specification already has the stronger solution:

```text
finite admitted instance inventory
+
finite candidate-domain inventory
+
GeneralizationDomains(shape)
+
candidate graph
+
SCC processing
```

The compiler should know the finite abstract state universe **before** open-ended recursive analysis begins.

That is the Principle-7 design.

---

# 16. Correct long-term body-summary architecture

The body-summary unification should be kept.

The state should remain conceptually:

```text
InstanceBodyState =
    instance
  + admitted input domain
```

But `admitted input domain` must come from a finite, preconstructed candidate universe.

Then:

```text
(instance, I)
        ↓
InstanceBodySummary
        ├── produced
        ├── completion
        ├── may_not_complete
        └── safety
```

and recursive calls create dependencies only on another state already admitted in that finite universe.

The SCC machinery can then close cycles without:

- magic fuel;
- open-ended dynamic widening;
- unbounded domain invention.

---

# 17. Required tests before AP-30

The following tests should gate the next step.

## 17.1 Widened-domain false refutation — must accept

```next
f = (x) =>
    x == 0
        ? f(1)
        : x == 1
            ? 1
            : 1 + "x"

f(0)
```

Expected:

```text
accepted
```

The trap reachable elsewhere in `Number` must not refute the represented `f(0) → f(1)` execution.

---

## 17.2 Mixed function/non-function callee — must reject

```next
good = () => 1

root = (b) =>
    (b ? good : 1)()
```

Expected:

```text
non-function alternative contributes operation-safety failure
→ caller rejected
```

---

## 17.3 Known + unknown function alternative — must not sharpen from known branch alone

Analyzer-level state:

```text
callee =
    Equals(good)
    ∪
    Kind(Function)
```

Expected combined result:

```text
known good branch
+
unknown function branch
→ conservative combined application outcome
```

The unknown branch must not disappear.

---

## 17.4 Changing non-singleton recursive domain — must terminate

Conceptually:

```next
f = (x, y) => f(x + y, y)
```

with:

```text
x : Range(0,1)
y : Range(1,2)
```

Expected:

```text
analysis terminates by construction
```

not because:

- a stack limit was reached;
- execution fuel was exhausted;
- dynamic widening happened to stabilize.

---

# 18. What is approved

The following Archive(9 changes are worth keeping:

- `(instance, input-domain)` body-summary identity;
- same-shape/different-capture separation;
- same-instance/different-singleton-domain handling;
- exact non-recursive return propagation;
- shared safety/completion/non-recursive return analysis;
- removal of user-function oracle execution;
- concrete function-union enumeration;
- elimination of Lambda-shape safety identity.

These are all improvements.

The current blockers are specifically in:

```text
recursive domain closure
```

and:

```text
partial application-alternative enumeration
```

not in the unification concept itself.

---

# 19. Updated status

| Area | Verdict |
|---|---|
| `(instance, domain)` summary identity | **✅ correct direction** |
| Same shape / different captures | **✅** |
| Same instance / different singleton domain | **✅ tested** |
| Shared safety/completion/nonrecursive return | **✅ strong consolidation** |
| Exact nonrecursive return | **✅** |
| Concrete singleton-function union enumeration | **✅ partial** |
| Dynamic Kind generalization for recursive safety | **🔴 unsound for refutation** |
| Termination for arbitrary contract-domain chains | **🔴 not guaranteed** |
| Mixed known/non-function callee union | **🔴 soundness gap** |
| Mixed known/unknown function union | **🔴 soundness gap** |
| Full correlated application alternatives | **🟡 not yet wired into normal path** |
| AP-30 | **⏸ hold** |

---

# 20. Recommended next step

Keep the `InstanceBodySummary` unification.

Do **not** revert to:

- Lambda-shape safety stacks;
- oracle execution;
- independent body-safety walks.

Instead:

1. Move recursive body-summary states onto the specification's **precomputed finite instance/domain candidate universe**.
2. Remove dynamic recursive-domain widening as the mechanism that establishes termination.
3. Preserve directional safety evidence:
   - broad-domain proof of safety can establish narrow-domain safety;
   - broad-domain refutation may refute a narrow state only with a represented witness belonging to that narrow state.
4. Make application alternative handling total:
   - concrete function alternative → analyze it;
   - unknown function alternative → conservative/Unproven contribution;
   - non-function alternative → operation-safety contribution;
   - no live alternative may silently disappear.
5. Reuse the joint correlated operand machinery so callee alternatives remain paired with their represented argument alternatives.

A concise implementation directive would be:

> **Keep `InstanceBodySummary`, but make its recursion range over the specification's advance-bounded finite `(instance, admitted-domain)` candidate graph rather than dynamically generated `Contract` domains. Safety refutation must carry a represented witness valid for the demanded state. Application analysis must account conjunctively for every live correlated alternative, including unknown-function and non-function leaves; no alternative may be silently dropped.**

---

# Final verdict

The Archive(9 unification passes architectural review.

Its current recursion closure and application-alternative enumeration do not yet pass soundness/termination review.

The most important new rule is:

> **A trap discovered only after widening to a broader domain cannot refute a narrower call unless the trap has a witness represented by that narrower call.**

And the most important termination rule remains:

> **The analyzer's recursive state universe must be finite in advance; it should not depend on dynamically inventing domains until one happens to repeat.**

Finally:

> **Every live application alternative must contribute to the combined outcome. Known concrete functions may be analyzed precisely, but unknown-function and non-function alternatives must not disappear.**

I would fix those three boundaries before proceeding to AP-30, because AP-30's own structured-witness discipline depends directly on them.
