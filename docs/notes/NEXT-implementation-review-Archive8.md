> ## 📗 STATUS: **HISTORICAL** — record of a past review/audit; not current guidance
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Left unedited.

# NEXT Implementation Review — Archive(8)

**Review focus:** verification of the Archive(7 body-safety corrections, the new edge-following safety mechanism, recursion cutoff identity, multi-callee safety, and whether body safety is ready to proceed to AP-30.

## Executive verdict

Archive(8 genuinely fixes the two concrete soundness regressions identified in the previous review:

1. parameter/local callees are now followed through the actual abstract call site;
2. callee safety is checked using the argument domain carried by that call edge rather than a propagated/root domain.

The dead-arm narrowing added to `analyze_match` also correctly fixes the paired false-rejection case.

However, the replacement introduces a new **soundness blocker**:

> `SAFETY_STACK` is keyed only by `Lambda` shape.

That can suppress analysis of:

- a different closure instance produced from the same Lambda shape but with different captures;
- the same closure instance when recursively called under a different demanded input domain.

In addition, normal `analyze_apply` only invokes body safety when the callee contract is a singleton `Equals(cv)`, so a call with multiple possible concrete function alternatives can still bypass safety propagation.

The body-safety mechanism is therefore improved but not yet general enough to be considered normatively sound.

The consistent architectural solution is now clear:

> **Use `(concrete instance, demanded input domain)` as the unit of interprocedural body analysis and fold safety, completion, return information, and future `may_not_complete` into a shared `InstanceBodySummary` carried by the existing finite candidate/SCC machinery.**

AP-30 should remain paused until this foundation is corrected.

---

# 1. Archive(7 counterexamples are genuinely fixed

The new `body_safety` no longer uses the previous:

```text
reachable_closures
+
group_domains
```

walk as its semantic basis.

Instead, nested applications surface safety through the normal abstract application path.

That means an actual call such as:

```next
bad = () => 1 + "x"

invoke = (f) => f()

invoke(bad)
```

can resolve `f` from the abstract value carried by the parameter and propagate into `bad`.

Likewise:

```next
helper = (x) => x + 1

root = (n) => helper("x")
```

checks `helper` using the actual call-edge argument domain:

```text
String
```

rather than incorrectly reusing the root's:

```text
Number
```

domain.

## Verdict

**Both Archive(7 false-acceptance classes are fixed.**

---

# 2. Dead-arm narrowing is a good correction

The Archive(7 precision counterexample was:

```next
helper = (x) =>
    x == 0 ? 1 : 1 + "x"

root = () => helper(0)
```

The previous analyzer could inspect the dead second arm and produce a false trap.

Archive(8 changes `analyze_match` so that:

```text
proven-empty region
    → skip arm

proven-false guard
    → skip arm

proven-true guard
    → consume region

uncertain guard
    → preserve remaining uncertainty
```

This is the correct direction.

For `x = Equals(0)` the trapping branch becomes unreachable and is not analyzed as a live execution.

## Verdict

**Approved.**

---

# 3. New blocker: `SAFETY_STACK` is keyed by Lambda shape only

The new recursion guard is conceptually:

```rust
static SAFETY_STACK: RefCell<Vec<Lambda>>
```

and body safety cuts recursion when:

```rust
if stack.contains(&shape) {
    return [];
}
```

This reintroduces an identity mistake already discovered and fixed in the return-fact system:

```text
same Lambda shape
≠
same semantic analysis state
```

For body safety, the relevant state must include at least:

```text
concrete closure instance
+
demanded input domain
```

not only the Lambda shape.

---

# 4. Counterexample A — same shape, different captures

Consider:

```next
bad = () => 1 + "x"

make = (f) => () => f()

b = make(bad)
c = make(b)

c()
```

`b` and `c` are distinct closures created from the same inner Lambda expression.

Their shape is the same, but their captures differ:

```text
b captures bad
c captures b
```

Concrete execution is:

```text
c()
→ b()
→ bad()
→ trap
```

But body safety can behave like:

```text
body_safety(c)
    push shape S

    analyze c body
        → calls b()

        body_safety(b)
            shape(b) == S
            S already active
            → cutoff
```

`b`'s capture-dependent body is skipped before it can lead to `bad`.

Potential result:

```text
c()
→ accepted
```

despite guaranteed concrete trapping.

## Classification

**Soundness blocker.**

---

# 5. Counterexample B — same instance, different demanded input domain

Changing the stack key from `Lambda` to only `ValueRef` would still not be enough.

Consider:

```next
f = (x) =>
    x == 0
        ? f("x")
        : x + 1

f(0)
```

For the outer call:

```text
x = Equals(0)
```

the second branch is correctly dead.

The live branch makes a recursive call:

```text
f("x")
```

The recursive semantic state is therefore:

```text
same closure instance
+
different input domain = String
```

Under `String`:

```text
x + 1
```

traps.

But a stack keyed only by shape sees that `f` is already active and cuts the nested analysis.

Potential result:

```text
f(0)
→ accepted
```

even though:

```text
f(0)
→ f("x")
→ "x" + 1
→ trap
```

This demonstrates that the correct safety state is not merely:

```text
Lambda
```

or even:

```text
ValueRef
```

but:

```text
(instance, demanded input domain)
```

## Classification

**Soundness blocker.**

---

# 6. Multi-alternative callees still bypass body safety

Normal `analyze_apply` currently invokes body safety only when the callee contract is a singleton:

```text
Contract::Equals(cv)
```

That handles:

```text
one exact function
```

but not:

```text
multiple live function alternatives
```

Consider:

```next
bad = () => 1 + "x"
good = () => 1

root = (b) =>
    (b ? bad : good)()
```

Analyze:

```text
root(Boolean)
```

The final callee can be represented abstractly as:

```text
Equals(bad) ∪ Equals(good)
```

That is not a singleton `Equals(cv)`.

If body safety is only invoked for singleton callees, neither alternative is recursively inspected through the safety mechanism.

Yet one admitted execution calls:

```text
bad()
```

and traps.

Potential result:

```text
root(Boolean)
→ accepted
```

despite a concrete trapping execution within the admitted domain.

## Classification

**Soundness gap.**

---

# 7. Current “actual abstract call edge” handling is therefore incomplete

Archive(8 correctly improved body safety from syntactic closure reachability to actual call-site propagation.

But the current implementation still only fully follows:

```text
singleton concrete callee
+
current edge argument domain
```

The general abstract application semantics require:

```text
every live callee alternative
+
its correlated actual argument domain
```

This is especially important because NEXT already has joint-operand/correlation machinery designed to prevent false callee/argument pairings.

Body safety should eventually consume that same representation.

---

# 8. Additional precision issue: `without_inference` can erase useful return facts

`body_safety` still analyzes bodies under a mode that suppresses nested return inference.

That prevents recursive analysis explosion, but it can also make a callee's result collapse to `Top`.

Example:

```next
always = () => true

root = () =>
    always()
        ? 1
        : 1 + "x"
```

Concrete execution is always safe.

But if nested analysis sees:

```text
always() → Top
```

instead of:

```text
always() → Equals(true)
```

the condition is opaque.

Both branches may remain live and:

```text
1 + "x"
```

can produce an `Error`.

Potential result:

```text
root()
→ rejected
```

even though the function is concretely safe.

This is primarily a **precision/completeness issue**, not a false-acceptance soundness problem.

But it reinforces the same architectural conclusion:

> body safety should not be a separate traversal that deliberately discards return information.

---

# 9. Why a simple `SAFETY_STACK` key fix is not enough

A tempting patch would be:

```text
Vec<Lambda>
    ↓
Vec<(ValueRef, Vec<Contract>)>
```

That would address the two immediate identity counterexamples.

However, it raises the next question:

> what happens if a recursive cycle produces a sequence of distinct abstract input domains?

A raw stack over arbitrary instance/domain pairs does not itself establish the global finite termination argument.

NEXT already has the machinery intended to solve exactly this:

- finite admitted-instance inventory;
- candidate graph;
- domain-indexed facts;
- SCC-ordered induction;
- structurally advance-bounded analysis.

Therefore body safety should reuse that machinery rather than introduce a second recursion semantics.

---

# 10. Move `InstanceBodySummary` forward

The natural unit is:

```text
InstanceBodyState =
    concrete instance
  + demanded input domain
```

Each state should produce a summary such as:

```text
InstanceBodySummary {
    produced,
    completion,
    may_not_complete,
    findings
}
```

Then interprocedural analysis becomes:

```text
(instance, input domain)
        ↓
analyze body
        ↓
application encountered
        ↓
enumerate every live callee alternative
        +
derive correlated argument domain
        ↓
dependency on (callee instance, callee input domain)
        ↓
candidate graph / SCC closure
```

This single mechanism can support:

- return facts;
- completion behavior;
- body safety;
- `may_not_complete`;
- eventual caching.

That is cleaner than maintaining separate overlapping mechanisms for each.

---

# 11. Required adversarial regressions

Before proceeding further, add these tests.

## 11.1 Same shape, different captures — must reject

```next
bad = () => 1 + "x"

make = (f) => () => f()

b = make(bad)
c = make(b)

c()
```

Expected:

```text
trap surfaced
```

---

## 11.2 Same instance, changed recursive domain — must reject

```next
f = (x) =>
    x == 0 ? f("x") : x + 1

f(0)
```

Expected:

```text
recursive call analyzed over String
→ x + 1 traps
→ caller rejected
```

---

## 11.3 Multiple possible callees — must reject

```next
bad = () => 1 + "x"
good = () => 1

root = (b) =>
    (b ? bad : good)()

root(Boolean)
```

Expected:

```text
bad alternative remains live
→ trap surfaced
```

---

## 11.4 Return-dependent safe path — must accept

```next
always = () => true

root = () =>
    always() ? 1 : 1 + "x"

root()
```

Expected:

```text
always() return fact preserved
→ false branch dead
→ no false trap
```

The first three are soundness gates.

The fourth protects against unnecessary rejection when body safety is unified with return inference.

---

# 12. Updated status

| Area | Status |
|---|---|
| Oracle execution of user calls | **✅ fixed** |
| Parameter-callee propagation | **✅ fixed for singleton callees** |
| Actual edge argument domain | **✅ fixed for singleton callees** |
| Dead-arm narrowing | **✅ good** |
| Shape-only safety cutoff | **🔴 soundness blocker** |
| Same-instance/different-domain recursion | **🔴 soundness blocker** |
| Multi-alternative callee safety | **🔴 soundness gap** |
| Return-dependent safety precision | **🟡 incomplete** |
| `InstanceBodySummary` / SCC integration | **⬜ should move forward now** |
| AP-30 | **⏸ hold until this is fixed** |

---

# 13. Recommended next step

Do **not** restore oracle execution.

Do **not** proceed to AP-30 yet.

Do **not** treat `SAFETY_STACK` as a second independent recursive proof mechanism.

Instead:

```text
body safety
        ↓
fold into
(instance, demanded input domain)
        ↓
InstanceBodySummary
        ↓
existing finite candidate/SCC machinery
```

A precise implementation directive is:

> **Make `(concrete callee instance, demanded input domain)` the unit of interprocedural body analysis. Enumerate every live correlated callee alternative at each application edge, derive that edge's actual argument domain, and carry safety findings as part of the same SCC-closed body summary used for return/completion reasoning. Remove shape-only safety cutoff semantics once the unified finite graph owns recursion.**

---

# Final verdict

Archive(8 is a meaningful improvement.

The Archive(7 false-acceptance regressions are fixed, and the dead-arm narrowing is a useful precision improvement.

But the replacement safety recursion guard is still too coarse:

> **Lambda shape is not a sufficient identity for body-safety analysis.**

The same closure shape can represent different captured environments, and the same closure instance can require analysis under different demanded input domains.

Additionally:

> **body safety currently follows only singleton concrete callees, so union/multi-alternative application can still bypass the safety path.**

These are not unrelated defects.

They all point to the architecture NEXT already has:

```text
instance
+
demanded input domain
+
finite candidate/SCC analysis
```

The next step should therefore be to unify body safety with the existing interprocedural summary/fact machinery rather than continue expanding `SAFETY_STACK`.

I would hold AP-30 until that foundation is corrected.
