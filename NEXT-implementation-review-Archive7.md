> ## 📗 STATUS: **HISTORICAL** — record of a past review/audit; not current guidance
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Left unedited.

# NEXT Implementation Review — Archive(7)

**Review focus:** verification of the Archive(6) body-safety increment, removal of closed-call oracle execution, and soundness of the new interprocedural safety propagation.

## Executive verdict

Archive(7) genuinely achieves the architectural goal of removing full user-function execution from the analyzer:

```text
analyze_apply
    no longer
        ↓
eval_expr(full user call)
```

The seven acceptance tests for the new body-safety increment are present and meaningful, including the critical divergence case showing that:

```text
loop = () => loop()
loop()
```

terminates under static analysis without executing the user's recursive function through the oracle.

However, the replacement `body_safety` mechanism introduces a **new soundness problem**.

The current implementation propagates `Error` findings by walking a syntactic/reachable closure set and assigning domains through `group_domains`.

That mechanism is not sufficient for general body safety because:

1. `reachable_closures` deliberately omits some genuine runtime call edges, especially parameter/local callees;
2. `group_domains` may analyze a callee under a propagated/root domain rather than the domain carried by the actual call edge;
3. syntactic reachability alone does not prove that a locally trapping callee path is actually reachable under the current caller/domain.

The oracle-execution debt is therefore fixed, but **the replacement safety propagation is not yet normatively sound for arbitrary programs**.

The recommended next step is not to restore oracle execution. Instead, body safety should be folded into the existing **instance + demanded-input-domain** call graph / SCC architecture.

---

# 1. The oracle-execution coupling is genuinely removed

The previous analyzer contained a closed-call constant-folding path that executed fully known user functions through the oracle:

```text
analyzer
    ↓
eval_expr(full call)
```

That created an architectural and termination problem:

```text
closed recursive call
        ↓
analyzer attempts constant fold
        ↓
oracle executes user function
        ↓
user function diverges
        ↓
analyzer hangs / overflows
```

Archive(7 removes this path.

`analyze_apply` now proceeds through ordinary analyzer machinery:

```text
analyze_known_callee
        ↓
body_safety
        ↓
callee_completion
        ↓
call_return
```

rather than executing the call through `eval_expr`.

## Verdict

**Fixed.**

---

# 2. The divergence acceptance test is meaningful

One of the new acceptance tests uses the equivalent of:

```text
loop = () => loop()
loop()
```

and verifies that analysis terminates.

This is particularly important because it tests the architectural property rather than only a return value:

> Static analysis no longer depends on running a potentially diverging user function.

That is a strong regression test and should remain permanently.

## Verdict

**Good architectural gate.**

---

# 3. Direct and simple transitive body traps now work

The new body-safety implementation catches cases such as:

```text
bad = () => 1 + "x"
bad()
```

and the simple captured-callee transitive case:

```text
helper = () => 1 + "x"
bad = () => helper()
bad()
```

The mechanism walks the reachable closure group and analyzes each discovered closure body.

For these cases, the new implementation is effective because:

- the callee is discoverable by the existing body walk;
- there is no difficult call-domain transformation;
- the trapping operation is proven directly inside the discovered body.

## Verdict

**Working for the tested capture-graph subset.**

---

# 4. The new problem: `body_safety` uses the wrong graph abstraction

The body-safety implementation is conceptually:

```rust
for (g, args) in group_domains(callee, root_args, cenv) {
    if let Some(a) = analyze_instance_body(&g, &args, cenv, interner) {
        findings.extend(
            a.findings
                .into_iter()
                .filter(|f| f.severity == Severity::Error)
        );
    }
}
```

The corresponding design rationale says, in effect:

> safety is monotone reachability, therefore walking `reachable_closures` is sufficient.

That conclusion is too strong.

Safety propagation is monotone only over **semantically live call edges carrying the actual instance and demanded input domain**.

A syntactic reachable-closure relation is not enough.

There are two separate failure modes.

---

# 5. Soundness gap 1 — parameter/local callees can be omitted

The current body-walk infrastructure was originally designed for return induction.

It deliberately does not fully resolve every possible call target.

In particular, it may omit:

- parameter callees;
- local callees.

That was sound for return inference because:

```text
missing recursive/callee edge
        ↓
smaller candidate inventory
        ↓
less proof power
        ↓
Unproven
```

A missing edge could reduce precision, but could not create a false proof.

That argument does **not** transfer to body safety.

For safety:

```text
missing call edge
        ↓
callee body trap never inspected
        ↓
caller can be accepted
```

which is a false acceptance.

---

## 5.1 Concrete counterexample: parameter callee

Consider:

```next
bad = () => 1 + "x"

invoke = (f) => f()

invoke(bad)
```

Concrete execution of `invoke(bad)` traps.

But the callee `bad` is passed through a function parameter.

The static closure-reachability walk for `invoke` does not necessarily contain `bad` as a captured-function edge.

Inside the symbolic body analysis of `invoke`, the parameter `f` may correctly carry the concrete function value.

However, nested interprocedural inference is deliberately suppressed while analyzing the current body.

Therefore there may be no second mechanism that walks into `bad` and surfaces its body trap.

Potential result:

```text
invoke(bad)
    → accepted
```

even though:

```text
invoke(bad)
    → concrete trap
```

## Classification

**Soundness gap.**

---

# 6. Soundness gap 2 — callee safety may be checked under the wrong domain

The current `group_domains` mechanism remains an interim approximation.

For same-arity reachable closures, it can propagate the root call-site domain to the reachable callee.

Conceptually:

```text
root called with domain D
        ↓
reachable helper has same arity
        ↓
analyze helper under D
```

But the actual call edge inside the root may pass an entirely different domain.

For return inference this was already flagged as provisional.

For body safety, using the wrong domain can produce a false acceptance.

---

## 6.1 Concrete counterexample: actual edge domain differs from root

Consider:

```next
helper = (x) => x + 1

root = (n) => helper("hello")
```

Analyze:

```text
root(Number)
```

`root` and `helper` both have arity 1.

The current same-arity propagation may therefore analyze:

```text
helper(Number)
```

Under that domain:

```text
x + 1
```

is safe.

But the actual call edge is:

```text
helper(String)
```

and concretely:

```text
"hello" + 1
```

traps.

Therefore:

```text
body_safety(helper, Number)
```

does not justify:

```text
body_safety(actual helper call)
```

Potential result:

```text
root(Number)
    → accepted
```

despite the actual reachable call trapping.

## Classification

**Soundness gap.**

---

# 7. The same coarse walk can also create false rejection

The direction can fail the other way.

A helper may contain a trapping branch that is impossible under the actual call edge.

Example:

```next
helper = (x) =>
    x == 0 ? 1 : 1 + "x"

root = () => helper(0)
```

The actual call is:

```text
helper(Equals(0))
```

so the trapping branch is unreachable.

If the helper is instead analyzed under a broad accepted domain such as:

```text
Number
```

or `Top`, the bad branch may become live and produce an `Error`.

Blindly propagating that local `Error` to `root` could therefore reject:

```text
root()
```

even though the actual call path is safe.

This demonstrates an important distinction:

> A trap proven inside a callee under some domain is not automatically a trap proven for every upstream call to that callee.

The proof must be tied to the domain carried by the specific call edge.

## Classification

**Potential false rejection / path-domain precision problem.**

---

# 8. Why the existing seven tests all pass

The seven acceptance tests are valuable.

But they mostly exercise cases where the current approximation happens to be appropriate.

The successful transitive-trap case is structurally similar to:

```text
helper = () => trap
bad = () => helper()
```

Here:

- the helper is discoverable as a captured closure;
- both functions have the same zero-argument domain;
- no argument-domain transformation is required.

That is the ideal case for:

```text
reachable_closures
+
group_domains
```

The test suite does not yet cover the harder cases:

```text
parameter callee

local/dynamically resolved callee

actual call domain ≠ propagated/root domain

branch-narrowed safe callee call
```

So the seven tests establish correctness for a useful subset, not for general interprocedural body safety.

---

# 9. The correct abstraction is already present elsewhere in NEXT

The fix should not be to make `reachable_closures` collect more syntax.

The correct unit of interprocedural reasoning is already established by the application/induction architecture:

```text
(instance, demanded input domain)
```

Body safety should follow the **actual abstract call edges** discovered while analyzing a body.

Conceptually:

```text
caller instance
+
caller input domain
        ↓
symbolically analyze caller body
        ↓
encounter application
        ↓
resolve possible concrete callee instance(s)
        +
derive actual argument domain
        ↓
callee body summary over that domain
```

Recursion then closes through the existing finite candidate/SCC machinery.

This gives safety the same identity discipline that return facts now use.

---

# 10. Move `InstanceBodySummary` forward

The repository already had a future refinement conceptually resembling:

```text
InstanceBodySummary {
    produced,
    completion,
    may_not_complete,
    findings
}
```

This should probably move forward now.

The current architecture is split:

```text
return induction
    → candidate/SCC graph

body_safety
    → separate reachable_closures walk

completion
    → separate body analysis
```

The stronger architecture is:

```text
(instance, input domain)
        ↓
InstanceBodySummary
        ├── produced
        ├── completion
        ├── may_not_complete
        └── findings
        ↓
shared candidate/SCC machinery
```

Then:

- return facts;
- completion behavior;
- body safety;
- future `may_not_complete`;

all refer to the same semantically meaningful instance/domain node.

That eliminates the mismatch between:

```text
return proof identity
```

and:

```text
safety proof identity
```

---

# 11. Required adversarial tests

Before considering the body-safety increment complete, add tests that attack precisely the missing abstraction.

## 11.1 Parameter callee — must reject

```next
bad = () => 1 + "x"

invoke = (f) => f()

invoke(bad)
```

Expected:

```text
rejected / proven trap surfaced
```

---

## 11.2 Actual edge domain differs from root — must reject

```next
helper = (x) => x + 1

root = (n) => helper("x")
```

Analyze `root(Number)`.

Expected:

```text
helper analyzed over String for this edge
→ trap surfaced
```

The root's `Number` domain must not be substituted for the helper call's actual argument domain.

---

## 11.3 Narrowed safe call — must accept

```next
helper = (x) =>
    x == 0 ? 1 : 1 + "x"

root = () => helper(0)
```

Expected:

```text
helper analyzed over Equals(0)
→ bad branch dead
→ root accepted
```

A broad helper-domain analysis must not manufacture a false upstream trap.

---

## 11.4 Unsafe edge must not inherit safer caller domain

```next
helper = (x) => x + 1

root = (n) => helper("x")
```

The relevant invariant is:

```text
callee body safety
must be established over
the domain carried by the concrete abstract call edge
```

—not over:

- the callee's general accepted domain;
- the caller's root domain;
- an arbitrary same-arity propagated domain.

---

# 12. Recommended wording correction in `DECISIONS.md`

The current rationale approximately states:

> safety is monotone reachability, so `reachable_closures` is the right tool.

That should be withdrawn or narrowed.

A better statement is:

> **Safety propagation is monotone only over semantically live instance/domain call edges. Syntactic closure reachability alone is insufficient because it can omit dynamically resolved callees and can lose the input-domain/path information required to justify a caller-level refutation.**

This captures both newly identified failure modes.

---

# 13. Updated status

| Item | Verdict |
|---|---|
| Full user-call oracle execution | **✅ removed** |
| Diverging call no longer executed | **✅** |
| Direct body traps | **✅** |
| Simple capture-based transitive traps | **✅** |
| Structural termination of current walk | **✅** |
| Parameter/local callee safety | **🔴 unsound gap** |
| Actual call-domain propagation | **🔴 unsound gap** |
| Path/domain-sensitive caller refutation | **🟡 incomplete** |
| `body_safety` as final general mechanism | **❌ not yet** |
| AP-30 | **⬜ owed** |
| `may_not_complete` | **⬜ owed** |
| Phase A | **⬜ owed** |

---

# 14. Recommended next step

Do **not** restore oracle execution.

Do **not** proceed directly to AP-30 yet.

Instead:

```text
replace separate body_safety reachability walk
        ↓
instance/domain-aware body summaries
        ↓
actual abstract call edges
        ↓
shared SCC/candidate machinery
```

A precise implementation directive would be:

> **Make body safety interprocedural over `(callee instance, demanded input domain)` rather than over syntactic reachable closures. Derive callee safety requests from actual abstract application edges while analyzing the caller body, and close recursive dependencies through the existing finite SCC machinery. Fold findings into an `InstanceBodySummary` alongside produced/completion information.**

This preserves the architectural success of Archive(7—the analyzer no longer executes user functions) while fixing the coarse replacement mechanism.

---

# Final verdict

Archive(7 makes real and important progress.

The most important success is:

> **The analyzer no longer executes arbitrary closed user-function calls through the oracle, and divergence no longer threatens analyzer termination through that path.**

That architectural correction should remain.

However, the new separate `body_safety` reachability walk is too coarse to serve as the final safety proof mechanism.

Its two critical weaknesses are:

> **It can miss real callees such as parameter/local function values.**

and:

> **It can analyze a discovered callee under a domain different from the domain carried by the actual call edge.**

Both can lead to incorrect analyzer judgments.

The right correction is not to return to oracle execution. It is to reuse NEXT's stronger existing abstraction:

```text
instance
+
demanded input domain
+
finite call graph/SCC reasoning
```

for body safety as well as return inference.

This is exactly the kind of issue the checkpoint process is intended to expose: Archive(7 fixes a genuine architectural debt, and this review identifies where the first replacement mechanism is too coarse before it becomes entrenched.
