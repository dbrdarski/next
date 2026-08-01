> ## 📗 STATUS: **HISTORICAL** — record of a past review/audit; not current guidance
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Left unedited.

# NEXT Architecture Review — Accepted Domains vs Call-Site Body Safety

## Executive verdict

The recent review rounds identified real local bugs, but the review process itself was operating at the wrong architectural layer.

The central mistake was repeatedly asking:

```text
Is this call-site body-safety propagation mechanism sound?
```

instead of first asking:

```text
Why does this mechanism exist?
```

The decisive finding is:

```text
analyze(() => 1 + "x")
→ accepted = true
→ findings = []
→ contract = Top
```

If the NEXT specifications describe:

- **E11 — InferredAcceptedDomain**
- **C§12.1 — the body's domain**
- **E3 — body-derived domain**

then the implementation appears to be missing the more fundamental mechanism:

```text
function body
    ↓
symbolic analysis
    ↓
derive the input domain over which that body is valid
    ↓
InferredAcceptedDomain
```

Instead, the current implementation appears to derive accepted domains primarily from parameter patterns and then attempts to recover body safety later at call sites.

That inversion explains why several rounds of locally valid fixes kept generating another layer of complexity.

---

# 1. The central architectural miss

The current implementation behaviour:

```text
analyze(() => 1 + "x")
→ accepted = true
→ findings = []
→ contract = Top
```

is the strongest signal.

The function body:

```next
() => 1 + "x"
```

contains an unconditional invalid operation.

There is exactly one possible input tuple:

```text
()
```

and the body is not valid for that input.

If accepted domains are genuinely body-derived, the natural result is:

```text
AcceptedDomain = ∅
```

or the equivalent NEXT representation.

The body should not need to be rediscovered later by walking outward from every call site.

---

# 2. What the implementation appears to be doing instead

The current direction has effectively become:

```text
Lambda definition
    ↓
accepted_domain(parameter pattern)
    ↓
body safety largely not represented in accepted domain
```

Then, because applications still need to know whether the body can trap, later mechanisms were added:

```text
call site
    ↓
analyze callee body
    ↓
propagate body traps
    ↓
propagate transitive traps
    ↓
track instance/domain identity
    ↓
widen recursive safety domains
    ↓
classify all callee alternatives
    ↓
...
```

That is structurally backwards if the language design intends the function's callable domain to be inferred from the body itself.

---

# 3. Why the review rounds became a wild-goose chase

Each review finding was locally valid.

The problem was that each fix strengthened the wrong layer.

The progression looked roughly like:

```text
call-site body_safety walk
    ↓
misses parameter callees

edge-following body_safety
    ↓
shape cutoff aliases instances

(instance, domain) body summary
    ↓
widening leaks refutations

finite admitted basis
    ↓
structural unions are not actually finite

total callee alternatives
    ↓
more witness/inhabitance problems
```

Each review correctly found the next unsound corner.

But none of those reviews asked whether body validity should have been represented before application analysis began.

That is why the mechanism kept growing instead of converging.

---

# 4. The more natural NEXT architecture

Assuming the specification text means what it appears to mean, the architecture should probably look more like:

```text
function body
    ↓
symbolic analysis
    ↓
body-derived input requirements
    ↓
InferredAcceptedDomain
    ↓
closure/function semantic information
```

Application then begins with:

```text
actual argument domain
        ↓
is it contained in AcceptedDomain?
```

rather than:

```text
actual argument domain
        ↓
reanalyze transitive body graph
to discover whether execution traps
```

This is both simpler and more aligned with the terminology in the design.

---

# 5. Simple example: numeric requirement

Consider:

```next
f = (x) => x + 1
```

The parameter pattern may initially admit something broad.

But body analysis derives the requirement:

```text
x must support numeric addition with 1
```

So the accepted domain should narrow accordingly.

Conceptually:

```text
parameter-pattern domain
∩
body-derived requirement
=
InferredAcceptedDomain
```

For this example, that may become something equivalent to:

```text
Number
```

depending on the precise numeric semantics.

---

# 6. Unconditionally invalid body

Consider:

```next
bad = () => 1 + "x"
```

There are no parameters.

The only input tuple is:

```text
()
```

The body is invalid for that input.

So the inferred accepted domain should naturally become:

```text
∅
```

Then:

```next
bad()
```

is rejected because:

```text
() ∉ AcceptedDomain(bad)
```

No transitive call-site body-safety mechanism is needed to discover the invalid operation.

---

# 7. Should an uncalled empty-domain function itself be an error?

This is one of the two important open semantic questions.

My current architectural preference is:

> **No — not merely because its accepted domain is empty.**

A function definition does not execute its body.

Therefore:

```next
bad = () => 1 + "x"
```

could legitimately construct a function value whose accepted domain is empty.

Conceptually:

```text
bad : ∅ → ...
```

or the equivalent NEXT representation.

Then:

```next
bad()
```

is rejected because the application is outside the function's accepted domain.

This has several advantages:

- function creation does not pretend the body executed;
- higher-order programs may still store or pass the function;
- closure identity remains separate from whether the closure currently has any valid inputs;
- captured environments can naturally make a closure callable or uncallable.

However, this should be checked against the normative specification before being ratified.

This is an architectural recommendation, not yet a statement that the spec already settles it.

---

# 8. Capture-dependent accepted domains

The second major open question is:

> **How does a body-derived accepted domain depend on captured values?**

Consider:

```next
make = (y) => (x) => x + y
```

The inner Lambda's accepted domain depends on the captured value `y`.

For example, if different closures capture semantically different values, their callable domains may differ.

This fits naturally with NEXT's closure-instance model:

```text
closure =
    canonical Lambda
  + captured environment
```

Then:

```text
AcceptedDomain(closure)
=
analyze Lambda body
under captured environment
```

So accepted-domain inference may be **closure-instance-sensitive**, not merely Lambda-shape-sensitive.

This aligns with a lesson already learned repeatedly during the recent reviews:

```text
same Lambda shape
≠
same semantic closure instance
```

---

# 9. Example: capture-dependent validity

Conceptually:

```next
make = (y) => (x) => x + y
```

If:

```text
y = 1
```

the body may require:

```text
x : Number
```

If:

```text
y = "s"
```

the required domain may differ depending on NEXT's addition semantics.

The important point is that the body-derived requirement must be computed under the actual captured environment.

Therefore the natural unit is not merely:

```text
LambdaShape
```

but:

```text
LambdaShape
+
captured semantic environment
```

which is already close to the closure identity architecture.

---

# 10. What recent work may still be valuable

The conclusion should not be:

> everything from the previous rounds was wasted.

Several fixes appear independently justified.

## 10.1 Instance + input-domain identity for recursive facts

The correction from:

```text
Lambda shape
```

to:

```text
closure instance
+
input domain
```

for recursive facts still makes architectural sense.

That issue exists independently of call-site body-safety propagation.

## 10.2 Removing `segment_nullable(..., 8)`

Replacing arbitrary recursive fuel with finite structural cycle detection was plainly correct.

That aligns directly with Principle 7.

## 10.3 Keeping arbitrary fuel out of normative analysis

The distinction between:

```text
bounded diagnostic/test execution
```

and:

```text
normative analyzer verdict
```

remains important.

## 10.4 Removing full user-function oracle execution

The analyzer should still not execute arbitrary user functions through the reference oracle to decide normal static judgments.

That correction remains valid.

## 10.5 Correlated application alternatives

The AP-29/AP-30 work around preserving actual callee/argument correlation is independent and still valuable.

## 10.6 Dead-arm/path narrowing

Path-sensitive elimination of unreachable branches is useful analyzer infrastructure regardless of where accepted-domain inference ultimately lives.

---

# 11. What now looks suspect

The mechanisms most likely to be artifacts of the wrong layer are those added specifically to discover body validity at call sites.

Examples include:

```text
body_safety

SAFETY_STACK

transitive body-safety propagation

the safety portion of InstanceBodySummary

recursive safety-domain widening

admitted safety-domain basis
```

Some pieces may still be reusable internally.

But their existence should no longer be assumed.

The right question is:

> If `InferredAcceptedDomain` is implemented as specified, which of these mechanisms are still necessary?

If the answer is "none" or "very little," deletion is better than further refinement.

---

# 12. The Archive6 turning point

The key review mistake happened when the closed-call oracle fold was removed.

Without the fold:

```next
bad = () => 1 + "x"
bad()
```

stopped being rejected.

The review response was:

```text
we need interprocedural Lambda-body safety propagation
```

The better architectural question should have been:

```text
why does bad not already carry an empty accepted domain?
```

That would have led directly to:

```text
accepted_domain
```

and body-derived domain inference.

Everything after that was largely an attempt to reconstruct missing function semantics during application analysis.

---

# 13. A better review method for the next phase

The next review should not begin from another repository diff.

It should begin from the specification.

The central questions are:

```text
What exactly is InferredAcceptedDomain?

When is it computed?

What body information contributes to it?

How are body operation requirements converted into input-domain constraints?

How do captures parameterize it?

How does recursion participate?

How does application consume it?

What does an empty accepted domain mean?
```

Only after those questions are answered should the implementation be inspected.

The review direction should therefore reverse:

```text
specification
    ↓
semantic model
    ↓
required implementation mechanism
    ↓
current code comparison
```

rather than:

```text
current code
    ↓
find next counterexample
    ↓
patch
```

---

# 14. Start with embarrassingly small examples

The next architecture review should avoid beginning with recursion.

Use the smallest cases possible.

## 14.1 Empty input tuple, invalid body

```next
() => 1 + "x"
```

Question:

```text
What is its InferredAcceptedDomain?
```

Expected architectural answer should be explicit.

---

## 14.2 Simple numeric requirement

```next
x => x + 1
```

Question:

```text
How does the body constrain x?
```

---

## 14.3 Conditional requirement

```next
x =>
    x == 0
        ? 1
        : x + "x"
```

Question:

```text
What input region is actually accepted?
```

This forces the analyzer to explain path-sensitive accepted-domain inference.

---

## 14.4 Captured requirement

```next
y => x => x + y
```

Question:

```text
How does the captured y change the inner closure's accepted domain?
```

---

## 14.5 Only then recursion

Once the preceding cases are architecturally clear, introduce recursion.

The recursion design should operate over a clearly defined semantic object:

```text
body-derived accepted-domain relation
```

rather than inventing safety propagation rules first.

---

# 15. The likely semantic flow

A plausible architecture is:

```text
parameter pattern
    ↓
initial candidate input domain
    ↓
symbolic body analysis
    ↓
derive operation/input obligations
    ↓
combine obligations path-sensitively
    ↓
InferredAcceptedDomain
```

For a closure:

```text
canonical Lambda
+
captured environment
        ↓
body-domain inference
        ↓
closure-specific AcceptedDomain
```

Then application:

```text
joint actual argument domain
        ↓
AcceptedDomain coverage test
        ↓
Proven / Refuted / Unproven
```

This is much simpler than discovering body traps recursively at every call site.

---

# 16. Relationship to return analysis

Accepted-domain inference and return analysis should remain distinct concepts.

A function may have:

```text
AcceptedDomain = D
```

while its produced value over `D` is another problem:

```text
ReturnContract(D)
```

This distinction is useful.

Body analysis can derive:

```text
where the function is callable safely
```

separately from:

```text
what values it returns
```

and:

```text
whether it always produces a value
```

This separation may significantly simplify the current application/induction architecture.

---

# 17. Relationship to operation safety

If an operation in the body requires:

```text
x ∈ C
```

then that requirement should contribute to the function's accepted domain.

For example:

```next
x => x + 1
```

derives a numeric requirement on `x`.

For an impossible operation:

```next
() => 1 + "x"
```

the body-derived input domain becomes empty.

This makes operation safety fundamentally a **domain inference problem** rather than primarily a call-site graph-propagation problem.

---

# 18. Relationship to the three-voice analyzer

This architecture still fits NEXT's:

```text
Proven
Refuted(witness)
Unproven
```

discipline.

Accepted-domain inference need not pretend to solve every possible semantic question.

For an input region:

```text
definitely inside accepted domain
    → Proven

concrete represented input outside accepted domain
    → Refuted(witness)

cannot prove either
    → Unproven
```

The difference is that the evidence derives from the function's semantic accepted-domain analysis rather than from ad hoc recursive call-site safety walking.

---

# 19. Main conclusion

The recent reviews were not useless.

They successfully exposed that the implementation mechanism kept violating:

- instance identity;
- domain identity;
- witness direction;
- finite-state guarantees;
- alternative completeness.

But those repeated failures were a symptom.

The deeper issue is:

> **The implementation appears to be compensating at application time for body-derived accepted-domain semantics that were never implemented at function analysis time.**

That is the big-picture correction.

---

# Final recommendation

Pause the current patch-by-patch review loop.

Do not continue refining call-site body-safety propagation until the specification-level accepted-domain architecture is understood.

The next task should be a **spec-first design audit** of:

```text
E11 — InferredAcceptedDomain

C§12.1 — body domain

E3 — body-derived domain
```

with the goal of answering:

```text
How does a NEXT function derive the exact or conservative set of inputs
for which its body is semantically valid?
```

Only then should the implementation be compared against that model.

If that audit confirms the interpretation above, the likely result is not another large subsystem.

It is probably:

```text
implement body-derived accepted domains
        +
delete a substantial amount of call-site safety machinery
```

That would be a much healthier direction than continuing to make the current workaround more sophisticated.
