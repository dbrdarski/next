# NEXT Implementation Review — Archive(10)

**Review focus:** Archive(9 follow-up fixes now present in Archive(10): total callee-alternative enumeration, widened-domain refutation discipline, the finite admitted-domain basis, and readiness to proceed toward AP-30.

## Executive verdict

Archive(10 makes real progress and **does fix the two callee-union failures from the previous review**.

The new:

```text
CalleeAlt =
    Known(ValueRef)
  | UnknownFunction
  | NotAFunction
```

classification is present, and normal `analyze_apply` now accounts for every syntactic live leaf of a callee `Contract` instead of extracting only known `Equals(function)` leaves.

That correctly fixes:

```next
(b ? good : 1)()
```

and the analyzer-level case:

```text
Equals(good) ∪ Kind(Function)
```

The old whole-contract `disjoint(callee, Function)` shortcut is indeed removed/subsumed.

Archive(10 also adds:

- a total `Contract::kind_abstraction`;
- a program-literal/Kind admitted-domain rule;
- downgrading of `Error` findings discovered only after recursive-domain widening;
- the requested growing-`Range` termination regression.

However, I would **not yet call the new body-summary recursion path fully sound or Principle-7 complete**.

I found three important issues:

1. **Widening downgrades `Error` findings but not `Completion::FallsThrough`.** A fall-through witnessed only in the widened domain can therefore still falsely refute a narrower call at an expecting seat.
2. **The claimed finite admitted exact-domain universe is not structurally finite because arbitrary nested `Union`s of admitted literals are themselves admitted, and unions are not canonicalized/deduplicated before becoming `(instance, domain)` keys.** A recursive program can therefore generate an infinite sequence of syntactically distinct but semantically repetitive union domains without ever triggering Kind widening.
3. **`NotAFunction` means “provably disjoint from Function,” not “represented non-function execution exists.”** A semantically empty but non-`Bottom` leaf can therefore be classified as a trapping alternative and produce an `Error`, contrary to the specification's inhabitance/witness discipline.

So:

> **The total-alternative refactor itself is a good fix.**

But:

> **the widened-summary evidence rules and the admitted-domain key space still need one more tightening before AP-30.**

---

# 1. Total alternative enumeration is genuinely implemented

Normal application analysis now classifies callee leaves as:

```rust
enum CalleeAlt {
    Known(ValueRef),
    UnknownFunction,
    NotAFunction,
}
```

and recursively visits `Union` branches.

The intended meanings are:

```text
Known(fn)
    → analyze the concrete closure precisely

UnknownFunction
    → cannot resolve a concrete function
    → produced = Top
    → completion = MayFallThrough
    → Warning

NotAFunction
    → represented call would operation-safety trap
    → produced = Bottom
    → Error
```

`Bottom` leaves are dropped.

This is a substantial improvement over the previous implementation, where only concrete `Equals(function)` leaves were extracted and all other leaves could disappear when at least one known function was present.

---

# 2. Archive(9 §17.2 is fixed

The previous counterexample:

```next
good = () => 1

root = (b) =>
    (b ? good : 1)()
```

with:

```text
b : Boolean
```

produces a callee abstraction containing both:

```text
Equals(good)
```

and:

```text
Equals(1)
```

Archive(10 classifies them separately:

```text
Equals(good) → Known(good)
Equals(1)    → NotAFunction
```

The non-function alternative contributes an operation-safety `Error`.

Therefore the bad branch can no longer disappear merely because a valid function alternative is also present.

## Verdict

**Fixed.**

---

# 3. Archive(9 §17.3 is fixed

For:

```text
callee =
    Equals(good)
    ∪
    Kind(Function)
```

Archive(10 now gets:

```text
Known(good)
+
UnknownFunction
```

The unknown alternative contributes:

```text
produced   = Top
completion = MayFallThrough
safety     = Warning / unproven
```

so the result cannot sharpen to:

```text
Equals(1)
```

merely because `good()` returns `1`.

This is the correct conservative direction.

## Verdict

**Fixed.**

---

# 4. The old whole-contract disjoint check is genuinely subsumed

The earlier application path first asked approximately:

```text
calleeContract ⟂ Function ?
```

for the whole callee contract.

That shortcut is no longer the main operation-safety gate.

Each leaf is now classified independently by `callee_alternatives`.

For mixed unions this is strictly better because the analyzer no longer has to choose between:

```text
whole union overlaps Function
→ lose the non-function branch
```

and:

```text
whole union disjoint
→ reject everything
```

## Verdict

**Good refactor.**

---

# 5. Important qualification: this is total over `Contract` leaves, not yet the full joint application relation

The new code is total over the leaves of the **projected callee contract**.

It is not yet the full v0.8.1 application algorithm over:

```text
joint [callee, ...arguments] AnalysisContract
```

and its correlated live alternatives.

Normal `analyze_apply` still starts from:

```text
callee Contract
+
separate argument Contracts
```

and calls:

```text
callee_alternatives(calleeContract)
```

The repository correctly continues to register the joint-correlated driver as owed.

Therefore the accurate status is:

> **callee-leaf totality fixed**

rather than:

> **full §1 live-alternative application semantics fully wired**

This is primarily an integration/precision distinction, but it matters for provenance.

---

# 6. New blocker: widening downgrades safety findings but not completion evidence

Archive(10 correctly recognizes the variance problem identified in the previous review:

```text
trap found in broad domain
⇏
narrow call traps
```

When a recursive call is widened, `Error` findings are changed to `Warning`.

Conceptually:

```text
Error after widening
    ↓
Warning
```

That prevents a broad-domain trap from directly refuting the narrower demanded state.

This is good.

But the exact same evidence problem exists for:

```text
Completion::FallsThrough
```

and that state is **not** downgraded.

The widened summary currently retains:

```text
completion = a.completion
```

unchanged.

---

# 7. Why `FallsThrough` has the same variance problem as `Error`

`Completion::FallsThrough` means:

> a represented execution has been proved to complete without a value.

At an expecting seat this becomes an **Error/refutation**.

Suppose a narrow recursive state is widened:

```text
D_narrow
    ⊂
D_broad
```

and body analysis over `D_broad` discovers a fall-through execution that exists only in:

```text
D_broad \ D_narrow
```

Then:

```text
FallsThrough(D_broad)
```

does **not** establish:

```text
FallsThrough(D_narrow)
```

This is exactly analogous to:

```text
RefutedSafety(D_broad)
⇏
RefutedSafety(D_narrow)
```

unless a witness is represented in the narrower state.

---

# 8. Concrete shape of the false-rejection class

Conceptually, consider a recursive function where:

```text
narrow recursive input
    → always produces a value
```

but after widening to `Number`:

```text
some additional Number inputs
    → fall through
```

For example, a body structurally like:

```text
if x == 0:
    recurse into a computed positive value
else if x > 0:
    return 1
else:
    fall through
```

The demanded recursive state may contain only the positive computed value.

After widening to:

```text
Number
```

negative values are admitted and the analyzer can prove fall-through.

Archive(10 would correctly downgrade any safety `Error` produced only by the widened domain.

But it currently retains:

```text
completion = FallsThrough
```

and that can propagate to the original narrow call.

At an expecting seat:

```text
FallsThrough
→ Error
```

producing a false rejection.

---

# 9. Required correction for widened completion

A widened body's completion should obey the same evidence direction as safety.

At minimum:

```text
widened + Produces
    → Produces

widened + MayFallThrough
    → MayFallThrough

widened + FallsThrough
    → MayFallThrough
```

unless there is a represented fall-through witness belonging to the narrower demanded domain.

The stronger final form is already specified by the application design:

```text
CompletionWithoutValue =
    ProvenAbsent
  | ProvenPresent(ApplicationWitness)
  | UnprovenPossible
```

Then the rule is explicit:

```text
broad ProvenPresent(w)
    refutes narrow state
iff
w is proved represented by narrow state
```

Otherwise:

```text
UnprovenPossible
```

is the correct projection.

## Classification

**Soundness blocker.**

---

# 10. The finite admitted-domain idea is directionally good

Archive(10 replaces the previous partial `generalize()` strategy with a total:

```text
Contract::kind_abstraction()
```

that maps arbitrary contract forms into a small Kind/Top basis.

Examples:

```text
Range(...)          → Kind(Number)
Greater(...)        → Kind(Number)
Tuple(...)          → Kind(Tuple)
Record(...)         → Kind(Record)
Intersection(...)   → Top
Difference(...)     → Top
```

This fixes the previous growing-`Range` counterexample:

```text
Range(0,1)
→ Range(1,3)
→ Range(2,5)
→ ...
```

because a computed recursive Range is no longer retained indefinitely.

It is widened to:

```text
Kind(Number)
```

which stabilizes.

## Verdict

**Good direction and a real improvement.**

---

# 11. New Principle-7 problem: admitted `Union`s are not a finite syntactic state space

The termination argument says, approximately:

```text
exact states are made from
program literals + finite Kinds

therefore the exact recursive state universe is finite
```

That would be true if each domain position were normalized to a canonical element of a finite powerset.

But that is not what the current representation guarantees.

`domain_admitted` recursively accepts:

```text
Union(a, b)
```

whenever both leaves are admitted.

At the same time, analyzer unions are ordinary binary `Contract::Union` trees.

`union_of` does not:

- flatten;
- sort;
- deduplicate;
- canonicalize equivalent unions.

Therefore the following contracts are structurally distinct keys:

```text
Equals(0)

Union(Equals(0), Equals(0))

Union(
    Union(Equals(0), Equals(0)),
    Equals(0)
)

Union(
    Union(
        Union(Equals(0), Equals(0)),
        Equals(0)
    ),
    Equals(0)
)

...
```

Every leaf is an admitted program literal.

So `domain_admitted` returns `true` for every member of this infinite syntactic sequence.

No Kind widening occurs.

And `(instance, domain)` key equality is structural.

---

# 12. Concrete recursive termination counterexample class

Consider conceptually:

```next
f = (x, b) =>
    f(b ? x : 0, b)
```

analyzed at:

```text
x = Equals(0)
b = Boolean
```

The literal `0` occurs in the function body, so it belongs to the admitted literal vocabulary.

With an unknown Boolean condition, the first argument can evolve abstractly as:

```text
Equals(0)
↓
Union(Equals(0), Equals(0))
↓
Union(
    Union(Equals(0), Equals(0)),
    Equals(0)
)
↓
...
```

Because unions are not canonicalized, each recursive call can create a new structural contract.

Every one is admitted exactly.

Therefore:

```text
domain_admitted == true
```

at every step.

`kind_abstraction` is never invoked.

And the `ACTIVE_BODIES` key never repeats.

So the analyzer can still have an unbounded recursive abstract-state chain even though the set of semantic atomic values is finite.

## Classification

**Principle-7 termination blocker.**

---

# 13. How to fix the admitted-union problem

There are several sound options.

## Option A — conservative short-term fix

Do not admit `Union` as an exact recursive-domain form.

Only admit atomic basis elements:

```text
Kind
Top
Bottom
Indeterminate
Equals(program literal)
```

Any recursive union immediately goes through:

```text
kind_abstraction
```

This loses precision but immediately restores the finite-state argument.

## Option B — canonical finite union basis

If literal unions are important for precision, normalize them into a canonical finite-set representation:

```text
flatten
deduplicate
canonical order
remove subsumed alternatives
```

Then a vocabulary of `N` admitted atoms has at most:

```text
2^N
```

semantic union states per position.

The important point is that key equality must use that canonical normal form.

## Option C — the specification's final route

Preconstruct the finite candidate-domain inventory explicitly and only allow recursive body-summary states from that inventory.

This remains the cleanest long-term architecture.

---

# 14. Alternative enumeration still needs inhabitance-backed refutation

There is another subtle issue in the new `NotAFunction` branch.

Current classification is:

```text
if leaf is provably disjoint from Function
    → NotAFunction
    → Error
```

But the application specification requires a refutation to have a represented execution.

A contract leaf can be provably non-function **and empty**.

`callee_alternatives` currently drops only syntactic:

```text
Bottom
```

not every contract proven empty.

---

# 15. Example: empty but non-`Bottom` leaf

Consider the contract:

```text
Intersection(
    Kind(Number),
    Kind(String)
)
```

Its denotation is empty.

But it is not structurally:

```text
Bottom
```

The current `disjoint(..., Function)` logic can prove it disjoint from `Function`, so it is classified as:

```text
NotAFunction
```

and contributes an `Error`.

Yet there is no represented call at all.

The application spec's discipline is:

```text
proven-empty alternative
    → drop / vacuous

uncertain inhabitance
    → Unproven

represented non-function witness
    → Refuted
```

not:

```text
non-Bottom + disjoint from Function
    → automatically Refuted
```

This is especially relevant because analyzer narrowing can construct raw:

```text
Contract::Intersection(...)
```

without universally normalizing every empty intersection to `Bottom`.

## Classification

**Potential false-rejection soundness gap.**

---

# 16. Recommended `CalleeAlt` evidence refinement

The enum itself is useful, but `NotAFunction` should carry or derive inhabitance evidence.

Conceptually:

```text
CalleeAlt =
    Known(ValueRef)
  | UnknownFunction
  | ProvenNonFunction(ApplicationWitness or callee witness)
  | UnprovenAlternative
```

or, equivalently:

```text
proven empty
    → omit

proven inhabited + disjoint(Function)
    → NotAFunction(witness)

possibly inhabited + disjoint(Function)
    → Unproven
```

The exact representation can vary.

The important semantic rule is:

> **disjointness proves that an inhabitant would trap; it does not by itself prove that an inhabitant exists.**

---

# 17. Widened warnings are also not actually propagated as claimed

The changelog says widened findings are:

> "never dropped silently — they stay visible as the third voice."

Inside `instance_body_summary`, `Error`s are indeed downgraded to `Warning`.

However, normal known-callee application currently imports only:

```text
summary.errors()
```

into the caller.

That method filters to:

```text
Severity::Error
```

only.

So warnings created specifically by widening are not propagated interprocedurally.

This is **not a soundness problem**.

It is the already-registered diagnostic gap around warning propagation.

But the current documentation claim should be softened:

```text
widened refutations are downgraded so they cannot reject
```

is correct.

```text
they remain visible at every caller
```

is not currently true.

---

# 18. What Archive(10) does successfully close

The following previous findings are genuinely improved or fixed:

| Previous issue | Archive(10) status |
|---|---|
| Known + non-function alternative silently dropped | **✅ fixed for inhabited concrete case** |
| Known + unknown-function alternative sharpened from known branch | **✅ fixed** |
| Whole-contract callability shortcut loses mixed-union structure | **✅ removed/subsumed** |
| Growing `Range` recursive domains | **✅ fixed by total Kind abstraction** |
| Broad-domain `Error` directly rejecting narrow state | **✅ prevented by downgrade** |
| Total Kind abstraction on arbitrary Contract forms | **✅ implemented** |

These are meaningful corrections.

---

# 19. Remaining blockers before AP-30

| Area | Verdict |
|---|---|
| `CalleeAlt` leaf enumeration | **✅ much better** |
| Concrete function + concrete non-function | **✅ fixed** |
| Concrete function + unknown function | **✅ fixed conservatively** |
| Full joint correlated application driver | **🟡 still not normal path** |
| Widened safety Error | **✅ downgraded** |
| Widened `FallsThrough` evidence | **🔴 soundness blocker** |
| Growing Range chain | **✅ fixed** |
| Growing admitted-Union structural chain | **🔴 termination blocker** |
| Non-function leaf inhabitance requirement | **🔴 potential false-refutation gap** |
| Widened warning propagation | **🟡 diagnostic gap** |
| AP-30 | **⏸ hold** |

---

# 20. Recommended next step

Keep the `CalleeAlt` refactor.

Keep `kind_abstraction`.

Keep the distinction between exact admitted domains and widened domains.

Before AP-30, tighten three things.

## 20.1 Downgrade existential completion evidence after widening

At minimum:

```text
widened FallsThrough
    → MayFallThrough
```

unless a fall-through witness is proved represented by the original demanded domain.

Eventually use the full:

```text
ProvenAbsent
ProvenPresent(ApplicationWitness)
UnprovenPossible
```

representation.

## 20.2 Make the admitted domain universe actually finite by representation

Either:

```text
do not admit Union exactly
```

or:

```text
canonicalize admitted unions to finite-set normal form
```

or move fully onto the preconstructed candidate-domain inventory.

The current recursive definition:

```text
Union(admitted, admitted) is admitted
```

is insufficient without canonical union identity.

## 20.3 Require inhabitance evidence before `NotAFunction` becomes an Error

A leaf merely proven disjoint from `Function` should not refute unless the application analysis has a represented inhabitant/witness.

Proven-empty alternatives must disappear.

Uncertain inhabitance should remain the third voice.

---

# Final verdict

Archive(10's **total alternative enumeration is a good and substantive fix**.

The two examples you reported are genuinely corrected:

```text
(b ? good : 1)()
```

now rejects, and:

```text
Equals(good) ∪ Kind(Function)
```

no longer sharpens from the known branch alone.

The finite Kind abstraction also genuinely closes the previously demonstrated growing-`Range` chain.

But the new implementation still has two foundational issues before its termination/evidence story is complete:

> **A widened body's `FallsThrough` evidence can still refute a narrower call even though the fall-through may exist only in the widened region.**

and:

> **The "finite admitted vocabulary" does not imply a finite structural key universe while arbitrary nested unions of admitted atoms remain exact and non-canonical.**

There is also an inhabitance issue in `NotAFunction`:

> **disjoint from Function proves what happens if a value exists; it does not prove that a represented value exists.**

Those are the boundaries I would fix before AP-30, because AP-30 itself is precisely about not manufacturing refutations from unrepresented executions.
