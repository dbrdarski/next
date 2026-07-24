# NEXT — Handover: Indeterminate, algebraic canonicalization, and the future Number model

**Date:** 2026-07-24  
**Status:** discussion handover only — **no specification change has been made by this session**.  
**Purpose:** preserve the reasoning chain from the `Indeterminate(_/0)` challenge through the author's intended future Number architecture, while separating author decisions/clarifications from strong working directions and still-open mathematical research.

---

## 1. Executive snapshot

This thread began while revisiting the reviewer-originated exclusions from the function-equality canonicalization slice: zero-annihilation (`0 * e -> 0`), cancellation (`e - e -> 0`), and demand-dropping identities (`x + 0 -> x`, etc.). Those exclusions profoundly affect how much algebraic structure can participate in canonical identity and therefore how much runtime interning can collapse equivalent values/functions.

The discussion exposed a larger architectural direction:

1. **The author does not want a generic `_ / 0` Indeterminate value.** `1/0`, `2/0`, `0/0`, etc. should preserve their specific canonical mathematical structure rather than immediately collapsing to one generic marker.
2. **Same canonical indeterminate value may cancel with itself.** If `X` is one exact canonical value, `X - X -> 0`; this is distinct from subtracting two merely similar or same-class indeterminate values.
3. **Algebraic canonicalization should not be weakened merely to preserve inferred domain requirements.** Derive/retain the semantic contracts first, then allow the body to canonicalize. Function identity can distinguish equal canonical bodies with different domains/contracts.
4. **Rationals are deliberately temporary.** The author's intended post-PoC Number is a canonical mathematical expression DAG, with a complex-capable full form, an integer fast representation for indexes/simple integer arithmetic, and a numerical renderer that “pixelates” the exact DAG into the author's planned **millesimal** infinite-precision rendering: radix 1000, with each millesimal digit (`0..999`) stored in a 10-bit cell (`2^10 = 1024` possible patterns), so only 24/1024 of the code space is unused.
5. This makes today's canonicalization work foundational to the eventual Number identity model, not merely a compiler optimization.
6. The long-term goal is explicitly mathematical: users should eventually be able to work on mathematical problems, and limits/asymptotic machinery are not ruled out.

The session therefore shifts the important question from “how much syntax may the compiler simplify?” to:

> **What mathematical equivalences belong to the canonical identity theory, and what semantic/domain information must survive separately so that aggressive canonicalization remains correct?**

---

## 2. Provenance and status discipline

### 2.1 No spec changes in this thread

The author explicitly stated that this session is **idea exploration, not a specification edit**. Existing documents still encode the status quo until a later ruling/erratum is intentionally made.

### 2.2 Why the subject opened

The immediate context was the equality-freeze exclusion trio:

- zero-annihilation: `0 * e -> 0`
- cancellation: `e - e -> 0`
- demand-dropping identity elimination: e.g. `x + 0 -> x`

The handover from the preceding session established that these exclusions were **reviewer-originated and absorbed into the documents without an explicit author ruling**. That makes them eligible for deliberate reconsideration rather than being treated as immutable author intent.

### 2.3 Core distinction discovered

The reviewer's exclusion logic had fused two different concerns:

- the **canonical algebraic result/body**;
- the **semantic constraints originally imposed by evaluating that expression**.

The author's counterproposal is to stop requiring the first to carry all of the second.

---

# Part I — Indeterminate identity

## 3. Author clarification: no generic Indeterminate

The author rejected the generic form:

```text
Indeterminate(_/0)
```

as the intended long-term model.

Instead, specific zero-denominator results should preserve their canonical mathematical identity, e.g.:

```text
1/0
2/0
0/0
```

The conceptual point is not primarily display syntax. Preserving the numerator preserves mathematical information that generic `_ / 0` destroys.

Consequences:

```text
1/0 != 2/0
```

while an algebraically identical numerator should canonicalize:

```text
(2 - 1)/0 == 1/0
```

assuming the numerator canonicalizes to `1`.

This is compatible with universal interning: independently constructed but mathematically canonical-identical zero-denominator values can still share one pointer. What is rejected is collapsing *different* canonical mathematical values solely because both have denominator zero.

---

## 4. Same instance/canonical value versus same category

A repeated correction in the discussion was the distinction between:

```text
X - X
```

where both operands are the **same exact canonical value**, and:

```text
X - Y
```

where `X` and `Y` are merely both indeterminate/infinite-class values.

The author's position is that the first should be understood through identity:

```text
X - X = 0
```

including when `X` is a specific indeterminate result.

This must not be confused with the usual analytic statement that an undifferentiated `infinity - infinity` is indeterminate. That conventional notation may stand for two different growths. The scenario here is one exact canonical object subtracted from itself.

Therefore:

```text
X = 1/0
X - X -> 0
```

is a candidate algebraic law, while:

```text
X = 1/0
Y = 2/0
X - Y
```

does **not** cancel merely because both belong to an Indeterminate/Numeric family.

The earlier assistant reasoning that treated same-class infinity/Indeterminate as equivalent to same-instance identity was explicitly corrected.

---

## 5. Why `1/0` matters for cancellation

Preserving `1/0` rather than `_ / 0` gives the canonicalizer enough information to recognize exact self-cancellation.

With a generic value:

```text
1/0 -> Indeterminate(_/0)
2/0 -> Indeterminate(_/0)
```

both would become the same pointer and the system could no longer distinguish:

```text
a - a
```

from:

```text
a - b
```

when `a = 1/0`, `b = 2/0`.

With specific canonical forms:

```text
a = 1/0
b = 2/0

a != b
a - a -> 0
```

while `a - b` remains a separate mathematical expression/result unless the chosen mathematics proves a further reduction.

This was a major reason the author rejected numerator erasure.

---

## 6. No generic propagation rule

Once there is no generic Indeterminate, the earlier idea “an arithmetic operation involving Indeterminate simply propagates an Indeterminate marker” is no longer an adequate model.

The two candidate directions are instead:

### Branch A — compositional exact Indeterminates

If mathematics does not yet provide a stronger reduction, preserve the exact operation composition:

```text
1/0 + 2/0
-> Indeterminate(
     Add(
       Indeterminate(1/0),
       Indeterminate(2/0)
     )
   )
```

The exact spelling/representation above is illustrative only. The important law is **preserve canonical composition rather than collapse to a generic marker**.

This branch can still admit safe algebraic identities such as self-cancellation or identities when deliberately defined.

### Branch B — mathematical interpretation

Rather than treating these as uninterpreted symbolic error-like expressions, define a real mathematical structure in which the objects participate in laws derived from mathematics.

For example, if the chosen algebra justifies something equivalent to a formal infinite scale, it might allow:

```text
1/0 + 2/0 -> 3/0
1/0 - 1/0 -> 0
```

but only because the mathematical structure warrants those equations, not because the compiler guesses them.

### Hybrid direction

The most plausible long-term architecture may be:

> **Always preserve a canonical symbolic object; apply increasingly strong mathematically certified reductions where a theory supports them.**

Thus unsupported expressions remain compositional; supported ones collapse to stronger canonical forms.

---

# Part II — Domain contracts and algebraic canonicalization

## 7. Author correction: canonicalization may drop syntax without dropping its contract

The original objection to:

```text
x + 0 -> x
```

was that `x + 0` imposes a numeric demand while plain `x` does not.

The author pointed out a simpler architecture:

> **Derive/retain the original semantic contracts before canonicalization. Canonicalization may then reduce the body without losing the domain requirement.**

Therefore:

```text
f = x => x
g = x => x + 0
```

can both end with canonical body:

```text
x
```

while retaining different domains:

```text
f: Any -> identity
g: Numeric -> identity   // exact umbrella naming still under discussion
```

so:

```text
f != g
```

This means demand preservation need not be implemented by artificially retaining algebraically redundant syntax.

---

## 8. Important equality consequence

Under the above model:

```text
x => x
!=
x => x + 0
```

because the accepted domains differ.

But:

```text
(x: Numeric) => x
==
x => x + 0
```

if `x + 0` accepts exactly Numeric and both otherwise have the same semantic envelope.

Similarly, potentially:

```text
x => x + 0
==
x => x * 1
```

if both canonicalize to the same result body and induce the same complete semantic constraints.

And:

```text
(x: Numeric) => 0
==
x => 0 * x
```

**only if** all relevant semantics coincide under the eventual Numeric/Indeterminate algebra.

The key is:

> Function identity is not merely the reduced body; the retained domain/semantic envelope participates as well.

---

## 9. “Type contract” versus complete semantic envelope

The discussion initially spoke of retaining the type/domain contract. A refinement was recorded: for general operand-erasing rewrites, input kind alone may not always capture every semantic difference.

For example:

```text
0 * compute(x)
```

may erase evaluation/completion behavior if reduced blindly to `0`.

So a future identity key may need to preserve some canonical semantic envelope such as:

```text
canonical algebraic body
+ accepted-domain contract
+ result relation/contract
+ completion obligations
+ act-kind/effect constraints where relevant
+ resolved captures / recursive identity
```

Exact contents are **not decided**. The important decision-shaped insight is only that algebraic normalization and semantic constraints can be represented separately.

This removes the false binary:

- either keep `x + 0` forever to remember Numeric-ness;
- or erase it and become unsound.

A third route exists: canonicalize the algebra, retain the semantics independently.

---

## 10. Consequence for the reviewer-originated exclusion trio

The discussion substantially weakens the rationale for permanently excluding:

```text
x + 0 -> x
x * 1 -> x
x - x -> 0
0 * x -> 0
```

from comprehensive canonicalization.

The author has **not yet issued a normative replacement ruling**, but the working direction is now:

> The long-term canonicalizer should strive for mathematically comprehensive normalization; domain/safety semantics should not force algebraically redundant syntax to survive merely as hidden metadata storage.

This matters beyond functions: the future Number itself is intended to be a canonical expression DAG, so elementary algebraic identities must eventually participate in numeric identity where mathematically valid.

---

# Part III — `Number`, `Indeterminate`, and possible `Numeric`

## 11. The missing umbrella category

The discussion exposed that `Number` and `Indeterminate` may need a broader static category.

Proposed working shape:

```text
Numeric
|- Number
`- Indeterminate
```

or equivalently as a contract-level union rather than necessarily a new runtime tag.

Motivation:

If:

```text
X + 0
```

is valid for both ordinary resolved numbers and specific Indeterminate numeric results, then its domain is broader than ordinary `Number` but narrower than `Top`.

That would explain:

```text
(x: Numeric) => x
==
x => x + 0
```

while:

```text
(x: Number) => x
```

may be narrower if `Number` excludes Indeterminate.

**Status:** strong working direction, not formally ratified. The future canonical Number DAG may cause the final taxonomy to be different; e.g. “Indeterminate” may become a subset/state of the single Number universe rather than a peer runtime kind.

---

## 12. What “Indeterminate” now appears to mean

The thread moved away from:

> “Arithmetic failed; emit one generic failure-like numeric marker.”

Toward something closer to:

> “A precise canonical mathematical expression exists, but it has not reduced to an ordinary resolved numeric value under the current mathematical theory.”

This interpretation is more compatible with:

```text
1/0
2/0
```

remaining different values and with mathematical simplification later discovering relationships between them.

However, the final ontology of `Indeterminate` is still open because the author intends a much richer Number model after the first language phase.

---

# Part IV — The author's future Number architecture

## 13. Rationals are intentionally temporary

The current arbitrary-precision rational Number is a first-phase implementation vehicle, not the intended final numerical model.

The author disclosed the intended long-term direction:

> **The full Number is essentially a canonical algebraic/mathematical DAG representation.**

The term “algebraic DAG” here means a DAG of canonical mathematical operations/objects, not necessarily the narrow mathematical class “algebraic numbers.”

---

## 14. The exact DAG is the number; numerical digits are a rendering

The future architecture is conceptually:

```text
Canonical mathematical Number DAG
              |
              | render / "pixelate"
              v
requested numerical representation / precision
```

The exact DAG is the semantic identity.

A decimal/binary/etc. approximation is a view/rendering of that identity, not the stored truth of the number.

Examples conceptually:

```text
sqrt(2)
pi
sqrt(2) + pi
2 + 3i
```

remain exact canonical mathematical objects. Asking for digits does not replace their identity with those digits.

The author calls the rendering format **millesimal**. Its settled core idea is a radix-1000 positional representation:

```text
one millesimal digit = 0..999
one storage cell      = 10 bits
2^10                  = 1024 possible bit patterns
used                   = 1000
unused                 = 24
code-space utilization = 1000/1024 = 97.65625%
unused fraction         = 24/1024   = 2.34375%
```

A millesimal digit therefore naturally carries three decimal digits' worth of radix information while fitting in a 10-bit cell. The `1000/1024` figure describes **representation density**, not numerical precision: only 24 of the 1024 available 10-bit patterns are unused.

The millesimal form is intended as an effectively unbounded / progressively extendable numerical rendering. It is **not the semantic identity of the number**: the exact canonical mathematical DAG remains the Number, and millesimal digits are its requested numerical “pixelation.”

---

## 15. Complex-capable full Number

The author intends the full form to be a **complex number type** rather than making complex arithmetic an unrelated wrapper bolted onto a simpler scalar model.

Conceptually, expressions such as:

```text
sqrt(-1)
2 + 3i
```

belong naturally inside the Number universe.

Exact details — branch cuts, multi-valued functions, principal values, algebraic/transcendental constants, etc. — were **not discussed or decided**.

---

## 16. Integer optimization / representation fast path

The intended implementation will still optimize the overwhelmingly common exact integer cases:

```text
0
1
5
1000
```

particularly for indexes and simple integer arithmetic.

This is an implementation representation optimization, not intended to create a semantically separate arithmetic universe.

Conceptually:

```text
Number representation
|- optimized integer form
`- canonical mathematical DAG form
```

with promotion/collapse as appropriate.

Example direction:

```text
2 + 3 -> optimized integer 5
sqrt(4) -> canonicalize -> optimized integer 2
2 + sqrt(3) -> DAG
```

Exact storage strategy remains future work.

---

## 17. Why today's canonicalization becomes foundational

With a canonical DAG Number, expressions such as:

```text
x
x + 0
x * 1
x - x + x
```

must not remain distinct numeric identities merely because their source syntax differs when the chosen mathematics proves them equal over the relevant domain.

Therefore today's work on:

- commutativity/associativity;
- literal folding;
- like-term combining;
- identities;
- cancellation;
- annihilation;
- domain-sensitive normalization;

is effectively the first version of the future Number's **identity algebra**.

This is why the equality-freeze discussion became substantially more important after the Number design was revealed.

---

# Part V — Future mathematics direction

## 18. Long-term language goal

The author stated that a long-term goal is for NEXT to become genuinely mathematical: users should eventually be able to work on mathematical problems, not merely call conventional numeric libraries.

Existing mathematical languages/CAS/proof systems will need proper comparative research later. No claim was made in this session that NEXT already replaces them.

Limits are explicitly **not off the table**.

---

## 19. Mathematical paths surfaced for `/0` and infinite behavior

Several research directions were mentioned as candidates, **not adopted designs**:

- limits and asymptotic/growth-rate semantics;
- formal infinitesimals/infinite quantities;
- Laurent-series-like or other non-Archimedean structures;
- totalized-division algebras such as meadow/wheel-related literature;
- mathematical systems in which different `x/0` values may remain distinct;
- compositional symbolic expressions when no stronger theory is adopted.

The key author reaction was that entering limit mathematics is acceptable given the long-term goal.

The handover should not select one of these theories. They are a future research agenda.

---

## 20. Canonical identity versus mathematical provability

A critical future distinction was identified:

### Canonical identity

The fixed, deterministic normalization theory says two values are the same canonical object, so they intern to the same pointer and runtime `==` remains O(1).

### Broader mathematical equivalence

A theorem prover/solver may be able to prove two different canonical forms mathematically equal without requiring that the base interner solve arbitrary mathematics.

This separation is important because mathematical equivalence can become arbitrarily hard or undecidable in rich theories, while runtime value equality must remain cheap and deterministic.

Working principle:

> **Canonicalization should be increasingly mathematically powerful, but it need not be mathematically omniscient.**

A stronger reasoning layer may prove more than the base identity theory.

---

## 21. Assumption-sensitive mathematics fits the contract architecture

Mathematical identities are frequently domain-qualified. Example pattern:

```text
sqrt(x^2)
```

may simplify differently under assumptions such as real-valued `x`, non-negative `x`, etc.

The existing architecture's separation between canonical shape and analysis instances parameterized by contracts appears suitable for future assumption-sensitive mathematical normalization.

Potential long-term shape:

```text
universal canonical form
+
stronger canonical/proven result under a certified domain/assumption context
```

No exact mechanism was decided.

---

## 22. Compiler termination versus mathematical computation

The existing principle that compiler analysis must terminate by construction should remain separate from future mathematical computation.

A future operation such as:

```text
solve(...)
prove(...)
limit(...)
integrate(...)
```

may be an ordinary pure computation and need not inherit the compiler analyzer's finite-state/advance-bound requirement.

This keeps the compiler trustworthy/terminating without artificially limiting what users may compute mathematically.

---

## 23. Contracts versus future mathematical propositions

The current contract system is primarily unary/set-oriented: what values may inhabit a position.

Serious mathematics eventually needs relations/propositions such as:

```text
x < y
x + y = 10
forall x ...
exists x ...
```

A future mathematical proposition/equation/relation layer may therefore be cleaner than forcing all relational mathematics into the current contract algebra.

This is future architecture only; no change to the current contract system was proposed here.

---

# Part VI — Concrete examples retained from the discussion

## 24. Function/domain canonicalization examples

Assuming a future `Numeric` domain:

```text
x => x
!=
x => x + 0
```

because their accepted domains differ.

But:

```text
(x: Numeric) => x
==
x => x + 0
```

if their complete semantic envelopes coincide.

Likewise candidate:

```text
x => x + 0
==
x => x * 1
```

when both mean exactly Numeric identity.

This illustrates the governing idea:

```text
canonical body + canonical semantic/domain envelope
```

rather than preserving redundant arithmetic solely to remember the domain.

---

## 25. Indeterminate identity examples

Candidate identity-preserving behavior:

```text
a = 1/0
b = 2/0

a != b
a - a -> 0
```

But:

```text
a - b
```

remains a specific expression/result unless a mathematical theory proves a reduction.

For a separately constructed but canonical-identical value:

```text
a = 1/0
c = (2 - 1)/0
```

canonicalization should be able to make:

```text
a == c
```

if `(2 - 1)` reduces to `1` before/within the numeric DAG normalization.

---

## 26. Open example: `1/0 + 2/0`

Two still-live possible outcomes illustrate the main branch:

### Pure composition

```text
1/0 + 2/0
-> canonical Add(Div(1,0), Div(2,0))
```

classified as an indeterminate numeric expression.

### Mathematical reduction

```text
1/0 + 2/0
-> 3/0
```

**only if** the selected future mathematical algebra justifies this law.

No choice was made.

---

# Part VII — Explicit corrections/retractions from the discussion

## 27. Do not carry these forward as settled reasoning

### 27.1 Generic `_ / 0`

Rejected as the desired long-term direction. Preserving the specific numerator/expression is important for canonical mathematical identity.

### 27.2 “Same infinity” treated as generic `infinity - infinity`

The assistant initially answered using conventional undifferentiated infinity. The author corrected that the scenario is **the same exact instance/canonical value**. `X - X` and `X - Y` must not be conflated.

### 27.3 Generic Indeterminate propagation

The notion that operations simply propagate one generic Indeterminate is incompatible with the no-generic-Indeterminate direction. Operations must preserve/derive a specific canonical mathematical result.

### 27.4 Algebraic identities must be excluded to preserve Number demands

Too strong. Domain/contracts can be derived and retained separately, allowing the algebraic body to canonicalize.

### 27.5 Rationals as the likely long-term Number representation

Incorrect. They are explicitly temporary. The intended full Number is a canonical mathematical DAG with a separate numerical rendering mechanism.

---

# Part VIII — Open questions / research agenda

## 28. Immediate mathematical questions

1. What exact mathematical object is represented by `a/0`?
2. What laws distinguish `1/0`, `2/0`, and `0/0`?
3. Should `1/0 + 2/0` remain composed or reduce to something like `3/0`?
4. What is multiplication among zero-denominator/infinite forms?
5. What is division between them, e.g. `(2/0)/(1/0)`?
6. How should `0/0` differ from nonzero-over-zero poles/infinite forms?
7. Which identities remain universally valid across the whole future Number universe?
8. Which identities require domain assumptions?

## 29. Number-model questions

1. Final relationship among `Number`, `Numeric`, and `Indeterminate`.
2. Whether Indeterminate remains a runtime kind, a contract/category, or merely a subset/state of canonical Number DAGs.
3. Exact DAG node inventory for algebraic, transcendental, complex, limit, series, etc. expressions.
4. Exact semantics of the integer fast representation and promotion/collapse.
5. Canonical representation of complex values and branch-sensitive operations.
6. Rules for when a DAG can collapse to an optimized scalar representation.

## 30. Canonicalization questions

1. Which mathematical theories participate directly in **identity/interning**?
2. Which theories belong only to a stronger prover/equivalence layer?
3. How are domain assumptions incorporated without making global identity context-dependent?
4. How is canonicalization kept terminating/deterministic as the mathematical theory grows?
5. How are semantic envelopes/contracts canonicalized so equivalent functions intern together after aggressive body normalization?
6. How should the reviewer-originated equality-freeze exclusions be rewritten once this direction is formally ruled?

## 31. Numerical rendering questions

1. Formal operational specification of the **millesimal** renderer beyond the settled core definition: radix 1000; digits `0..999`; one digit per 10-bit cell (`2^10 = 1024` patterns); 24 unused patterns (`24/1024 = 2.34375%` overhead).
2. Precision request model.
3. Error/interval/certification model for renderings.
4. Rendering of complex values.
5. Rendering behavior for exact symbolic values that do not admit a conventional finite approximation.
6. Relationship between rendering and limit/asymptotic objects.

## 32. Mathematical-language research agenda

Later comparative research should include:

- computer algebra systems;
- symbolic mathematical programming languages;
- exact-real arithmetic systems;
- algebraic-number representations;
- non-Archimedean/infinite/infinitesimal systems;
- limit/asymptotic frameworks;
- theorem provers/proof assistants;
- languages where mathematical assumptions/domains affect simplification.

The purpose should be architectural learning, not feature imitation.

---

# Part IX — Architectural assessment after the disclosure

## 33. Effect on the long-term NEXT assessment

The future Number disclosure strengthens rather than weakens the current architecture's mathematical direction.

Reasons:

- immutable canonical values are already the base model;
- eager interning already turns canonical identity into pointer identity;
- exact arithmetic is already preferred over floating approximation;
- canonicalization is already a constitutional mechanism rather than an optional optimizer;
- functions themselves are moving toward canonical semantic identity;
- contracts already provide domain/set information that can qualify mathematical laws;
- the analyzer already distinguishes proven/refuted/unproven;
- the compiler's termination discipline can remain separate from arbitrarily rich user-level mathematical computation.

The final conceptual assessment given in the session was approximately:

```text
Overall NEXT conceptual architecture: ~9.7/10
Long-term mathematical-language suitability: ~9.5/10
```

The main uncertainty is no longer whether the architecture can host serious mathematics. It is the substantial future research required to define the mathematical Number algebra and the boundary between canonical identity and stronger provable equivalence.

---

# Part X — Pick-up order

## 34. Recommended order when this thread resumes

1. **Do not edit the spec yet.** Keep this handover as the exploratory record.
2. Formalize the author ruling (if still desired) that specific `a/0` forms retain mathematical identity and generic `_ / 0` is rejected.
3. Decide whether `Numeric` is needed now as a contract/category or should wait for the future Number design.
4. Revisit the equality-freeze exclusion trio under the rule: **derive/retain semantic contracts, then canonicalize algebraically**.
5. Define the minimum semantic envelope that must participate in function identity after aggressive canonicalization.
6. Separately open the mathematical research thread for the zero-denominator algebra (`1/0`, `2/0`, `0/0`, sums/products/quotients).
7. Later write the future Number architecture document: canonical mathematical DAG + integer fast path + complex-capable semantics + numerical renderer.
8. Only after the mathematical identity model is clearer, decide how much of it should land in the base runtime canonicalizer versus a stronger mathematical proof/equivalence layer.

---

## 35. One-sentence continuity statement

> **NEXT is moving toward a model where Numbers are exact canonical mathematical DAG values, numerical approximations are renderings of those values, and algebraic canonicalization should be as mathematically comprehensive as the retained domain/semantic envelope safely permits; specific indeterminate expressions such as `1/0` must therefore preserve canonical identity rather than collapsing into a generic `_ / 0` marker.**

