# Review — Updated NEXT Semantics Companion v0.1

**Compared against:** the prior repository copy of `next-semantics-companion-v0-1.md`  
**Review scope:** only the newly changed semantics: closure interning, total interpolation, trap-ledger synchronization, and the ruling on open recursive identity.

## Executive verdict

The update is directionally correct and improves the semantics companion substantially.

Accepted architectural changes:

1. universal pointer equality is restored for closures through shallow interning;
2. function construction is explicitly separated from call memoization;
3. structure interpolation becomes total;
4. the obsolete `unprintable-interpolation` trap is deleted;
5. strict openness and shape-based recursive value identity are finally ruled.

No foundational defect is introduced.

Two focused integration seams remain before this revision is fully closed:

1. the newly ruled prohibition on observing open group values is not represented in the oracle rules or trap concordance;
2. the new print/parse law is broader than the actual rendering rule, and canonical Record/String rendering is not specified precisely enough.

These require a small semantics patch, not an architectural redesign.

---

# 1. Closure interning — accepted, with one explicit-key correction

The new rule is coherent:

```text
acyclic closure key =
    canonical-code pointer
    + capture pointers

μ-group members =
    jointly interned at window close

runtime equality =
    pointer equality universally

calls =
    never memoized
```

This correctly distinguishes:

- canonicalizing a function **value**;
- memoizing a function **application**.

The former is part of value identity; the latter is explicitly absent.

It also restores congruence automatically:

```text
f == g  ⇒  [f] == [g]
```

and aligns acyclic closures with the broader canonical immutable-value model.

## Required precision

The key must observably include the function's `actKind`.

Two closures with identical parameter/body shape and captures but different act-kinds are not the same value, because world admission differs:

```text
pure    () => 1
effect  () => 1
```

If `canonical-code pointer` already denotes the complete canonical `Lambda`, including:

```text
parameter pattern
body
actKind
```

then the architecture is already correct. State that explicitly.

Recommended wording:

```text
Acyclic closure key =
(
    canonical Lambda pointer
        // includes parameter pattern, body, and actKind
    canonical capture-pointer vector
)
```

This is a self-containment correction, not a redesign.

---

# 2. Total interpolation — accepted in principle

Removing `unprintable-interpolation` is a good simplification.

The resulting model is cleaner:

- interpolation never adds a safety obligation;
- a Template always produces a String;
- Functions and Indeterminates have deterministic display forms;
- Tuple and Record rendering is deterministic;
- the analyzer no longer carries a printability proof that has no semantic value.

The following decisions are coherent:

```text
top-level String:
    inserted verbatim

String inside a structure:
    quoted and escaped

Function:
    <Function>

Indeterminate:
    <Indeterminate _/0>
    <Indeterminate 0/0>
```

Showing only the Indeterminate form is particularly important because its operands are not part of value identity.

---

# 3. The print/parse law is currently mis-scoped

The document says both:

```text
String verbatim at top level
```

and:

```text
literal-formed values render as literals
parse ∘ print = identity on that fragment
```

These statements are not true for a top-level String.

For example, interpolating the String value `"abc"` yields:

```text
abc
```

not:

```text
"abc"
```

Reparsing `abc` does not produce the original String value.

The current implementation tests the round-trip property only on structured literal values and does not include a top-level String. That is the correct effective perimeter, but the document needs to say so.

## Required correction

Define the law recursively and exclude raw top-level String interpolation:

```text
Canonical-source rendering is defined for the source-literal fragment:

- Boolean
- Null
- Number
- String when rendered in a nested literal seat
- Tuple whose members are recursively source-renderable
- Record whose keys and values are source-renderable

For that fragment:

    parse(renderCanonicalLiteral(v)) == v

Template interpolation itself is different:

- a top-level String contributes its raw units;
- all other values use their deterministic display rendering.
```

An aggregate containing a Function or Indeterminate is deterministic display text, but not a parseable source literal.

This separates two currently conflated operations:

```text
template display rendering
canonical source-literal rendering
```

They can share implementation, but their laws are not identical.

---

# 4. Canonical Record rendering is underspecified

The update says Records render as canonical literal forms in sorted-key order.

That is not enough because Record keys can be arbitrary computed Strings, not only identifiers.

A key such as:

```text
"a-b"
"two words"
"quote\"key"
```

cannot be emitted safely as:

```text
{a-b: 1}
```

The canonical printer needs a frozen key rule.

Recommended rule:

```text
If a key is a valid canonical IDENT:
    key: value

Otherwise:
    ["escaped key"]: value
```

For example:

```text
{a: 1, ["a-b"]: 2, ["two words"]: 3}
```

Sorting should use the same canonical String-key order used by Record identity, preferably stated explicitly as lexicographic UTF-16 code-unit order if that is the existing rule.

Add conformance cases for:

- a computed key containing punctuation;
- a key containing quotes and backslashes;
- an empty-string key;
- keys whose Unicode scalar order and UTF-16 order could differ.

---

# 5. UTF-16 rendering must preserve code units exactly

Strings are specified as UTF-16 values.

Therefore canonical quoted rendering must operate on UTF-16 code units, not through a lossy Unicode-scalar conversion.

If lone surrogate code units are representable through the imported JavaScript escape grammar, then a canonical printer must preserve them, for example:

```text
\uD800
```

rather than replacing them with U+FFFD.

Required wording:

```text
Nested String rendering is a deterministic, lossless encoding of the
String's UTF-16 code units into accepted source-literal syntax.
Unpaired surrogate units are escaped individually.
```

Top-level raw String interpolation should likewise concatenate the original UTF-16 units directly.

This is necessary for the claimed round-trip law and for deterministic value rendering.

---

# 6. Strict openness — the ruling is coherent

The new ruling:

```text
construction is not identity;
closed rational shape is identity
```

is consistent with universal interning.

The consequences are coherent:

```text
a = [() => b]
b = [() => a]

a == b
```

when the two-root graph minimizes to the same one-root rational shape, and:

```text
a2 = [() => b]
a2 == a
```

through late-twin fold-in after the group closes.

Keeping location markers nominal is also essential. It prevents closures touching distinct state locations from merging merely because their code shape matches.

This is the right architectural choice for NEXT's value model.

---

# 7. Open-value observation is missing from the oracle semantics

The ruling depends on the μ-package law that open construction state is never observable.

During a mutual-group window, an open member may be used to construct another member of the same group, but it may not be:

- compared with `==`;
- passed as an ordinary call argument;
- exported;
- returned beyond the window;
- observed by an unrelated interleaved statement.

The updated semantics companion does not operationalize this.

Its environment domain still lists only:

```text
immutable value
slot
under-initialization marker
```

and the trap table has no explicit open-value-observation behavior.

Consider:

```text
a = [() => b]
seen = a == a
b = [() => a]
```

The group specification rejects `seen`, but the current oracle rules do not say where evaluation traps if this invalid kernel program is executed.

That conflicts with the companion's own doctrine:

```text
every analyzer-proven-absent runtime situation has an oracle trap;
trap classes correspond to compile-error classes.
```

## Two valid repairs

### Option A — fold it into `unbound-evaluation`

Treat an open group member as not yet an established value:

```text
Ref(open member) outside construction of the same SCC
    → trap: unbound-evaluation
```

Then update the trap row:

```text
unbound-evaluation
    → B4 boundness + μ open-value observation prohibition
```

This preserves the count of thirteen classes.

### Option B — add a dedicated trap

```text
open-value-observation
```

and increase the count to fourteen.

This gives a more precise oracle/analyzer concordance but makes the recent “thirteen classes” statement stale again.

Option A is smaller and conceptually defensible because an open graph is construction state, not yet a language value.

Whichever option is chosen, the semantics must distinguish:

```text
same-group construction reference:
    permitted as an internal μ edge

ordinary observation:
    traps
```

---

# 8. The trap-count amendment is conditionally accepted

Deleting `unprintable-interpolation` is correct, and the remaining named trap list contains thirteen classes.

However, that count is closed only after the open-value-observation rule is assigned to an existing class.

Therefore:

```text
thirteen traps
```

is accepted if open observation is explicitly folded into `unbound-evaluation`.

Otherwise the correct count is fourteen with a new class.

---

# 9. Cross-reference repair

Section 7 says:

```text
The mechanism ... lands with §5
PENDING-§5
```

Within the semantics companion, §5 is “The two staging theorems,” not μ-canonicalization.

Name the target document explicitly:

```text
PENDING — μ-canonicalization specification §§5–6
```

or the exact implementing section.

This is a simple but important normative-reference correction.

---

# 10. Recommended new conformance cases

Add these alongside the existing interpolation and μ cases:

```text
PR-06:
top-level String interpolation is raw and is explicitly outside
the parse/print identity property.

PR-07:
Record with a non-IDENT key renders using computed-key syntax and
reparses to the same pointer.

PR-08:
quoted rendering preserves lone UTF-16 surrogate units exactly.

PR-09:
aggregate containing Function or Indeterminate renders
deterministically but is not claimed parseable.

FE-07:
same body and captures with different actKind are unequal values.

MU-18:
an unrelated statement observing an open group member is rejected;
the oracle counterpart traps under the selected trap class.

MU-19:
same-group construction references remain legal while MU-18 is
rejected.
```

---

# Final assessment

```text
Closure interning ruling:             accepted
Calls-not-memoized clarification:     accepted
Total interpolation architecture:     accepted
Deletion of printability trap:        accepted
Strict-openness identity ruling:      accepted

Remaining hard integration seams:     2
    - open-value observation in oracle semantics
    - exact perimeter and encoding of canonical rendering

Additional precision repairs:         2
    - actKind explicitly included in closure identity
    - μ-package cross-reference corrected

Foundational redesign required:       no
Focused semantics patch required:     yes
```

The changes improve the language and close previously open decisions. The remaining problems are concentrated at the boundary where those decisions become executable oracle laws. Once that boundary is written precisely, this update should be confirmatory.
