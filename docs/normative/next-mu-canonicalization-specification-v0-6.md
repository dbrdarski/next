# NEXT Recursive Identity and Canonicalization Specification v0.6

**Date:** 2026-08-08. **Status:** author-ruled, design-closed. **Supersedes:**
`next-mu-canonicalization-specification-v0-5.md` for function shape, closure identity,
recursive-group representation, Algorithm A, and analyzer-instance identity. The v0.5 equality
freeze, openness law, value-graph exact-verification law, and recursive-contract obligations remain
in force where this document does not replace them.

## 1. One function, one code shape

Every function has its own finite canonical code. Bound parameters and local binders are replaced
by positional de-Bruijn identities; immutable free references are replaced by positional capture
references. In the current kernel encoding those positions are printed as `$n` and `@capn`.
Source names, source-group membership, declaration order, and member names are absent from code
identity. `ActKind` and literal payloads remain part of the code.

Closure conversion is conceptual application of an outer capture function, not new surface syntax
and not an extra user-visible call:

```next
@mutable x = 1
f = () => x
```

has canonical organization `(capture x) => (() => @cap0)`. Formation supplies the current
immutable value of a Pure read; invocation supplies only the source-declared arguments. A later
write cannot change the formed Pure function. Mutator writes use their separate setter/staging
channel and are not location captures in Pure identity.

## 2. The applied function is the identity

A closed function value is canonical code applied to an ordered immutable capture graph:

`FunctionValue = Apply(CanonicalCodePointer, CaptureEdges[])`.

For an acyclic closure, every edge ends at an already-interned value and the interner uses the
shallow key `(code pointer, capture pointers)`. For recursive closures, capture edges may form a
finite rational graph. The rooted graph—not a declaration group—is the value. Two roots are equal
exactly when their canonical code labels and corresponding capture edges are bisimilar. After
interning, runtime `==` remains pointer comparison and calls are never memoized.

There is no `GroupTemplate`, group-level code pointer, entry slot, canonical member ordering,
source-group reconstruction, group capture-routing table, or serialized `μRef`. Those constructs
are not alternate implementations of this law; they are superseded machinery.

## 3. Recursion is a construction condition

The compiler/evaluator discovers recursive construction by the reference SCC of declarations in
one lexical item sequence. A self edge or multi-member SCC opens a construction window. The window
allocates provisional roots, connects self/sibling capture positions, and closes all roots jointly
after every required dependency has arrived. It contributes no semantic identity and disappears
after closure.

The SCC answers only *which values must be tied together before observation*. It does not prove
termination. Termination is a later behavioral judgment over reached calls and their arrived
arguments; recursion discovery stops when an already-reached function edge is encountered and
records that transition for the grounding/safety procedures.

Open values remain unobservable: equality, export, return past the window, and ordinary calls over
an unresolved root are illegal. Construction may compose open aggregates and closures inside the
same window. At close, no unresolved marker escapes.

## 4. Canonical examples

```next
a = () => b()
b = () => a()
```

Both functions have the same canonical code `K = (captured) => () => captured()`. Construction
forms the equations `a = K(b)` and `b = K(a)`. Their rooted rational trees are bisimilar and intern
to one pointer. The equivalent self loop interns to that same pointer.

```next
even = (n) => n == 0 ? true  : odd(n - 1)
odd  = (n) => n == 0 ? false : even(n - 1)
```

The recursive capture position is the same kind of edge, but the canonical code labels differ at
`true` versus `false`; the two roots remain distinct. Renaming `even`/`odd`, renaming parameters, or
permuting declarations changes neither result.

## 5. Value-graph interning

At window close:

1. Rewrite every provisional self/sibling reference to a positional graph edge.
2. Require the complete reachable graph to contain no unresolved capture.
3. Compute a coarse fingerprint only to select candidate buckets.
4. Compare each candidate by exact rooted bisimulation with a visited-pair set.
5. Reuse the established canonical root or publish a new closed graph, then redirect every
   provisional handle to its canonical root.

A fingerprint never establishes equality. Aggregate nodes participate in the same mixed graph, so
the tuple/record flagships remain ordinary consequences of rooted bisimulation. The current locked
root-vector backing may later become one allocation with internal offsets; that is a layout and
reclamation refinement, not a semantic identity layer.

## 6. Analyzer instances and late local calls

A concrete analysis instance is its canonical closed function `ValueRef`. When a function value
actually flows through a value seat but its immutable captures are known only by contract (for
example a factory product returned from `makeAdder(someInput)`), analysis may carry a descriptor:

`FlowingInstance = Apply(CanonicalCodePointer, InternedCaptureContractTuple)`.

This descriptor is analysis metadata, not a formed closure value and not runtime identity. Code
and capture tuple are interned under the same identity owner as their facts; source spelling is
diagnostic provenance only. `Known(S)` is a finite set of such represented flowing alternatives,
and application processes every live member through the correlated-alternative driver. A repeat
closes only through a domain-indexed fact covering the same complete descriptor and arrived
arguments; code-shape repetition alone proves nothing.

A local lambda over an outer function argument is a different case. It is not formed before the
outer function executes, so analysis must not invent a symbolic captured value or a cyclic
metadata graph. A direct local call is resolved late by ordinary closure conversion for the
judgment: outer bindings become additional leading arguments of an analyzer-only closed function.
For example:

```next
outer = (limit) => {
  f = (n) => n == 0 ? limit : f(n - 1)
  => f(3)
}
```

is judged as `F(limit, 3)`, with the recursive transition `F(limit, n - 1)`. `limit` is an
invariant arrived argument; it is not a termination measure and is not represented as a closure
value. Recursion discovery stops at the reached `F` back-edge and records the argument drift.
Safety, return, completion, and grounding use the ordinary concrete fact graph for this lifted
identity. Runtime execution remains unchanged: executing `outer` forms `f` with the current
concrete value of `limit`.

## 7. Recursive contracts

Named recursive contracts retain their own progress-guarded canonical constructor graph and least
fixpoint denotation from the recursive-contract specification. They do not acquire function
`GroupTemplate` identity. Contract SCC discovery, admissibility, constructor normalization, and
rule-set-versioned interning remain analyzer operations distinct from runtime function equality.

## 8. Equality freeze and conformance

The v0.5 equality-freeze list remains unchanged: retained-operand reordering, literal folding, and
demand-preserving like-term combination are admitted; zero-annihilation, cancellation,
demand-dropping identity elimination, and any rewrite erasing a potentially diverging operand stay
excluded.

MU/FE expectations remain stable. Their mechanism assignment is updated:

- MU-01/MU-03 test construction-window discovery only.
- MU-06 tests rename and member-permutation invariance of canonical function values.
- MU-07 tests exact rooted-graph bisimulation.
- MU-14/15/16 test distinct code, equal-capture collapse, and cross-construction collapse directly
  on instantiated value graphs.
- MU-17 tests mixed aggregate/function rational graphs.
- MU-18/MU-19 retain open-observation rejection and same-window construction legality.
- Analyzer regressions must prove canonical symbolic-instance interning, capture distinction,
  instance-set traversal, and domain-indexed recursive cutoff without a group-identity side channel.

*End of Recursive Identity and Canonicalization Specification v0.6.*
