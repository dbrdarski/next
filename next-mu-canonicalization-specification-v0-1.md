# NEXT — μ-Canonicalization Specification v0.1

**Date: 2026-07-17. Status:** the owed C§17 item, now fully specifiable — its one user input landed (open-value identity = shape, via strict openness [user, 2026-07-17]; the two-steps-of-y principle; bisimulation collapse embraced; locations nominal per the split rule). Normative for build step 4 (the canonicalizer). One algorithm, three clients: canonical code (function shape, layer 2, cache keys), function value equality (layer 1), and recursive contracts (C§9). Flips the suite's PENDING-§5 register when implemented.

**Reconciliation note (read first).** The identity ruling fixes *what*: a value's identity is its rational tree — its infinite unfolding — over atoms. This spec fixes *how*, under the interning amendment (closures are plain allocations, never hash-consed): **code** canonicalizes eagerly at compile time (interned, pointer-keyed); **function value equality** evaluates lazily, per comparison, as bisimulation over value graphs. "Group windows / joint canonicalization" from the ruling discussion survive as the code canonicalizer's static grouping (SCCs of forward references), not as runtime tables. Semantics are identical either way — shape is identity; this is the arrangement that costs nothing at closure construction.

---

## 1. Term domain and atoms

Canonicalization operates on kernel code terms and on value graphs built from them. **Atoms** — opaque labeled leaves, never unfolded, never merged across distinct labels:

- interned data values (label = the canonical pointer; they are already canonical),
- location markers (label = binding identity, fork 13) — the split rule, restated hard: locations are nominal; same-body closures over distinct locations yield different leaves, hence different trees, hence distinct values; μ-machinery canonicalizes around location atoms and never touches them,
- primop tags, act-kind, field-name strings, literal payloads (structural labels).

## 2. Binder form (code side)

μ-binders are **positional and nameless**: `μ*[k]` binds k slots; references are `⟨d, i⟩` — slot i of the d-th enclosing binder (d = 0 innermost). Single-slot groups render as plain `μ` with refs `⟨d⟩`. No source name survives into canonical code. The code canonicalizer processes binding-group SCCs (connected components of forward references among consecutive bindings) jointly; a lone self-reference is a component of one — closing at its own statement, per the standing rule.

## 3. Normal-form laws (the frozen tree-construction rules)

1. **No vacuous binder** — a μ whose slots are unreferenced is erased.
2. **Adjacent-binder merge** — a μ directly under a μ at the same term point merges into one group binder, refs re-indexed.
3. **Minimal group** — the binder binds exactly a reference-SCC; members not on a cycle split out beneath it. Proximity in source is not grouping; only genuine mutual reference is.
4. **Slot dedup (the collapse law — ruled)** — slots whose bodies are bisimilar under slot-identification merge into one slot. This law is `a == b == y`: the shape-symmetric two-slot group normalizes to the single-slot self-loop.
5. **Canonical slot order** — after law 4, choose the slot permutation whose serialization (total order on terms: tag-lexicographic, children in positional order, μ-refs by `⟨d,i⟩`) is lexicographically least. **Uniqueness theorem:** a tie between two permutations is a nontrivial slot automorphism, which implies bisimilar slots, which law 4 already merged — contradiction; hence the minimal permutation is unique. (This is the member-ordering rule; its foundation is the ruling's "truly symmetric slots are one slot.")
6. **Value trees** — the tree of a closure value is `node(canonical-code, [capture-trees…])`: data captures are atomic leaves (their pointers), location captures are atomic leaves (binding ids), function captures are their own trees, recursively — loops make the tree rational. Late-twin fold-in is not a special rule: `a2 = [() => b]` builds the same rational tree as `a`, so equality falls out of the definition.
7. **Contracts** — named recursive contracts (`R = expr-mentioning-R`, incl. groups) canonicalize under laws 1–5 identically, μ over contract constructors; C§9's certified unfolding operates on these canonical forms.

## 4. Algorithms

**A. Eager code canonicalization** (compile time, per binding-group SCC): (1) resolve names positionally (de-Bruijn) and mark group references as μ-refs; (2) apply laws 1–3; (3) run **partition refinement** (Paige–Tarjan style) over the group's term graph — initial partition by node label and arity, refine to stability — quotient = the bisimulation-minimal form, which effects law 4; (4) order slots by law 5, serialize, intern: canonical code is pointer-keyed forever. Complexity O(E log N) per group; groups are small (program text bounds them).

**B. Lazy value equality** (runtime `f == g`): compare the two value graphs by **bisimulation with a visited-pair set**: node labels are canonical-code pointers (from A) and atom labels; children compared positionally; a revisited pair is **assumed-equal** (coinductive step — this is exactly what terminates `y == z`, and what makes `a == y` true). Cost O(min graph size); data `==` remains a pure pointer test — only function-containing comparisons ever walk. Optional optimization, semantics-free: cache a computed canonical-tree fingerprint per closure after first comparison.

**C. Open-value edge** (completeness rule): a still-unresolved marker (its binding not yet bound) compares as its binding atom — nominal while open; resolution wins the moment it exists. In practice comparable pairs are post-window (windows are statement-bounded and `==` evaluates at statements); the rule exists so the semantics is total.

## 5. Clients, precisely

- **Layer 2 / cache keys:** algorithm A's interned canonical code is the function shape; act-kind is part of the key [1.0.2]; C§13.4's "de-Bruijn-ordered free-variable contract tuple" presumes exactly A's positional form.
- **Layer 1 / runtime `==`:** algorithm B, per the interning amendment. FE-03 (spelling variants), FE-04 (`x = [() => x]` in a tuple — the tuple's function child compares via B; the F7 interning-key corner remains the runtime review's), FE-05, FE-06 all flip to passing.
- **Contracts:** law 7 canonical forms; recursive-subcontract rows and Part D's future embedding theorem consume them.

## 6. The freeze declaration (per the equality-freeze doctrine, J1)

Runtime `==` is observable semantics; the rule set determining it is enumerated and frozen per language-semantics version. **v1's ==-determining set:** positional α-conversion; μ-laws 1–6; polynomial NF over pure arithmetic bodies (the standing `x => x + x == x => 2 * x` commitment, H-05). Nothing else — boolean-DNF, region tables, and all future analyzer normalization improve analysis only and may grow freely without touching `==`. [Declared here under the doctrine; flagged for the author — amending this list is a semantics-version event.]

## 7. Conformance (suite deltas)

**Flip on landing:** FE-03, FE-04, FE-05, FE-06, H-05's `==` observation. **New cases:** MU-01 vacuous-μ erasure; MU-02 adjacent-binder merge; MU-03 minimal-group split (acyclic neighbor not bound into the μ); MU-04 mixed group with a location capture — μ-shape canonicalizes, location distinctness preserved (two instantiations over fresh `@state` remain unequal); MU-05 recursive-contract pair canonicalizing equal; MU-06 property test — canonical form invariant under member permutation and renaming (random small groups); MU-07 cross-check — algorithm B agrees with bounded naive unfolding on small graphs; MU-08 `isEven`/`isOdd` — distinct bodies, two slots, no collapse, deterministic order.

**Pipeline placement:** build step 4, with normalization; the harness laws (`eval ∘ normalize = eval`, idempotence) cover A's rewrites; B ships with its own MU-07 cross-check.
