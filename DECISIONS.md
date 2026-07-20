# DECISIONS.md — NEXT implementation changelog

Provenance discipline (CLAUDE.md § Process): what the specs **mandated**, what I
**chose** where a representation was left open, and what I'm **asking** the author.
Status tags mirror the compendium's vocabulary. Newest entries first.

---

## 2026-07-19 — Contracts C.1: the algebra + denotational membership (Part C begins)

`src/contract/` (mod.rs, tests.rs). Compendium C§4 (contract algebra) + C§16
(denotational kernel). 10 membership seeds; full suite 163, 0 ignored, clippy
clean. **First analysis-layer code** — legitimate now the oracle + harness are
green (hard rule 1).

- **Delivered:** the `Contract` enum (C§4): `Top`/`Bottom`, `Kind`, `Equals`,
  `Range`, `Greater`/`GreaterEq`/`Less`/`LessEq`, `Mod{n,r}`, `Geo{b,r}`,
  `Union`/`Intersection`/`Difference`, `Record`/`HasField`/`Tuple`,
  `Indeterminate`. Plus `Contract::contains(v)` — denotational membership
  (`v ∈ ⟦C⟧`, C§16), decidable for every constructor, brute-tested against the
  oracle's interned values.
- **Notes on specific rules:**
  - `Equals` uses the oracle's `values_equal` (bisimulation), so a fresh
    structurally-equal value satisfies it — not pointer identity.
  - `Mod{n,r}` denotes integers `x ≡ r (mod n)` (rational moduli clear to the
    integer lattice, C§3.1); non-integers are excluded.
  - `Geo{b,r}` (`r>1`, `b≠0`) is decided by dividing out `r` — terminates since
    `r>1` shrinks the quotient.
  - `NotEquals` is **not** a constructor — it is `Difference(Top, Equals(v))`
    (C§4), and tests exercise it that way.
- **`Record(fields)` field-openness — RESOLVED [user, 2026-07-20]: exact.**
  (Was flagged `[ask-author]`.) A `Record` contract denotes a record with
  **exactly** those fields (no others), each satisfying its contract — matching
  the pattern layer's exact-by-default `PRecord(fields, rest?, exact)` (E9) and
  full-keyed records (E11). `HasField(key)` is the open "at least this field"
  form. Membership updated: `record_contains` now also checks the key set matches
  (equal counts + all listed fields present ⇒ equal key sets).
- **Deferred:** named recursive contracts (C§9 `[owed]`) — no constructor yet;
  they need the certified-unfolding doctrine + μ-binder contract canonicalization.
- **Next (C.2):** three-valued subcontract `A ⊑ B` (proven/refuted/unproven),
  brute-tested against membership.

---

## 2026-07-20 — RULING [user]: function `==` and analyzer function-equality are ONE truth

A foundational ruling from the author, superseding the μ v0.5 §8 / recursive-
contracts §2 framing where runtime `==` (syntactic, frozen) and analyzer
contract-equality (contract-directed, versioned) are *separate*. For **function
values** they must be a single notion. Recorded here; flagged for the spec author
(the two docs need a small amendment — see below).

### The principle
The whole premise of NEXT is that the contract system prevents runtime bugs. If
the contract system concludes `f == g` while the runtime computes `f != g`, the
contract system has lied about runtime reality at that point — the premise breaks.
So there must be **one** notion of function equality, used both statically
(analyzer) and dynamically (runtime `==`). Not "equal in the contract system but
not at runtime." This is a soundness/consistency requirement, not aesthetics.

### The mechanism (how one truth is realized)
There is a compilation step; canonicalize there.
1. **Compile time:** canonicalize every function to a canonical form.
   Canonicalization includes **both** the syntactic μ-laws (α, reorder, `x+x→2x`,
   μ-binder laws) **and** **contract-directed collapse** — e.g. `0*x → 0` fired
   *only* where the analyzer has proven the precondition (`x: Number`), carrying
   the domain forward so the collapsed form has the same accepted domain.
2. **Intern** functions by that canonical form.
3. **Runtime `==`** is a pointer test on the canonical form — still O(1).
4. The **analyzer** reasons about the *same* canonical form.

Consequence: `(x:Number)=>0*x` and `(x:Number)=>0` collapse to one canonical form
⇒ they are `==` at runtime *and* in the analyzer. One artifact, one truth, no
discrepancy. (No circularity: the analyzer *produces* canonical forms; the runtime
*compares* them. No non-termination: the analysis is bounded, Principle 7.)

### The "syntactic floor + contract-directed rules" model
- The μ §8 syntactic slice is **not** the permanent definition of `==`. It is the
  **floor** — what is provable with *zero* contract information.
- Contract-directed collapses are **additional canonicalization rules** that fire
  when the analyzer proves their preconditions, folding into the *same* canonical
  form.
- `==` therefore **strengthens** as the prover improves (a semantics-version
  event; the language already versions its semantics). Within a compiler version
  it is fixed and deterministic; across versions it moves *closer* to true
  equality — the right direction, and one truth at every version.

### The one hard limit (a boundary, not a discrepancy)
True extensional function equality is **undecidable** (Rice's theorem) — no
procedure decides it for arbitrary functions. So `==`, unified or not, is
necessarily **sound but incomplete**: it may fail to notice some genuinely-equal
pairs, but it never calls distinct functions equal. Crucially, when the two
systems are unified this incompleteness is **shared** — `f == g` (runtime) ⟺
analyzer-proves-`f == g` ⟺ same canonical form, always the same answer. No runtime
bug slips through a spot where the contract system said "equal," because it is
literally the same decision. The gap that remains is the shared floor of
decidability, not a rift between analyzer and runtime.

### Consequences for this implementation
- **`==` is defined architecturally as "canonical-form equality," open to
  contract-directed rules** — *not* "syntactic-only equality." The current code
  already computes `==` on the canonical shape (`equal.rs` / `canon.rs`), so this
  is forward-compatible: today `==` = the syntactic floor (`0*x != 0`, since
  nothing has proven `x: Number`); when the analyzer lands, its proven equalities
  join the canonical form and `==` strengthens, staying one truth.
- This **aligns with the deferred "universal interning" re-architecture** (μ v0.5
  §6): interning functions by canonical form + a pointer-test `==` *is* the
  mechanism above. So that deferred item and this ruling are the same work.
- **Contract-directed collapse requires the analyzer** (domain inference), which
  isn't built yet — so no code change now; the ruling fixes the *definition* and
  the forward path.

### Flagged for the spec author (small amendments)
- **μ §8:** reframe the "frozen syntactic ==-set" as the *floor* of a canonical
  form that contract-directed rules extend (each extension a semantics-version
  event) — rather than a permanently-syntactic `==`.
- **Recursive-contracts §2:** the line *"contract equality is analyzer identity,
  **not** runtime value equality"* reads as a permanent *separation*. For
  **function-value** `==` that separation is the discrepancy being rejected — it
  should read "function `==` is canonical-form equality, computed at compile time,
  shared by analyzer and runtime." (That line may have meant *contract-expression*
  equality — `Range==Range` — which is genuinely analyzer-internal; but for
  function values, unify.)

---

## 2026-07-20 — Reconcile with updated specs (μ v0.5 + recursive-contracts v0.2)

The author replaced the μ spec (v0.1 → **v0.5**, four review rounds) and added
`next-recursive-contracts-specification-v0-2.md` (the C§9 package), and amended
the compendium (B1/B3/B4/C§9/C§11/C§12.3/F1–F3). Reviewed all; made the necessary
fixes. Full suite 164, 0 ignored, clippy clean.

### Fixed now (real conformance bug)
- **Polynomial NF narrowed to the frozen `==`-slice (μ v0.5 §8).** My previous
  poly-NF did full polynomial normalization, which **over-equated**: distribution,
  cancellation (`x−x`), annihilation (`0*x`), and identity-elimination (`x+0`,
  `x*1`) — all now **permanently excluded** because they change divergence and
  operation-safety demands (`(x)=>x−x` demands `x` be a Number and traps
  otherwise; `(x)=>0` does not — so they are *not* the same function). `poly.rs`
  rewritten to the three permitted rewrites only — commutative/associative
  reordering, literal folding (no variable erased), like-term combining where
  every variable survives (`x+x → 2*x`, H-05 kept) — **aborting** (rebuild with
  normalized children, otherwise unrewritten) whenever a rewrite would erase an
  operand or drop a demand. No distribution. Verified: the four excluded
  rewrites now compare `!=` (MU-10), H-05 and reordering/folding still `==`.
- **MU-17** (mixed-aggregate flagships): the record self-reference variant
  `r = { f: () => r }` interns equal like the tuple flagship — already handled by
  algorithm B's bisimulation; added as a test.
- **Docs:** CLAUDE.md now lists six normative docs (μ → v0.5, recursive-contracts
  v0.2 added). μ-v0.1 kept on disk as history.

### Deferred (flagged — not behavioral-correctness bugs)
- **Universal interning restored (μ v0.5 §6 / B1 / F1–F3).** v0.5 *reverses* the
  v0.1 "closures are plain allocations" amendment: closures now intern shallowly
  (acyclic key = (canonical-code pointer, capture pointers); μ-group members at
  window close by group fingerprint), so runtime `==` is a **pointer test** and
  Algorithm B becomes canonicalization-internal. My current runtime `==` uses
  Algorithm B (`values_equal`) directly — which I verified is **observably
  equivalent** (intern-by-(shape,captures) yields the same `==` results). So this
  is a **mechanism/performance** re-architecture, not a behavioral fix; it is
  entangled with the construction-window machinery (§4), so it is deferred and
  logged, not silently skipped.
- **Open-value observation prohibition (μ v0.5 §4 / MU-09 / B4).** An *analyzer*
  compile-error; it does not affect the oracle's runtime for accepted programs.
  The "nominal while open" edge in `equal.rs` is withdrawn by the spec and is now
  dead for accepted programs; it becomes moot under the interning re-architecture.
- **Algorithm A capture routing + capture-space ordering + capture vector
  (μ v0.5 laws 4/8, §5).** My `mu.rs` is the pre-routing core (laws 1/3/5);
  MU-14/15/16 (the makePair code-vs-value distinction, the instantiated
  group-value graph) need capture routing and the instantiated graph — layer-2,
  deferred with the analyzer.

### Newly unblocked (next)
- **Recursive contracts (C§9)** are now fully specified (v0.2) — the C.1
  `[ask-author]`-adjacent deferral. Buildable: admissibility, vector-lfp
  denotation, progress-guarded subcontract, productivity emptiness.

---

## 2026-07-19 — Algorithm A: eager code canonicalization of binding groups (μ spec §4A)

`src/oracle/mu.rs` + `src/oracle/mu/tests.rs` (new). μ-Canonicalization Spec
§2/§3/§4A. 6 MU conformance tests; full suite 153, 0 ignored, clippy clean.

- **What it is:** canonicalizes a set of (mutually) recursive bindings into
  **canonical code** — mutual references become positional μ-refs `⟨d,i⟩`,
  recursion is grouped by SCC, each group serialized in a canonical slot order.
  This is the **layer-2 shape** for C§13.4 cache keys and recursive contracts
  (C§9). **No runtime consumer yet** (layer-1 `==` is algorithm B); `mu.rs` is
  `#![allow(dead_code)]` and exercised only by the MU tests until the analyzer
  lands.
- **Delivered (the testable core):**
  - Tarjan **SCC** over a scope-respecting free-reference graph (binder-aware, so
    a shadowed group name is not an edge).
  - **Laws 1 + 3:** only genuine cycles (a self-loop or ≥2 SCC) become μ-groups;
    acyclic neighbours split out and reference the group by canonical key.
  - **Positional encoding:** intra-group refs → μ-refs, λ/match-bound vars →
    de-Bruijn, cross-SCC refs → canonical key, free names → by name.
  - **Law 5 / canonical slot order:** the lexicographically-least serialization
    over all slot permutations (brute-forced — groups are tiny; O(k!) with k
    small, avoiding a full Paige–Tarjan implementation).
  - **Content-based constant serialization** (not pointer) so canonical codes are
    stable across interners — the cross-program rename/permutation invariant.
  - Conformance: **MU-01** (vacuous-μ erasure — non-recursive binding gets no μ),
    **MU-03** (minimal-group split — acyclic neighbour not bound in), **MU-06**
    (invariance under member renaming and permutation), plus self-recursion → a
    1-slot μ and a distinctness sanity.
- **Deferred (flagged):** **law 2** (adjacent/nested-binder merge — only arises
  with nested groups), **law 4** (bisimulation collapse of truly-symmetric slots
  — law 5 gives permutation-invariance but not slot *merging*; needs partition
  refinement), and **MU-02/MU-05** (the former needs nested groups, the latter
  needs contracts). These are precision refinements for the analyzer, not
  correctness gaps for what exists.
- **`// [ask-author]`:** none. The build-ahead nature was raised with the user and
  accepted before implementation.

---

## 2026-07-19 — Polynomial NF over arithmetic bodies (frozen ==-set, H-05)

`src/oracle/poly.rs` (new), `src/oracle/{canon.rs,eval.rs,mod.rs}`, `src/value.rs`.
μ-Canonicalization Spec §6. 3 new poly seeds; full suite 147, 0 ignored, clippy
clean. Closes the last observable gap in the frozen `==`-determining set.

- **Delivered:** shape canonicalization now puts arithmetic subterms into
  polynomial normal form, so algebraically-equal bodies share a shape and compare
  `==`: `x+x == 2*x` (H-05), constant folding, commutativity, `x-x == 0`,
  distribution, `x*x == x**2`, multivariate commute.
- **Representation:** a polynomial is `monomial → rational coefficient`; a monomial
  is `atom-key → exponent`. Atoms (variables) are non-arithmetic subterms,
  serialized canonically (so equal atoms unify) and normalized recursively;
  handled operators are `+ - *`, unary `-`, division by a **nonzero constant**, and
  a **nonnegative integer constant** power. Reconstruction emits a deterministic
  canonical `Expr` (monomials and factors in serialized order).
- **Soundness — only total exact-rational identities are used:** `x/x`, `x % y`,
  `x/0`, and variable / negative / non-integer powers are **left as atoms**, never
  simplified — so a partial op is never equated with a total one. Verified: `x/x`
  ≠ `1`, `x % x` ≠ `0`, `x` ≠ `x+1` all stay distinct; and NF-equal functions are
  shown to compute the same value. Evaluation is untouched (shapes drive identity
  only; closures run their original body).
- **Known incompleteness (conservative, flagged):** poly-NF can *eliminate a
  capture* (e.g. `(a) => k - k` ⇒ `0`), leaving a vacuous entry in `free_vars`
  that `==` still compares — so two such constant functions with different `k`
  compare unequal (a sound false negative). Closing it needs a capture
  prune/renumber pass after NF (analogous to μ-law 1's "no vacuous binder"); left
  as a follow-up since real code rarely hits it.
- **Frozen `==`-set status:** positional α-conversion ✓, μ-laws' observable effect
  via algorithm B ✓, polynomial NF ✓ — the `==`-determining set is now
  observationally complete (modulo the capture edge above). Amending the set is a
  semantics-version event (spec §6).
- **`// [ask-author]`:** none.

---

## 2026-07-19 — μ-canonicalization: value identity via bisimulation (the spec landed)

`next-mu-canonicalization-specification-v0-1.md` (new normative doc, author-
provided), `src/oracle/{canon.rs,equal.rs}`, `src/value.rs`, `src/oracle/{mod.rs,
eval.rs}`. **All ignored seeds now green — 144 tests, 0 ignored, clippy clean.**
This closes the μ half deferred earlier and *re-architects* the previous entry.

- **The ruling (author):** open-value identity = **shape**, via strict openness;
  bisimulation collapse embraced; locations nominal (fork-13 split). The prior
  three open questions are all answered by the spec.
- **Architecture correction:** the previous "de-Bruijn half" interned functions by
  a canonical *key with captures inlined*, bailing to opaque on recursion. The
  spec's arrangement (interning amendment) is different and is what I now
  implement:
  - **Closures are plain allocations, never hash-consed** — `FnValue` has pointer
    identity, so the interner treats functions (and structures containing them) as
    distinct allocations.
  - **Code shape is canonicalized (algorithm A, α + capture-slot layer, `canon.rs`):**
    bound vars → positional `$k`, free vars → capture slots `@cap`i (names kept in
    `free_vars`, resolved lazily). Captures are *not* inlined; the shape is finite,
    so shape identity is structural.
  - **Runtime `==` is algorithm B (`equal.rs`):** bisimulation over value graphs
    with a visited-pair set; a revisited pair is assumed equal (the coinductive
    step). Data `==` stays a pointer test (fast path); only function-containing
    comparisons walk. Locations compare nominally (same slot ⇒ equal); the
    open-value edge (§4C) compares an unresolved capture by name.
- **Seeds flipped:** `y=[()=>y] == z=[()=>z]` (self-ref), `a==b==y` (law-4 collapse
  at the value level, via the memo — no code μ-minimization needed for layer 1),
  mutual-recursion group equality, MU-04 (location nominality), MU-08
  (isEven/isOdd distinct), plus α-equivalence and capture-by-value. MU-07 ships:
  algorithm B is cross-checked against a bounded naive unfolding.
- **Deferred (layer 2 / analyzer, gated):** algorithm A's *full* μ-binder
  minimization — SCC grouping, Paige–Tarjan partition refinement, laws 1–5,
  canonical slot order — produces the interned canonical *code* used by C§13.4
  cache keys and recursive contracts (C§9). Layer-1 `==` does not need it (B's
  coinductive bisimulation already collapses symmetric recursion), so it lands
  with the contract phase. Also deferred: **polynomial NF** over arithmetic bodies
  (the frozen set's H-05 item, `x => x + x == x => 2 * x`) — a distinct shape
  normalization, not yet implemented.
- **Frozen `==` set (spec §6) noted:** amending it is a semantics-version event.
- **`// [ask-author]`:** none.

---

## 2026-07-19 — §5 canonical function identity (de-Bruijn half) [superseded by the μ-canonicalization entry above]

`src/oracle/canon.rs` (new), `src/value.rs`, `src/oracle/` (mod.rs, eval.rs).
Kernel AST §5. 5 new identity seeds green; the `((x)=>x)==((y)=>y)` seed
un-ignored; full suite 137 (+1 ignored); clippy clean. First slice of the §5 work
we deferred (with the author's sign-off).

- **Delivered:** function-value identity is now **canonical**, not pointer-based.
  `make_closure` computes a `FnKey`:
  - `Canonical(Lambda)` — the body with bound variables α-renamed to positional
    canonical names (`$0`, `$1`, …) and free variables replaced by the constant
    they captured (an immutable value) or a location marker (a Box slot —
    location identity participates in function identity, B1). Structurally-
    identical functions with equal captures now compare `==`.
  - `Opaque(u64)` — when a free variable is not yet resolvable (self/mutual
    recursion under initialization: the μ case), canonicalization **bails** and
    the closure gets a unique id (distinctness). Always sound: it can only fail to
    merge, never wrongly merge.
- **Value layer:** `ClosureRef` → `FnValue { closure, key }`; `==`/hash are by
  `key` only. Evaluation still walks the original body against the captured env
  (unchanged eval path), so late binding / mutual recursion are unaffected.
- **Seeds now green:** α-equivalence (incl. multi-param and nested lambdas),
  capture-by-value equality and inequality, identity through structures
  (`[(x)=>x] == [(y)=>y]`), and self-equality of recursive (opaque) functions.
- **Still deferred (μ half):** the §7 group-identity pair (`y = [() => y]` /
  `z = [() => z]`) — their bodies self-reference, so they canonicalize to opaque
  and stay `#[ignore]`d. Closing it needs μ-markers (rational-tree comparison),
  which the compendium marks `[owed]`.
- **Chosen — per-oracle opaque counter:** reset to 0 per `Oracle`, so a program
  and its normalization assign matching opaque ids (keeps the `eval ∘ normalize`
  harness consistent for recursive-function-valued programs). Correct because
  canonical dedup only fires on equal captures, and the harness compares
  structurally-equivalent programs.
- **`// [ask-author]`:** none.

---

## 2026-07-19 — Build-order step 4: normalization + property harness — **BUILD ORDER COMPLETE (the gate)**

`src/normalize/` (mod.rs, tests.rs). Kernel AST §5 + Part I harness laws. 5
normalize tests green (incl. the property harness over a 22-program corpus); full
suite 132 (+2 ignored); clippy clean.

- **Mandated (Part I), the deliverable:** the property harness enforces, against
  the oracle, `eval ∘ normalize = eval` and idempotence
  (`normalize(normalize(m)) == normalize(m)`) over a corpus spanning every node
  kind. This is the machine-checked link between the normalizer and the truth
  source.
- **Chosen — active rule set (small, spec-named, clearly eval-preserving):**
  - Template **adjacent-segment folding** (§4).
  - **Literal template → constant**: a template with no interpolations is the
    string it denotes.
  Everything else is a structure-preserving recursive map, so further rules bolt
  on in one place.
- **Deferred (consistent with the §5 sign-off):** the heavy §5 canonicalization —
  de-Bruijn free-variable ordering and μ-binder canonicalization — is *not* built
  here; it lands with canonical function identity. The harness is designed so
  those rules, once added, are checked by the same `eval ∘ normalize = eval` law.
- **Chosen — outcome comparison:** the harness runs original and normalized forms
  in the *same interner*, so produced values compare by pointer and traps by
  class (`Result<ValueRef, TrapClass>`), giving an exact "same outcome" check.
- **`// [ask-author]`:** none.

### Build-order status: **gate reached.**
Steps 1–4 (value layer → lexer/parser/desugar → oracle → normalization + harness)
are complete and green. Per Part I we **stop here**: contracts / the three-valued
checker / demand core / recursion analysis are the explicitly-gated later phase,
not to be started until the author opens it. Outstanding within the completed
scope: the two `#[ignore]`d §5 function-identity seeds, and the small B6 tail
already noted (all logged).

---

## 2026-07-19 — Build-order step 3 (part 3): B6 effect harness — **oracle complete**

`src/value.rs`, `src/interner.rs`, `src/oracle/` (harness.rs new; eval.rs,
mtch.rs). Semantics companion §4 + B6. 6 effect seeds green; full suite 126
(+2 ignored); clippy clean. **This completes build-order step 3 — the oracle.**

- **Mandated (§4/B6), implemented and tested:**
  - New value kind `ValueData::Native` (pointer-identity `NativeRef`): a
    host-callable that runs Rust when applied — the only way host effects (which
    aren't expressible in NEXT) can exist. `eval_apply` dispatches native-vs-
    closure; natives honour the world admission matrix (effect-kind ⇒ effect world
    only).
  - Host-effect doubles injected by the harness: `println`/`exit` (record into an
    observable `HostIo` buffer) and a fallible `readFile` (returns a Failure).
  - `Failure` is the one prelude Record shape (`path` + `reason`); the `Failure`
    contract pattern matches it structurally (E9 — Failure discharge dissolves
    into contract-as-pattern). A failed effect returns a Failure that flows as
    ordinary data — nothing unwinds.
  - **`then`/`catch` proven to be NEXT library code:** the seed defines them in
    NEXT source (over `Match`) and shows a success flowing through `then` while a
    Failure short-circuits it and is recovered by `catch` — no interpreter
    builtins.
- **Chosen — entry programs need not end in a value:** `run_module_in` now returns
  null when the last statement completes without a value (an entry may end in an
  effect statement), rather than trapping. The expecting-seat demand still fires
  in genuine value positions (bindings, operands, …), which the seeds check.
- **Chosen — line-leading `[`/`(` starts a new statement** (parser): a postfix
  index/call only attaches on the same line as its target; a `[`/`(` opening a
  fresh line begins a new statement (the greedy-continuation hazard, §1.1). `.` /
  `?.` still continue across lines (unambiguous). This is the same class of fix as
  the arrow `=>` line rule.
- **`// [ask-author]`:** none. `exit` as a double records the code and returns
  rather than terminating (the real host limit is outside the semantics, §4).

---

## 2026-07-18 — Build-order step 3 (part 2): worlds + mutator staging

`src/oracle/` (mod.rs, eval.rs). Semantics companion §3 (Apply/Write) + §5
staging theorems. 6 new mutation seeds green; full suite 118 (+2 ignored);
clippy clean. Covers task 3c.

- **Mandated (§3), implemented and tested:**
  - `Write` legal only in mutator world (else `world-admission` trap); stages into
    the pending set π.
  - Slot reads use **read-your-writes** (π if staged, else σ).
  - Mutator application: from mutator world **join** the current transaction (same
    π, no publish); from effect world **begin** (π := ∅), run, and **publish** at
    completion. Mutator Apply outcome is `CompletedWithoutValue` (return-nothing
    law).
  - **Publish** commits only staged slots whose value differs by pointer (the
    interning-exact equality guard, B7/G1); a trap publishes nothing (§5).
  - Effect application runs the body in effect world; the world admission matrix
    (pure→{pure}; mutator→{pure,mutator}; effect→all) is enforced with
    `world-admission` traps on violation.
- **Chosen — commit counter on the store:** the equality guard's "fires nothing"
  is otherwise unobservable without the (fenced) reactive layer, so `Store` counts
  *actual* commits and a `run_program_commits` test helper asserts an equal write
  commits zero times. Test-only observability; no semantic effect.
- **Chosen — "invisible until outermost completion" is tested via join
  accumulation:** in the sequential oracle, σ is only inspectable post-transaction,
  so the nested-join seed asserts the accumulated result (inner write visible to
  outer read via shared π, single publish) rather than mid-transaction σ.
- **Deferred to a small follow-on (B6 effect harness):** host effects (test
  doubles for `println`/`exit`), `Failure` records as plain data, and the
  `then`/`catch` prelude functions. These need a native-callable value kind; the
  mutation core (the delicate part) and effect-world mutator invocation are done.
- **`// [ask-author]`:** none.

---

## 2026-07-18 — Build-order step 3 (part 1): pure oracle core + Match

`src/env.rs`, `src/oracle/` (`mod.rs`, `eval.rs`, `mtch.rs`, `tests.rs`).
Semantics companion §3, the pure fragment. 29 oracle seeds green; full suite 112;
clippy clean. Covers tasks 3a + 3b.

- **Mandated (§3), implemented and tested:** exact rational arithmetic; total
  division (`x/0` ⇒ Indeterminate) with left-most Indeterminate propagation
  through arithmetic; `==`/`!=` as pointer equality (Indeterminate is an ordinary
  value); ordering comparisons trap `undischarged-Indeterminate`; late binding via
  a runtime environment (direct + mutual recursion work); `Match` as the sole
  control node with the completion triple; construction (tuple/record, later-wins,
  spreads); access (field/index/slice, demand vs `?.` totals, from-end,
  clamped-total slices); grapheme string index/slice (pinned `unicode-segmentation`);
  template stringification by B2 rules. Nine trap classes fire end-to-end.
- **Chosen — runtime environment (not §5 resolution):** `Scope` chain with names;
  a binding is marked `UnderInit` while its RHS evaluates, so `x = x` traps
  `unbound-evaluation` while a self/mutually-recursive lambda is fine (its body
  isn't evaluated at bind time). This is the agreed approach (see the §5 deferral
  entry below).
- **Chosen — closures capture the environment by reference** (`Rc<Scope>`), which
  is what makes late binding / mutual recursion fall out. Function identity is
  `ClosureRef` pointer identity (the conservative approximation already signed
  off).
- **Chosen, spec-faithful clarifications:**
  - `tested-seat` trap is **guard-only** (companion §3). A non-Boolean *ternary
    condition* desugars to a Boolean-exhaustive match, matches no arm at runtime,
    and surfaces as `expecting-seat` (the analyzer rejects it up front). Both are
    tested.
  - Contract-as-pattern: the runtime-decidable **Kind** checks (`Number`,
    `String`, `Boolean`, `Null`, `Tuple`, `Record`, `Function`) and
    `Indeterminate` are implemented; user-defined contract patterns trap (they
    need the contract engine — analyzer phase).
  - `%` on rationals is the truncation-toward-zero remainder; `**` supports
    **integer exponents only** (irrational-producing ops are omitted from the PoC,
    B2) — a non-integer exponent traps `operation-safety`.
  - Entry-file top level evaluates in **effect world** (the one derivation the
    companion makes, §2).
- **Deferred to step 3c (part 2):** mutator/effect *application* (worlds admission
  is checked, but a mutator/effect call currently traps a placeholder), `Write`
  evaluation, the pending-set/read-your-writes/publish staging, host effects, and
  Failure records. `DidNotComplete` (divergence) is genuine non-termination, not a
  represented value.
- **`// [ask-author]`:** none.

---

## 2026-07-18 — Decision [user-approved]: defer §5 canonicalization; approximate function identity

Sign-off recorded before starting the oracle (step 3). **What the oracle does:**
evaluates kernel AST by resolving names against a runtime environment (late
binding, B4 / semantics §1 `ρ`) — no de-Bruijn/§5 canonicalization pass is built
yet. **What that costs, in full (nothing else):**

- Function-value identity is *approximate*. Same-meaning functions with different
  written shape (α-equivalent, or equivalent-but-differently-written bodies) may
  intern distinct instead of equal. This propagates to values that *contain*
  functions; pure data (numbers/strings/tuples/records of data) stays exact.
- Observably, only `==` on functions (and function-containing structures) is
  affected. The approximation is **conservative**: it can only *fail to merge two
  equal functions*, never merge two different ones — so no wrong `true`, and no
  effect on any produced non-function value, control flow, world/mutation
  semantics, trap, or completion outcome. Soundness is untouched.
- The `y = [() => y]` / `z = [() => z]` interning seed and the §7 group-identity
  pair stay `#[ignore]`d with a note pointing here, until §5 lands.
- Function-value interning is confined to one place (a `ClosureRef` pointer
  identity for now); swapping in §5's canonical-body key later is a localized
  change and does not touch the oracle's evaluation logic.

**User: "consider it settled."**

---

## 2026-07-18 — Build-order step 2c: desugar to kernel AST

`src/desugar/` (`mod.rs`, `hask.rs`, `tests.rs`). Kernel AST spec §4 (the closed
catalog) + E10. 27 desugar-equivalence seeds green; full suite 83; clippy clean.
**This completes build-order step 2.**

- **Mandated (§4 rows), all implemented and tested:** pipes → `Apply`;
  `? :`/`&&`/`||`/`!` → `Match`; `??` → null-arm `Match` (scrutinee once); `~a||b`
  / `~a&&b` → falsy-set selection matches; `!~x` → falsy Boolean match; hasks →
  `Lambda` over holes; alternation → arm expansion; pins → equality guard; block
  bodies → scrutinee-less `Match`; compound/path mutation → `Write` of a
  functional update; arrows → pure `Lambda` over the argument-tuple pattern (the
  arity model). The `?? vs ~||` false distinction is verified structurally (2 arms
  vs 3).
- **Chosen — output is *pre-canonicalization* kernel AST:** `Ref`s carry
  `BindingRef::Name` and `Write` carries `SlotRef::Name` (added this step). Name →
  positional/location/μ resolution and de-Bruijn canonicalization are §5/analyzer
  work, deliberately not done here — desugar is purely syntactic.
- **Chosen — synthetic names use a `%` prefix** (e.g. `%h0`, `%pin1`, `%hrest0`),
  which no surface identifier can contain (identifiers are `_`/`$`-free
  alphanumerics), so generated bindings never collide with user names.
- **Chosen — hask holes collected on the fly** via a scope stack rather than a
  separate rewrite pass: a `#` pushes a scope, holes register synthetic params,
  popping builds the parameter tuple. Nested `#` opens a fresh scope (E4). v0.1
  supports all-anon, all-indexed, and single-rest shapes.
- **Deferred with a clear `DesugarError` (not silently guessed):** mixing plain
  `_` and indexed `_n` holes; index/slice *mutation* targets (field-path updates
  are done); nested pins and nested alternation; `@computed`/`@reactive` and
  anonymous `@` forms (the fenced reactive layer, G1). Each returns a specific
  error message. These are the honest v0.1 boundaries; none is a semantic
  invention.
- **`// [ask-author]`:** none. Every deferral is either a fenced subsystem or a
  syntactic corner that errors cleanly rather than guessing.

---

## 2026-07-18 — Build-order step 2b: surface parser

`src/parse/` (`surface.rs`, `parser.rs`, `mod.rs`, `tests.rs`). Grammar §§2–5.
30 seed tests green (E2 worked parses + §10); full suite 56; clippy clean.

- **Chosen — two-stage pipeline (surface AST then desugar):** the parser emits a
  faithful *surface* AST that keeps all sugar; lowering to the kernel form is a
  separate pass (2c). The kernel spec calls the desugar catalog "closed and
  normative", so keeping it a standalone, separately-tested pass is the right
  seam. The analyzer still never sees sugar.
- **Mandated (§3 ladder):** full precedence ladder as recursive descent, with the
  settled associativities — pipes `|>` left / `<|` right with the **unparenthesized
  mixing ban** (parse error); `**` right-assoc admitting unary on the right
  (`-x ** 2 ≡ -(x ** 2)`, `2 ** -3` legal); ternary right-assoc; `??`/`||` shared
  tier; unary `-`/`!`/`~` stacking. Hasks as loose prefix (tier 4) with the
  grouped `#(...)` primary for below-tier positions.
- **Mandated (§8):** brace rule (record vs block by first token) applied at arrow
  bodies, with the `@`-arrow forced-Block exception threaded via a parser flag.
  `x => {}` is the empty record.
- **Chosen — statement separation by greedy termination, not line pre-splitting:**
  the parser consumes each statement as far as the grammar allows (the documented
  greedy-continuation behavior), then the next statement begins naturally. Strict
  L1/L2 line *enforcement* (rejecting two statements on one line) is deferred to a
  later diagnostic pass; token lines are preserved for it.
- **Chosen — arrow `=>` must be on the same line as its params.** This is the one
  place L2 is load-bearing for *correctness*, not just diagnostics: without it,
  `x = n` ⏎ `=> x` inside a block greedily reads `n => x` as an arrow and swallows
  the else-arm exit. Requiring the `=>` to sit with its params (bare ident, or the
  matching `)`) resolves it. A `=>` opening a fresh line is a block-body arm.
  Flag: this rejects the unusual `(a, b)` ⏎ `=> body` split-arrow; confirm that's
  acceptable.
- **Chosen — binding/mutation/expression disambiguation** via the statement-only
  operators `=` and `:=`/compounds (which never appear in the expression grammar):
  try a bind target then `=`; else a path then a mutation op; else an expression.
  Save/restore on the token index makes the attempts cheap.
- **Chosen — contextual keywords** (`module`/`import`/`export`/`from`/`when`/
  `where`) committed by seat shape; `import` in particular only commits when a `{`
  or a name follows. A variable literally named after a contextual word in an
  ambiguous head position is a known unsupported edge — flag if it matters.
- **Chosen — pattern classification at parse time (§4/§8):** `true`/`false`/`null`
  → prelude-constant patterns; capitalized identifier → contract pattern; else a
  fresh binding. Alternation `|` and pins `^` parsed structurally (they desugar in
  2c).
- **`// [ask-author]`:** none blocking. The two "flag" items (split-arrow across
  lines; contextual-word-as-variable in head position) are the only confirmations.

---

## 2026-07-17 — Build-order step 2a: lexer

`src/lex/` (`token.rs`, `lexer.rs`, `tests.rs`). Grammar spec §1. 14 seed tests
green; full suite 27; clippy clean.

- **Mandated (§1.4 / §4 desugar):** literals resolved at lex time — `Number`
  carries an exact `Rational`, `Str` carries UTF-16, escapes processed. Numeric
  bans implemented: no BigInt `n` suffix, no legacy octal / leading zeros, no
  trailing-dot. Bases `0x`/`0o`/`0b`, exponents, `_` separators.
- **Mandated (§1.1):** no newline tokens; each token records its line so the
  parser can enforce L1/L2. Maximal munch with T1 (`?.` not before a digit — the
  `a ?.5 : b` seed), T2 (`...` beats `.`), T3 (compound mutation ops are single
  tokens).
- **Chosen — leading-dot number disambiguation:** `.5` is a number unless the
  previous token can end a postfix target (ident/`)`/`]`/`}`/number/string/
  hole), in which case `.` is member access. Tracks one token of history.
- **Chosen — trailing-dot ban scope:** `5.` erroring is required; refined so
  `5.foo` lexes as `5 . foo` (member access) and only a *dangling* dot (before
  whitespace/operator/EOF) errors. Numbers having no fields is left to the
  analyzer, not pre-judged by the lexer. Flag if the author wants `5.<ident>` to
  also be a lexical error.
- **Chosen — templates:** interpolations are captured as *pre-lexed* token
  sub-streams (`TemplateElem::Interp(Vec<Token>)`); the parser parses each as an
  Expression. Brace-depth is handled by reusing the main token loop (nested
  string/record braces are consumed as whole tokens, so a `}` inside a nested
  literal never closes the interpolation).
- **Chosen — string escape set:** the JS-standard set (`\n \t \r \0 \b \f \v \\
  \" \'`), `\xHH`, `\uXXXX` (one UTF-16 unit, surrogate halves allowed), `\u{…}`
  (astral → surrogate pair); templates add `` \` `` and `\${`. Matches §1.5's
  "JS standard set plus `\u{…}`".
- **Chosen — identifier classes:** std `is_alphabetic`/`is_alphanumeric` as an
  approximation of Unicode XID_Start/XID_Continue, excluding `_` and `$` per
  §1.3 (so `_`-holes and `$`-interpolation never collide). A `unicode-ident`
  dependency would make this exact; deferred as not worth a dep at v0.1. Flag if
  strict XID conformance is wanted.
- **Minor — `_0`:** grammar says indexed holes are `_n`, n ≥ 1. `_0` currently
  lexes as `IndexedHole(0)`; rejecting n = 0 is left to the parser/analyzer.
- **`// [ask-author]`:** none blocking. The two "flag if…" items above (strict
  XID; `5.<ident>` strictness) are the only choices worth a confirmation.

---

## 2026-07-17 — Build-order step 1: repo + value layer

### Preconditions
- All four normative documents present and read: design compendium v1.0,
  grammar spec v0.1 (added by the author this session), kernel AST spec v0.1,
  semantics companion v0.1. The grammar spec was initially missing; once added,
  its own closing line ("`cargo init` is ungated") plus Part I §365 confirmed the
  gate is open.
- **Chosen — toolchain:** no Rust was installed on the machine. Installed via
  `rustup` (author-approved) → stable `1.97.1`. Pinned in `rust-toolchain.toml`
  for reproducible conformance runs (the oracle is the truth source).

### Dependencies (Cargo.toml)
- **Mandated (Part I step-0):** `num-rational` `BigRational`; fixed-precision
  decimal crates rejected. Added `num-bigint`, `num-integer`, `num-traits`.
- **Chosen — `num-bigint = "0.4"`:** `cargo add` first resolved 0.5.1, which put
  *two* `BigInt` types in the tree (0.5 direct vs the 0.4 that `num-rational`'s
  `BigRational = Ratio<BigInt>` uses). Pinned our direct dep to 0.4 so there is
  one `BigInt`. Not a semantic decision; a tree-hygiene fix.
- **Mandated + Chosen — `unicode-segmentation = "=1.13.3"`:** grapheme ops must
  pin the Unicode table version (CLAUDE.md step 3 / semantics §3 E8). Pinned
  *exactly*. Not yet used (grapheme string ops are step 3); declared now so the
  version is fixed from the start.

### Value layer (`src/rational.rs`, `src/value.rs`, `src/interner.rs`)
- **Mandated (B1):** immutable, eagerly interned values; `==` is pointer
  comparison for every type; locations are not values.
  - **Chosen — hash-consing representation:** `ValueRef = Rc<ValueData>` with
    pointer-based `Hash`/`Eq`; `ValueData` derives structural `Hash`/`Eq`. Because
    children are already canonical, comparing children by pointer *is* structural
    comparison, so the derived key is exact. The interner is
    `HashMap<ValueData, ValueRef>`. This is a standard hash-cons; the compendium
    names the semantics (pointer equality), not the mechanism.
- **Mandated (B2):** exact rationals; decimal-iff-terminating printing. B2's
  printing predicate ("reduced denominator's primes ⊆ {2,5}") implemented exactly
  via `power_of_ten_factors`; scaling to `10^max(twos,fives)` yields no spurious
  trailing zeros (proof sketch in code comment). Flagship seed `0.1+0.2==0.3`
  green.
  - **Chosen — integer rendering:** an integer rational (`denom == 1`) prints with
    no decimal point (`3`, not `3.0`). B2 gives round-trip examples for fractions
    but is silent on the integer spelling; `3` is the natural canonical form and
    the grammar bans the trailing-dot `3.` form anyway. Low-risk; flag if the
    print doctrine later says otherwise.
  - **Chosen — `Rational::from_decimal` helper:** a value-layer convenience/B2
    demonstrator (handles sign, leading-dot, exponent, `_` separators). The lexer
    (step 2) owns *real* literal diagnostics; this is not that.
- **Mandated (semantics §1):** value kinds Boolean, Null, Number, String (UTF-16
  storage), Tuple, Record, Function, Indeterminate(form). All present.
  - **Chosen — record canonical form:** fields stored sorted by UTF-16 key, keys
    unique. Record field order is not observable (structural `==`), so `{a,b}` and
    `{b,a}` intern equal. Construction applies later-wins on duplicate keys (E5
    RecordCons); literal-literal duplicate rejection is an upstream (parser)
    concern, not enforced here.
  - **Chosen — `Indeterminate` forms:** modeled the two the semantics names
    (`_/0`, `0/0`) as an enum. Interned like any value (§3: a plain value, not a
    trap).
  - **Deferred — `FunctionValue` captures:** type defined as `(lambda, capture
    map)` with captures = value / μ-marker / location per semantics §1, but left
    empty; function *construction* and capture resolution are the oracle's job
    (step 3). Consequently the `y = [() => y]` / `z = [() => z]` interning seed is
    **deferred to step 3** — it needs μ-markers and evaluation, which do not exist
    yet. Recorded so the seed is not forgotten.

### Kernel AST (`src/ast.rs`)
- **Mandated (kernel AST spec §§1–3):** full node inventory — expressions,
  declarations/module structure, patterns — with **no source spans** (B4 side
  table) and every node deriving `Hash`/`Eq` so kernel forms intern (§5). Types
  only this pass; no evaluation, no desugaring, no canonicalization yet.
  - **Chosen — `BindingRef { Name | Positional }`:** the spec says canonical
    bodies replace immutable-binding names with positional (de-Bruijn) refs (§5),
    but the parser emits names first. Modeled both lifecycle forms in one enum;
    the normalizer (§5) will rewrite `Name → Positional`. Faithful to the spec's
    stated canonicalization, not an invented representation.
  - **Chosen — pattern rests encoded inline** as `PatElem`/`PatField` variants
    (rather than a separate `rest?` field) so a tuple's *middle* rest keeps its
    position. The "one rest per level" invariant is an analyzer/parser check, not
    a type-level constraint.
  - **Followed — extension points omitted:** reactive-fence act kinds
    (`@reactive`, `@computed`) and other §7 parked forms are deliberately absent;
    `ActKind` is `{Pure, Mutator, Effect}` only.

### Open items carried forward (implement as stated; do not resolve)
- Mutator returns = return-nothing (current law); returns-leaning is an extension
  point.
- Open-value group identity: strict-openness-with-statement-group-windows
  (semantics §7) — to be isolated behind one module when the oracle lands.
- Module in a value seat: unimplemented → clear error (later).
- Template interpolation of non-printable structures: trap (later).

### `// [ask-author]`
None this pass. No unavoidable judgment calls beyond the tagged representation
choices above, all of which the specs already sanction.

### State
`cargo test` green (13 tests): exactness flagship, B2 printing (terminating /
non-terminating / integer / negative / round-trip), interning pointer-equality
(leaves, nested tuples, record order-independence, later-wins). `cargo clippy`
clean.
