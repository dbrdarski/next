> ## 📗 STATUS: **HISTORICAL** — record of a past review/audit; not current guidance
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Left unedited.

# Spec-first audit — accepted domains, the region table, and the skipped build step

**Phase 1 deliverable.** No code was written for this document. It answers the
architecture review's §13 questions from the normative texts, works its §14 examples,
and separates *what the specifications settle* from *what they leave owed*.

**Headline.** The missing mechanism is **larger and more precisely specified** than
"body-derived accepted domains". The documents describe a three-layer substrate —
**symbolic summary template (per shape) → instantiated region table (per instance) →
call-site input obligation** — which is the **`demand core + template/instance split`**
step of Part I's build order. That step was skipped, and C§13.2's *consumers* (analysis
instances, return facts, the induction) were built on top of the hole. Every mechanism
the last five rounds added was reconstructing that substrate forward, at call sites, one
counterexample at a time.

---

## 1. The architecture is specified, and it is not what I built

**C§13.2, opening sentence — the whole design in one line:**

> **One symbolic control summary per lambda shape; instantiated regional analyses
> parameterized by captured-environment contracts.**

**C§13.2, the call-site procedure:**

> A call site resolves its callee to an analysis instance (shape + environment contracts
> — exact for const closures, contract-level for factory products like
> `makeAdder(someInput)`), **obtains the instantiated region table**, **checks the input
> obligation at full precision**, selects **every row whose intersection with the
> argument is not proven empty**, and contract-evaluates the selected rows' result
> expressions over the argument tuple, memoized.

Note what this does **not** say: *analyze the callee's body*. It says **obtain** the
instantiated region table — a per-instance artifact, computed once and cached — and
consult it.

**C§13.4 makes the caching explicit:**

> **Template cache** (function shape → symbolic summary template); **Instance cache**
> ((shape, **annotated** captured-environment contract tuple) → instantiated region table
> + per-row grounding certificates)

**C§18 says when it lands:**

> the template/instance split enters **with the demand core** (const closures make shape
> and instance coincide, so the kernel pays no complexity until factories appear)

**Part I, build order (CLAUDE.md: "do not reorder"):**

> … contracts + three-valued checker → **demand core + additive recursion** → the
> re-entry ladder

**Measured state of the implementation:** no demand core exists (`src/` has no demand
module; no backward/subscription/preimage machinery). No symbolic summary template
exists. No region table exists. `analyze_apply` instead re-derives body information per
call site, which is why it needed instance identity, domain identity, widening, evidence
downgrades, and an advance-bounded domain universe — none of which the specified
architecture requires, because in it **a body is analyzed once per instance, never per
call**.

---

## 2. The review's eight questions, answered from the texts

### Q1 — What exactly is `InferredAcceptedDomain`?

**Settled.** The set of argument tuples for which the body's derived demands are
satisfied.

- **E11:** *"**DeclaredInput ⊑ InferredAcceptedDomain** (the declared input satisfies
  **every demand the body derives**; it may be stricter — C§12.1's split variance)"*
- **C§12.1:** *"Input preconditions may be stricter than **the body's domain**; return
  postconditions must contain all outputs."*
- **E3:** *"**body-derived domain** — uses of the rest tuple narrow accepted lengths
  (`first = (...values) => values[0]` rejects `first()`)"*

It is a **derived** object. `where` never declares it — `where` is *"a verified assertion
about inference, never trusted, never a mode"* (E11). Enforcement is not `where`'s job:
*"body `when` (and the parked require-form) change the domain itself, where only
documents-and-verifies"*.

### Q2 — When is it computed?

**Settled: once per instance, not per call site.** C§12.3's three identity layers:

> (2) **Function shape** = canonical lambda body + μ-structure … keys the **symbolic
> summary template** — control normalization with captured names held symbolic (guards
> mentioning captured names — `n <= limit` — cannot finish normalizing until the capture
> is known). (3) **Analysis instance** = shape + annotated captured-environment contract
> tuple … keys every instantiated analysis product: **the instantiated region table** …,
> grounding certificates …, proven return facts, and fact-graph nodes.

So: symbolic once per **shape**; instantiated once per **instance**; consulted at every
call. Both layers are cached (C§13.4).

### Q3 — What body information contributes to it?

**Settled as an inventory** — C§5, *Where Contracts Come From*:

> Literals and const bindings …; **pattern matches (wildcard is the accumulated
> Difference)**; `when`/`where`; **operations**; returns; **call demands**; **predicates
> branched on**; box-binding references contribute the location's content contract.
> **[permanent]** Relations between values are outside the algebra.

So: each operation's C§7 safety demand, gathered **path-sensitively** (the match
remainder is the path condition), plus demands from nested calls, plus `when` guards.
The `[permanent]` line is a real boundary: a requirement relating two inputs to each
other (`x < y`) is outside the algebra and cannot enter the domain.

### Q4 — How do body operation requirements become input-domain constraints?

**This is the one genuinely under-determined point, and it needs a ruling.**

**C§13.1 — The Model:**

> Demands propagate **backward untransformed as subscriptions**; resolution is forward
> through the operation rules (each carrying its C§7 safety verdict); **adjudication
> where the demand was asked**, three-valued. Two-variable operations are ordinary nodes.
> **Eager preimage transformation is an optimization** (short-circuiting; origin-phrased
> diagnostics). No stall concept.

Read literally, the *base* model never materializes an accepted domain: a demand is a
subscription that sits at its origin and is adjudicated there once the operand's contract
arrives forward from the call. Turning *"`x + 1` demands Number of `x`"* into *"the
accepted domain is `Number`"* **is** the preimage transformation — which C§13.1 calls an
**optimization**.

But E11 requires `DeclaredInput ⊑ InferredAcceptedDomain` — a subcontract test between
two contracts — so the domain must be **materializable as a contract** at least wherever
a `where` is present. And E3's `first()` rejection reads as a domain the callee owns,
not as a per-call adjudication.

> **Q for the author:** is `InferredAcceptedDomain` (a) the **eagerly preimaged** object —
> materialized once per instance, a real contract, the thing call sites test against — or
> (b) the **subscription set**, with the domain materialized only where a `where` demands
> it? Both yield the same verdicts; they differ in where the work lives, whether the
> domain is nameable in diagnostics, and how much of C§13.1's "optimization" is actually
> mandatory. The region table (Q2) reads like (a).

### Q5 — How do captures parameterize it?

**Settled: the accepted domain is instance-level, not shape-level.** C§12.3 again:

> the instantiated region table (`Equals(v)` captures **substitute as constants** —
> constant-parameter extraction at the summary level; **non-singleton captures may leave
> a guard relational between two non-singletons → opaque, handled conservatively per the
> regionalization law**)

This independently confirms the review's §8–§9: `make(1)` and `make("s")` are different
instances with different accepted domains. It also names the degradation rule — a
relational guard between two non-singleton captures goes **opaque**, handled
conservatively, rather than being solved.

### Q6 — How does recursion participate?

**Two distinct mechanisms, both specified in outline.**

1. **Return facts** — C§13.2: *"Recursive references never unfold; they resolve through
   **proven return facts**"*, settled by C§13.2a's SCC vector induction. **This part is
   built** (and its instance+domain identity is the Archive4/5 correction, which stands).
2. **The derived input contract** — this is **grounding** (C§10), not operation demands.
   The Phase-A grids are explicit: factorial's *"Derived input contract:
   `Intersection(GreaterOrEqual(0), Mod(1, 0))`"*, countdown−2's `GE(0) ∧ Mod(2,0)`,
   isEven/isOdd's `GE(0) ∧ Mod(2,0)`. These come from drift/base/orbit reasoning — *"the
   orbit n, n−1, n−2, … hits 0 iff n is a non-negative integer"* — **not** from any
   operation's safety demand.

So a recursive function's accepted domain has **two independent sources**: operation
demands (Q3/Q4) *and* grounding (C§10). The A-NEG battery is the acceptance test for the
second, and **the grounding arc is not built** — which is the same conclusion I reached
earlier by a different route.

### Q7 — How does application consume it?

**Settled** — C§13.2's procedure (quoted in §1): input obligation at full precision, then
row selection by non-empty intersection, then contract-evaluate the selected rows.
Three-valued per C§13.1 (*"adjudication where the demand was asked, three-valued"*), with
the witness discipline of the application package.

### Q8 — What does an empty accepted domain mean?

**Not specified anywhere.** I searched the normative texts; nothing rules on it.

Arguments on record that bear on it:
- **For "not an error at the definition":** a definition does not execute its body; B5's
  world model is about *calls*; higher-order code may legitimately hold an uncallable
  value; and captures can make an instance uncallable while the shape is fine. This is
  the architecture review's stated preference.
- **For "error at the definition":** it is dead code containing a *proven* trap, and
  NEXT is compile-time-only with no runtime failure. E10 already has a **lint tier** for
  a related case (*"Bare pure-expression statements: legal with the goes-nowhere
  warning"*), which suggests a third option: **lint, not error**.

> **Q for the author:** empty `InferredAcceptedDomain` at a definition — error, warning
> (goes-nowhere family), or silent, with the rejection landing only at call sites?

---

## 3. The small examples, worked against the model

**14.1 `() => 1 + "x"`** — one input tuple, `()`. The `+` demand (both-Number or
both-String) is refuted on constants, referencing **no parameter**. No input avoids it ⇒
**AcceptedDomain = ∅**. Derivable at the *template* level — no captures needed, no call
site needed. This is the case that should never have required call-site machinery.

**14.2 `x => x + 1`** — `+` demands both-Number or both-String; `1` is Number, so the
String rail is dead ⇒ demand on `x` is `Number`. **AcceptedDomain = `Tuple([Number])`**.

**14.3 `x => x == 0 ? 1 : x + "x"`** — the region table, in miniature:

| row | input region | demands | result |
|---|---|---|---|
| 1 | `Equals(0)` | — | `Equals(1)` |
| 2 | `Difference(Top, Equals(0))` | `x : String` | `Kind(String)` |

**AcceptedDomain = `Equals(0) ∪ (String ∖ Equals(0))`** = `Equals(0) ∪ String`. This is
precisely why the *region table* is the right object rather than a single contract: the
domain is the union over rows of *(row region ∩ that row's satisfied demands)*, and the
same table simultaneously yields the return contract per row. One structure, computed
once, answers safety, domain, and return.

**14.4 `y => x => x + y`** — the inner shape's summary holds `y` symbolic; the instance
substitutes. `y = 1` ⇒ inner domain `Number`; `y = "s"` ⇒ inner domain `String`. Same
shape, different instances, different accepted domains — exactly C§12.3's layer-3 rule.

**14.5 recursion** — `factorial`: operation demands give `Number`; **grounding** gives
`GE(0) ∧ Mod(1,0)`; the accepted domain is their intersection. The second conjunct is
unobtainable from operation demands alone — it requires C§10.

---

## 4. What the specifications leave owed

These block a faithful implementation and need the author:

1. **Region-table computation steps — explicitly owed.** C§17's owed list literally
   contains *"region-table computation steps"*. The *concept* is normative (C§12.3,
   C§13.2, C§13.4); the *procedure* for turning a body into rows is not written. This is
   the single most load-bearing gap. Application spec §3 (*Template instantiation*) is
   the same gap seen from the other side: it **names** the ingredients — symbolic slots,
   constant extraction, regionalization, opaque relational guards, `E × A` row
   denotations, annotated env keys — without stating the procedure that produces rows.
   C§12.3 likewise invokes *"the regionalization law"* by name without stating it.
2. **Q4's eager-vs-lazy ruling** (§2 above).
3. **Q8's empty-domain semantics** (§2 above).
4. **The grounding arc (C§10)** — needed for Q6's second source and for A-NEG. Also
   listed owed in C§17 (*"§10.4's four soundness obligations"*, *"the case-6 composed
   example"*, *"mutual-recursion spec + executable examples"*).

> **Withdrawn ask (recorded, 2026-07-26).** A draft of this audit listed a fifth item —
> *"app spec v0.2 is absent from the repo; v0.8 §3 delegates template-instantiation
> detail to it"*. **That was wrong.** `MANIFEST.sha256.txt` — the canonical library —
> lists only `next-application-induction-specification-v0-8.md`, so no file is missing.
> **"As v0.2" is a changelog idiom** meaning *"unchanged since v0.2"*, used six times in
> v0.8, and where content matters it is restated in place (§5: *"As v0.2: admission
> `I ⊆ GroundedRows(instance)`; straddles partition; verification by the partition
> rule…"*; §10: *"As v0.2, plus: `GeneralizationDomains` is extraction-rule-bounded…"*).
> The header confirms the v0.2 round's changes were *"all integrated here"*. §3 is
> genuinely thin — its content is a **list of named concepts** (symbolic slots, constant
> extraction, regionalization, opaque relational guards, `E × A` row denotations,
> annotated env keys) rather than a procedure — but that thinness **is** item 1
> (region-table computation steps, owed in C§17), not a missing document. Folded into
> item 1; the ask count is four.

---

## 5. Implication for the recovery

The reviewer's estimate — *"implement body-derived accepted domains + delete a
substantial amount of call-site safety machinery"* — is right in direction, and this
audit makes it concrete:

**Build (the skipped step):** demand core (C§13.1) → symbolic summary template per shape
→ instantiated region table per instance → call-site input obligation + row selection
(C§13.2).

**Delete (subsumed):** the call-site body-safety mechanism and everything that exists
only to bound it — `instance_body_summary`'s safety role, `domain_admitted`,
`kind_abstraction`, `literal_values`, the widening/downgrade pair, `ACTIVE_BODIES`.

**Keep (independently justified, per the review's §10):** instance+domain fact identity;
the `segment_nullable` structural fix; fuel out of normative analysis; no oracle
execution of user functions; correlated-alternative work; dead-arm/path narrowing — the
last of which becomes *more* central, since region rows **are** path conditions.

**Also correct:** the existing body-safety tests are written as call-site assertions over
unconditionally-invalid bodies (`() => 1 + "x"`). Under this architecture those are
**definition-site** facts (AcceptedDomain = ∅). They pass either way, which is exactly
why they never caught the design error. They should be re-framed as domain assertions.

**Recommended order:** (1) author rules on §4's five items; (2) region table + demand
core for the **non-recursive, capture-free** fragment, with §3's 14.1–14.3 as the gate;
(3) instantiation over captures (14.4); (4) recursion, return facts already in hand
(14.5) — grounding last, as its own arc.

Nothing should be deleted until the replacement passes the behaviours the current tests
encode: `bad()` rejected, `f("hello")` rejected, `helper(0)` accepted, divergence
terminates, no user function executed during analysis.

---

*Phase 1 of the recovery agreed with the author, 2026-07-26. Phase 2 (build) and Phase 3
(delete) are gated on §4's rulings.*
