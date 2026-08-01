# NEXT — Late Resolution v0.5: Demand-Triggered, Dependency-Complete Judgment

**2026-07-27. Supersedes v0.4 (on disk as history). Status: DESIGN-CLOSED — final confirmatory round
(round 5) returned ACCEPTED with one optional wording nit, applied in place below; author stamp 2026-07-27.
Serves as the architectural gate for Investigation 2.** The confirmatory round found the core law sound and one remaining
over-integration: v0.4 collapsed **four distinct layers** — the judgment's semantic proposition key, its
proof dependencies, the cache/trust namespaces, and the verdict's reuse scope — into one "semantic identity."
v0.5 separates them, matching C§13.2a/C§13.4/C§16, which already keep these layers apart (fact keys exclude
proof closures; certificates carry provenance; "a sound proof stays semantically true forever" while prover
trust is versioned separately). Three smaller fixes: demand origin precedes resolvability; formation may
contain nested behavioural obligations; the relational entry reclassified as a boundary example. Patch
1.0.9's policy status remains carried (§3, §4, C7).

Provenance: the law's substance and anchoring dissolutions **[user]**; systematization assistant work
product; corrections **[reviewer-1..4]**.

---

## 1. The law

> **Demand-triggered, dependency-complete judgment.** A behavioural judgment is produced only for a
> source-authored seat or assertion, or a compiler proof obligation mandated by a fixed language rule. Every
> demand has a **named origin and a judgment class**; it may be **resolved** only once its complete semantic
> key can be constructed. The judgment is resolved under a **semantic key containing every parameter on
> which the truth of the judgment depends** — the relevant analysis instance, the input/row domain, the
> demanded contract, correlated operand alternatives, and the seat context (act world; expecting/statement
> position), as relevant to the judgment class — interpreted within the current **compiler-semantics
> namespace**. Stable preparatory artifacts may be formed whenever their own inputs are complete; resolved
> judgments may themselves be materialised and cached. **A cached result is reusable only under the matching
> proof-kernel trust namespace, with sufficient certificate provenance, and within the verdict class's
> permitted reuse scope.** No preparatory artifact and no cached judgment may claim a verdict whose semantic
> key omits a dependency. Uncertainty produces the judgment class's third-voice outcome under that class's
> verdict policy; it never authorizes exclusion or invented evidence.
>
> The law is **neutral on correctly keyed optional precision artifacts** — such as a bounded, branch-local,
> non-value-borne held relation. Their adoption is a separate complexity/precision decision, not a
> consequence of this law in either direction.

Clarifications:

1. **"Late" names a dependency location, not a time.** Too early is a declaration-time answer missing
   call/capture facts. The two directions of the grain rule differ in status [reviewer-2]: **dependency
   completeness is the soundness law**; the **coarsest reusable complete key** is cache discipline
   [terminology, reviewer-4] — recomputing with complete facts is waste, not unsoundness.
2. **A user assertion originates a demand where it is written — and resolves at its complete key**
   [reviewer-3, tightened reviewer-4]. A `where` assertion originates at the declaration seat, carrying its
   origin, class, and the *recipe* for its dependencies; it is resolved for the asserted analysis instance
   once that instance's capture-dependent identity is complete, under `DeclaredInput` (`BodySafe(instance,
   DeclaredInput)`, E-8/E-11). Origin of the question and grain of the answer are different things. `conform`
   is different [reviewer-1]: an ordinary **boundary-operation seat** producing a shaped value or `Failure`.
3. **The compulsory checks are demands.** Operation safety firing on arrival (C§7 — even when the result is
   unused), exhaustiveness, act-world admission, completion: fixed-rule compiler obligations with named
   origin and class. What the definition excludes is the uninvited universal question.
4. **What the law forbids is precisely the dependency-incomplete verdict.** It forbids neither preparation
   nor the caching of answers.

## 2. The four identity layers [restructured, reviewer-4]

Kept distinct, as C§13.2a/C§13.4/C§16 already keep them:

**Layer 1 — the semantic proposition key.** *What is being claimed*: `BodySafe(instance, DeclaredInput)`;
`ReturnFact(instance, row-set I, demanded C)`; `Subcontract(A, B)`; `ApplicationAdmission(jointOperands,
actWorld)`; `Completion(core, expectingContext)`. The key contains the parameters whose values can change
the proposition's truth. This is the layer governed by *dependency completeness is soundness*.

**Layer 2 — proof dependencies and certificate provenance.** Supporting facts, fact-graph edges, SCC
hypothesis vectors, environment/domain bindings, concrete witnesses. These **establish** a judgment under
its key; they are **not** parameters of the proposition — `ReturnFact(instance, I, C)` is the same theorem
whether proved through facts A+B or fact D. C§13.2a represents them as graph edges; C§16 carries them in
certificates — precisely so fact keys never absorb their proof closure. Where a particular judgment
genuinely has an assumed fact as a semantic premise, that premise is explicit in *its* key —
judgment-specific, never a universal rule.

**Layer 3 — the two namespaces.** The **compiler-semantics namespace** fixes what the language and contract
rules *mean*: the semantic key is interpreted within it. The **proof-kernel namespace** governs *trust* in
cached certificates: a kernel change does not change `A ⊑ B` as a proposition — it invalidates confidence in
an earlier prover's answer ("a sound proof stays semantically true forever, but a buggy prover may have
minted an invalid 'proven'" — C§13.4's own rationale). One implementation namespace, two conceptual roles.

**Layer 4 — verdict reuse scope.** *How long the result may be reused*, set by verdict class: proven/refuted
permanent in-namespace; subcontract-unproven rule-set-versioned; fact-unproven per-compilation. The same
proposition carries different reuse policies for different verdict classes — lifetime is cache validity,
never identity.

**The invariant** (this law's cache clause, and C§13.4's): every cached judgment has a dependency-complete
semantic key, matching compiler-semantics and proof-kernel namespaces, sufficient certificate provenance,
and a verdict-class-correct reuse scope — "every entry a fact or an appropriately-scoped shrug."

**The two mistakes the separation prevents** [reviewer-4]: *exploding fact keys* (absorbing supporting
facts, hypothesis vectors, and certificate detail into keys — destroying canonical fact identity and SCC
reuse) and *treating proof validity as theorem semantics* (describing a kernel update as changing what the
language means rather than which answers are trusted).

## 3. Obligations and products [reviewer-2]

**Formation obligations** — establish identity, canonical representation, or well-formedness: value and
contract canonicalisation and interning; recursive-contract admissibility; symbolic-template construction;
fixed candidate-inventory construction. Run when their own formation inputs are complete — eager where
identity or well-formedness requires it (Principle 5). **A formation procedure may generate subordinate
behavioural proof obligations** [reviewer-4] — recursive-contract admissibility requires the tuple family's
permanently proven minimum-length fact for a guarding sibling segment (C§9) — each governed by its own rules;
the top-level question remains formation.

**Behavioural judgment obligations** — answer demanded questions about behaviour: operation safety; call
admission; row selection for an input; grounding over a domain; `Numeric` discharge at a strict seat;
completion; a subcontract demanded by a seat. Require a demand and a dependency-complete key.

**Materialised products — orthogonal to both.** The result of either obligation may be stored once its
complete identity is known: templates and instance tables (formation products); EvaluationCores
(analysis-result products at their deliberately seat-independent key); **subcontract verdicts, proven return
facts, and certificates — cached judgments**. C§13.4 deliberately contains all three flavors under the §2
invariant.

Every **direct ledger instance** in §7 is a dependency-sensitive judgment **or artifact** placed at a
coarser grain than its dependencies [wording per the final confirmatory round]; the boundary example and
analogous entries are labelled as what they are.

## 4. Preconditions, classified [reviewer-1]

**Semantic requirements:** complete and sound dependency visibility at the judgment grain; every semantic
dependency explicit in analysis state — **hidden or unmodelled effects/state force earlier summaries or
conservative boundaries** [reviewer-3]; NEXT's explicit world/state model (act worlds, snapshot-relative
reads, pending write-sets, `Union(T, Failure)` effect results) keeps admitted dependencies visible, so
Mutator and Effect bodies remain analyzable; advance-bounded, provably terminating resolution (C§13.3); a
sound per-class fallback policy.

**NEXT's realizations and enablers:** Transparent modularity (the visibility choice — opaque boundaries would
reintroduce summaries *as boundary formation artifacts*); the template/instance split (the grain law realized
for captures); contracts-as-sets with three-voiced verdicts; canonical identity and interning; pure guards
and snapshot-relative expression purity (the strong special case of explicit state).

**Narrow policy:** Principle 9's gray — **grounding only**, and itself **under revision per 1.0.9** (leaning
rejection; current law in force until stamped).

**The retained diagnosis, at demonstrated scope:** many architectures force earlier summaries — separate
compilation hides source, hidden effects destabilize later answers, opacity hides dependencies. Imported
solutions carry that forcing as an invisible assumption; within NEXT's transparent boundary, a judgment seat
can recover its admitted dependencies.

## 5. Verdict policy is per judgment class [reviewer-1]

- **Safety-unproven → compile error.** Un-suppressible [user, 2026-07-17]; the Mutators-cannot-fail theorem
  stands on exactly this.
- **Grounding-unproven → per Principle 9.** Current law: warned gray region compiles. **Status 1.0.9:** under
  revision, heavily leaning toward rejection (divergence reframed [user]: not a runtime *error* but a *bug* —
  a stuck program). Either outcome moves only the seat consequence; the verdict vocabulary is untouched.
- **Precision-unproven → conservative widening.** Uncertainty selects, never deselects.
- **Refutation → only with jointly-represented, realizable witnesses.** Evidence is never invented; the
  product proves absence, never presence.

Lateness does *not* mean compilation always proceeds: an unproven safety judgment at a call blocks, rightly.
What lateness guarantees is that the judgment was made with its dependencies present.

## 6. Grain examples, and costs

Semantic keys (all interpreted within the compiler-semantics namespace; reuse per Layer 4):

- shape template ↦ **shape**
- instantiated region table + per-row certificates ↦ **(shape, annotated capture tuple)**
- proven return fact ↦ **(analysis instance, row-set I, demanded C)**
- EvaluationCore ↦ **(interned canonical expression, annotated free-variable tuple)** — deliberately
  seat/world-independent
- final call judgment ↦ **core + seat world + expecting/statement context** — admission and completion
  judged at each seat, never cached into the core

**Costs, stated honestly.** *Error locality:* a flawed body surfaces at a call, possibly far from the flaw —
mitigated by `where` (a deliberate early demand, resolving at its complete key) and by
once-per-unique-judgment-key computation. *Work distribution:* analysis cost lands at judgment grains;
C§13.4's caches are the accounting. *Whole-program character:* the law leans on dependency visibility,
currently provided by Transparent modularity, with the boundary-summary consequence named in §4. *Universal
questions remain askable* — as assertions; the analyzer never asks them uninvited.

## 7. The ledger [restructured, reviewer-4]

**Direct dissolutions** — a dependency-sensitive judgment or artifact was placed at a coarser grain than
its dependencies [heading per the final confirmatory round — entry 3 is the artifact-grain case]:

1. **The accepted-domain reification chain**: the stored universal object (`InferredAcceptedDomain`) → the
   empty-domain question asked of the reified object → the consumer-spec phantom minted for it — one causal
   chain, dissolved whole by ordinary demand-triggered body checking at the call (Appendix M, 2026-07-24).
2. **The region-table arc (central specimen):** v0.1 pre-computed exclusion by subtracting a *may*-region —
   an approximation turned into exclusion before exactness and the actual remaining domain existed; the fix
   moved first-match to the ordered walk, where both are present.
3. **Capture-dependent regionalization** — instance-keyed, never shape-keyed (C§12.3's three layers).

**Direct application under investigation:**

4. **Per-call grounding [user] — direction settled, mechanism pending** [reviewer-2]. Settled: grounding is
   demanded for the actual call domain, never universally inferred uninvited; basins as derived contracts and
   partial basins are the settled direction. Pending: the procedure — basin derivation, step floors, orbit
   refutation, fact and cache identities — is Investigation 2's owed derivation.

**Boundary example** [reclassified, reviewer-4] — what the law forbids and what it leaves open:

5. **The relational guard**: the relation remains part of the guard's **runtime semantics**; at the static
   test seat the analyzer derives only the fixed unary regional consequences its rule inventory supports —
   an unsupported relation projects to the conservative floor (`Top`, non-exact; the non-singleton pin) and
   is **not reified into a coarser or global contract or verdict**. The [permanent] exclusion of relational
   *contracts* from the algebra stands; a correctly keyed, bounded, branch-local, non-value-borne suspension
   would *satisfy* this law and remains a **[parked]** precision option (region-table arc §8) — a complexity
   ruling, not a theorem of late resolution.

**Analogous corrections** — same spirit, different primary driver [reviewer-1]: late binding/letrec
(formation-timing); tier-0's death (§12.2 and Principle 7 are the killing law; demand locality assisted); the
structural/arithmetic measure unification (algebra design — peeling *is* constant drift on a length whose
contract is intrinsically `GE(0) ∧ Mod(1,0)`).

Three direct dissolutions, one direct application under investigation, one boundary example, and three
analogies are the demonstrated scope; some corrections also rest on canonicalization, termination, or
algebra design.

## 8. The checklist (v0.5)

**C1 — Formation obligation or behavioural judgment obligation?** Identity, canonical form, admissibility,
template/inventory construction → apply the formation law to the top-level question; **enumerate any
subordinate behavioural proof obligations separately** [reviewer-4], each under its own rules. Behaviour
under input/demand/seat → judgment; continue. Materialisation is orthogonal — either result may be cached at
its complete identity.

**C2 — Name the demand.** A source-authored seat/assertion, or a fixed-rule compiler obligation — named
origin and judgment class at creation; **resolution only once the complete semantic key can be constructed**
[reviewer-4]. No demand → a formation obligation, or an imported universal question; find which before
proceeding.

**C3 — Enumerate every semantic dependency of the proposition.** Shape/instance; annotated captures; joint
correlated operands; input/row domain; demanded contract; path narrowing; act world; expecting/statement
context. **Supporting facts are proof dependencies (Layer 2), not key parameters — unless a specific
judgment makes a premise semantic, explicitly.**

**C4 — State the complete semantic key; then choose the coarsest reusable one.** Key completeness is the
soundness requirement; the coarsest reusable complete key is cache discipline. Reuse additionally requires
the matching namespaces, certificate provenance, and the verdict class's reuse scope (§2's invariant).

**C5 — Resolve with the existing inventory.** Operation transfer, region table, ordered remainder walk,
subcontract, fact graph, backward demand propagation, canonicalization, the witness discipline. A new
mechanism must be argued against the inventory ("fixes delete or reuse") and the categorical prohibitions:
§12.2 no-evaluation-as-grounding; no budgets or effort-dependent search; no relational contracts in the
algebra; no parametric facts (withdrawn 2.6.1).

**C6 — Exhibit the advance bound** (13.3(1)). None → no proof; the class's conservative result applies.

**C7 — Apply the class's verdict policy** (§5): grounding-unproven per Principle 9's current status [1.0.9];
safety-unproven blocks; precision-unproven widens; refutation only with realizable witnesses.

**C8 — Import red flags** — stop and re-derive when a proposal: stores a behavioural verdict before all its
dependencies exist; asks an unrequested universal behavioural question; **turns an approximation into
exclusion** (an *exact* complement is legal); bakes call/seat priority into a coarser artifact; introduces
effort-dependent search or fuel; pleads "before it's too late" without naming the dependency that
disappears; creates distinctions the semantic model doesn't have.

## 9. Grounding: a compatibility sketch, not a discharge [reviewer-1]

The grounding capability is architecturally **compatible** with this law: the demand is a call's
grounding/return-fact request; the candidate proposition key is (instance, input/row domain, demanded
contract); the candidate mappings to existing machinery are — base ↦ the non-recursing region-table rows;
drift ↦ the transfer-rule shift between the recursive argument's contract and the parameter's; basin ↦
backward demand propagation (the −4-trap move); step floor ↦ a derived bound from call facts (D-2); orbit
refutation ↦ a fact-graph SCC with all-forced edges and no base transition.

**These are candidate mappings.** Investigation 2 must derive the exact fact identities, transition rules,
witness conditions, advance bounds, and the cache identity per §2's four layers. The lexicographic
certificate (D-1(e)) is the **currently identified** mechanism gap [reviewer-2]; the derivation may expose
further gaps.

## 10. Standing note

Thread A remains reclassified by §3's line: open-value observation legality is a **formation-timing**
question — "is this value formed yet?" — so pre-internable static groups are a legitimate formation-timing
option, not an eager-judgment import. The lens changes which arguments are admissible, not the ruling.

---

*v0.5 — five rounds (1–4 + final confirmatory ACCEPTED); the 1.0.9 policy status carried in §4, §5, C7.
DESIGN-CLOSED, author stamp 2026-07-27. The architectural gate for Investigation 2.*
