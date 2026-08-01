# NEXT — IMPLEMENTATION STATUS (AUTHORITY)

**Created 2026-07-31 (Tier-0 rebaseline). This file is the single current authority on
implementation status.** Where any other maintainer document disagrees with this file about *what
is built, what is trusted, or what to do next*, **this file wins**.

**What this file is not.** It makes **no semantic rulings**, defines no mechanism, and changes no
design. It does not rewrite history: contradictory documents keep their text and are *labelled*
below. Design authority remains entirely with the manifest-verified normative specifications (§1).

**Doc status vocabulary used here:** `CURRENT` · `HISTORICAL` (true when written; not guidance) ·
`SUPERSEDED` (contains guidance that must not be followed) · `KNOWN UNSOUND` (code that can return
a wrong verdict).

### Recovery rebaseline — 2026-08-01

Recovery starts from measured behavior, not from the last completion claim. The first code repair is
now complete: the proven-fact memo key previously recorded value captures and call inputs, but not the
named contracts that the function body reads from `ContractEnv`. The same canonical body containing a
pattern `N => ...` therefore collided under `N = String` and `N = Number`. The key now records the
complete named-contract environment as a canonical interned key argument, and both memo orders are
regression-tested. This was an **incomplete pure-memoization key**, not a mutable-cache or
cache-lifetime problem. Clearing the memo between compilations only hid the missing dependency.

The second repair is also complete under the 2026-08-01 Part XII ruling. Runtime unresolved
arithmetic is represented as `Indeterminate(DivZero(a))` or `Indeterminate(ModZero(a))`, with the
form tag and canonical Number operand together forming the interning key. Thus `1/0 != 2/0`,
`(2-1)/0 == 1/0`, and `1/0 != 1%0` by ordinary pointer equality. `Numeric` is the contract union
`Number ∪ Indeterminate` (not a `Kind`), while form-sensitive contracts retain the distinction
between `DivZero` and `ModZero`. Division and remainder transfer add only their own form when a zero
divisor is possible. `Indeterminate` and `Numeric` work as source contract patterns; `ZeroDen` has
been removed and is not an alias. Arithmetic/ordering that consumes either form traps/rejects as
undischarged until its algebra is ruled. Removing fake arithmetic propagation also exposed and
closed a fact-graph leak: an unresolved cutoff dependency can no longer be recursively proved by the
quarantined body summary or upgraded from graph-`Unproven` during diagnostic rechecking.

The third repair closes the missing executable-program demand origin. `--check` now walks module
items in source order and retains one typed record for every executable binding RHS, slot
initializer, and statement. Each record keeps its origin, expecting-vs-statement seat, evaluation
world, inferred contract, completion voice, and findings. Fixed operation-safety demands therefore
fire even when a statement discards its result, while only expecting seats demand a produced value.
Headerless entry items are checked in Effect world, named-module items in Pure world, slot
initializers in Pure world, and function bodies in the world owned by their `ActKind`; writes are
admitted only in Mutator bodies. Transfer remains symbolic and never runs the module; T2.2 adds the
narrow bounded-Pure-call exception used solely to realize a completion witness. Check mode starts
with the same inert harness values as run mode (`String`, `println`, `exit`, `readFile`), so prelude
use is resolved rather than falsely reported unbound.

The fourth repair wires ordinary application to the settled candidate graph and deletes the
quarantined recursive checker. `analyze_apply` now requires `BodySafe(instance, I) = Proven`, reads
completion from the corresponding completion fact, and uses the shape-bounded outcome projection
for produced values (with return induction for recursive results). Safety-unproven is converted to
an unsuppressible error only at the consuming seat. An outer graph settlement publishes every
proven dependency fact under its complete memo key, while diagnostic verification cannot launch a
nested graph past a shape cutoff. Outcome summarization has its own §4a active-shape sequence, so a
safe divergent recursion is analyzed coarsely and terminates rather than overflowing. The retired
`bodycheck.rs` file, module export, reaching primitives, and implementation-specific tests are gone;
the machinery gate requires them to remain absent.

The fifth repair completes T2.2's completion evidence path. A proven application fall-through now
carries the represented `(callee, arguments)` pair; Pure calls mint that evidence only when the
fuel-bounded oracle actually returns `CompletedWithoutValue`. Produced values, traps, and fuel
exhaustion mint nothing. Match carries a selected arm's whole outcome upward and the enclosing
consumer applies the completion demand, preserving the statement-vs-expecting distinction. The
completion fact uses the existing region-table partition, so exhaustive recursion such as
`countDown` keeps its narrowed recursive fact while the recursive partial-producer regression is
live and rejecting. Effect/Mutator bodies are not run to hunt for witnesses.

The sixth repair completes T2.3's application-path unification. `application.rs` now owns the one
alternative traversal, AP-29/AP-30 projection weakening, and componentwise outcome join;
`analyze_apply` analyzes operand expressions and supplies each alternative's settled safety,
completion, and return contribution. The old inline callee loop and application-specific join are
deleted, and a machinery gate forbids routing around `drive_application`. At that slice boundary the
expression environment still carried erased `Contract`s, so its bridge kept argument contracts
opaque and made no source-level correlation claim; the eighth repair below closes that obligation.

The seventh repair makes the existing `where` return demand consume the canonical three-voice
return judgment. A represented completing Pure call outside the declared return contract now
survives as `Refuted(RealizedWitness { arguments, produced })`; failure of the global abstract fact
proof without such evidence remains `Unproven`. `check_return_claim` keeps refutation first and now
uses the same domain-aware candidate graph as safety and completion, preserving recursive proof
behavior rather than falling back to its former single-candidate pass. `ProgramVerdict` retains
every checked declaration as a typed `ReturnDemand` through policy, so the two rejecting voices
receive distinct diagnostics without losing their evidence. Realized probes have an explicit
Pure-closure guard; Effect and Mutator bodies are never executed during this check.

The eighth repair carries `AnalysisContract` through the live source-expression path. `TypeEnv`,
expression outcomes, static tuple/record construction, Match alternatives, narrowing, immutable
bindings, and exact accesses now retain annotated structure and function-instance metadata. The
normative AP-29 source example therefore reaches the canonical application driver as the joint
alternatives `(numFn, 5)` and `(strFn, "hello")`, never the synthesized cross-pairs. When the
callee and arguments are immutable projections of the same correlated source binding, the access
adapter projects each source alternative as one tuple; unrelated projected sources retain the
driver's legal cross-product approximation and its unproven-only failure price. Exact aggregate
folding remains available by recovering a singleton value from annotated tuple/record structure.
The adjacent region-table bug exposed by this test is also closed: a block-shaped Match with a
preceding bind/statement remains one whole-body row, so safety/return/grounding consumers cannot
discard its executable prefix and then analyze an unbound result expression.

The ninth repair preserves safety judgments through program policy. `Analysis` now carries typed
primitive-operation and body-safety demands through every expression composition; executable demand
records retain them, and `ProgramVerdict` records every declared `BodySafe(instance, I)` check with
its instance, domain, and Proven / Refuted / Unproven verdict. Primitive refutations retain their
operand tuple, and `BodySafetyEvidence` retains nested typed demands, so wrapping an operation in a
body fact no longer discards that witness. Safety verification classifies typed evidence before
diagnostic policy, while a separate definite untyped trap still dominates an unrelated Unproven
demand. RT-14 and AP-29 weaken non-represented refutations to Unproven before policy. Unproven
diagnostics remain advisory inside the fact calculation and gain the ruled unsuppressible Error only
at the executable or declared consuming boundary.

This stricter policy exposed a prior AP-29 false accept: correlated local-projection calls were absent
from candidate discovery, their body fact remained Unproven, and the old `where` adapter emitted only
its non-blocking warnings. Discovery now reads the same annotated joint application operand as the
live analyzer and threads block-local bindings in source order. The represented `(numFn, 5)` and
`(strFn, "hello")` dependency facts are therefore genuinely discovered and proved; no policy bypass
is needed. Discovery keeps the safety-context guard active while contract-evaluating those operands,
so it does not settle nested facts during the discovery phase.

The tenth repair closes the operation-transfer half of the function-identity drift. Exact equality
transfer had compared two `Equals(function)` operands with `ValueRef` pointer equality even though
closure construction is not yet universally interned and the oracle still uses the temporary
coinductive equality path. Two extensionally equal recursive closures at different allocations
therefore made the analyzer produce exact `false` while the oracle produced `true`. Exact singleton
equality and inequality transfer now use the same oracle value-equality relation as execution. A
red-first recursive-function regression pins both `==` and `!=`; it also asserts that the two inputs
are still different pointers so the test cannot accidentally hide the outstanding construction fix.

The eleventh repair completes that construction fix and supersedes the tenth repair's temporary
bridge description. Resolved acyclic closures intern immediately by canonical code plus capture
pointers/location atoms. A late-bound acyclic closure stays `Open` until its dependency arrives.
Recursive binding SCCs receive one construction window: every member is under initialization at the
window start, provisional roots are not observable, and all internal markers resolve together at
close. Stored tuple/record children then close bottom-up; function candidates probe a shape
fingerprint bucket and Algorithm B verifies an exact graph match before reuse. Redirected provisional
handles are normalized at every compound constructor. The analyzer's non-executing closure collector
closes sibling graphs through the same interner after its late-binding pass.

Runtime `==` is now only `ValueRef::ptr_eq`; Algorithm B is canonicalization-internal. Equal resolved
captures, alpha/polynomial source variants, self/mutual recursion, symmetric-group collapse, and mixed
tuple/record cycles all produce one exposed pointer. Distinct captures, act kinds, and box locations
remain distinct. MU-18 is live: an interleaved `a == a` inside `a`/`b`'s open window traps
`unbound-evaluation`. A machinery gate prevents routing runtime equality back through Algorithm B.

The twelfth repair closes the repository-wide formatting gate. `cargo fmt --all` was applied as one
mechanical Rust-only rewrite after the semantic repairs, and `cargo fmt --all -- --check` is now
green. The semantic, machinery, lint, and normative-manifest gates retain the same outcomes after the
rewrite.

**Remaining measured P0 implementation drift: none in this recovery rebaseline.** This does not mean
the language implementation is complete: the ignored and staged work recorded below remains outside
the P0 recovery set.

The first post-recovery Phase-A slice activates A-VER's union-boundary and Indeterminate-discharge
subset. `data.body` over `Union(Response, Failure)` still rejects because `Failure` does not guarantee
that field; after an exhaustive `Response` / `Failure` contract-pattern match, the selected Response
row now carries its field image into the declared return demand and proves `String`. The defect was in
forward result resolution: field output recognized only a top-level exact `Record`, so the effective
row contract `(Response ∪ Failure) ∩ Response` produced `Top` even though safety had proved the access.
Field output now follows `Union`, `Intersection`, and `Difference` with `Bottom` for branches on which
access cannot succeed. The direct-reject/narrowed-accept pair is live at both analyzer and conformance
boundaries; the broad A-VER row remains ignored for its other cases.

**Recovery order:** memo-key completeness, ruled Indeterminate-form/Numeric semantics, typed
executable program demands, ordinary-application fact wiring, the structured completion witness /
typed seat boundary (T2.2), application-path unification (T2.3), and the existing `where` return
demand's realized-refutation consumer, source-level AP-29 operand propagation, exact function
operation transfer, universal function construction/interning, and repository formatting are
complete. Normative files remain manifest-protected and were not edited by these implementation
slices.

---

## 1. Normative specifications — CURRENT (design authority)

All 19 manifest-verified files (`shasum -c MANIFEST.sha256.txt` → 19/19 OK, checked 2026-08-01).
**These are not to be edited as part of any implementation work.**

`next-design-compendium-v1-0.md` (patch 1.0.18) · `next-grammar-specification-v0-1.md` ·
`next-kernel-ast-specification-v0-1.md` · `next-semantics-companion-v0-1.md` ·
`next-test-suite-specification-v0-1.md` · `next-mu-canonicalization-specification-v0-5.md` ·
`next-recursive-contracts-specification-v0-2.md` · `next-application-induction-specification-v0-8.md` ·
`next-tuple-length-family-specification-v0-3.md` · `next-region-table-specification-v0-3.md` ·
`next-phase-a-worked-examples-recovered.md` · `CLAUDE.md` · `OwedItems-CLOSED.md` ·
`HANDOVER-open-threads-2026-07-23.md` · `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md` ·
`next-termination-decisions-v4.md` · `next-late-resolution-v0-5.md` ·
`next-grounding-spec-v1-handover.md` · `next-grounding-specification-v0-5.md`

**Recorded staleness inside normative files — NOT to be "fixed" by implementation work.** These are
noted so no one implements a phantom; correcting them is an author/design action:

| Where | Stale text | The governing statement |
|---|---|---|
| region-table §6 / §11 | describes a "separate, deliberately small specification" deriving `InferredAcceptedDomain` | **Dissolved** by the 2026-07-24 erratum (compendium Appendix M): no accepted-domain object exists |
| region-table header | title says patch 0.3.1; body describes 0.3.2 | body is the later text |
| compendium C§7 | generic `x/0 → Indeterminate(_/0)` marker model | the later manifest-governed rulings (`HANDOVER-indeterminate-…-2026-07-24.md` Parts XI–XII, 2026-07-27/2026-08-01) adopt specific `Indeterminate(DivZero(a))` / `Indeterminate(ModZero(a))` identity and `Numeric = Number ∪ Indeterminate`. The core text is stale; the ruling is settled and implementation drift must follow it |
| grounding v0.5 header | "DRAFT … nothing herein is closed until stamped" | compendium 1.0.18 records it DESIGN-CLOSED; the stamp record itself is **not present** — author-owned |

---

## 2. Document status register

| Document | Status | Note |
|---|---|---|
| **`IMPLEMENTATION-STATUS.md`** (this file) | **CURRENT** | The implementation-status authority |
| The 19 manifest'd specs (§1) | **CURRENT** | Design authority; staleness recorded above, not edited |
| `DECISIONS.md` | **CURRENT** as an append-only provenance log | Newest dated entry wins per topic; **individual older entries are HISTORICAL** and must not be read as present-tense guidance |
| `NEXT-completion-plan.md` | **CURRENT (subordinate)** | Tier structure and the owed/liveness synthesis stand; where it conflicts with this file, this file wins |
| `PROGRESS.md` | **SUPERSEDED** | Snapshot, doc-sync rows, "§6 next increments", and the increment-ledger detail are stale (they describe the retired app-induction-tail plan, cite `SAFETY_STACK` which does not exist, and list 10 analyzer modules where there are 13). Retained as history |
| `OwedItems.md` | **SUPERSEDED as guidance; CURRENT as an owed catalogue** | §0.1 is the later framing; §0.1-history and the "swap is DONE / LANDED" passages are **HISTORICAL**. Item lists remain useful; ordering/priority claims do not bind |
| `NEXT-owed-breadth-foundation-map.md` | **SUPERSEDED** | Its F0-before-demand-core ordering was **incorrect** (see §5) and its "replace-and-rebuild" framing is not authorized (§5). Diagnosis of the missing foundation stands as history |
| `NEXT-F0-operation-rulebook-draft.md` | **HISTORICAL** | Design record for a feature that is now built |
| `NEXT-spec-audit-accepted-domains-phase1.md`, `NEXT-architecture-review-*.md`, `NEXT-implementation-finding-accepted-domains.md` | **HISTORICAL** | Superseded by the 2026-07-24 errata and later work |
| `NEXT-implementation-review-Archive{4,5,7,8,9,10}.md`, `NEXT-analyzer-core-checkpoint-review-8.1a-8.1c.md`, `NEXT-implementation-progress-review-Archive4-updated.md` | **HISTORICAL** | Author review rounds; record only |
| `next-mu-canonicalization-specification-v0-1.md` | **HISTORICAL** | Superseded by v0.5 (manifest'd) |
| `next-semantics-companion-v0-1-update-review.md`, `next-grounding-landing-ledger-patches-1-0-18.md` | **HISTORICAL** | Review/patch records |

---

## 3. Implementation trust boundaries

| Path | Status | Nature |
|---|---|---|
| `analyzer::bodycheck` and its reaching core | **DELETED 2026-08-01** | The known-unsound forward reaching-domain checker is no longer compiled or present. `machinery_gate` bans the file, module identifier, and `check_recursive_body` / `reachable_rows` / `grow` identifiers from `src/` |
| Safety-unproven policy | **RESOLVED 2026-08-01 — RULED [user]: it blocks** | `BodySafety::Unproven` and `OpSafety::Unproven` remain typed through `Analysis` and program records. Their fact-layer diagnostics are advisory; executable/declared consumers add the unsuppressible Error after retaining the typed verdict. Completion (`MayFallThrough`) remains a different judgment class (application §1.6) |
| `analyzer::grounding` — `ground()` / `drift_away` / `Verdict` | **CORRECTED 2026-07-31; still UNWIRED** | The §6 slice is complete: forced-path selection, witness-bearing `Refuted(Refutation)`, superseded header claim removed. Its *coverage* gaps (GR-18 point-base, peel-k, oscillator, closed-orbit, §8 WorldDecided, multi-param mutual) remain owed — those are incompleteness (→ `Unproven`), not unsoundness. **Wiring still requires separate authorization** |
| `analyzer::safety` — the **candidate graph** (§6 / C§13.2a) | **BUILT AND WIRED 2026-08-01** | Ordinary known-closure application consumes `BodySafe(instance, I)`. Discovery closure → SCC collapse → reverse-topological → one joint vector pass; dependencies proved by the outer pass are memoized under their own complete keys. `countDown` over a covering declared domain and a divergent self-loop prove; an uncovered repeated-shape chain remains **Unproven**, never a manufactured refutation. Mutual and multi-parameter changed-domain executable calls now reject at the seat because safety is unproven; finer classification remains separately owed |
| `oracle::mu` — construction windows + **Algorithm A group templates** | **RUNTIME WINDOWS WIRED; SERIALIZED TEMPLATE PARTIAL/UNWIRED** | The reference-SCC walk supplies the runtime construction windows used by module/block evaluation. The separate serialized layer-2 artifact has positional μ-refs, genuine-SCC grouping, and canonical slot order, but is still test-only; law 2 (nested-binder merge) and law 4 (partition-refinement slot merging) remain deferred. Runtime MU-14/15/16 identity no longer depends on that artifact: value-graph close plus Algorithm B realizes those rows at construction. |
| `oracle::canon` — per-lambda shape | **BUILT, wired** | α-renaming (`$0`), capture slots (`@cap0`), polynomial NF. This is what `make_closure` (`eval.rs:239`) actually calls |
| **Layer-2 template → analyzer-key join** | **MISSING — CACHE CONFORMANCE/PRECISION GAP** | Runtime function identity is complete through construction interning. The remaining join is analyzer-facing: `mu::canonicalize_group` still does not supply the serialized group shape required by C§13.4 fact/template keys. Current keys use canonical per-lambda shape plus capture contracts, so equivalent recursive groups can miss a memo hit. The failure direction is recomputation/Unproven, never reuse of the wrong fact. |
| `analyzer::induction` pipeline — candidate discovery, domain derivation (`obligation::accepted_domain`, a **dissolved** concept), `summarize_instance` consumption, same-arity domain propagation (marked interim), candidate-to-candidate-only edges | **NON-AUTHORITATIVE** | Not a ready foundation. **Its independently valid SCC utilities (e.g. `scc_reverse_topo`, the reverse-topological order) may be reused.** There is **no** authorized broad replace-and-rebuild project |

**Not quarantined** (trusted): the lexer, parser, desugar, oracle interpreter, normalization harness,
value/interner layer, and the contract algebra including `contract::numeric` + `contract::operation`
(F0), whose soundness is brute-tested against the oracle.

---

## 4. Known analyzer pins — 1 `#[ignore]`d in lib

This precision gap blocks acceptance where proof is absent; it is not permission to reintroduce
reaching domains, widening, or manufactured witnesses.

| Gate | Current behavior | Actual blocker |
|---|---|---|
| **1b** exact recursive singleton chain | `f(0) → f(1) → 1` is safe, but the second `f` repeats a shape and §4a admits no new node through that path; the seat rejects safety-unproven | grounding §4 exact-singleton fact chains. A row-wide fact is insufficient because the same row also contains trapping inputs |

Resolved by the 2026-08-01 wiring:

- **2b mutual/helper domain change:** the executable program is no longer silently accepted. Global
  discovery reaches the changed-domain dependency, §4a cuts off the repeated shape, and
  safety-unproven blocks at the application seat. The graph verdict is honestly **Unproven**, not
  permanently Refuted: no admitted realized witness has been attached.
- **2a multi-parameter domain change:** likewise no longer a false acceptance. Until §5
  argument-tuple projection exists, the changed-domain repeated-shape fact remains Unproven and the
  seat rejects. The missing projection is now a precision/classification gap, not a soundness hole.
- The broad-domain factorial safety and recursive-return tests are live again. Their `Number` fact
  covers `n - 1`; safety now consults the completion cross-claim and return induction instead of
  treating the recursive operand as a false possible fall-through.
- **3 recursive arm fall-through:** released by T2.2. The represented Pure call is realized through
  the bounded oracle, the `ApplicationWitness` survives Match outcome composition, and only the
  enclosing expecting consumer rejects it. The statement-seat counterpart remains accepted.
- Direct tests of the deleted checker were removed with it. They tested implementation internals,
  not stable language IDs; their live application/graph counterparts remain.

Conformance holds 11 `#[ignore]`s (6 broad Phase A · 4 module/linking · M-04). A split A-VER
union-boundary/Indeterminate row and MU-18 are live and green.

---

## 5. Forbidden machinery (binding)

1. **No reaching-domain fixpoint, no widening, no candidate synthesis, and no
   grounding-as-analysis-cutoff.** (Grounding is a behavioural judgment; C§13.3 bounds the symbolic
   procedure independently.)
2. **Imprecision produces `unproven` — never another prerequisite.** A sound-but-coarse rule
   returning unproven is a correct outcome; it is not a reason to build a preceding layer. *(This
   supersedes the foundation map's F0-before-demand-core ordering, which rested on the opposite
   assumption.)*
3. **Fact domain `I` and demanded contract `C` remain distinct** — everywhere, as separate fields.
   `I` is the input/row domain a fact is claimed under; `C` is the demanded contract. An operand
   obligation is **not** automatically a fact's input domain.
4. **No broad replace-and-rebuild project.** The quarantined paths are non-authoritative; that is a
   trust statement, not a licence for a sweeping rewrite. Independently valid utilities may be reused.
5. Previously killed by ruling and still killed: fuel of any kind in normative analysis, tier-0
   evaluation-as-grounding, constructed-witness inventories, supplied-measure annotations,
   invariant synthesis, generic state-carrier framing (grounding §14).

---


### Mechanical enforcement — `tests/machinery_gate.rs` (added 2026-07-31)

The five boundaries above were prose only, and prose did not hold them: a forward-reaching
/widening engine was built on 2026-07-31, passed all four blockers, and was reverted whole.
Ten checks now enforce the part a machine can see. The original six were verified against injected
violations; checks 7–10 pin the exact absent source mechanisms exposed by the measured AP-29,
typed-boundary, and runtime-equality regressions. A gate that cannot fire is not a gate.

1. `src/analyzer/summary.rs` (the reverted engine) and sibling names must not exist.
2. The retired `bodycheck.rs`, its module identifier, and its reaching-core identifiers
   (`check_recursive_body`, `reachable_rows`, `grow`) must be absent from `src/`.
3. `callee_completion` still consults the settled completion fact — `Produces` at a call site
   may not be asserted by a coarse body pass (a false **accept**, the dangerous direction).
4. `analyze_apply` must call `drive_application` and may not restore its own callee-alternative
   enumeration or application outcome join.
5. `demand::adjudicate` must consume `check_return_claim` and may not restore a parallel direct
   `prove_claim` / `joint_vector_pass` return-proof path that drops realized evidence.
6. `realized_refutation` must carry an explicit Pure-closure guard; its non-executing Effect/Mutator
   boundary may not rely only on the bounded evaluator's current entry-world policy.
7. The live application path must retain `AnalysisContract` in `TypeEnv` and may not route back
   through the erased operand bridge.
8. `Analysis`, executable demands, declared body demands, and `BodySafetyEvidence` must retain typed
   safety judgments rather than leaving findings as the only program-boundary representation.
9. Safety candidate discovery must use the same correlated/annotated joint operand path as live
   application and may not restore the direct-captured-name-only resolver.

**Scope, stated rather than glossed:** the gate catches a literal repeat of the retired engine. It
does **not** catch a renamed reimplementation. That stays a review obligation, under the standing
rule that when a pinned blocker goes green the **mechanism** is
reported, not merely the outcome. If a check fires, the fix is never to relax it — imprecision
yields `unproven`, never another prerequisite and never a growth loop.


### T1.4 — COMPLETE 2026-08-01: ordinary application consumes settled facts

The earlier swap failed because settlement re-entrancy was guarded globally and because the memo key
omitted named-contract dependencies. Both prerequisites are now closed, and the application path has
been swapped without retaining the reaching checker.

- `analyze_apply` requires the three-voiced `safety::prove` result and applies the ruled blocking
  policy at the seat. It takes completion from `safety::completes`; recursive produced values use
  return induction, while acyclic dependencies preserve exact body outcomes.
- The in-progress marker is the complete fact key, not a thread-global “settling” answer. An outer
  graph pass publishes every proven dependency candidate under its own complete key. Nested,
  hypothesis-relative settlements are still discarded.
- Safety verification has an explicit dynamic context so an unresolved cutoff dependency remains
  Unproven during diagnostic recovery instead of launching a nested proof past the cutoff.
- Outcome projection follows §4a's active shape sequence. Re-entering a shape contributes coarse
  `Top` / possible completion, preventing stack overflow on `loop = () => loop()`; settled return
  and completion facts sharpen that projection where licensed.
- The old `bodycheck.rs` path and reaching primitives are deleted and mechanically banned.

**Witness correction:** the mutual changed-domain example is rejected, but the candidate graph alone
returns **Unproven**, not Refuted. The repeated `f` shape is not admitted through that path, and no
realized exact witness is attached. This is the required honest voice; late-resolution §5 still
blocks the executable call. The same mechanism closes the multi-parameter false acceptance while
leaving §5 tuple projection as an owed precision feature.

**Still separate:** blocker 1b needs grounding's exact-singleton chains; blocker 3 needs structured
completion evidence through the consumer. Neither is a reason to restore forward reaching domains.

---
## 6. Historical prerequisite slice — ✅ COMPLETE 2026-07-31

> **Status: done; retained for provenance.** All three corrections landed; grounding remains
> **unwired** and no forbidden machinery was introduced. The later program-demand, memo, and T1.4
> slices are recorded above and in `DECISIONS.md`.

**Correct `analyzer::grounding` while it remains unwired.** Nothing else is authorized; in
particular **`BodySafe(instance, I)` must not be started** until this is complete.

1. **Forced-path selection.** A recursive transition may be admitted only when the path to it is
   *forced* — exact selection, or another applicable must-condition, at every step. Syntactic
   presence of a self-call is not sufficient (this is the G-BUG cause).
2. **Persistent refutation evidence.** Every refutation must carry its admitted represented-exact
   **root witness and certificate**, persistently. *(The Rust representation is not predetermined.)*
3. **Remove the superseded claim** in the module header that grounding bounds or terminates
   analyzer unfolding / replaces widening as the analysis's termination bound.

**Done means:** G-BUG's gate passes on the mechanism above; grounding remains **unwired**; no
forbidden machinery introduced; existing suites unchanged. — **All satisfied.** Detail in
`DECISIONS.md` (2026-07-31 grounding-correction entry).

---

## 7. Test baseline (measured 2026-08-01, not inherited)

| Suite | Result |
|---|---|
| `cargo test --lib` | **438 passed, 0 failed, 1 ignored** (exact-singleton chain) |
| `cargo test --test conformance` | **114 passed, 0 failed, 11 ignored** (A-VER subset activated) |
| `cargo test --test machinery_gate` | **10 passed, 0 failed** |
| `cargo clippy --all-targets -- -D warnings` | **0 warnings** |
| `cargo fmt --all -- --check` | **PASS** |
| `shasum -c MANIFEST.sha256.txt` | **19/19 OK** |

Earlier counts appearing in other documents (323 / 371 / 377 / 380 / 383 / 384 / 396 / 409 / 413 /
417 / 421 / 424 / 426) are
**HISTORICAL**; this table is current.
**Green ≠ complete:** the §4 exact-singleton fact-chain gate remains pinned.
