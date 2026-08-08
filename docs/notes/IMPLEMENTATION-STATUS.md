# NEXT — IMPLEMENTATION STATUS (AUTHORITY)

**Created 2026-07-31 (Tier-0 rebaseline). This file is the single current authority on
implementation status.** Where any other maintainer document disagrees with this file about *what
is built, what is trusted, or what to do next*, **this file wins**.

**What this file is not.** It makes **no semantic rulings**, defines no mechanism, and changes no
design. It does not rewrite history: contradictory documents keep their text and are *labelled*
below. Design authority remains entirely with the manifest-verified normative specifications (§1).

**Author amendment recorded 2026-08-08.** The later ruling on recursive function identity
supersedes the `GroupTemplate` / group-level code-identity portions of the manifest-protected μ
v0.5, application v0.8, and compendium text: recursive groups are construction windows only.
Identity is each function's canonical positional code applied to its immutable positional capture
graph. The protected files remain unchanged pending a controlled normative revision; the ruling,
implementation, and tests are recorded in `DECISIONS.md` and below.

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

The second post-recovery Phase-A slice (2026-08-03) activates A-VER's **Failure-overlap wrapper
demand** (B6 [1.0.2]) at the one adapter boundary that exists today — a declared fallible return.
Where a `Union` alternative is provably on the `Failure` rail, every success alternative must be
proven disjoint from the prelude `Failure` shape, else an Error demands the explicit success
wrapper; ordinary emptiness checking only, and `conform` inherits the same rule at its own boundary
when it lands. The red/green pair (open `HasField` success shape rejects; exact-record wrapper
accepts) is live at both analyzer and conformance boundaries. A-VER's remaining broad cases are the
comparison-chain hint, full exhaustiveness diagnostics, and act-kind admission over source unions.

Blocker 1b was **re-expected the same day under an author ruling** (grounding §14's deferral
stands): the honest reject-as-Unproven expectation is live, and acceptance is the `#[ignore]`d
deferred-extension twin — detail in §4 and `NEXT-implementation-finding-blocker-1b-v1-scope.md`.

**Principle 9 was stamped the same day [user, 2026-08-03]: the gray tier is dead.** Unproven
grounding is a compile error, never a warning, at every seat. Grounding is therefore **wired** —
its first consumer is the stamped law itself: the program checker adjudicates a typed
`GroundingDemand` for every distinct recursive-callee/domain pair at executable seats and for every
`where` over its declared domain. A provably diverging call errors with its witness
(`loop = (n) => loop(n); x = loop(1)` names the written start `1`); proven-terminating recursion
(`countDown` over `GE(0) ∧ Mod(1,0)`) still accepts; collatz-class recursion rejects honestly.
The compendium's Principle 9 text still carries the pre-stamp wording — the normative stamp record
is an author-owned edit; `DECISIONS.md` (2026-08-03) is the provenance record until it lands.

**The module linking core landed (2026-08-04):** `src/link.rs` — static whole-program
resolution over one shared store; named imports install the exported binding itself (slots stay the
same location — live cross-module reads), whole-module imports and `m = Counter` aliases rewrite
statically to hidden namespace bindings, duplicate module names and headerless exports are project
errors (the latter enforced at the desugarer for the single-file path too). Runtime linking only:
`--check` still treats imports as metadata — project-level analysis is the follow-up. Conformance
ignores drop to 7 (6 broad Phase A · M-04).

**The group orbit landed (2026-08-04):** bare mutual pairs close with no contracts —
`grounding::group_orbit_domain` derives one shared envelope from the group's cross-call drifts and
half-line stops (reusing the shared-measure certificate's own reading); the joint induction proves
both members' facts over it. The GR-07 row flipped to acceptance. Remaining mutual precision: point
bases across members (parity ping-pong) and non-unit shared lattices for non-point starts.

**The WorldDecided classifier landed, v1 (2026-08-04):** `grounding::world_decided` is GR-24's
sound recognizer for self-recursive Effect instances (fresh observation on every cycle by syntax +
dataflow; completing arm as the seed; stale-carried, decorative, unguarded, and mutual shapes all
refused), consumed at seats per GR-26's order (refutation dominates; all-Grounded keeps ordinary
completion; only honest Unproven is excused, recorded as `world_decided` on the typed demand).
Effect-world polling loops compile; mode-dependent domains (specimens 15/21/27) stay honestly
unproven pending the per-region closure. Downstream world-conditioned sequencing metadata is not
yet propagated — nothing consumes it today.

**Coverage is resolution [author, 2026-08-03]:** a demanded fact is answered by any settled
proven fact of the same instance/environment/claim whose domain **contains** the demanded one —
`factcache::covering`, consulted in the same resolution step as the exact-pointer hit (its trivial
case) and during discovery (a covered dependency mints no node). Only Proven transfers down.
`where` declarations settle in a pre-pass, so their source position is immaterial. A concrete call
inside a declared, proven domain now resolves through that fact with zero re-analysis
(`f(5, 0)` under `f where (Number, Number)` — the two-parameter case no orbit reaches).

**Repeated shapes close through drift-derived orbits [author, 2026-08-03; corrected same day]:**
the first cut of this slice proposed repeated-shape candidates over the Kind basis — **caught by
the author as an imported widening reflex and replaced**. `grounding::derived_orbit_domain` now
composes the orbit envelope from GR-05's own certificate (exact integer start, constant negative
drifts, landing base): `countDown(5)` derives `Range(0,5) ∧ Mod(1,0)`, discovery proposes the fact
over it, and the ordinary vector induction proves it — C§13.3(1)'s "derived grounding contracts",
strictly tighter than any Kind. Contract-free concrete calls to terminating recursion accept; no
certificate (collatz, ascending drifts, non-numeric edges) means no envelope and the honest cutoff;
blocker 1b's honest-Unproven pin holds (its 0 → 1 edge drifts up). `kind_abstraction` is residual
again per the completion plan's Tier-4 note. The correction is logged in `DECISIONS.md` — the
third author-caught import; the machinery-gate scope note ("a gate cannot catch a renamed
reimplementation — that stays a review obligation") performed exactly as written.

**Hypothesis stacking + nested-seat completion landed (2026-08-04):** `with_hypotheses` now
**stacks** the ambient table (innermost-wins lookup) per C§13.2a's "hypotheses assumed jointly",
so a settlement nested inside another pass keeps the ambient facts visible; its soundness half is
a new publication guard — a settlement entered under **any** ambient hypotheses is
hypothesis-relative and is discarded by `factcache::finish` like a nested one (the DEPTH guard
alone cannot see hypotheses installed without a `begin`). The two guarded application branches
(active safety context; failed safety) answer their completion voice from assumed completion
facts and settled coverage (read-only, never a settlement past the cutoff) and their produced
voice from `call_return` for recursive callees — §1.6's separate judgment classes; the safety
voice stays honestly Unproven. This slice also **re-landed** two produced-path sharpenings the
2026-08-04 instrumentation entry had recorded but whose commit had not actually carried
(discrepancy audited in `DECISIONS.md`). Measured: McCarthy 91's safety, completion, and
`where (Number) => Number` return claim all **prove** — `infer_return_fact(m, [LessEq(111)])`
derives exactly the `(90, 101]` zone — and the program rejects on exactly one voice, the
Principle-9 termination demands. The remaining McCarthy gap is the landing-zone grounding
certificate over the nested call (GR specimen 7).

**The nested landing-zone certificate landed (2026-08-04): McCarthy 91 accepts, all reals.**
`grounding::nested_zone_shape` reads grid §6's closed form off the written program (ascending
half-line stop `n > T`/`n >= T` tested first, exit shift `n + s`, one shared climb drift
`m(n + d)`, one-level feed-back `m(m(n + d))`); `nested_zone_descent` grounds it from the
written constants — `d > 0`, lap net `d + s > 0`, and grid step 3's feed-back `F(C) ⊑ C`
induction through the ordinary return-fact machinery (return over `LE(T+d)` inside the zone
`(T+s, T+d+s]`). The ascending-stop envelope `LessEq(T+d+max(s,0))` joins
`derived_orbit_domain` for safety-discovery cutoffs, and `call_return` retries a failed
inference over the derived envelope (containment-guarded — coverage applied to the return
question). More than one nesting level declines (Knuth's k-fold diverges for McCarthy's own
constants) and is pinned as a rejecting twin. GR specimen 7 is live; conformance ignores are
**3** (Ackermann + the 2 Part-D adoption gates). Detail and the honest review-provenance note
in `DECISIONS.md` (2026-08-04).

**The joint lexicographic certificate landed (2026-08-04): Ackermann accepts; no real
certificate pin remains.** `grounding::lex_grounded` mechanizes GR-13/14: point floors from the
`== k` guards, `GE(floor) ∧ Mod(1,0)` envelopes, gated unit decreases (the negated point test on
the call's path), domain closure at every position with the nested call's membership through the
proven return fact (GR-13's return half), and one fixed dictionary over GR-14's injective-sequence
enumeration. The enabling repairs: guard-region narrowing at the expression layer AND the
discovery walk (E-4/E9's remainder law — nested tested matches kept their narrowing);
`verify_completes` multi-parameter partition; a semantic uninformative filter for return
proposals (`Union(…, Top)` is as vacuous as `Top`); `Contract::difference` normalizing
proven-disjoint exclusions (C§4's family); and `FUELED_MAX_CALL_DEPTH` 256 → 48 (measured:
≈21 KiB interpreter stack per call level in debug overflowed 2 MiB test threads before fuel —
a process abort, now a clean machine-limit verdict; conformance ~13 s → ~1 s). GR specimen 5 is
live. **Conformance ignores: 2 — the Part-D adoption gates, the author's to open.** Detail in
`DECISIONS.md` (2026-08-04).

**T2.4 recursive source contracts landed (2026-08-04): `Contract::Ref` is live.**
`eval_recursive_contract_bindings` — the C§9 two-pass (in-order, then one joint pass with failed
names bound to `Ref`) — feeds both front ends: the checker rejects inadmissible groups with the
spec's two definition errors (negative polarity; unguarded cycle, with hint), the oracle
pre-passes admissible groups before item order and answers runtime contract-as-pattern
membership through `recursive::contains`. The μ construction-window filter excludes
all-contract "value groups". Analyzer-side Ref-bearing contracts stay conservatively honest;
group-aware subcontract/emptiness consumers are the next increment. Four `recursive_contracts`
conformance rows. Detail in `DECISIONS.md` (2026-08-04).

**T2.5 string-length contracts landed (2026-08-04):** strings join the tuple-length family —
`value_length`/`length::len` count grapheme clusters (literal counts exact; `Kind(String)` =
`GE(0)`), and F0's `Add` string rail produces `LengthRestricted(Kind(String), D)` via
`concat_image` with the sound seam envelope `[left.lo, hi_a + hi_b]` (floor from the left
operand only — clustering merges rightward-in; the −2 ZWJ seam family is the pinned witness).
`subcontract` gains the two sound `LengthRestricted` proof arms (`LR(T,D) ⊑ B` if `T ⊑ B`;
`LR ⊑ LR` componentwise) so lifted produced contracts still discharge plain String demands.
Detail in `DECISIONS.md` (2026-08-04).

**Group-aware consumers landed (2026-08-04): `Contract::Ref` is no longer opaque to the
analyzer.** `subcontract` routes Ref-mentioning pairs through the ambient recursive group
(`rec_group_guard`, RAII dynamic scope; a `ROUTING` flag guards the walk's own fallback), so
narrowing, dead arms, exhaustiveness, region remainders, and the `where` demands all consume
C§9's progress-guarded induction — emptiness included. The region walkers additionally collapse
a fully-consumed remainder to `Bottom` (the completion coverage discipline, applied to
`select`/`select_multi`/`remaining_multi`) — an across-the-board sharpening the recursive
pattern rows exposed. Structural matches over recursive unions prove exhaustive without
wildcards; contract patterns consume their domains and kill later arms. Detail in
`DECISIONS.md` (2026-08-04).

**T3.1 first cut landed (2026-08-04): instantiated region tables.** `region_table_in` reads
guards after capture substitution — case (a) singleton captures exact (constant-parameter
extraction), case (b) bounded captures through the spec's finite operator transfer (may-regions,
never exact), cases (c)/(d) unchanged. `collect` now defines literal-constant module bindings
into the shared scope so `capture_env` sees them at `where`-pre-pass time (computed bindings
stay honestly opaque). W-1 flips at module level; W-2/W-3 pinned at lib level. Remaining T3.1:
the RT-09 annotated-tuple instance cache, the guards' own path demands, multi-parameter capture
substitution, and the factory-product instance flow (C§13.2 plumbing, separately owed). Detail
in `DECISIONS.md` (2026-08-04).

**The factory instance flow landed (2026-08-04, exact-singleton cut):** a body-nested lambda
whose canonical free variables all resolve to singleton values **constructs its closure during
analysis** (`make_closure_in` — construction evaluates nothing; universal interning makes the
product canonical), so factory products are known instances at their call seats and the whole
fact machinery applies — including the instantiated region table over the captured threshold.
Non-singleton captures keep the sound coarse `Kind(Function)`; the annotated instance-metadata
union stays owed. `where` on a product *binding* remains a named residue. Detail in
`DECISIONS.md` (2026-08-04).

**Check-mode project analysis landed (2026-08-04):** `link::check_project` — the shared
`assemble` (front/index/validate/resolve/topo, one implementation for run and check) feeding
`analyze_program_project` per module in order: imported value bindings installed from the
exporter's checked scope, exported named contracts seeded into the importer's contract
environment. Cross-module traps reject at the importing seat; imported contracts carry
declared domains. Named residues: exported slots (no check-mode scope binding — MOD-03 stays
runtime-verified) and whole-module contract access in contract seats. Detail in
`DECISIONS.md` (2026-08-04).

**RT-09 landed (2026-08-04; immutable-query corrections 2026-08-08): the instance memo.**
`region::instance_table` performs one derivation and returns one answer allocation per complete
query `(canonical applied function ValueRef, named contracts)`, consolidating the seven call sites
that rebuilt the instantiated table by hand. The function value determines its canonical code,
capture graph, parameter form, and one retained source representative while cached `Row`s remain
source-spelled. α-variants that universal interning resolves to one function therefore share that
representative and rows; distinct canonical values cannot exchange them.
Single- and multi-parameter tables use the same immutable memo family. Detail in `DECISIONS.md`
(2026-08-04 and 2026-08-08).

**Multi-parameter capture substitution landed (2026-08-04):** the positional regionalizer
reads captures through the same case inventory (singleton exact per position; bounded
may-region; sibling params stay case (c)); `instance_table_multi` joins the RT-09 cache — the
three multi consumers share one derivation per instance. Detail in `DECISIONS.md`
(2026-08-04).

**The imported layer-2 group identity was removed (2026-08-08) [user ruling].** Fact and RT-09
instance queries key directly by the canonical applied function `ValueRef`. Recursive sibling
edges are ordinary positional capture-graph edges already represented by that value; no analyzer
pass reconstructs source groups, serializes μ-refs, assigns group slots, or excludes sibling
captures to manufacture a second identity. Symbolic instances now use interned canonical code
applied to an interned positional capture-contract tuple; symbolic fact queries add arrived
arguments and named contracts under the same interner owner. The original 2026-08-04 join remains
in `DECISIONS.md` as superseded provenance.

**The guards' own path demands landed (2026-08-04) — a measured false accept closed.** The
partition verify paths analyzed only row results; a guard that traps (mixed `+`) or tests a
non-Boolean seat was invisible, accepting programs the oracle traps on. Region rows now carry
their guard seats, and both verify paths (single and multi) run a guard-demand walk: arrivals =
remaining ∩ pattern region, guard analyzed under its arriving domain, `check_tested_seat` (E10
strict Boolean), evidence through RT-14's weakening (`definite && pattern_exact` — may-region
guards advise, never refute). Both false-accept programs now reject; all guard-bearing green
rows (countDown, McCarthy, Ackermann, gcd) unchanged. Conformance `guard_demands` pins both
directions. Detail in `DECISIONS.md` (2026-08-04).

**The RT-01…14 rows closed (2026-08-05) — with two measured honesty defects fixed.** All
§10 suite obligations are pinned (conformance `region_rows` + existing lib/instantiation
rows). New machinery, each at its spec-named seat: the §E9 unreachable-branch error at
`analyze_where`, walking the instantiated table **from Top** (the recovered grid's `Strict`
factorial refutes the declared-domain reading — internal recursion lawfully arrives outside
the entry contract; `[ask-author]` markers on the reading and on the ExpectingSeat class
reuse); **definite arrival** threaded through `Selected`/`SelectedN` (RT-14: refutations only
through definitely-reached rows — a trap behind an opaque guard's else now rejects through
Unproven, never Refuted); the **E10 produce claim** at the `where` (`Claim::Completes` over
the declared domain, Pure bodies only) — closing a measured false accept (oracle traps
ExpectingSeat on the uncovered input; the analyzer accepted). A first attempt seating
coverage inside `safety::prove` was rejected by the statement-seat pin and reverted —
fall-through belongs to the consumer, not body safety. Difference-aware `disjoint`/
`is_empty`/`provable` rules carried the exhaustiveness proofs. Detail in `DECISIONS.md`
(2026-08-05).

**Tier 4 consolidation landed (2026-08-05):** the consumption discipline is two walk
engines (`region::walk_rows`/`walk_rows_multi`) with six former copies as thin visitors (the
RT-14 defect was drift between copies — structurally impossible now); the four three-voice
verdict enums are aliases of one `contract::Voice<W>` (zero consumer churn; `grounding::
Verdict` and `BodySafety` documented as deliberate divergences); the completion tri-states
are verified as AP-29's type-enforced witness boundary with one named conversion
(`CompletionWithoutValue::of`) and the coarse path's realized-witness policy documented; the
three `intersect` copies are one simplifying `Contract::intersect`. Phase-3 set: residual
`kind_abstraction` deleted (zero consumers); `summarize_instance`'s per-call role confirmed
already gone (induction role live); `accepted_domain` kept — live argument-obligation +
interim group domains (replacement v0.8.1 §5 unbuilt; the plan's deletion gate forbids).
Detail in `DECISIONS.md` (2026-08-05).

**Tier 5 opened (2026-08-05): the A-SND discharge battery is live** (conformance
`tier5_discharge` — evidence, not proof; §13.5's supplement discipline). Five batteries +
one recorded stub: layer (1) at family breadth (= the semantics theorem's executable
face), §13.1–3 sampled certificate termination (zone/lex/multigraph grids), GR-23a witness
validity (refutation witnesses diverge), layer (3) under the stamped uniform law (no
call-seat gray class; rejected programs run trap-free; world-decided runner stubbed),
recursive-contract membership vs the oracle; layer (2) was already
`operation_soundness_sweep`. **Two defects caught on arrival:** the bounded runner wore
the sampler's depth calibration (48) and called it divergence — it now runs on a dedicated
256 MiB thread with its own allowance (4096), `Completed` carrying the canonical literal
form; and record-pattern binders never bound in the partition paths (false
UnboundEvaluation) — rows carry their pattern, both partition consumers bind per E9, and
the projectors see through `Leaf(Intersection)` (sound either-side rule, no construction).
Still owed: the γ-per-world battery, the world-decided runner, all paper-proof halves.
Detail in `DECISIONS.md` (2026-08-05).

**A5 ruled and landed (2026-08-05):** the uncalled-proven-unsafe-body diagnostic is
**lint domain** [user] — `uncalled_unsafe_lints` advises at the definition when an
unreferenced function's body is proven to trap; seats keep the blocking judgment; three
conformance pins. Detail in `DECISIONS.md` (2026-08-05).

**The sampler's license revoked (2026-08-05) [user]:** fueled analyzer-side evaluation
was never spec-licensed (AP-19/AP-30 define witness *shapes*, not an evaluation
*procedure*) — `realized_refutation` is closed (false return claims land the honest
Unproven voice; still rejections); `realized_completion` is rebuilt **structural**
(proven-member points + the instantiated row walk; nothing executes) so all completion
soundness holds. Four pins re-recorded. The T3.5 bounded harness is suite tooling and
stands. Same session: A2 (walk-from-Top) and A3 (class borrowing) RULED and converted;
A4(2) gray-acknowledgment allowed for unproven recursion only (spelling reserved); A7
where-on-product-binding ruled EXTEND (queued). Detail in `DECISIONS.md` (2026-08-05).

**Nested-factory false rejection fixed (2026-08-06):** both application paths that answer
while the safety voice is coarse collapsed the **produced** contract to `Top` for
non-recursive callees, contradicting the §1.6 doctrine stated in their own comments. A
function produced by a nested call therefore became unresolvable, rejecting correct code
(`build = () => makeCounter(7)(3)`) that the module-level form accepted. Both now answer
from `analyze_instance_body` (settles no fact, bounded by the shape cutoff). Pinned as
conformance `nested_factory_application`. Detail in `DECISIONS.md` (2026-08-06).

**`where`-isolation restored (2026-08-06) [user chose option D]:** graph discovery and
body verification used different predicates for "is this dependency established?" —
discovery accepted a covering published fact and dropped the node, verification accepted
only graph-derived hypotheses — so a `where` could change a *call site's* verdict, against
E11's "no new caller obligations". Both now call one read-only `safety::established`
(hypotheses, then published facts by coverage). Pinned as conformance `where_isolation`:
across five declared domains, adding a call adds no error. At that checkpoint B4 remained
open; the contract-level and canonical-identity landings below close its acyclic source path.
Detail in `DECISIONS.md` (2026-08-06).

**Contract-level analysis instances landed (2026-08-06; canonicalized 2026-08-08) —
C§13.2's "plumbing".** A lambda with a non-singleton capture carries
`Known([Apply(canonical code, positional capture contracts)])` beside `Kind(Function)`;
both safety branches pass the **annotated** produced contract so the metadata survives.
Application now walks every live member of `Known(S)`, admits every act kind through the
ordinary seat-world rule, and settles bodies through interner-owned symbolic facts keyed by
the full instance plus arrived arguments and named contracts. A repeated code node closes
only when the active full instance/domain covers it; another capture tuple or uncovered
domain is safety-unproven, never silently accepted. Pinned by `contract_level_instances`,
the symbolic-instance identity/coverage unit rows, and the instance-union traversal row.

**Recursive local calls over outer arguments landed (2026-08-08; eagerness correction):**
analysis does not materialize a cyclic `AnalysisContract` closure graph. The source closure
forms only when the outer function executes. A direct local call is instead closure-converted
for the judgment: arrived outer bindings become leading arguments of an analyzer-only closed
fact identity (`f(limit, n)`), enclosing-function discovery records the dependency, and the
ordinary safety/return/completion/grounding graph stops at `f(limit, n - 1)` to judge drift.
Invariant environment positions are carried, not treated as termination measures. Pinned live by
`cli_recursive_local_call_carries_outer_arguments_lazily`.

**GR-19 numeric payload safety and GR-26 local Fibonacci released (2026-08-08).** The
late local-call correction made GR-26's already-grounded `go` fact close; its stale ignore is
removed. GR-19 exposed the adjacent, distinct case: `sumUntil(n, acc)` descends in `n` while
`acc` changes through `acc + n`. Discovery still does not unfold the concrete chain. At the
repeated edge it proposes one advance-bounded fact domain: the existing descent certificate
supplies `n`'s orbit envelope, while a changed non-measure position may become `Number` only
when the arrived argument is proven Number and every written recursive expression for that
position is a safe primitive transfer whose output remains within Number. The ordinary joint
fact pass must then prove the whole body over that domain. This is the fixed GR-19 extraction
rule, not kind-menu widening, accumulated reaching domains, execution, or a termination
measure for `acc`. A nonnumeric-edge twin proves the proposal declines before settlement.

**Union remainders empty out (2026-08-07):** `Contract::difference` now distributes over
union arms (`(X∪Y)∖Z = (X∖Z)∪(Y∖Z)`), `Equals(v)∖Z` reduces to `Bottom` by membership when
`Z` contains `v`, and `union` drops `Bottom` arms. Before this, an ordered walk's remainder
became an opaque stack of `Difference` nodes and **three** exact point arms exactly covering
a three-member union were not proven exhaustive (two were). Pinned as conformance
`union_remainders`. This was the prerequisite for A6's routing-forced operation images.
Detail in `DECISIONS.md` (2026-08-07).

**Exact operation images, routing-forced (2026-08-07) — A6's first slice [superseded
mechanism].** The initial whole-body coarse-then-exact retry proved the ruling's examples,
then was deleted when the held-image mechanism landed. The historical measurement remains:
the author's six-arm product and A6 flagship accept; a genuinely missing arm is refused.

**A7 landed (2026-08-07):** a `where` now attaches to a binding proven to hold an exact
function value — `c = makeCounter(5)`, `c where (Number) => Number`. `collect` resolves the
bindings a `where` names by analysing them against the defined siblings and accepting only
an exact function value; resolution is deliberately scoped to those names, because
analysing every non-lambda binding in the declaration pre-pass regressed the non-tail
mutual pair. Pinned as conformance `where_on_products`. Detail in `DECISIONS.md`
(2026-08-07).

**Held images, correlated branch cells, and narrowing by arrival (completed 2026-08-08) —
A6's mechanism.** The cheap rulebook result remains the hull. `analyze_primop` carries an
unforced `HeldImage` in the expression environment; a routing match alone forces it.
`BranchSet` cells carry nominal source assignments, and operation composition is a natural
join: a source reused through a derived node stays diagonal, while equal-contract independent
parameters still cross. Match outputs retain the arriving assignments, so routing a derived
value narrows every source and derived local simultaneously (BR-09). Nested images preserve
chains. The former 256-combination cutoff is gone: finite represented cells are the work,
with no fuel or global precision mode. Images are deliberately absent from
`AnalysisContract`, so calls, returns, structures and recursive/fact boundaries collapse to
ordinary contracts (BR-15) and no memo key depends on source allocation. The original retry,
mode flag and mode-key field remain deleted. Pinned by `exact_images`, including shared,
independent, shadowed, BR-09, missing-arm and 289-cell rows; `exact_image_reach` pins rebuilding
fresh local cells after a call-boundary collapse. Detail in `DECISIONS.md` (2026-08-08).

**Normalization wired (2026-08-07).** The kernel-AST §5 phase existed with its rules,
corpus and harness — and was never called. `desugar::lower_program` (desugar ∘ normalize) is
now the single lowering step, and every production front end routes through it, so the
oracle and the analyzer cannot be handed different spellings. Pinned by
`the_pipeline_lowers_through_normalization`, which observes the *form* — the one thing an
evaluation-preserving pass cannot be caught by. **Open:** whether `poly`'s arithmetic
rewrites (`x + x → 2*x`, today applied only to function-shape identity) should move into
the phase, which μ §8 makes a semantics-version question. Detail in `DECISIONS.md`
(2026-08-07).

**The first RT-09 query repair (2026-08-07) was necessary but incomplete.** Analyzing one
program changed the verdict of the next: a program that compiles **alone** and **on a fresh
thread** was **rejected** when another ran first. Cause, measured: RT-09's `InstanceKey` is
built from the **α-renamed** shape, so `(n) => … n …` and `(k) => … k …` key identically —
while a cached row's `result` is an expression in the *original* spelling, and the lookup hands
back this closure's parameter beside those cached rows. The analyzer binds `k`, the rows ask for
`n`, nothing resolves. Adding the parameter names fixed that witness, with **no cache clearing**;
an earlier clear-at-entry workaround was expiry rather than memoization and was reverted [user].
The 2026-08-08 audit then found the same class through recursive sibling spelling (`cd` versus
`loop`): the process-thread table exchanged rows between separate identity owners. The complete
correction is owner-local knowledge plus the retained-representative query component above. Pinned as conformance `analysis_is_isolated_per_program`
(AI-01…04). Detail in `DECISIONS.md` (2026-08-07 and 2026-08-08).

**Persistent analyzer memos migrated to the interning authority (2026-08-08) [user direction].**
`MemoInterner` is a generic, type-indexed immutable query→answer store owned by `Interner`; the
first answer publication wins and subsequent hits reuse that allocation. The existing persistent
families — proven facts, RT-09 single/multi rows, and local group construction — no longer live in
process thread-locals. Fact and RT-09 queries use the canonical function value and an interned
named-contract environment; facts additionally intern their input and claim. Only active-settlement recursion markers remain
thread-local because they are dynamic control state, not knowledge. No project/generation identity
is present in a query: sharing one `Interner` deliberately shares identities and facts today, and
a future process-global owner needs no query migration. The default check convenience API still
creates a fresh owner; making the runtime owner global is separately blocked by the current
`Rc`/location/retention model. Runtime calls remain never memoized. This is the substrate and the
migration of every persistent analyzer memo that currently exists, not completion of the still
absent C§13.4 template/evaluation/subcontract families.

**Canonical Pure closure conversion ruled and landed (2026-08-08) [user].**
Free lexical scope is represented as an explicit positional capture parameter space in canonical
IR, separate from the function's user-visible parameters. Thus `@mutable x = 1; f = () => x` has
the conceptual closure-converted form `(capture x) => (() => x)`: formation supplies the current
**value** of `x` once, and calls still supply only `f`'s declared empty parameter list. A later
write to the slot does not alter this pure closure's captured value. Self-reference is the same
mechanism over an open graph: `loop = x => loop(x)` has conceptual form
`(capture loop) => (x => loop(x))`; the construction window supplies the self edge and closes the
rational graph before interning. This is canonical IR, not new surface syntax and not a runtime
extra call.

The final function value is therefore canonical code plus a positional capture-value vector (or
the corresponding closed recursive-group graph), not the current raw source `Lambda + Rc<Scope>`
payload. Source may survive as non-identity diagnostic metadata. This also removes a pure read's
slot location from function identity: equal current values produce equal pure closures regardless
of which slot supplied them; different current values remain different capture pointers.

**Landed 2026-08-08.** `FnValue` now carries canonical code plus an ordered capture vector;
invocation executes that canonical code in a fresh frame populated as `@cap0`, `@cap1`, … and no
longer executes a retained source `Lambda + Env`. The source lambda remains analyzer/diagnostic
metadata only. Runtime construction of a Pure closure resolves a slot capture immediately through
read-your-writes and stores the current interned value. Consequently equal snapshots from distinct
stores/slots intern together, different snapshots do not, and a later write is invisible to the
already-formed Pure closure. The prior shared-interner `SlotId(0)` alias is pinned as a cross-store
regression.

Construction-window-only `Deferred` operands may temporarily retain the construction scope. Joint
close rewrites them to ordinary value captures or positional `RecursiveGroup` edges, canonicalizes
the complete graph, updates every root through verified redirects, and locks the group target
vector. No exposed Pure closure retains a `Deferred` operand or `Location`. Function publication
now requires the **entire reachable capture graph** both to resolve and to be materially finalized:
no raw `Deferred` operand may remain anywhere in it. Checking only the immediate vector admitted
the second member of a mutual pair prematurely and broke completion induction; treating a
dynamically resolvable `Deferred` edge as publishable also let an acyclic wrapper retain a
pre-close recursive intermediary instead of the canonical root. Both paths are pinned.
Redirects also carry a weak source-identity guard, because address-only redirects became stale once
provisional closures could be reclaimed and their addresses reused. The current Rust backing for a
locked recursive group is a vector of canonical root handles; replacing that backing with the
specification's one-allocation/interior-offset layout remains a representation/reclamation
refinement, not a semantic or identity-path gap.

**No Mutator ruling is implied or needed here:** Mutators are their own class. Their `Write` nodes
resolve the target binding's compiler-provided setter/update channel; in NEXT that setter stages
into π and the existing outermost-completion rule publishes. It is not a hidden location capture in
an ordinary Pure function. This scope correction follows the ODDO precursor audit at commit
`9966261`: ODDO lowers state to getter/setter pairs, passes dependencies as generated parameters,
and makes the mutator finalizer invoke the setters. ODDO's current `@mutable` implementation still
uses a JavaScript `let` directly, so NEXT takes the architecture, not a one-to-one lowering: both
`@state` and `@mutable` writes use their binding's setter internally, with only state adding its
reactive publication behavior.

**Mutator transient representation is directed but deferred (2026-08-08) [author ruling;
non-blocking].** The relevant ODDO runtime mechanism is its recursive copy-on-write proxy, not just
the generated setter call: a mutator opens current state behind a transient proxy; the first write
clones the touched aggregate, nested child writes propagate replacement toward the root, and the
finalizer materializes the resulting root for the setter. NEXT will use that architecture with its
own value law: committed inputs remain immutable and interned; a Mutator may open non-interned
mutable drafts, copy only the path it writes, and share/join those drafts across nested Mutators.
Outermost successful commit then locks/freezes and interns the changed structure bottom-up before
staging/publication applies the canonical-pointer equality guard. A draft is not a language value,
must not enter the interner, and must not escape its transaction. The current oracle has no such
draft layer: it eagerly constructs and stages complete interned replacement `ValueRef`s in π. That
already realizes the specified transaction observations; replacing its internal representation
with transient COW is a later Mutator implementation slice and does not block canonical Pure
closure conversion or the interner/memo migration.

**Local functions resolve (2026-08-07) [author ruling].** A block's named lambda bindings are
built as closure values *before* any initializer is analyzed, sharing one scope — the
late-binding law the module pre-pass and the canonicalizer already applied. Before this, a
locally-bound recursive function had itself free while its own initializer was analyzed, no
closure value could be made, and every call resolved as "not a known function": the function
was invisible to the whole analysis and its termination was never adjudicated. Now `fib`'s
local `go` is **Grounded on both edges** and a diverging local is **Refuted** with the arriving
argument. Pinned as conformance `local_functions_resolve`. GR-26 moved from a resolution gap to
the same body-safety gap as GR-19 at that checkpoint; both were released by the 2026-08-08
fact-domain corrections recorded above. Detail in `DECISIONS.md` (2026-08-07/08).

**Principle 9's recursion-discovery coverage hole closed (2026-08-07; wording corrected
2026-08-08) [author ruling] — a soundness fix.**
`ground_demand` opened with `if !is_recursive(callee) { return; }`, so a seat whose callee
merely *reached* recursion was never checked and the program compiled. Measured:
`wrap = (k) => [spin(k)]`, the block form, and all three act worlds all **compiled**. Only a
body that was exactly a call was caught; act bodies are blocks, so every act was in the hole.
Fixed by late resolution: when the seat callee is not itself on a cycle, walk its body under
the arriving domain to discover the calls it actually makes, with the arguments those calls
receive. When a call closes the active call cycle, expansion stops and grounding adjudicates
that cycle from the recorded edge transformations and drift. The walk discovers recursion; it
does not recursively solve termination. Carrying arguments down is what keeps
`run = (n) => [countDown(n)]` at `run(5)` accepted. No new machinery:
`analyze_instance_body` already guards repeated shapes. Pinned as conformance
`termination_reaches_through_a_caller`. Closed Phase GR rows GR-13 and GR-16; GR-30 moved
from unchecked to an honest coverage gap. That final gap closed on 2026-08-08: positive
progress/landing certificates now see through a block containing exactly one statement, whose
completion behaviour is identical to that statement's. The projection is a separately memoized
immutable view in the shared `Interner`; general block sequencing and the stability-sensitive
refutation view remain untouched. GR-30 now proves ordinary completion and mints no
`WorldDecided` label. Detail in `DECISIONS.md` (2026-08-07/08).

**`++` joins Tuples too (2026-08-07) [author ruling].** Two sequences of the same kind —
Strings or Tuples, never mixed, never numeric. Tuple results route through
`Contract::concat`, the same smart constructor `[...a, ...b]` uses, so segment structure
survives. Pinned as conformance `concat_over_tuples`. It unblocked `GR-29`, which now passes —
the row asserting no false cycle refutation is minted from an unestablished path. At that
measurement `GR-22B` and `GR-03A` exposed the missing GR-11 closed-orbit producer; the
2026-08-08 increment below closes that route. Detail in `DECISIONS.md` (2026-08-07/08).

**Phase GR initial measurement (2026-08-07) — 23 specimen rows, 15 green, 8 measured gaps.** Conformance
`grounding_specimens`, one test per Grounding Specification §15 specimen, with the P-1 flip
applied (every "unproven" row asserts rejection *and* that no refutation was minted). It was
proposed to test grounding; **only one of the first four gaps it found was in grounding.** GR-08
oscillator is a grounding gap (cycle composition does not fire); GR-19 is a *safety* gap
(grounding proves it, body safety rejects it); GR-26 is a *resolution* gap (a recursive
function inside a block never reaches the prover); GR-13/16 revealed that **act-world
recursion raises no termination demand and compiles** — `@mutate spin = () => { spin() }` is
accepted. Principle 9 is enforced in the pure world, partially in the effect world, and not at
all in the mutation world. The battery also caught a vacuous assertion in its own `gr_30`
(`all()` over an empty vector). This paragraph is the arrival measurement: GR-13/16, GR-19 and
GR-26 are now live and green. GR-08 subsequently went live on 2026-08-08 through constant-drift
edge-labelled cycle composition; variable/multi-parameter ProgressRange composition remains owed.
Detail in `DECISIONS.md` (2026-08-07/08).

**GR-03B exact tuple chain released (2026-08-08).** A written exact flat tuple now follows
GR-09's selected dependency path through nested guards: `[3, 2] → [2] → []`. Slice transfer
already preserved the singleton structurally as `Tuple([Equals(2)])`; it is now reified to the
same interned `Equals([2])` value used by the fact key. The ordinary global dependency graph then
settles safety, completion, and return facts over the three exact nodes before the grounding
verdict licenses the call. No runtime call is evaluated or memoized.

The termination candidate is deliberately the acyclic fragment: one direct-self Pure function,
one flat exact tuple argument, and strict top-level length decrease on every selected recursive
edge. Same-length recursion, `f([l])` structural nesting, Mutators, mutual control locations, and
the pooled zero-drift/closed-orbit cases decline. Exact aggregate operands now use their existing
annotated singleton value in the oracle-backed primitive fold, so `[] == []` and `[3,2][0] == 7`
select exact Match paths instead of falling back to `Boolean`. The same canonical singleton
normalization is used by fact-domain coverage, integrating the chain with the shared interner
rather than creating a chain-local identity table. GR-03B is live. The following GR-11 increment
reuses this graph for the cyclic ending; GR-20 remains the separate derived-segment gap. Detail in
`DECISIONS.md` (2026-08-08).

**GR-11 exact closed-orbit refutation released (2026-08-08).** The direct-self exact tuple graph
now keeps GR-09's ordered strict dependencies. A reached back edge refutes only when every earlier
dependency on every chosen edge has an acyclic exact closure and independently proves
`Completes`; an unproven prefix makes the candidate contribute nothing, preserving GR-29. The
certificate records the canonical root witness, cycle entry, edge path, and completing prefixes.
`Refutation.witness` is consequently a canonical interned `ValueRef`, not a numeric-only
`Rational`; numeric drift-away diagnostics retain their exact number through that value.

GR-03A now refutes from the written root `[3, 7, 2]` after reaching `[7, 2]`, whose selected path
self-loops. GR-22B records `f([])` as the completing prefix before the `[7] → [7]` edge and refutes
with written witness `[7]`. This is finite symbolic graph discovery over pooled root leaves, not
runtime execution or a recursive termination solver. The landed scope remains one direct-self
Pure function over one flat exact tuple; mutual control factor Q, body-constant insertion, and
the wider GR-10 exact-chain license remain conservative `Unproven`. GR-20 is now the only ignored
measured Phase-GR coverage target. Detail in `DECISIONS.md` (2026-08-08).

**Consequence suppression (2026-08-07) [author ruling].** An operation whose operand already
produced an Error now records nothing of its own and yields `Bottom` — it cannot run, so it has
no obligation to report. This extends the descendant-suppression already working across
bindings down into a single expression, removing the two "cannot prove `Add` safe" lines that
followed every failing sub-expression. Siblings are untouched: independent failures all still
report. Only an **Error** suppresses — an *Unproven* operand still earns the seat's
unsuppressible Error, which is what rejects the program. Pinned as conformance
`consequence_suppression` (CS-01…05). It also exposed an A12 cost, reported not fixed:
normalization flattens `(1 + "x") + (2 * "y") + (3 * "z")` so the site `1 + "x"` no longer
exists, and diagnostics lose it. Detail in `DECISIONS.md` (2026-08-07).

**Rejected-program residue measured (2026-08-07).** With anchoring inert in pure code,
normalization reorders operands of programs the analyzer rejects, and 44 of 84 constructed
two-operand chains change **trap class** (`null.x + {a: 1}.b` → `NullReceiver` raw,
`AbsentField` normalized). My earlier "narrow, all `OperationSafety`" estimate was wrong.
What holds: all sixteen §6 suite rows are stable (single trapping site, nothing to reorder) and
are now pinned; and the analyzer reports **every** independent failure, so no compile-time
error is hidden. What is given up: the oracle no longer runs a *rejected* program strictly
left-to-right. Option left open for the author — normalize for analysis/identity only and let
the oracle evaluate the raw form. Detail in `DECISIONS.md` (2026-08-07).

**Anchoring narrowed to act bodies (2026-08-07) [author rulings].** Principle 9 is stamped —
unproven termination is an **error**, already implemented and verified, though the termination
doc still reads "warns and compiles" and is manifest-protected (discrepancy logged). Purity is
a property of the expression, not of a module or an enclosing lambda. Together those mean an
accepted program has **no bottoms**, so in pure code nothing observes operand order:
reordering and combining are both free, and `f() + g() == g() + f()` and `g() + g() == 2 * g()`
are true again. Anchoring survives only inside `@mutate`/`@effect` bodies. Both defects
recorded earlier the same day were witnessed by programs that **do not compile**; the harness
law is now claimed for accepted programs, with effect order checked directly instead. Detail in
`DECISIONS.md` (2026-08-07).

**A12 landed (2026-08-07) [author ruling] — the arithmetic slice governs the lowered
form, and two §8 master-law violations closed with it.** μ §8's three rewrites moved from
`canon.rs` (shape identity only) into the normalization phase inside `lower_program`, so the
oracle, the analyzer, and — re-run after α-conversion — shape identity all read one
rewriting; `poly.rs` became `src/normalize/arith.rs` and shed its own recursion. Checking the
rules against the master law *before* promoting them found two that failed it, both already
live at value level: reordering moved a call past a diverging one (`k(spin, bad)` trapped
alone, diverged with an unrelated `h` above it), and like-term combining erased a call
(`(g) => g() + g()` interned equal to `(g) => 2 * g()`). Fixed by **anchoring** — an operand
that can call or write holds its position and never merges. The property harness was itself
unsound (both runs shared an interner, so the normalized module re-executed the raw
closures); it now uses separate interners, and a fuel-differential law sweeps five budgets, as
§8 prescribes. Pinned as conformance `arithmetic_normal_form`. Detail in `DECISIONS.md`
(2026-08-07).

**`++` for String concatenation (2026-08-07) [author ruling] — closes a shipped
unsoundness.** Wiring the normalization phase exposed it: μ §8's commutative reordering
treats `+` as commutative, but `+` also concatenated, so `s + "y"` and `"y" + s`
canonicalized to one shape and interned to one value — **defining one function changed what
another computed**, and `(s) => s + s` compared equal to `(s) => 2 * s`. The rails are now
separate operators: `PlusPlus` token, `PrimOp::Concat`, `eval_concat`, and the String rail
(with T2.5's grapheme-seam bound) moved off `Add`, which is Number-demanding like the other
arithmetic. The frozen rewrite list needed no amendment. Pinned as conformance
`concat_operator`. The grammar and compendium still describe the overload
and are manifest-protected; the author's ruling **supersedes** them — settled, not tracked. Detail in `DECISIONS.md` (2026-08-07).

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
| `SNAPSHOT-2026-08-07.md` | **CURRENT (subordinate)** | A session record for 2026-08-07: what was resolved, the 11-row gap map, and the decisions waiting on the author. Reasoning lives in `DECISIONS.md`; this file wins on any conflict |
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
| `analyzer::grounding` — `ground()` / `drift_away` / `Verdict` | **WIRED AT PROGRAM SEATS 2026-08-03** under the stamped Principle 9 [user: gray is dead — unproven grounding is an error, never a warning]. Every distinct (recursive callee, argument domain) at an executable seat, and every `where` over its declared domain, adjudicates a typed `GroundingDemand`; `Refuted` errors with its canonical root witness, `Unproven` errors honestly | The §6 slice is complete: forced-path selection, witness-bearing `Refuted(Refutation)`, superseded header claim removed. Constant single-parameter mutual SCCs check every edge-labelled simple cycle and close member-specific safety orbits (GR-08). The direct-self exact tuple graph proves strict descent and carries GR-11 required-dependency closed-orbit evidence. Remaining *coverage* gaps include peel-k/restrict-len, variable and multi-parameter ProgressRange composition, mutual/body-constant exact-chain extensions, and GR-20's derived segment facts — incompleteness (→ `Unproven`), which under the stamp **rejects**; broadening coverage is precision work with a live consumer |
| `analyzer::safety` — the **candidate graph** (§6 / C§13.2a) | **BUILT AND WIRED 2026-08-01; CARRIED/NUMERIC-PAYLOAD DOMAINS 2026-08-08** | Ordinary known-closure application consumes `BodySafe(instance, I)`. Discovery closure → SCC collapse → reverse-topological → one joint vector pass; dependencies proved by the outer pass are memoized under their own complete keys. `countDown`, invariant multi-argument descent, GR-19's operation-verified numeric payload, and a divergent self-loop prove. An unsupported uncovered repeated-shape chain remains **Unproven**, never a manufactured refutation; general call-edge-derived domains remain separately owed. |
| `oracle::mu` — recursive construction windows | **WIRED; IDENTITY-FREE [user, 2026-08-08]** | The reference-SCC walk only schedules allocation and joint closure during module/block evaluation. The serialized group artifact, μ-ref serializer, and slot-permutation search are deleted. Canonical code plus the closed positional value graph owns identity; Algorithm-B exact verification remains inside recursive value interning. |
| `oracle::canon` — per-lambda shape | **BUILT, wired** | α-renaming (`$0`), capture slots (`@cap0`), polynomial NF. This is what `make_closure` (`eval.rs:239`) actually calls |
| Recursive analyzer instance identity | **CANONICAL APPLIED IDENTITY + LATE LOCAL CALLS 2026-08-08 [user]** | Concrete `FactKey` and RT-09 consume the canonical function `ValueRef`; flowing function products may carry canonical code + an interned positional capture-contract tuple as metadata, and symbolic facts add arrived/named contracts. Direct local recursion over outer arguments uses analyzer-only closure conversion with those bindings as ordinary arguments; it constructs no cyclic symbolic source value. No `ShapeKey::Group`, source sibling reconstruction, or member key remains. |
| `analyzer::induction` pipeline — candidate discovery, domain derivation (`obligation::accepted_domain`, a **dissolved** concept), `summarize_instance` consumption, same-arity domain propagation (marked interim), candidate-to-candidate-only edges | **NON-AUTHORITATIVE** | Not a ready foundation. **Its independently valid SCC utilities (e.g. `scc_reverse_topo`, the reverse-topological order) may be reused.** There is **no** authorized broad replace-and-rebuild project |

**Not quarantined** (trusted): the lexer, parser, desugar, oracle interpreter, normalization harness,
value/interner layer, and the contract algebra including `contract::numeric` + `contract::operation`
(F0), whose soundness is brute-tested against the oracle.

---

## 4. Known analyzer pins — 1 `#[ignore]`d in lib

The one ignore is a **deferred-by-ruling acceptance twin**, not a v1 proof gap; it is not
permission to reintroduce reaching domains, widening, or manufactured witnesses.

| Gate | Current behavior | Actual blocker |
|---|---|---|
| **1b** exact recursive singleton chain — **RE-EXPECTED 2026-08-03 [user]: the deferral stands** | `f(0) → f(1) → 1` rejects as **Unproven, never Refuted** — live and green as the v1-honest expectation (`the_narrow_exact_chain_rejects_unproven_and_the_widened_trap_does_not_refute`). The earlier acceptance expectation was **outside grounding v1's chain license**: the chain varies a *numeric* argument, and GR-10(3) admits flat-sequence varying state only — numeric finite-state walking is the **finite-product extension, deferred by user ruling** (grounding §14; specimens 11/22). See `NEXT-implementation-finding-blocker-1b-v1-scope.md` | the deferred finite-product exact-chain extension. Acceptance activates only if the author stamps it into scope; the `#[ignore]`d twin (`a_the_exact_numeric_chain_accepts_under_the_deferred_extension`) is its gate. The prior "grounding §4 chains" attribution was incomplete — §4's *v1* license never covered this shape |

Resolved by the 2026-08-01 wiring:

- **2b mutual/helper domain change:** the executable program is no longer silently accepted. Global
  discovery reaches the changed-domain dependency, §4a cuts off the repeated shape, and
  safety-unproven blocks at the application seat. The graph verdict is honestly **Unproven**, not
  permanently Refuted: no admitted realized witness has been attached.
- **2a multi-parameter domain change:** likewise no longer a false acceptance. The §5
  positional partition is live; invariant non-measure positions and GR-19's operation-verified
  numeric payload now close without unfolding. Other changed-domain repeated shapes remain
  Unproven and reject. General call-edge-derived domains are still a precision/classification
  gap, not a soundness hole.
- The broad-domain factorial safety and recursive-return tests are live again. Their `Number` fact
  covers `n - 1`; safety now consults the completion cross-claim and return induction instead of
  treating the recursive operand as a false possible fall-through.
- **3 recursive arm fall-through:** released by T2.2. The represented Pure call is realized through
  the bounded oracle, the `ApplicationWitness` survives Match outcome composition, and only the
  enclosing expecting consumer rejects it. The statement-seat counterpart remains accepted.
- Direct tests of the deleted checker were removed with it. They tested implementation internals,
  not stable language IDs; their live application/graph counterparts remain.

Conformance holds 4 `#[ignore]`s: 1 measured Phase-GR coverage gap and 3 author-gated
adoption/world-runner rows. GR-19, GR-26, the split A-VER union-boundary/Indeterminate row,
module/linking rows, M-04, MU-18, GR-30, GR-08, GR-03A, GR-03B and GR-22B are live and green.

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

**Still separate (historical wording corrected 2026-08-08):** blocker 1b is the explicitly
deferred finite-product/numeric exact-chain extension; GR-03B's v1 flat-tuple acyclic fragment is
live. Blocker 3 needs structured completion evidence through the consumer. Neither is a reason to
restore forward reaching domains.

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

## 7. Test baseline (measured 2026-08-08, not inherited)

| Suite | Result |
|---|---|
| `cargo test --lib` | **490 passed, 0 failed, 1 ignored** (the deferred-extension acceptance twin, §4) |
| `cargo test --test conformance` | **261 passed, 0 failed, 4 ignored** in default and serial order (1 measured Phase-GR gap + 3 adoption/world-runner gates) |
| `cargo test --test machinery_gate` | **13 passed, 0 failed** |
| `cargo clippy --all-targets -- -D warnings` | **0 warnings** |
| `cargo fmt --all -- --check` | **PASS** |
| `shasum -c MANIFEST.sha256.txt` | **19/19 OK** |

Earlier counts appearing in other documents (323 / 371 / 377 / 380 / 383 / 384 / 396 / 409 / 413 /
417 / 421 / 424 / 426 / 438 / 439 / 447 / 452 / 455 / 244 / 250 / 473) are
**HISTORICAL**; this table is current.
**Green ≠ complete:** the deferred finite-product extension's acceptance twin, one Phase-GR
coverage target, three author-gated conformance rows, and the staged work recorded elsewhere in
this file remain open.
