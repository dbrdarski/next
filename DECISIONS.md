# DECISIONS.md — NEXT implementation changelog

Provenance discipline (CLAUDE.md § Process): what the specs **mandated**, what I
**chose** where a representation was left open, and what I'm **asking** the author.
Status tags mirror the compendium's vocabulary. Newest entries first.

---

## 2026-07-21 — Tuple family §2: `len` — Λ-semantics with exactness stamps

`src/contract/length.rs` (new) + `recursive::contract_emptiness` + 6 TL cases.
Full suite 225, 0 ignored, clippy clean.

- **`len(group, c) → Len { contract, stamp }`** with `Stamp = Exact | Approx`. The
  soundness law `Λ(T) ⊆ ⟦contract⟧` holds always; `Exact` additionally claims
  `⟦contract⟧ = Λ(T)`, provenly. An **uninhabited shape yields `(Bottom, Exact)`** —
  impossible shapes are never realizable lengths, and this is checked *first*, so it
  governs every other row.
- **Non-recursive rows:** exact tuples/records → `Equals(k)` stamped by the
  inhabitation triage (proven-inhabited → `Exact`; unproven → `Approx`, since an
  unproven shape may be empty); open records → `GE(n)`; `Concat` → the C§7 sum;
  `Union` → the union of branch lengths (`Exact` iff all branches are — the union of
  exact sets is exact). Summation is exact only when **both operands are finite
  exact sets**; a `GE` operand pushes the rule to the minima and stamps `Approx`,
  which is the "approximate *rule*" half of §2's condition, not just approximate
  operands.
- **Recursion — the weighted-graph solver.** SCC members are states; each recursive
  alternative is an edge weighted by its nonrecursive length contribution; base
  alternatives contribute accepting lengths. Achievable sets are saturated to a bound
  **computed in advance** from the finite label sets (Principle 7), then rendered as
  an ultimately-periodic contract: per residue class, the smallest point from which
  the class is complete becomes a `Mod ∩ GE` tail, and anything below stays an
  explicit `Equals` exception.
- **The period is the gcd of CLOSED-WALK weights**, computed by edge potentials
  (`pot[u] + w − pot[v]` per edge), *never* the gcd of individual transition weights.
  TL-19 is the test that separates them: `R = Tuple() | Tuple(E)++S; S = Tuple(E)++R`
  has two weight-1 edges but cycle weight 2, so `Λ(R)` is the evens and `Λ(S)` the
  odds; an edge-gcd of 1 would erase the parity. The test asserts both directions
  (R rejects every odd, S rejects every even).
- **Exactness is forfeited**, dropping to `(GE(minimum), Approx)`, when an
  alternative is **nonlinear** (>1 own-SCC reference — TL-15) or a label falls
  outside the **finite-exact boundary** (TL-22's infinite increment language). Both
  sound.
- **TL cases:** TL-13 `Repeat(Bottom)` → `(Equals(0), Exact)`, never `GE(0)` — the
  recursive branch Bottom-normalizes through `Contract::concat`'s §1 rule, so the
  base alone survives. TL-14 increments {2,3} over {0} → `{0} ∪ [2,∞)` exact, with
  **length 1 unrealizable** (the semigroup gap — the naive "smallest element of the
  residue class" rendering would have wrongly admitted it). TL-19, TL-15, TL-22 as
  above, plus the non-recursive rows.
- **Scope:** §3's refutation discipline (Approx may refute *intersection emptiness*
  by disjoint uppers, but may **never** supply a subcontract refutation witness),
  `restrictLen`/`LengthRestricted` (§3), the alignment procedure (§4), and the
  grapheme seam summaries (§5) are the remaining family pieces. `len` is not yet
  wired into `subcontract`, so no verdict currently depends on a stamp.
- **`// [ask-author]`:** none.

---

## 2026-07-21 — `Concat` + `sourceProgress` (tuple family §1; RC patch 0.2.2)

The algebra prerequisites for the tuple-length family. Full suite 219, 0 ignored,
clippy clean.

- **`Contract::Concat(segments)`** — a tuple that splits into consecutive segments,
  positive in every segment. Smart constructor `Contract::concat(..)` applies §1's
  normal forms: nested Concats **flatten** associatively; the canonical empty-tuple
  segment **erases**; adjacent exact segments **fuse**; and an **uninhabited segment
  never erases** — it Bottom-normalizes the whole Concat, since erasing it would
  turn an empty contract into an inhabited one. Uninhabitance there uses only
  *permanent structural* facts (`structurally_uninhabited`), never temporary
  analysis state, exactly as §1 requires.
- **Membership** is the denotational reference: a backtracking split over
  consecutive windows, with fixed-arity segments consuming exactly their arity. The
  analyzer's alignment procedure (§4) decides the *contract* question without
  enumerating and is a later increment.
- **Recursive layer (RC 0.2.2):**
  - positivity now descends through `Concat` segments;
  - **guardedness**: a `Concat` edge guards a segment when some *sibling* has a
    permanently proven structural minimum length ≥ 1 (`min_extent`) — segment-local,
    so the proof never consults the productivity of the group under admission (the
    non-circularity clause). This is what admits `Repeat`;
  - **`sourceDepth` → `sourceProgress`**, and the subcontract gained an aligned
    `Concat ⊑ Concat` row that carries the source's **consumed extent** as progress
    — flat sequence recursion licenses reuse by what was consumed, not by nesting;
  - group-aware `Concat` membership and inhabitant enumeration (a bare
    `Contract::contains` cannot resolve `Ref`s inside segments).
- **RC-17/18/19 implemented.** RC-17 `Repeat(Number) ⊑ Repeat(Top)` proves *only*
  through consumed-extent progress (the revisited pair closes at advanced progress).
  RC-18 `Repeat(Number) ⊄ Repeat(String)` is refuted with a **complete finite tuple**
  witness `[1]` — asserted to be a whole tuple, not a naked element (§5.3). RC-19's
  mutual Record/Concat cycle terminates and stays inhabited.
- **Scope:** only the *aligned* `Concat ⊑ Concat` case (equal segment counts) is
  decided; the general alignment procedure (§4 forced-boundary peeling over unequal
  counts) lands `unproven` rather than guessing a split. Sound. `len` with its
  `Exact | Approx` stamps (§2) is the next increment.
- **`// [ask-author]`:** none.

---

## 2026-07-21 — CORRECTION: structure interpolation is total (the trap is deleted)

**I implemented a ruling that had already been reversed.** Structure interpolation
was ruled **total [user, 2026-07-18]**; I was working from a stale CLAUDE.md that
still read *"trap, per spec — the print doctrine is deliberately open"*, and this
session I built, defended in conversation, and documented the *opposite* of the
ruling — including telling the author the doctrine was doc-open when it had been
closed three days earlier. Root cause: I trusted the CLAUDE.md snapshot in my
session context instead of re-reading the file from disk. Full suite 212, clippy
clean.

Authority: compendium 1.0.8 — *"Structure interpolation is total: every value
renders — Tuple/Record as canonical literal forms (sorted-key records; inner
strings quoted), `<Function>`, `<Indeterminate _/0>`/`<Indeterminate 0/0>` (the
form, never operands); literal-formed values round-trip (parse ∘ print = identity,
a harness law); angle-bracket forms are visibly non-parseable."* Test-suite spec
line 57 makes the deletion explicit: *"The former fourteenth class,
unprintable-interpolation, is deleted."*

- **Oracle `stringify` is now total** (`render_value`): Tuple → `[a, b]`; Record →
  `{k: v}` **sorted by key**; nested Strings quoted and JS-escaped while a
  *top-level* String interpolates raw; Numbers via B2; `<Function>` for closures and
  natives; `<Indeterminate _/0>`/`<Indeterminate 0/0>` — the **form only**, so `1/0`
  and `2/0` are indistinguishable (interning forbids remembering operands, PR-04).
- **`TrapClass::UnprintableInterpolation` removed.** Thirteen classes remain,
  bijective with suite T-01…T-14 (the ID range is stable; one case superseded —
  "never delete a case").
- **Analyzer `analyze_template`**: the printability demand is gone entirely — a
  template always yields `Kind(String)` and carries **no** finding. Interpolations
  remain expecting seats, so a genuinely trapping subexpression still reports.
  Deleted the now-dead `Printability`/`printable_value`/`printability`/`union`
  helpers.
- **Suite PR-01…05 implemented** as named cases. PR-05 (parse ∘ print = identity)
  initially failed for a methodological reason worth recording: `run_program_value`
  builds a **fresh interner per call**, so comparing values across two calls by
  pointer is meaningless. Added `eval_in(interner, src)` so the original, its
  rendering, and the re-parse all share one interner — then the law is the pointer
  test it should be. Also: `;` is not a statement separator (L1 — newline-separated).
- **`OwedItems.md` rewritten** against C§17 patch 1.0.8: every item it previously
  listed has been discharged by the author (tuple family and application/induction
  now **specified**; print doctrine **ruled**; arrow contract **superseded** by
  `AnalysisContract`). It now indexes what C§17 still owes.

---

## 2026-07-21 — Named contracts: static contract-expression evaluation (C§12.2) + patterns

`src/contract/expr.rs` (new) + a `ContractEnv` threaded through the analyzer + 5
tests. Full suite 209, 0 ignored, clippy clean.

- **Contract expressions are statically evaluated (C§12.2 / §292).** Contract
  constructors are predeclared prelude *names* and a named contract is an ordinary
  binding of a contract expression (`Percent = Range(0, 100)`), so
  `eval_contract(expr, env) → Option<Contract>` interprets a kernel `Expr`:
  constructor applications (`Range`/`Greater`/`GreaterEq`/`Less`/`LessEq`/`Mod`/
  `Geo`/`Equals`/`HasField`/`Union`/`Intersection`/`Difference`/`Tuple`), prelude
  names (the seven Kinds, `Top`, `Bottom`, and the `Failure` shape), **structural
  literals** (a tuple literal of contracts is a tuple contract; a record literal is
  a record contract), and references to already-bound named contracts.
  `build_contract_env` folds a sequence of `name = contract-expression` bindings
  into a [`ContractEnv`], so later contracts compose earlier ones
  (`Grade = Union(Percent, Null)`).
- **One resolution path.** The analyzer's `contract_ref` (contract-as-pattern, E9)
  now *delegates to* `eval_contract`, so patterns and contract expressions agree by
  construction rather than by two hand-kept name tables.
- **Threaded through the analyzer.** Every `analyze_*` now carries
  `cenv: &ContractEnv` beside the value-level `TypeEnv`, so a user contract resolves
  wherever a pattern appears — including nested `Match`es inside operands.
- **The payoff, tested with controls:** `Percent = Range(0, 100)` now (a) *narrows*
  an arm — `match x { Percent => … }` with `x : Number` is correctly **not
  exhaustive** (an unresolved name would widen to `Top` and wrongly look total), and
  (b) *refutes* a destructuring bind — `Percent = 500` is a `refuted-binding` error.
  Both tests assert the empty-env control behaves oppositely, so they prove
  resolution actually happens rather than passing vacuously.
- **Scope (implementation-owed, not doc-owed):** **recursive/mutual source
  contracts** — a named contract referencing itself or its group — do not yet build
  a `RecGroup`; a self/forward reference simply fails to resolve (`None` → `Top`, no
  narrowing; sound). The C§9 machinery it would feed is already implemented and
  green; wiring source → `RecGroup` is my next increment. Numeric/string constructor
  arguments must be literals; statically evaluating *computed* contract arguments is
  the remaining C§12.2 surface.
- **`// [ask-author]`:** none.

---

## 2026-07-20 — Analyzer: `Apply` (C§7 / B5 / E10 — application)

`src/analyzer/mod.rs` `analyze_apply` + a Tuple-arity disjoint rule + 2 tests and
closed `Apply` concordance rows. Full suite 204, 0 ignored, clippy clean.

- **Closed calls fold exactly.** Known callee value (`Equals(closure/native)`) plus
  singleton plain args → reconstruct `Apply(Const, [Const…])` and run `eval_expr`,
  predicting world-admission / argument-obligation / spread-kind / not-a-function /
  expecting-seat exactly. Corpus gained an identity call (produces), an arity
  mismatch (argument-obligation), a non-function callee (operation-safety), an
  Effect call in the pure world (world-admission), and a non-Tuple spread
  (spread-kind).
- **Open calls, reasoned:** each `Spread` arg must be `⊑ Kind(Tuple)` (else
  spread-kind error / warning); a callee provably disjoint from `Kind(Function)` is
  operation-safety; and when the callee value is **known** (`Equals`), its act-kind
  is admission-checked and the argument tuple `Tuple([arg contracts])` is checked
  against `pattern_contract(params)` (argument-obligation, reusing the `Match`
  pattern machinery). A mutator callee `may_complete` (returns discarded).
- **World context = pure** (matching the `eval_expr` truth source). World threading
  and `Lambda`-body / function-shape analysis (C§13.2) are later increments, so:
  an **open** call's *return* types as `Top`, an unknown callee's act-kind/arg
  obligation is **not** checked (Unproven, silent), and a `Pure`/`Effect` body's
  completion is not derived (`may_complete = false` for non-mutators). All sound —
  no false accept in the tested pure-world concordance; the gaps are the honest
  cost of not yet analyzing function bodies.
- **C.2 rule added:** `Tuple(pa) ⌢ Tuple(pb)` disjoint when arities differ or any
  position is disjoint — the basis of the arity-mismatch argument-obligation.
- **`// [ask-author]`:** none.
- **Provenance correction (the deferred pieces are doc-owed, not merely
  unimplemented).** Unlike `Access`/`Match` (decided design, sequenced by me), the
  *deep* `Apply` deferrals rest on genuine **C§17 Owed** items now recorded in
  `OwedItems.md` §3–§4: the **`analyzeOperation` application table** (the app rule's
  admission + expecting-seat demand — owed verbatim), **domain-indexed return
  induction** details + the **instance / global-fact-graph** machinery (open-call
  return + body completion), and the absence of a **first-class function-shape
  (arrow) contract** (unknown-callee reasoning). What *was* decided and so
  implemented: the B5 admission matrix, argument-obligation as a parameter-pattern
  match, spread-kind, and the closed-fold technique.

---

## 2026-07-20 — Analyzer: `Match` (E9/E10 — the sole control node)

`src/analyzer/mod.rs` `analyze_match` + pattern machinery + `Analysis.may_complete`
+ expecting-seat demands + 4 tests and closed `Match` concordance rows. Full suite
202, 0 ignored, clippy clean.

- **Arm narrowing (E9).** Each arm narrows the scrutinee by its pattern —
  `pattern_contract` maps a `Pat` to a *superset* of its match set (sound for
  intersection): `Const → Equals`, `Wild`/`Bind → Top`, exact `Tuple`/`Record` →
  the structural contract, open record → `∩ HasField`, `Contract(ref)` → the prelude
  Kind (user contracts owed → `Top`). The arm body sees `remainder ∩ pattern`, and
  the **remainder** for later items is the accumulated Difference; a covering
  pattern (`remainder ⊑ pattern`) empties it. `bind_pattern` threads the narrowed
  contract to the pattern's names (e.g. `[a, b]` on `Tuple([Number, Number])` gives
  `a, b : Number`, proving `a + b` safe).
- **tested-seat (E10).** A guard must be `⊑ Boolean` — else error (provably
  non-Boolean) or warning.
- **refuted-binding (E9).** A destructuring `Bind` must be irrefutable
  (`value ⊑ pattern`) — else error (disjoint) or warning.
- **expecting-seat (E10) via `Analysis.may_complete`.** A `Match` whose remainder
  is not provably empty may complete without a value; the new `demand(...)` helper,
  called at every value-demanding seat (operands, elements, field values, template
  interpolations, access receiver/index/bounds, bind RHS, guard, arm result,
  scrutinee), turns that into an expecting-seat error. Statements are *not*
  expecting seats. A standalone non-exhaustive `Match` is fine (it just completes
  without a value); the error is only at a demanding seat — matching the oracle.
- **Result contract** = union of arm results (`Top` for an arm-less match).
- **Closed `Match` folds are not needed for exactness** — the structural reasoning
  already predicts the trap classes; the concordance corpus gained `match 5 {5=>10}`
  (produces), a non-Boolean guard (tested-seat), a non-exhaustive match in an
  operand (expecting-seat), and a refuted destructuring (refuted-binding), all
  agreeing with `eval_expr`.
- **Owed within `Match`:** `Pat::Contract` to a *user* contract resolves to `Top`
  (no narrowing) until a named-contract environment exists; tuple-rest / record-rest
  patterns widen (length ← C§17). Both sound (no false accept). `// [ask-author]`:
  none.

---

## 2026-07-20 — Analyzer: access demands (E6 — Field / Index / Slice)

`src/analyzer/mod.rs` `analyze_access` + supporting C.2 disjointness rules + 2
tests (closed access rows in the concordance corpus; open field reasoning). Full
suite 198, 0 ignored, clippy clean.

- **`Access(target, form, total)` (E6).** The demand form (`total = false`) must
  prove the receiver non-null and the field present / index in bounds; the total
  form (`?.`) totalizes null/absent/out-of-bounds to `null` and never traps on
  those; slices are clamped-total on the window but still demand a sliceable
  receiver and integer bounds.
- **Closed accesses are exact.** When the receiver (and any bound) is a singleton,
  `analyze_access` reconstructs a `Const`-childed node and runs the oracle's own
  `eval_expr` — predicting NullReceiver / AbsentField / IndexBounds /
  OperationSafety(slice) exactly. Added to the concordance corpus (field present /
  absent / null-receiver / `?.` totalization / tuple index in-bounds / out-of-bounds
  / from-end / totalized).
- **Field access fully reasoned on open receivers.** `⊑ HasField(name)` → accept
  (output = the field's contract when the receiver is an exact `Record`); `?.` →
  accept (result `∪ Null`); provably-disjoint from `HasField(name)` → **error**
  (NullReceiver if the receiver can be null, else AbsentField); otherwise a warning.
- **Index/Slice bounds are owed (C§17).** Open index/slice out-of-fold cases catch
  a provably-null receiver as an error, but otherwise emit a **warning** — bounds
  reasoning needs the tuple-length family, tracked in `OwedItems.md` (C§17 owed).
  Honest: not silently accepted.
- **C.2 disjointness rules this needed (added + soundness-tested):** a non-Record
  kind ⌢ `Record`/`HasField`; a non-Tuple kind ⌢ `Tuple`; an exact `Record` lacking
  field `k` ⌢ `HasField(k)`. New `contract::disjoint` public wrapper + a
  `disjoint_soundness` sweep (no provably-disjoint pair shares a pool value).
- **`// [ask-author]`:** none.

---

## 2026-07-20 — Analyzer (Part D begins): pure-fragment contract inference + §6 concordance

`src/analyzer/mod.rs` (new) + `oracle::eval_expr` (exposed) + 7 tests incl. the
exact concordance sweep and an open-term soundness sweep. Full suite 194, 0
ignored, clippy clean. This is the first analysis pass over kernel AST — legitimate
now that the oracle, normalization harness, and contracts C.1–C.3/C§9 are green
(CLAUDE.md hard rule 1).

- **`analyze(expr, env, interner) → Analysis { contract, findings }`.** Infers a
  contract over-approximating the produced value and gathers `Finding`s tagged with
  the oracle `TrapClass` they mirror (§6). `Severity::Error` = proven-to-trap (a
  rejection); `Severity::Warning` = unproven-safe (surfaced, not a rejection).
  `Analysis::accepted()` = no error findings.
- **The §6 concordance made executable.** For each `PrimOp`, findings come from the
  contract layer: constant-fold when every operand is `Equals(v)` — run the oracle's
  own `eval_prim`, so a closed expression's trap **class is predicted exactly**;
  otherwise `analyze_operation` (C.3), with `Refuted(witness)` → an error whose class
  is read back from the oracle trapping on that witness, and `Unproven` → a warning.
- **Why constant-fold (not just `analyze_operation`):** `analyze_operation` outputs
  `Kind(Number)` for `Add(Equals,Equals)`, which loses exactness — e.g. `(2+3)^-1`
  would then sample `0` and *falsely* report a `0^neg` trap. Folding keeps
  `(2+3) → Equals(5)`, so nested closed expressions predict traps exactly and match
  the oracle. This is the analyzer doing partial evaluation on constants.
- **Truth-sourced brute-test.** Exposed `oracle::eval_expr` (evaluate a closed
  kernel expr, pure world, empty env). The concordance test runs a corpus of closed
  expressions through both: `oracle traps ⇔ analyzer errors`, and the classes agree
  (covers `OperationSafety`, `UndischargedIndeterminate`, division totality, `0^neg`,
  non-integer exponent, Indeterminate propagation, nested/tuple/record). An
  open-term test confirms the soundness direction: an *accepted* expression over a
  variable's contract never traps on sampled admitted values.
- **Scope (this increment):** the pure expression fragment — `Const`, `Ref` (against
  a `TypeEnv`; unbound → `UnboundEvaluation` error), `PrimOp`, `TupleCons`,
  `RecordCons`, plus `Template` (added below). Next: access demands (E6 →
  Null/AbsentField/IndexBounds), then `Match`, then application.

- **Provenance of the not-yet-checked nodes (the honest three-way split).** The
  remaining nodes are *not* a single "documented gap"; there are three distinct
  statuses:
  1. **Design decided, implementation owed by me** (an increment boundary, not a
     spec gap): `Access` (E6 demands), `Match` (E9/E10: tested-seat, refuted-binding,
     expecting-seat, arm narrowing via accumulated Difference), `Apply`
     (`analyzeOperation(application)` — argument-obligation, world admission B5,
     expecting-seat, spread-kind), `Write`/worlds (B5 matrix; mutator return-nothing).
     The docs pin these; I simply haven't built them. They type as `Top`, unchecked.
  2. **Doc-owed contract family**: `TupleCons`/`RecordCons` *spread* and
     *tuple-length/concatenation* lean on **C§17 (owed)**; my `Top` for spread shapes
     is backed by a genuine open in the spec.
  3. **Doc-open (E11 print doctrine)**: `Template` structure interpolation is
     *trap-until-ruled* — the correct behavior is to **reject**, not accept.

- **`Template` implemented (correcting the earlier `Top`-as-accept).** Typing
  `Template` as `Top` silently *accepted* structure interpolation — an unsound
  acceptance against E11 (the oracle already traps `UnprintableInterpolation`). Now
  `analyze_template` demands printability per interpolation, mirroring the oracle's
  `stringify` (String/Number/Boolean/Null print; structures + Indeterminate trap):
  singleton → exact; `⊑ {String,Number,Boolean,Null}` → accept; provably a
  structure (`⊑ Kind(Tuple)∪Kind(Record)∪Kind(Function)`, or an `Indeterminate`) →
  **error**; otherwise → warning. Template's result contract is `Kind(String)`.
  Added to the closed-expression concordance corpus (printable + structure cases).
- **C.2 gap this surfaced (fixed):** subcontract lacked "a structured contract
  inhabits its kind" — added `Tuple(_) ⊑ Kind(Tuple)` and
  `Record(_) | HasField(_) ⊑ Kind(Record)` to `atom_provable`, and extended the C.2
  soundness sweep with `Kind(Tuple)`, `Kind(Record)`, a `Tuple([Number])` contract,
  and tuple values. (Numeric atoms already had `⊑ Kind(Number)`; this closes the
  structural analogue.)
- **`// [ask-author]`:** none — the `Template` behavior follows E11's stated
  "trap until ruled"; when the print doctrine is ruled, only `analyze_template`'s
  accept/reject boundary moves.

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

## 2026-07-20 — Contracts C§9: recursive contracts (admissibility, emptiness, subcontract)

`src/contract/recursive.rs` (new) + `Contract::Ref` + 10 RC tests. Recursive
Contracts Specification v0.2 (patch 0.2.1). Full suite 184, 0 ignored, clippy clean.

A recursive contract is a named binding in a `RecGroup` referencing itself/its
mutual group via `Contract::Ref`. Four subsystems, all over the finite canonical
graph (never a materialized unfolding, §4):

- **Admissibility (§1) → `admissible`, `DefError`.** Positivity by a polarity walk
  (`Difference(B,E)` flips E; a group reference at negative polarity → definition
  error) and structural guardedness by an unguarded-reachability graph (a reference
  reachable without crossing a `Tuple`/`Record` constructor; any cycle → error).
  RC-09 `Bad = Difference(Top, Bad)` rejected (negative); RC-10 `R = R` and
  `R = Union(Number, R)` rejected (unguarded, the latter with the "denotes Number"
  hint).
- **Membership (§3) → `contains`.** Inductive: `Ref`s resolve to definitions and the
  value strictly shrinks at each structural descent, so on admissible groups it
  terminates over finite acyclic data.
- **Emptiness (§6) → `emptiness` : bounded productivity closure.** Two monotone
  passes over the group's finite state space (each state flips at most once — no
  iteration budget, Principle 7): (1) *productivity* seeds inhabited leaves and
  flips a name when a `Union` branch / all `Tuple`·`Record` components / a resolved
  `Ref` become productive, **storing a finite witness at each flip**; (2)
  *exactness* marks the still-unproductive names `Empty` unless they depend on an
  opaque leaf (→ `Unproven`). RC-11 flagship `Record({next: R})` empty; RC-12 mutual
  `A/B` both non-empty with witnesses `{b: null}` / `null`; RC-13 mutual `A/B` both
  empty; RC-15 opaque `Kind(Function)` leaf → emptiness stays `Unproven`.
- **Subcontract (§5) → `subcontract` : progress-guarded pair induction.** Empty-source
  short-circuit (step 0) via the emptiness env; a per-pair **depth-stamped** hypothesis
  that closes a revisit as *holds* only at strictly greater source depth (a global
  progress flag would be non-conforming, RC-16); source depth increments only on
  `Tuple`/`Record` descent; `Ref` heads resolve without incrementing (μ-traversal);
  ordinary constructor rows otherwise; leaf pairs delegate to the C.2 check. RC-11
  `μR.Record({next:R}) ⊑ Number` **proven** via the empty source (v0.1 would have
  wrongly refuted); `NumList ⊑ AnyList` proven by closing the revisited tail-pair at
  greater depth. Soundness spot-checked against `contains`.

- **`Contract::Ref` added** to the core enum; bare (no ambient group) it denotes
  nothing — `contains` is `false`, `sample` empty — so non-recursive code is
  unaffected and recursive code resolves references first.

- **`// [ask-author]`:** none.

### Follow-up (same day) — the two owed rows closed

- **RC-14 recursive-`Intersection` emptiness over the finite product graph** is now
  built (`intersection_emptiness`/`inter`): product states are pairs `(a, b)`,
  Unions distribute, `Record`/`Tuple` descend into paired components, `Equals`
  decides exactly by membership, `Ref` pairs form product states cut on revisit
  (the least fixpoint — an intersection inhabited only *through* a cycle has no
  finite witness, so is empty), and leaf pairs bottom out in the C.2 `disjoint`
  check plus a sampled common witness. Wired into both `prod_eval` (witness) and
  `exact_eval` (voice). Tests: two individually-inhabited recursive contracts whose
  intersection is non-empty (shared base `1`) and empty (disjoint bases `1`/`2`).
- **§5.3 witness-assembled refutation** is now built: after a failed proof,
  `refute` enumerates finite inhabitants of the source at increasing unfolding
  depth (`REFUTE_DEPTH = 4`, a bounded search — no proof is ever capped) and returns
  the first re-verified `w ∈ ⟦A⟧ ∖ ⟦B⟧`. Sound (every witness re-checked), and
  empty sources yield no inhabitants so are never wrongly refuted (they short-circuit
  to `Proven` at step 0 first). Test: `NumList ⊄ StrList` refuted with a concrete
  number-list witness.
- **Remaining bounded-ness (sound, incomplete):** the refutation search and the
  leaf-pair witness sampling are depth/fan-out bounded, so a counterexample that
  only appears deeper than the bound stays `Unproven` rather than `Refuted`. No
  proof path is bounded. `// [ask-author]`: none.

---

## 2026-07-20 — Contracts C.3: operation transfer rules (`analyze_operation`)

`src/contract/operation.rs` (new) + `oracle::eval_prim` (exposed) + 5 tests incl.
an operation × input-grid soundness sweep. Compendium C§7 / C§16 obligation 3.
Full suite 174, 0 ignored, clippy clean.

- **`analyze_operation(op, [C₁…Cₙ]) → { safety, output }`** — the one uniform rule
  shape the spec mandates for every primop.
  - **`safety: OpSafety`** = `Proven` / `Refuted(witness tuple)` / `Unproven` — a
    subcontract carrying an *n-ary* witness. Proof side discharges the op's demand
    via C.2 `subcontract` (`+` wants two Numbers **or** two Strings; `- * / % < <=
    > >=` want two Numbers; `^` wants an integer exponent and no `0`-to-a-negative;
    `== !=` never trap). Refutation samples operand tuples and asks the **oracle**
    (`eval_prim`) whether they trap — the witness genuinely halts.
  - **`output: Contract`** over-approximates the image. Interval arithmetic where
    clean (`Range+Range`, `Range−Range`, `Range·Range` corner products, negation
    flips bounds), `Kind(Number)`/`Kind(Boolean)` otherwise.
- **Oracle as truth source:** extracted the value-level primop dispatch into
  `Oracle::apply_prim` and exposed `oracle::eval_prim(op, args, interner)`. The
  sweep runs every op over an input-contract grid, samples operand tuples, and
  checks: `Ok(v) ⇒ output.contains(v)` (no image escape), `Err ⇒ safety ≠ Proven`,
  and every `Refuted(w)` actually traps. This is Part I's "brute-forced per-rule
  against the oracle" applied to operations.
- **Two totality/passthrough subtleties made explicit** (both mandated by the
  semantics companion, surfaced by the sweep):
  1. **Division is total** — a `0` divisor yields `Indeterminate`, *not* a trap. So
     `/` and `%` are safety-`Proven` on any two Numbers, and the output unions in
     `Indeterminate(_/0)`/`(0/0)` exactly when `0 ∈ ⟦divisor⟧` (decided by
     `contains`).
  2. **Arithmetic passes an Indeterminate operand through unchanged** — so when any
     operand contract can contain an Indeterminate, the image includes that form
     (`with_indet_passthrough`). Without this the sweep caught `Add(Top,Top)` on an
     Indeterminate operand escaping a `Number∪String` output.
- **Known incompleteness → `Unproven`** (sound): non-interval numeric outputs fall
  back to `Kind(Number)`; `Pow` output is `Kind(Number)`; demands that C.2 can't
  yet prove (e.g. integer-exponent on a `Range`) yield `Unproven` unless a sampled
  tuple traps.
- **`// [ask-author]`:** none.

---

## 2026-07-20 — Contracts C.2: three-valued subcontract `A ⊑ B`

`src/contract/subcontract.rs` (new) + tests. Compendium C§8. 7 subcontract seeds
incl. an O(n²) soundness sweep; full suite 169, 0 ignored, clippy clean.

- **`subcontract(A, B) → Verdict`**: `Proven` (`⟦A⟧ ⊆ ⟦B⟧`), `Refuted(witness ∈
  ⟦A⟧ \ ⟦B⟧)`, or `Unproven`. Soundness is the invariant.
- **Proof side (sound):** structural rules — `A\E ⊑ B` from `A ⊑ B`; `A ⊑ B∩C` iff
  both; `A∪B ⊑ C` iff both; `A ⊑ B\E` iff `A ⊑ B` and `A ⌢ E` disjoint; the
  sound-but-incomplete "or" rules (`A ⊑ B∪C`, `A∩B ⊑ C`). Atom rules: `Kind`
  equality, numeric-atom ⊑ `Kind(Number)`, `Mod` lattice (`n2|n1` ∧ `r1≡r2 mod
  n2`), exact `Record` fieldwise, `Tuple` positional, `Equals(v)` via membership,
  and **interval containment with intersection meet** — so landing zones
  (`Intersection(Greater(T), LessEq(T+d))`, C§4) prove.
- **Refutation side (sound):** sample members of `A` and return the first that
  fails `B`. Interval sampling includes a **fractional near-bound point** (the
  rationals are dense, so a half-step witnesses gaps integer steps miss).
- **Brute-tested against membership** (the truth source): over a contract × contract
  sweep with a diverse value pool, every `Proven` has no counterexample in the pool
  and every `Refuted(w)` has `w ∈ ⟦A⟧ \ ⟦B⟧`. This is Part I's "per-pair rules
  brute-tested against the oracle."
- **Two dense-rationals subtleties surfaced** (my test expectations, not the
  checker): over rationals `(10,20] ⊄ [11,20]` (10.5 is the gap), and the
  landing-zone containment needs the interval *meet* (the conjunct-wise or-rule is
  incomplete). Both fixed — the checker was right.
- **Known incompleteness → `Unproven`** (never guessed): `Geo` subcontract rows,
  non-interval intersections/unions beyond the or-rules, and recursion. **Recursive
  contracts (C§9)** are the next layer, built directly on this pair-check as the
  progress-guarded induction (recursive-contracts spec §5).
- **`// [ask-author]`:** none.

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
