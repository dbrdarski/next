# Open decisions — author briefing, 2026-08-05

Compiled from: the in-code `// [ask-author]` markers, the conformance/lib ignore registers,
the completion plan's policy gates, the compendium's Principle 9 annotation, the handover
threads, and the session DECISIONS log. Three groups: **A** — decisions waiting on you;
**B** — items you already ruled deferred (listed so reopening is a choice, not an accident);
**C** — owed implementation work that needs no ruling.

---

## Group A — decisions actively waiting on you

### A1. The fueled refutation sampler — **OPEN. No ruling exists.**
**Provenance correction [same day]:** the sampler *was closed in the implementation* on
2026-08-05 — but that was my act during the discussion, on an inferred ruling the author
never issued ("a question is not a permission to change"). The author has neither
ratified nor reverted it; the de-facto state is recorded here so the eventual ruling is
made with full knowledge. What the unauthorized change did:
`realized_refutation` returns no witness (false return claims land the honest Unproven
voice — still rejections at their seats); `realized_completion` is rebuilt as a
**structural, non-executing derivation** (proven-member points + the instantiated row
walk — pattern membership is decidable, nothing runs), so every completion-soundness pin
holds. Four return-claim pins re-recorded with revocation notes. The decision space
the author actually holds: ratify the closure; restore the sampler under an explicit
machine-limit ruling; adopt a fuel-free procedure (evaluate only under a certificate
carrying a proven concrete bound — decline to run, never truncate); or separate the
verdict path (never evaluates) from diagnostic enrichment (a best-effort concrete
example computed after the verdict, unable to change it).

#### (original text, superseded)
**What it is.** During analysis, when a claim cannot be settled symbolically, the sampler
takes candidate inputs *from the program's own written arguments* (never synthesized), runs
them through a **fueled** oracle (200k steps, depth 48), and — only if a run **completes** —
uses the result as a realized witness. `OutOfFuel`/depth exhaustion mint nothing.
**Example.** `f where (Number) => Range(0, 10)` with `f = (n) => n * 2` and a call `f(30)`:
running the written argument 30 gives 60 — a completed run refuting the return claim with a
real witness. No symbolic reasoning needed.
**Why it's on your desk.** Your architecture forbids fuel as a semantic device; the sampler
uses fuel as a *machine bound* on a *witness hunt*. You asked whether that procedure shape is
legitimate at all. Options recorded:
- **(a) delete the sampler** — lose realized-witness refutations the algebra can't reach;
  those verdicts fall back to honest Unproven (rejections under the stamp, but with weaker
  diagnostics — "cannot prove" instead of "here is the counterexample").
- **(b) run only proven-grounded inputs** — no fuel needed (termination already proven for
  that input), fully clean; the sampler loses exactly the cases where grounding is unproven,
  keeping most of its value (written arguments to accepted calls are usually grounded).
- **(c) keep as-is with an explicit machine-limit ruling** — fuel stays, stamped as physics
  (the Principle 9 trap clause vocabulary), never semantics.
**My read:** (b) is the principled middle — it derives the sampler's license from an
already-proven fact instead of a budget.

### A2. **RULED [user, 2026-08-05]: walk-from-Top confirmed.** Marker converted in code.

#### (original text, superseded)
**What happened.** RT §4 mandates the unreachable-branch error for arms that are
"source-domain-empty after consumption over the function's whole parameter domain." I first
walked from the `where` domain; **your recovered grid refuted that reading**: the `Strict`
factorial (`where (Strict)`, Strict = integers ≥ 1, guard `n == 0`) has its base arm empty
over the *entry* contract but reached by the internal `f(n-1)` — entry contracts bound
callers, not the function. The committed walk runs from `Top`: only **prior arms' certain
consumption** can kill an arm.
**Example that errors:** `x :: { Number => 1  Number => 2 }` (arm 2 consumed by arm 1, dead
under every domain). **Example that stays silent:** the grid factorial; and `{ Number => 1
String => 2 }` under `where (Number)` (declared-domain narrowing is non-selection, not
deadness).
**Decision:** confirm the walk-from-Top reading (marker at `src/analyzer/program.rs`).

### A3. **RULED [user, 2026-08-05]: the borrowing is blessed.** Both markers converted.

#### (original text, superseded)
The §6 trap catalog is closed, and two static-only diagnostics had no row, so they borrow:
- The **unreachable-branch error** reuses `TrapClass::ExpectingSeat` (the E9/E10
  match-coverage family).
- A **malformed `where`** (unknown name, arity mismatch, un-evaluable contract expression)
  reuses `ArgumentObligation`.
**Decision:** bless the borrowing (message text carries identity — the definition-error
precedent), or mint a dedicated static-diagnostic class outside the trap concordance. The
second is cleaner taxonomy but touches the closed catalog's periphery, so it's yours.

### A4. **PARTIALLY RULED [user, 2026-08-05]:** pick (2) — the acknowledgment mechanism
is **allowed, for unproven recursion only** (never refuted recursion, never safety). The
surface spelling stays a reserved statute for its own session; nothing is implementable
until it is spelled. Pick (3) — the [permanent] family — still open (see the chat
explanation of what it decides).

#### (original text, superseded)
The rejection polarity is stamped and implemented (unproven grounding = error; the A-NEG
battery runs on it). The compendium's annotation leaves two picks:
- **(2) hard vs acknowledgeable:** does the gray-acknowledgment mechanism survive as
  **opt-in per-site consent** (an author writes an explicit acknowledgment and the site
  compiles-with-warning), or die entirely (total pure/mutation worlds — what is implemented
  today)? Example: a numeric search loop you *know* terminates but v1 can't prove — today it
  simply rejects; under acknowledgeable, `@acknowledge`-style consent (spelling reserved)
  would compile it warned. **Grounding only — never safety** (your standing constraint).
- **(3) the [permanent] gray family:** cross-orbit Diophantine and kin (collatz outside
  proven basins) — permanently **rejected**, accepted as the language's stance? Today they
  reject; this pick makes that *permanent doctrine* rather than v1 coverage.

### A5. Uncalled proven-unsafe body — **RULED [user, 2026-08-05]: warning/lint domain.**
Implemented same day (`uncalled_unsafe_lints` + three conformance pins): an unreferenced
function with a body proven to trap gets a definition-site **Warning** — never rejects,
never silent; referenced functions keep their seats' blocking judgment.

### A6. F0 Q1 — the union rule in operation images: hull · distribution · **laziness**
**Reframed 2026-08-05 under measurement. The earlier entry called this "purely a
precision/cost dial"; that was wrong in the direction that matters** — the hull does not
merely blur, it **manufactures values the program cannot produce and then rejects correct
programs for not handling them.** Measured: `hull.next` is total over its declared domain
and runs, yet the hull rejects it (E10 completion) while the same file under distribution
checks `ok`. Exact rationals make this categorical: once a finite set becomes an interval it
is dense, and no finite number of point rows can ever consume it again.

Three candidates now, not two:

1. **Interval hull (implemented).** Flatten each operand to its numeric envelope, apply the
   rule to the envelopes. Constant cost; destroys the set. `{1,2} * 2` →
   `Intersection(Range(2,4), Mod{2,0})` — note it *keeps parity*, so the information isn't
   lost so much as moved into a form the emptiness check cannot discharge.
2. **Distribution.** Apply the rule per combination of operand alternatives and join.
   Exact; arm count is the running product of the choice counts along a chain. Measured on
   a six-step pricing chain: ~72 arms, 146 rule applications, no verdict change — cheap
   there, unbounded in principle.
3. **Laziness — the held image [new, 2026-08-06].** Commit to neither at the operation:
   bind the result to a *suspended* image and let the **consuming seat** choose. A safety
   demand or a `⊑ Number` return check is answered from the cheap coarse form; a region
   walk dispatching on the value forces the exact product, and only there. Modelled on
   region-table §8's parked held-relation suspension ("analyze the suspension, don't expand
   it"), and it fits the existing shape: `AnalysisContract` is already contract + analyzer
   metadata, so the coarse answer stays in the interned canonical contract while the
   suspension rides in metadata — never a `Contract`, never interned, canonicalization
   untouched. The forcing rule falls out of the over-approximation asymmetry and is
   RT-14's discipline under another name: a **`Proven`** answer from the coarse form
   stands; **`Refuted`/`Unproven`** must force and re-ask.

**Why (3) is attractive:** it dissolves the dial. Options 1 and 2 need a global precision
level (and a hybrid needs an `N`); the held image lets the program's own structure decide
where exactness is paid for — nothing is computed for values nothing interrogates.

**Why (3) might not survive:** the fact cache keys on contracts, so a value coarse at one
seat and forced at another could key differently or settle twice. Memo-key completeness is
a failure this project has already had once; that interaction would have to be settled
*before* any implementation, not after. Order-independence (AP-10) and keeping the
forcing-consumer list closed are the other two open questions.

**Adjacent, independent, additive:** the emptiness check cannot enumerate a bounded
arithmetic progression (`Range ∧ Mod` denotes a finite set). Fixing that helps user-written
bounded integer contracts on its own — but it only recovers exactness where the hull was
*accidentally* exact (`{1,2,5} * 2` still fails), so it is not a substitute for the rule
choice.

Full record, both programs, traces, cost data, corrections, and the reproduction recipe:
`HANDOVER-hull-vs-distribution-2026-08-05.md` (Thread D in `OwedItems.md` §5).

### A7. **RULED [user, 2026-08-05]: extend — LANDED 2026-08-07.** `where` attaches to a
binding proven to hold an exact function value (`c = makeCounter(5)`). Resolution is scoped
to names a `where` mentions; pinned as conformance `where_on_products`.

#### (original text, superseded)
`c = makeCounter(5)` then `c where (Number) => Number` — errors today ("names no function
binding"): the `where` pre-pass resolves module **function bindings** only. The instance
machinery (RT-09) can already analyze the product; this is purely a *surface* decision —
may `where` attach to any binding proven to hold an exact function value, or only to
module-level function definitions?

### A8. Exported slots in check mode (MOD-03 residue)
Runtime linking installs an exported `@state` slot **itself** into the consumer (shared
store). Check-mode project analysis has no runtime store, so an exported slot has no scope
binding to harvest — imports of slots analyze coarse today. Decision: what does check mode
*claim* about an imported slot (its declared contract? Top? a dedicated slot-shape)?

### A9. **RULED [user, 2026-08-06]: `points` yields Strings, `units` yields Numbers — the
two views deliberately differ.** Landed same day: every code point is a well-formed String,
so a point compares and matches directly (`String.points("héllo")[1] == "é"`); a lone
surrogate half is not a String and E8 forbids minting one, so `units` stays Numbers
(`String.units("👋")` → `[55357, 56395]`). Marker in `harness.rs` converted; pinned as
conformance `s02b_points_are_strings_units_are_numbers`.

### A10. The two Part-D adoption gates (the last suite ignores besides the runner stub)
- **A-ACC contract-claim layer:** the Recursion/UniformFamily foresight battery — builder,
  map, reverse, zip, rotate with claims like `r.next⁷.top ⊑ Equals("y")`.
- **A-WRK grids 8–9:** makeLinkedList, pairUp ×3, rotate.
Both are expectation-only stubs until you open the **Part D families adoption** gate (D§9).
Opening it is a design adoption (the uniform-family contract layer), not an implementation
choice.

### A11. The small surface set (from the plan's policy gates, all unruled)
- **Literal parameter patterns** — `f = (0) => …` in parameter seats (pins are arm-only
  today).
- **Mutator returns** — current law return-nothing (implemented); your recorded leaning
  toward returns is an extension point awaiting a stamp.
- **Module dot-nesting** — `module a.b.c` surface.
- **Modules in value seats** — clear error today; any future story is yours.
- **Shadowing policy** — rebinding a name in nested scopes: allowed silently today;
  lint/error unruled.

---

## Group B — deferred by your own rulings (reopen only deliberately)

- **B1. GR-10(3) finite-product exact chains** — numeric finite-state walking (specimens
  11/22) and the reason the recursive `sum` over `IntList` is unproven. One lib pin sits
  ignored on exactly this. Reopening = stamping the extension into v1 scope.
- **B2. D-4 basin derivation** — `collatz(64)`'s Pow2 basin; deferred as a possible later
  improvement; collatz stays honestly unproven.
- **B3. μ laws 2/4** — nested-binder merge; partition-refinement slot merging.
- ~~**B4. Symbolic-instance fact keys**~~ — **MIS-FILED; REMOVED FROM THIS GROUP
  [2026-08-06].** This was never an author deferral and never an open question. C§13.2
  specifies it twice: *"A call site resolves its callee to an analysis instance (**shape +
  environment contracts — exact for const closures, contract-level for factory products
  like `makeAdder(someInput)`**)"* and *"Function-valued analysis results retain their
  possible analysis instances … as analyzer **metadata riding alongside their coarse
  `Kind(Function)` contract**, so callables … arrive at call sites with instances
  recoverable (**plumbing, not a contract constructor**)."* An instance carries capture
  **contracts**, not values, and the spec's own example is exactly the failing case. The
  implementation instead emits a bare `Kind(Function)` with no metadata when a capture is
  non-singleton, so nothing is recoverable at the call site — the behavior that sentence
  forbids. **Moved to Group C (owed implementation).** The consumer half already exists:
  the region-table machinery takes an environment of contracts and handles
  contract-described captures (case (b)); the producing and carrying half is what is
  missing. The fact-*keys* question is downstream of it and dissolves with it.
- **B5. The grapheme boundary-state compression** — lifting exact string-length arithmetic
  to abstract string *contracts*; needs segmenter category tables and a length-contract
  form.
- **B6. Async / non-polling Effects** — behind the reactive fence with the rest.
- **Threads A/B/C** (handover docs): open-value observation legality; function equality
  under the freeze slice; the equality-freeze exclusions' provenance. All PENDING-§5-
  adjacent; MU-10 and H-05 are the tests that move if these change.

---

## Group C — owed implementation (mine; no ruling needed)

- **C0. Analysis-instance metadata for factory products (C§13.2) — the former "B4".**
  A function value produced with non-singleton captures must carry its instance (shape +
  capture *contracts*) as metadata beside `Kind(Function)`, and a call site must resolve
  through it. Specified, unimplemented. Symptom: a `where` over any non-enumerable domain
  on a function that builds a helper from its own argument and calls it — rejected with
  "callee not resolved to a known function" (scratch program `w2.next`). **Not proven to be
  the sole remaining cause of that rejection**, only the specified piece that is missing.
- **C1.** The application package's four γ obligations as a sampled joint-operand battery
  per world (Tier 5's next slice).
- **C2.** The world-decided gray runner — host effects in the bounded oracle, then the
  recorded stub goes live.
- **C3.** Call-edge-derived domains (application spec v0.8.1 §5) replacing
  `accepted_domain`'s interim same-arity propagation.
- **C4.** The paper-proof halves of grounding §13.1–4, the μ obligations, and the semantics
  theorem — C§16 discharge proper (the executable batteries are supplements by §13.5's own
  words).
- **C5.** More RT/GR conformance breadth as features land; the remaining owed-items ledger
  rows.
