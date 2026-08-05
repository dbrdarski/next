# Open decisions — author briefing, 2026-08-05

Compiled from: the in-code `// [ask-author]` markers, the conformance/lib ignore registers,
the completion plan's policy gates, the compendium's Principle 9 annotation, the handover
threads, and the session DECISIONS log. Three groups: **A** — decisions waiting on you;
**B** — items you already ruled deferred (listed so reopening is a choice, not an accident);
**C** — owed implementation work that needs no ruling.

---

## Group A — decisions actively waiting on you

### A1. The fueled refutation sampler (AP-30) — procedure shape
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

### A2. The §E9 unreachable-branch walk: from `Top`, or from the declared domain?
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

### A3. Diagnostic classes for non-trap authoring errors (two markers, one family)
The §6 trap catalog is closed, and two static-only diagnostics had no row, so they borrow:
- The **unreachable-branch error** reuses `TrapClass::ExpectingSeat` (the E9/E10
  match-coverage family).
- A **malformed `where`** (unknown name, arity mismatch, un-evaluable contract expression)
  reuses `ArgumentObligation`.
**Decision:** bless the borrowing (message text carries identity — the definition-error
precedent), or mint a dedicated static-diagnostic class outside the trap concordance. The
second is cleaner taxonomy but touches the closed catalog's periphery, so it's yours.

### A4. Principle 9's two remaining policy picks (the stamp's leftovers)
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

### A6. F0 Q1 — `Union` distribution vs interval hull in operation images
`Union(Equals(1), Equals(10)) + Equals(1)`: distribution gives `Union(2, 11)` (precise,
cost grows multiplicatively per operand alternative); the hull gives `Range(2, 11)` (coarse,
constant cost — **implemented**). Purely a precision/cost dial on the operation rulebook;
observable when a downstream match tests `== 6` (hull can't exclude it, distribution can).

### A7. `where` on a product binding
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

### A9. `String.units` / `String.points` element representation
E8 pins only the **lengths** (S-02 asserts them). Implemented as Tuples of Numbers (UTF-16
code units / code points). Decision: bless Numbers, or rule a dedicated element form
(e.g. single-unit Strings), which would change `"é".points` from `[233]` to `["é"]`-shaped.

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
- **B4. Symbolic-instance fact keys** — the analyzer doesn't construct symbolic instances
  yet; keys deferred with them.
- **B5. The grapheme boundary-state compression** — lifting exact string-length arithmetic
  to abstract string *contracts*; needs segmenter category tables and a length-contract
  form.
- **B6. Async / non-polling Effects** — behind the reactive fence with the rest.
- **Threads A/B/C** (handover docs): open-value observation legality; function equality
  under the freeze slice; the equality-freeze exclusions' provenance. All PENDING-§5-
  adjacent; MU-10 and H-05 are the tests that move if these change.

---

## Group C — owed implementation (mine; no ruling needed)

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
