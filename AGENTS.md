# AGENTS.md — NEXT Language Implementation

You are implementing **NEXT**, a language whose design is complete and recorded in the normative documents in this repository. Your job is implementation, not design.

**Design method (read before adding any new analysis capability):** `next-late-resolution-v0-5.md` (v0.1–v0.4 superseded, on disk as history; four rounds integrated; five rounds, final confirmatory ACCEPTED — DESIGN-CLOSED, author stamp 2026-07-27; the gate for Investigation 2) — the late-resolution law, its preconditions, the nine-entry dissolution ledger, the formation-vs-judgment line, and the 8-point checklist (C1–C8). Run the checklist before proposing mechanisms; imports smuggle declaration-time eagerness.

**Open design threads — do not treat the affected text as settled:** see `HANDOVER-open-threads-2026-07-23.md`, continued by `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md` (later record wins on Thread C; **rulings 2026-07-27 in its Part XI: specific `a/0` identity formalized, `Numeric` contract adopted**). (A) open-value observation legality + its trap class; (B) function equality under the freeze slice; (C) the equality-freeze exclusions — provenance unratified (zero-annihilation, cancellation, identity elimination, and the closed-enumeration narrowing). All three are PENDING-§5-adjacent and block no current work; **MU-10 and H-05 are the tests that move if the rulings change.**

## Normative documents (read in this order)

1. `next-design-compendium-v1-0.md` — the master: architecture, semantics, ledgers, statuses. Wins on design intent.
2. `next-grammar-specification-v0-1.md` — what parses. Final; no throwaway notation.
3. `next-kernel-ast-specification-v0-1.md` — what exists after parsing: node inventory + the **closed desugaring catalog** (§4). The analyzer-facing form.
4. `next-semantics-companion-v0-1.md` — what running means: per-node evaluation rules, **oracle traps**, the trap↔compile-error concordance (§6).
5. `next-mu-canonicalization-specification-v0-6.md` — the 2026-08-08 author amendment for recursive function identity. Supersedes v0.5's `GroupTemplate`, group-entry-slot, source-group reconstruction, and serialized-μ machinery; v0.5 remains history for unchanged freeze/open-value laws.

Status vocabulary matters: [decided]/[owed]/[open]/[parked]/[leaning]/[fenced]. Nothing is [verified]. Fenced subsystems (reactive layer, concurrency, UI) are **not** in scope.

## Hard rules

1. **Interpreter before analyzer.** The oracle interpreter is the truth source; no contract/analysis code exists until the oracle and the normalization harness are green. This is the project's #1 named failure mode.
2. **Implement the semantics companion exactly** — including oracle traps as a distinct, non-value, non-catchable halt per §6. Traps are the executable surface for later soundness claims.
3. **Do not invent semantics.** Any gap is either an extension point (AST spec §7), a tagged [open], or a question for the author. Stop and ask; never fill silently. Mark any unavoidable judgment call with an `// [ask-author]` comment and surface it in your session summary.
4. **Property harness from day one of normalization:** `eval ∘ normalize = eval`, idempotence, brute-forced per-rule checks against the oracle.
5. All values are immutable and **interned**: same value = same pointer; `==` is pointer comparison, universally. Acyclic closures intern shallowly by `(canonical code pointer, capture pointers)`; recursive capture graphs close through exact rooted bisimulation and then obey the same pointer law. **Calls are never memoized**; only construction dedups. No runtime code analysis exists. Numbers are exact `BigRational` (num-rational). Fixed-precision decimal crates are explicitly rejected.
6. **Recursive groups are construction windows only.** Function identity is canonical per-function positional/de-Bruijn code applied to the immutable positional capture graph. Do not introduce `GroupTemplate`, group-level code identity, entry slots, source-group reconstruction, or serialized μ-refs. Concrete analyzer instances use canonical function `ValueRef`; flowing factory products may use canonical code plus an interned positional capture-contract tuple as analysis metadata, never as a formed runtime value. A local function over outer arguments remains unformed until execution; analyze a direct call by closure-converting those outer bindings to additional ordinary arguments, and discover recursion only at the reached back-edge.
7. **Recursive safety domains are fixed proposals, never reaching-domain growth.** Invariant non-measure arguments remain exact. GR-19 permits one changed numeric payload proposal only when the arrived contract is Number and every written recursive payload expression is proved safe and closed over Number by the operation rulebook; the joint fact pass must still prove the body. Do not turn this into kind-menu widening, chain unfolding, or generic invariant synthesis.

## Build order (Compendium Part I; do not reorder)

1. **Repo + value layer**: canonical rationals (printing per Compendium B2: decimal iff reduced denominator's primes ⊆ {2,5}), interner with pointer-equality semantics, kernel AST types.
2. **Lexer + parser** per grammar v0.1, emitting kernel AST through the closed desugar catalog. Line-sensitivity rules L1/L2; the maximal-munch lookaheads T1–T3.
3. **Oracle interpreter** per semantics v0.1: late binding, worlds + admission matrix, Match as the sole control node, completion outcomes, mutator staging (pending set, read-your-writes, join, publish-at-outermost-completion with the pointer-equality guard), `?.` one-step totals, clamped slices, grapheme string ops (unicode-segmentation; pin the version), Failure as plain data, host-effect harness.
4. **Normalization + harness** in the same sitting as 3's completion.
5. Stop. Contracts/analysis are a later phase, gated on the above being green.

## Test suite

The full suite is specified in `next-test-suite-specification-v0-1.md` — stable IDs, per-phase, with expected outcomes and the PENDING/PIN/PROVISIONAL/RECOVER registers. Implement phases 0–4 alongside their build-order steps; Phase A ships as ignored stubs with recorded verdicts. The list below is the short form:

## Conformance seeds (initial test suite)

- One program per §6 trap class (must trap; will later double as analyzer-rejection cases).
- The desugar-equivalence rows (AST §4) and worked parses (Compendium E2).
- Exactness flagship: `0.1 + 0.2 == 0.3` is `true`.
- Function equality: `y = [() => y]` / `z = [() => z]` compare equal; the shape-symmetric `a = () => b(); b = () => a()` pair collapses to the same pointer as its self-loop, while even/odd remain distinct by their code labels.
- `??` vs `~a || b` differing exactly on `false`.
- Nested-mutator join: inner writes invisible until outermost completion; equality-guard no-op write.
- Grapheme index/slice cases pinned to the Unicode table version.

## Known opens you will meet (implement as stated; do not resolve)

- **Mutator returns**: current law is return-nothing — implement it; the returns-leaning is an extension point.
- **Open-value recursive identity — RULED and implemented:** strict openness prevents observation during construction; the SCC window ties the positional capture graph and disappears. FE-05/FE-06 identity comes from canonical code plus verified value-graph interning, never group identity.
- **Recursive local calls over outer arguments — IMPLEMENTED 2026-08-08:** do not construct cyclic symbolic closure metadata. Runtime closure formation remains late. The analyzer closure-converts direct local calls to a closed fact identity with the arrived outer contracts as leading arguments (`f(limit, n)`), records enclosing-function dependencies through that identity, and judges drift when the recursive back-edge is reached. Pinned by `cli_recursive_local_call_carries_outer_arguments_lazily`.
- **GR-19/GR-26 — IMPLEMENTED 2026-08-08:** local Fibonacci and the descending-counter/numeric-accumulator specimen are live. The latter combines the existing descent envelope with the fixed operation-verified numeric-payload fact rule; unsupported changed payloads remain Unproven.
- **Module in a value seat**: unimplemented; a clear error is correct.
- **Template interpolation — RULED total [user, 2026-07-18]**: the trap is deleted; render literal forms for data (sorted-key records, B2 numbers, quoted inner strings), `<Function>` for functions, `<Indeterminate form>` for Indeterminates; parse∘print = identity on the literal fragment is a harness law (suite PR-01…05).

## Process

Keep a `DECISIONS.md` changelog. Small commits per build-order step. When the author reviews, provenance matters: what the specs mandated vs what you chose vs what you're asking.
