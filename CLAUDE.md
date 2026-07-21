# CLAUDE.md — NEXT Language Implementation

You are implementing **NEXT**, a language whose design is complete and recorded in four normative documents in this repository. Your job is implementation, not design.

## Normative documents (read in this order)

1. `next-design-compendium-v1-0.md` — the master: architecture, semantics, ledgers, statuses. Wins on design intent.
2. `next-grammar-specification-v0-1.md` — what parses. Final; no throwaway notation.
3. `next-kernel-ast-specification-v0-1.md` — what exists after parsing: node inventory + the **closed desugaring catalog** (§4). The analyzer-facing form.
4. `next-semantics-companion-v0-1.md` — what running means: per-node evaluation rules, **oracle traps**, the trap↔compile-error concordance (§6).

Status vocabulary matters: [decided]/[owed]/[open]/[parked]/[leaning]/[fenced]. Nothing is [verified]. Fenced subsystems (reactive layer, concurrency, UI) are **not** in scope.

## Hard rules

1. **Interpreter before analyzer.** The oracle interpreter is the truth source; no contract/analysis code exists until the oracle and the normalization harness are green. This is the project's #1 named failure mode.
2. **Implement the semantics companion exactly** — including oracle traps as a distinct, non-value, non-catchable halt per §6. Traps are the executable surface for later soundness claims.
3. **Do not invent semantics.** Any gap is either an extension point (AST spec §7), a tagged [open], or a question for the author. Stop and ask; never fill silently. Mark any unavoidable judgment call with an `// [ask-author]` comment and surface it in your session summary.
4. **Property harness from day one of normalization:** `eval ∘ normalize = eval`, idempotence, brute-forced per-rule checks against the oracle.
5. All values are immutable and **interned**: same value = same pointer; `==` is pointer comparison, universally. Closures intern **shallowly** — key = (code pointer, capture pointers), small-tuple cost (interim: the parsed-code object serves as the code pointer until the canonicalizer lands; spelling-variant duplicates compare unequal until then — false negatives only). **Calls are never memoized**; only construction dedups. No runtime code analysis exists. Numbers are exact `BigRational` (num-rational). Fixed-precision decimal crates are explicitly rejected.

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
- Function equality: `y = [() => y]` / `z = [() => z]` compare equal (via canonical code — pending-§5); the §7 group-identity pair (provisional strict-openness default — flagged, not ruled).
- `??` vs `~a || b` differing exactly on `false`.
- Nested-mutator join: inner writes invisible until outermost completion; equality-guard no-op write.
- Grapheme index/slice cases pinned to the Unicode table version.

## Known opens you will meet (implement as stated; do not resolve)

- **Mutator returns**: current law is return-nothing — implement it; the returns-leaning is an extension point.
- **Open-value group identity — RULED (shape, via strict openness)**: semantics §7 as written is normative; the group-canonicalization mechanism lands with §5; FE-05/FE-06 expectations are fixed (pending-§5 for mechanism only).
- **Module in a value seat**: unimplemented; a clear error is correct.
- **Template interpolation — RULED total [user, 2026-07-18]**: the trap is deleted; render literal forms for data (sorted-key records, B2 numbers, quoted inner strings), `<Function>` for functions, `<Indeterminate form>` for Indeterminates; parse∘print = identity on the literal fragment is a harness law (suite PR-01…05).

## Process

Keep a `DECISIONS.md` changelog. Small commits per build-order step. When the author reviews, provenance matters: what the specs mandated vs what you chose vs what you're asking.
