# CLAUDE.md — NEXT Language Implementation

You are implementing **NEXT**, a language whose design is complete and recorded in six normative documents in this repository. Your job is implementation, not design.

## Normative documents (read in this order)

1. `next-design-compendium-v1-0.md` — the master: architecture, semantics, ledgers, statuses. Wins on design intent.
2. `next-grammar-specification-v0-1.md` — what parses. Final; no throwaway notation.
3. `next-kernel-ast-specification-v0-1.md` — what exists after parsing: node inventory + the **closed desugaring catalog** (§4). The analyzer-facing form.
4. `next-semantics-companion-v0-1.md` — what running means: per-node evaluation rules, **oracle traps**, the trap↔compile-error concordance (§6).
5. `next-mu-canonicalization-specification-v0-5.md` — value/function identity: two graph domains (code vs value); Algorithm A (eager per-SCC code canonicalization, capture routing); Algorithm B (value-graph bisimulation, canonicalization-internal); **universal interning restored** (closures intern shallowly; runtime `==` is a pointer test); the enumerated, frozen `==`-slice (§8). Supersedes v0.1 (kept on disk as history).
6. `next-recursive-contracts-specification-v0-2.md` — C§9: named recursive contracts; admissibility (positivity + structural guardedness); vector-lfp denotation; progress-guarded pair-induction subcontract; productivity-closure emptiness.

Status vocabulary matters: [decided]/[owed]/[open]/[parked]/[leaning]/[fenced]. Nothing is [verified]. Fenced subsystems (reactive layer, concurrency, UI) are **not** in scope.

## Hard rules

1. **Interpreter before analyzer.** The oracle interpreter is the truth source; no contract/analysis code exists until the oracle and the normalization harness are green. This is the project's #1 named failure mode.
2. **Implement the semantics companion exactly** — including oracle traps as a distinct, non-value, non-catchable halt per §6. Traps are the executable surface for later soundness claims.
3. **Do not invent semantics.** Any gap is either an extension point (AST spec §7), a tagged [open], or a question for the author. Stop and ask; never fill silently. Mark any unavoidable judgment call with an `// [ask-author]` comment and surface it in your session summary.
4. **Property harness from day one of normalization:** `eval ∘ normalize = eval`, idempotence, brute-forced per-rule checks against the oracle.
5. Values are immutable and **interned**: same value = same pointer; `==` is pointer comparison. Numbers are exact `BigRational` (num-rational). Fixed-precision decimal crates are explicitly rejected.

## Build order (Compendium Part I; do not reorder)

1. **Repo + value layer**: canonical rationals (printing per Compendium B2: decimal iff reduced denominator's primes ⊆ {2,5}), interner with pointer-equality semantics, kernel AST types.
2. **Lexer + parser** per grammar v0.1, emitting kernel AST through the closed desugar catalog. Line-sensitivity rules L1/L2; the maximal-munch lookaheads T1–T3.
3. **Oracle interpreter** per semantics v0.1: late binding, worlds + admission matrix, Match as the sole control node, completion outcomes, mutator staging (pending set, read-your-writes, join, publish-at-outermost-completion with the pointer-equality guard), `?.` one-step totals, clamped slices, grapheme string ops (unicode-segmentation; pin the version), Failure as plain data, host-effect harness.
4. **Normalization + harness** in the same sitting as 3's completion.
5. Stop. Contracts/analysis are a later phase, gated on the above being green.

## Conformance seeds (initial test suite)

- One program per §6 trap class (must trap; will later double as analyzer-rejection cases).
- The desugar-equivalence rows (AST §4) and worked parses (Compendium E2).
- Exactness flagship: `0.1 + 0.2 == 0.3` is `true`.
- Interning: `y = [() => y]` / `z = [() => z]` intern equal; the §7 group-identity pair (provisional strict-openness default — flagged, not ruled).
- `??` vs `~a || b` differing exactly on `false`.
- Nested-mutator join: inner writes invisible until outermost completion; equality-guard no-op write.
- Grapheme index/slice cases pinned to the Unicode table version.

## Known opens you will meet (implement as stated; do not resolve)

- **Mutator returns**: current law is return-nothing — implement it; the returns-leaning is an extension point.
- **Open-value group identity**: implement the semantics §7 provisional default; keep it isolated behind one module so a ruling flips it cheaply.
- **Module in a value seat**: unimplemented; a clear error is correct.
- **Template interpolation of structures**: trap, per spec — the print doctrine is deliberately open.

## Process

Keep a `DECISIONS.md` changelog. Small commits per build-order step. When the author reviews, provenance matters: what the specs mandated vs what you chose vs what you're asking.
