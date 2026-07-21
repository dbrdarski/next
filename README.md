# NEXT

A reference implementation of **NEXT**, a contract language: exact rational
arithmetic, immutable interned values (same value = same pointer), `Match` as the
sole control node, total division via `Indeterminate`, and a contract system whose
job is to prove at compile time that programs cannot trap at run time.

The language design is fixed and recorded in the normative specifications in this
repository; this repo is the implementation of that design.

## Design documents

Read in this order:

1. `next-design-compendium-v1-0.md` — the master: architecture, semantics, ledgers,
   statuses. Wins on design intent.
2. `next-grammar-specification-v0-1.md` — what parses.
3. `next-kernel-ast-specification-v0-1.md` — what exists after parsing: the node
   inventory and the closed desugaring catalog.
4. `next-semantics-companion-v0-1.md` — what running means: per-node evaluation
   rules, the oracle traps, and the trap ↔ compile-error concordance.

Design-closed subsystem packages: μ-canonicalization (v0.5), recursive contracts
(v0.2), the tuple-length/concatenation family (v0.3), and the application &
induction package (v0.8). The conformance suite is specified in
`next-test-suite-specification-v0-1.md`.

`DECISIONS.md` is the implementation changelog (what the specs mandated, what was
chosen, what is being asked). `OwedItems.md` indexes the gaps the *documents* still
owe, as distinct from work merely not yet built.

## Architectural rule

**The oracle interpreter is the truth source.** It is contract-free by design, and
every contract and analyzer rule is brute-tested against it: membership, the
three-valued subcontract, the operation transfer rules, and the analyzer's
trap ↔ error concordance are all checked by running the oracle and comparing. No
analysis code was written before the interpreter and the normalization harness were
green.

## Build and test

```sh
cargo test      # the conformance and property suites
cargo clippy --all-targets
```

## Status

Implemented: the value layer, lexer, parser and desugaring, the oracle interpreter,
the normalization property harness, μ-canonicalization, the contract algebra
(denotational membership, three-valued subcontract, operation transfer rules,
recursive contracts), and an analyzer covering the expression layer with an exact
trap ↔ error concordance against the oracle.

In progress: the tuple-length family and the application & induction package.

## License

MIT — see [LICENSE](LICENSE). Copyright (c) 2026 Dane Brdarski.

## Acknowledgment

Language design and specifications by Dane Brdarski. The implementation was written
with [Claude](https://claude.com/claude-code) (Anthropic) working from those
specifications; individual contributions are recorded in the commit history.
Copyright rests with the author — Claude is credited as a tool and collaborator, not
as a rights holder.
