# NEXT

A reference implementation of **NEXT**, a contract language: exact rational
arithmetic, immutable interned values (same value = same pointer), `Match` as the
sole control node, total division via `Indeterminate`, and a contract system whose
job is to prove at compile time that programs cannot trap at run time.

The language design is fixed and recorded in the normative specifications in this
repository; this repo is the implementation of that design.

## Repository layout

| Path | Contents |
|---|---|
| `src/` | the implementation |
| `tests/` | the conformance suite (stable IDs) and the machinery gates |
| `docs/normative/` | the design authority — manifest-verified, not edited by implementation work |
| `docs/notes/` | working notes: status, changelog, plans, reviews, handovers |
| `MANIFEST.sha256.txt` | content hashes for the normative set (the stale-upload guard) |

Run `shasum -c MANIFEST.sha256.txt` before trusting a copy of the specifications.

## Design documents

Read in this order:

1. `docs/normative/next-design-compendium-v1-0.md` — the master: architecture,
   semantics, ledgers, statuses. Wins on design intent.
2. `docs/normative/next-grammar-specification-v0-1.md` — what parses.
3. `docs/normative/next-kernel-ast-specification-v0-1.md` — what exists after
   parsing: the node inventory and the closed desugaring catalog.
4. `docs/normative/next-semantics-companion-v0-1.md` — what running means: per-node
   evaluation rules, the oracle traps, and the trap ↔ compile-error concordance.

Design-closed subsystem packages: μ-canonicalization (v0.5), recursive contracts
(v0.2), the tuple-length/concatenation family (v0.3), the application & induction
package (v0.8), grounding (v0.5), region tables (v0.3), and late resolution (v0.5).
The conformance suite is specified in
`docs/normative/next-test-suite-specification-v0-1.md`.

`docs/notes/IMPLEMENTATION-STATUS.md` is **the authority on what is actually built**
— where any other note disagrees with it, that file wins.
`docs/notes/DECISIONS.md` is the implementation changelog (what the specs mandated,
what was chosen, what is being asked).

## Architectural rule

**The oracle interpreter is the truth source.** It is contract-free by design, and
every contract and analyzer rule is brute-tested against it: membership, the
three-valued subcontract, the operation transfer rules, and the analyzer's
trap ↔ error concordance are all checked by running the oracle and comparing. No
analysis code was written before the interpreter and the normalization harness were
green.

## Build and test

```sh
cargo run -- program.next          # run a program
cargo run -- --check program.next  # analyze without running

cargo test                         # conformance, property and machinery suites
cargo clippy --all-targets
shasum -c MANIFEST.sha256.txt      # verify the normative documents
```

## Status

| Suite | Result |
|---|---|
| library | 438 passed, 0 failed, 1 ignored |
| conformance | 114 passed, 0 failed, 11 ignored |
| machinery gates | 10 passed, 0 failed |
| normative manifest | 19/19 verified |

**Implemented:** the value layer, lexer, parser and desugaring, the oracle
interpreter with its traps and world admission, mutator staging, the normalization
property harness, universal function interning including recursive groups (runtime
`==` is pointer equality), the contract algebra, and a whole-program `--check` that
originates typed operation-safety, body-safety and return demands and settles them
against a domain-indexed fact graph.

**In progress:** the demand core's remaining origins, grounding's coverage and its
wiring, module linking, the divergence harness, and the lint tier. The twelve
ignored tests each record the specific gate they wait on.

**Not yet claimed:** general soundness. The analyzer has no demonstrated false
acceptance, but the C§16 discharge and the executable soundness harness are
unwritten, so that is an absence of evidence against, not evidence for. See
`docs/notes/IMPLEMENTATION-STATUS.md` for the current, measured position.

## License

MIT — see [LICENSE](LICENSE). Copyright (c) 2026 Dane Brdarski.

## Acknowledgment

Language design and specifications by Dane Brdarski. The implementation was written
with [Claude](https://claude.com/claude-code) (Anthropic) working from those
specifications; individual contributions are recorded in the commit history.
Copyright rests with the author — Claude is credited as a tool and collaborator, not
as a rights holder.
