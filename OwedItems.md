# OwedItems.md — normative gaps the implementation defers to

This registry tracks items that are **owed or open in the normative documents
themselves** — not work I have merely sequenced for later. Implementation-only
gaps (a decided design I haven't built yet) do *not* belong here; they live in the
build-order tasks and `DECISIONS.md`.

Status vocabulary mirrors the compendium: **[owed]** (design intends a rule, not
yet written), **[open]** (a decision the author has flagged as unresolved),
**[decided]** (settled — listed only when an extension point rides alongside).

Each entry records: the source, the current implementation behavior (always
**sound** — we never accept what a spec leaves trap-worthy), and what closing it
requires.

---

## 1. Tuple-length / concatenation contract family — **[owed]**

- **Source:** Kernel AST Specification v0.1 — `TupleCons` "Feeds the
  tuple-length/concatenation rule family (**C§17 owed**)." Arises for variable-length
  tuple contracts, rest parameters, and tuple spreads.
- **What is owed:** the contract algebra for tuple length and concatenation — e.g.
  the output contract of `[...a, x, ...b]`, length constraints, and how a
  rest-pattern splits a tuple contract. The Compendium reserves C§17 for it but has
  not written the rules.
- **Current implementation behavior:**
  - Analyzer: a `TupleCons` with any `Spread` element types as `Top` (shape not
    modeled) but still analyzes each child for findings. Spread-free tuples get the
    exact `Tuple([...])` contract.
  - Contracts: `Contract::Tuple` is exact positional only; no length/concat operator
    exists.
- **To close:** author writes C§17; then add the tuple-length/concatenation
  operators to the contract algebra and replace the analyzer's `Top`-for-spread with
  the derived shape. Relates to `analyze_operation` (a variadic tuple-build op) and
  to recursive contracts (variable-length tuples are a regular-shape recursion).

---

## 2. Print doctrine for structure interpolation — **[open]**

- **Source:** Semantics Companion v0.1 §6 — `unprintable-interpolation | the open
  print doctrine (E11) — trap until ruled`. CLAUDE.md lists it under "Known opens
  you will meet": *"Template interpolation of structures: trap, per spec — the print
  doctrine is deliberately open."*
- **What is open:** how (or whether) a Tuple/Record/Function/Indeterminate should
  render inside a template. Until ruled, interpolating one is a **trap**.
- **Current implementation behavior (faithful to "trap until ruled"):**
  - Oracle: `stringify` prints String/Number/Boolean/Null; anything else traps
    `UnprintableInterpolation`.
  - Analyzer: `analyze_template` demands printability per interpolation — a value
    provably in `{String, Number, Boolean, Null}` is accepted; a value provably a
    structure (or an `Indeterminate`) is **rejected** (error); anything unproven is a
    warning. Template's result contract is `Kind(String)`.
- **To close:** author rules the doctrine. Only the accept/reject boundary in
  `analyze_template` (and the corresponding `stringify` arms in the oracle) moves;
  the machinery stays.

---

## Related author-flagged opens (tracked elsewhere, listed for completeness)

These are genuine doc-opens but are already implemented per their **provisional
decided** law, so they are not blocking; recorded here so the registry is the one
place to look.

- **Open-value group identity** — Semantics Companion §7 **[open — user; the
  concrete `a2 == a` test pair is the whole decision surface]**. Implemented behind
  one module per the provisional "strict openness with statement-group windows"
  default (CLAUDE.md). A ruling flips it cheaply.
- **Mutator returns** — return-nothing is **[decided]** and implemented; the
  returns-leaning is a tagged **extension point [open]** (AST spec §7 / CLAUDE.md).
- **Module in a value seat** — unimplemented by intent; a clear error is the correct
  behavior (CLAUDE.md).

---

*Not in this file:* nodes whose analysis design is **decided** but that I have not
yet implemented (`Access` E6, `Match` E9/E10, `Apply` C§7/B5, `Write`/worlds B5).
Those are ordinary build-order work, tracked as tasks — the docs already pin them.
