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

## 3. `analyzeOperation` application table + interprocedural return induction — **[owed]**

- **Source:** Compendium **C§17 Owed** list, verbatim items: *"per-operation
  analyzeOperation tables (incl. the application rule's act-kind admission check and
  the expecting-seat completion demand)"*, *"domain-indexed induction details
  (partition rule, escaped-row evaluation, conservative row selection)"*,
  *"instance-chain cutoff spec"*, *"global fact-graph construction spec"*,
  *"template-instantiation spec"*. Architecture is laid out (§10.6/§10.7 return &
  vector induction; C§12.3 the three function-identity layers; C§13.2 input
  obligation + admission) — the compendium tags the cluster **"writing and proving,
  not designing."** The detailed executable rule tables are not yet written.
- **What is owed:** how a call site derives the callee's **return** contract and
  completion from the body (a return fact `for inputs ⊑ I, return ⊑ C` bound to an
  analysis *instance*), settled jointly across mutually-recursive functions via a
  global fact graph (SCC/vector induction); and the full **application** transfer
  table (admission + expecting-seat completion for arbitrary callees).
- **Current implementation behavior (analyzer `analyze_apply`):** analysis runs in
  the **pure world**; **closed** calls fold exactly through the oracle. For **open**
  calls the settled pieces are checked — spread-kind, non-function callee, and, for
  a **known** callee value, B5 admission + argument-obligation. Deferred to this
  owed item (all sound — never a false accept): an **open call's return** types as
  `Top`; an **unknown** callee's act-kind admission / argument obligation is **not**
  checked; a `Pure`/`Effect` body's completion is not derived (`may_complete = false`
  for non-mutators).
- **To close:** author writes the analyzeOperation application table + the
  return-induction/instance/fact-graph details; then the analyzer analyzes `Lambda`
  bodies (with param contracts bound), threads the world, and gives open calls a
  real return contract and completion.

## 4. First-class function-shape (arrow) contract — **[owed / gap]**

- **Source:** the enumerated contract algebra (Compendium C§4 / §292:
  `Range, Mod, Equals, Union, Difference, HasField, Geo, …`) has **no arrow
  contract** carrying act-kind + input + output. Function *identity/shape* is
  defined (C§12.3 three layers; act-kind is part of shape, C§13.2), but a
  **contract** describing a function's signature is not in the written algebra.
- **What is owed:** whether functions get first-class signature contracts (with the
  contravariant-input / covariant-output subcontract rule), enabling higher-order
  reasoning — an open callee's admission and return without knowing its exact value.
- **Current implementation behavior:** `Contract::Kind(Function)` only. Open callees
  are `Top`-returning and unchecked for admission (see item 3).
- **To close:** decide/spec the arrow contract; add it to the `Contract` algebra
  and to `subcontract` (arrow variance).

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
