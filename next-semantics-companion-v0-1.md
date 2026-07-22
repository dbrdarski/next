# NEXT — Semantics Companion v0.1 (Operational Semantics for the Oracle)

**Date:** 2026-07-17. **Status:** the evaluation rulebook the **oracle interpreter** implements — the truth source every C§16 obligation is tested against (Part I: interpreter before analyzer, no contracts in it). Normative over kernel AST v0.1 nodes; assembled from Compendium Parts B/E/F/G. **The oracle is contract-free by design**, so situations the analyzer must prove absent need a defined testing-time behavior: the **oracle trap** — an immediate halt that is *not a language value, not a Failure, not catchable*. Every trap class maps one-to-one to a compile-error class (§6); "the analyzer is sound" becomes the executable claim *accepted programs never trap*. Divergence is separate: it is gray's runtime face and simply runs (harnesses may fuel-limit externally).

## 1. Semantic domains

**Values** — immutable: Boolean, Null, Number (exact rational), String (UTF-16 storage; grapheme semantics E8), Tuple, Record, Function, Indeterminate(form). **Data values intern**: same value = same pointer, `==` is pointer comparison (B1). **Closures intern shallowly [user, restored]** — key = (canonical-code pointer, capture pointers); same value = same pointer universally; **calls are never memoized**; μ-group members intern at window close (markers stored; heap acyclic). **Locations (slots)** — runtime-internal mutable cells; never values (C§12.4, F4). **Store σ** — slot → committed content. **Pending set π** — slot → staged content; exists only inside a mutation transaction (B5). **Environment ρ** — name → binding, where a binding is an immutable value, a slot, or an *under-initialization* marker (B4). **Worlds w** ∈ {pure, mutator, effect} — derived from the enclosing `Lambda.actKind`, never from lexical nesting (E14). **Function value** — (canonical body, capture map, actKind): captures hold resolved values for immutable free names, μ-markers for under-init self/group references, location markers for slot references (C§12.3 layer 1, F3); eager vs lazy capture of immutables is unobservable (B4) — the oracle may do either. **Outcomes** of body evaluation: `Produced(v)` | `CompletedWithoutValue` | (non-termination). `CompletedWithoutValue` is not a value and never converts to one (E10, 1.0.2).

## 2. Programs, modules, entry

Resolution is static and whole-program (C§14, E12): imports alias bindings (slots stay live); duplicate module names were rejected upstream. A **module** body evaluates its items in file order under **pure world**: `Bind` and `SlotDecl` only ever *define* — `SlotDecl` allocates a fresh slot and commits its pure initializer (legal by the allocation-is-declarative ruling); no act call can occur (grammar + jurisdiction). Delivery timing is unobservable (E12). An **entry file** (no header, unimportable) is where *doing* lives (E12): its top level evaluates in **effect world** **[derived — E12's doing clause; the one derivation this document makes]**, so act calls are its normal statements. The static binding rule holds everywhere: evaluation may reference only earlier-established bindings, lambda bodies exempt (B4).

## 3. Evaluation rules, per node

Judgment ⟨e, ρ, σ, π, w⟩ ⇓ outcome (σ/π threaded; strictly left-to-right everywhere, spreads included — E3).

**Const(v)** ⇓ v.

**Ref(b)** — immutable binding → its value. Location marker → **read-your-writes**: π(slot) if staged in the current transaction, else σ(slot) (B5). Under-initialization marker → **trap: unbound-evaluation** (the accepted-programs theorem says this is unreachable; B4).

**Lambda(p, body, k)** — constructs and interns the function value; free immutable names resolve per late binding (at construction or first use — unobservable); self/group names still open become μ-markers; slot names become location markers. Yields the interned function value — shallow key; construction dedups, invocation never memoizes (B1).

**Apply(f, args)** — evaluate callee, then args left-to-right; a `Spread(e)` must evaluate to a Tuple (**trap: spread-kind** otherwise) and splices. **World admission** (B5's matrix): callee.actKind ∉ admitted(w) → **trap: world-admission**. Bind the complete argument tuple against the callee's parameter pattern — structural mismatch → **trap: argument-obligation**. Evaluate the body under the callee's own world:
- *pure callee* — outcome must be `Produced` at expecting seats (see Match); at statement seats any outcome stands.
- *mutator callee* — if w = mutator: **join** the current transaction (the ruling) — same π. If w = effect: **begin** a transaction (π := ∅), run the body, and on completion (`Produced` or `CompletedWithoutValue`) **publish**: for each staged slot, if the staged value ≠ committed value (pointer inequality — the interning-exact guard, B7/G1), commit; all commits land as one event (single mutation branch — trivially atomic in the sequential oracle). Non-completion publishes nothing. **Current law: the Apply's outcome is `CompletedWithoutValue`** — any arm-produced value is discarded at the seat **[current law; the Mutator-returns leaning is an extension point]**.
- *effect callee* — outcome is the body's outcome; results (including Failure records) are ordinary values, bindable in act context (B6).

**PrimOp(op, args)** — exact rational arithmetic; string concat on `+` with two Strings. **Division is total**: `x/0` ⇓ Indeterminate(`_/0`), `0/0` ⇓ Indeterminate(`0/0`). **Indeterminate propagation**: an arithmetic op with an Indeterminate operand yields that Indeterminate unchanged (left-most when two) **[tagged representation choice — the analyzer-side story is union-propagation, C§7; the runtime story is a single concrete flowing value]**. Ordering comparisons (`< <= > >=`) and any numeric-demand op receiving Indeterminate → **trap: undischarged-Indeterminate** (discharge is forced at demand sites — C§7); `==`/`!=` are ordinary value equality (Indeterminates are interned values; discharge them by match, E9). Kind mismatches (`Number + String`) → **trap: operation-safety**.

**Match(scrutinee?, items)** — evaluate the scrutinee once if present; then items in order: `Bind` — evaluate, match the (irrefutable) pattern, extend ρ (factual mismatch → **trap: refuted-binding**); `Stmt` — evaluate, discard any value (`CompletedWithoutValue` is fine here; the goes-nowhere warning is compile-time); `Arm(pat?, guard?, r)` — pattern (if present) matches structurally against the scrutinee, binding arm-locally; on match, the guard (if present) evaluates as a **strict tested seat**: non-Boolean → **trap: tested-seat** (the falsy-set behavior of `~` was desugared away — kernel guards are Boolean, E10/§4 of the AST spec); guard true → the node **exits** with `Produced(⟦r⟧)`; guard false or pattern miss → next item, arm bindings dropped. Items exhausted with no exit → `CompletedWithoutValue`. **Expecting seats** (bindings, arguments, operands, arm results, elements, destructuring right sides — E10) demand `Produced`: `CompletedWithoutValue` arriving there → **trap: expecting-seat**.

**TupleCons / RecordCons** — elements/fields left-to-right; spreads splice (record spread of a non-Record → **trap: spread-kind**); computed keys must be Strings (**trap: computed-key**); later-wins on collision (E5); intern the result.

**Access(t, form, total)** — evaluate the target (and index). *Demand forms* (total = false): Null receiver → **trap: null-receiver**; absent field → **trap: absent-field**; index — normalize from-end (−k ↦ len−k on the unit sequence), non-integer or out-of-bounds → **trap: index-bounds**. *Total forms* (`?.` family): Null receiver → Null; absent field → Null; out-of-bounds index → Null — one step; the produced Null travels onward as an ordinary value (E6). *Slices*: always total — normalize signs via length, clamp to reality, half-open window; empty window → the empty Tuple/String (E7). **Strings**: bare index/slice/length operate on **grapheme clusters** (UAX #29, versioned tables — E8); `String.units` / `String.points` views are prelude functions over the same machinery.

**Template(parts)** — concatenate; **interpolation is total [user ruling, 2026-07-18 — the unprintable-interpolation trap is deleted]**. Renderings, deterministic functions of the interned value, frozen with semantics: String verbatim at top level, quoted-and-escaped (literal form) inside structures; Number per B2; `true`/`false`/`null` by name; **Tuple/Record as their canonical literal forms** (records in canonical sorted-key order — field order isn't identity); **Function as `<Function>`**; **Indeterminate as `<Indeterminate _/0>` / `<Indeterminate 0/0>`** — the form, never the operands (operands aren't part of the interned value). The principle: literal-formed values render as literals (parse ∘ print = identity on that fragment — a harness law); the rest render in angle brackets, visibly non-parseable.

**Write(slot, e)** — w ≠ mutator → **trap: world-admission**. Evaluate e; stage π[slot] := v. Visibility follows read-your-writes; commitment happens only at the transaction's publication (above).

**SlotDecl / Bind / Stmt at module or block level** — as §2 and Match describe. **Where / Import / Module** — no runtime behavior (analyzer metadata and link structure).

## 4. Effects at the oracle boundary

The oracle needs a world to touch. **Host effects** are harness-provided functions with actKind = effect: test doubles for IO, a println, an exit. Their results are ordinary values — a failed host effect returns a **Failure record** (the one prelude shape, B6: path + reason fields), which flows as plain data; nothing unwinds, nothing propagates by itself; `then`/`catch` are the two prelude functions over `|>` (B6), implementable in NEXT itself against this semantics. The **trap clause** (machine limits) manifests in the oracle as the host process's own limits — outside the semantics, as ruled (Part A).

## 5. The two staging theorems, restated operationally

**Mutators cannot trap in ways pure code cannot.** Inspect §3's trap sources reachable in mutator world: world-admission excludes effects (the matrix), so no IO exists; every remaining trap class (safety, bounds, tested-seat, …) is one the analyzer discharges for *accepted* programs exactly as in pure world; Indeterminate is a value, not a trap. Hence in an accepted program a mutator body either completes — publishing once — or diverges — publishing nothing. Publication-only transactionality needs no rollback because §3 contains no mutator-reachable abort. **Every evaluated reference is bound** — `Ref` traps on under-init markers; the static binding rule plus lambda-body exemption make that trap unreachable in accepted programs; the analyzer's environment check (B4) is the proof obligation, this trap is its test.

## 6. Trap ↔ compile-error concordance (the oracle's contract with the analyzer) — **thirteen classes** [count stated — erratum 2026-07-18; the fourteenth, unprintable-interpolation, deleted by the total-interpolation ruling]

| Oracle trap | Analyzer obligation it mirrors |
|---|---|
| unbound-evaluation | B4 environment check; the boundness theorem |
| world-admission | B5 admission matrix (act-kind metadata, C§13.2) |
| expecting-seat | E10 expecting-seat rule; completion demand in `analyzeOperation(application)` |
| argument-obligation | C§13.2 input obligation at call boundaries |
| operation-safety | C§7 per-op safety verdicts |
| undischarged-Indeterminate | C§7 forced discharge at demand sites |
| null-receiver / absent-field / index-bounds | E6 access demands (`HasField`, bounds, non-null) |
| tested-seat | E10 strict Boolean at tested seats |
| refuted-binding | E9 destructuring irrefutability |
| spread-kind / computed-key | E5/E3 construction and call obligations |

Soundness, per class, becomes a property test: generate accepted programs, run the oracle, assert zero traps. Gray programs may diverge; they still must not trap.

## 7. Open-value identity **[RULED — user, 2026-07-17]**

Writing `==` for mutually recursive values forces the semantics-ledger fork (B4) into the open. Self-reference is ruled and closed: `x = [() => x]` canonicalizes at its own statement's end (window = the executing binding statement); `y = [() => y]` and `z = [() => z]` intern equal. The **group** case is the fork:

```
a = [() => b]        // at this statement's end, b is still open:
b = [() => a]        //   a's closure carries a marker for b
a2 = [() => b]       // after b closes — is a2 == a ?
```

**Strict openness**: open values cannot finalize until their group closes; identity is canonical-by-group — `a2 == a` holds, but the machinery tracks group windows. **Nominal markers**: markers are name-keyed; values flow while open; identity is construction-relative — whether `a2 == a` holds depends on marker resolution rules. **The oracle must implement one to run this program.** **RULED: strict openness — shape is identity.** The group *is* `y = [() => y]` written in two statements: construction is not identity, shape is. Hence `a2 == a`, and a shape-symmetric group collapses into the self-loop (`a == b == y`) — the coherent consequence, embraced. Location markers remain nominal (the split rule — state-touching closures never shape-merge). The mechanism (group windows, joint μ-canonicalization, late-twin fold-in) lands with §5; until then these `==` cases are PENDING-§5 with expectations fixed.

## 8. Conformance and harness laws

The oracle implements §§1–4 exactly; the normalizer (built immediately after, same sitting — Part I) is checked against it from day one: `eval ∘ normalize = eval`, idempotence, per-rule brute force. Conformance seeds joining Part I's suite: one program per §6 trap class (must trap unaccepted, must be rejected by the analyzer later); the §7 group-identity pair; the desugar-equivalence rows from the AST spec §8; a nested-mutator join case (inner writes invisible until outer completion); a read-your-writes case; an equality-guard no-op write (zero notifications when the reactive layer lands); the `?? vs ~||` false pair; grapheme index/slice cases pinned to the Unicode table version.

*End of Semantics Companion v0.1. Nothing remains before `cargo init`.*
