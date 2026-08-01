# NEXT — Kernel AST Specification v0.1

**Date:** 2026-07-17. **Status:** the **normative contract** promised by Part A's *semantics-over-form* principle — the kernel AST and its semantics are the language; surface syntax is one official rendering (the grammar spec, v0.1). The parser **emits** this AST; the oracle interpreter **evaluates** it; the normalizer **rewrites** it under the equal-under-rules doctrine; the analyzer's identity layers key on its canonical forms. Everything below is assembled from the Design Compendium v1.0 (1.0.3); parked act-cluster forms are extension points (§7). No new semantics is introduced here — where a representation choice existed, the choice is named and tagged.

**Doctrine carried in (normative context):** code is data — kernel forms are **eagerly interned canonical values**; equivalence-under-rules is pointer comparison (Part A P5, C§11). Nodes carry **no source spans**: provenance lives in the occurrence→span **side table** (B4), so interned code stays position-free while diagnostics keep demand origin, reference site, and resolution failure. The three function-identity layers (value / shape / analysis-instance, C§12.3) key on the canonical forms defined here; **act-kind is a component of function shape** (C§13.2, 1.0.2). Statement normalization **never moves box reads across a Mutator boundary** (B5 dep 3).

---

## 1. Node inventory — expressions

Every expression node evaluates to an interned value (B1 — universal; closures shallow-keyed) or participates in an act body's sequencing. `Expr :=` one of:

**`Const(v)`** — an interned value embedded directly. Post-resolution form of literals and of the prelude names `true`/`false`/`null` (which are bindings at the surface, values in canonical code). Numbers are exact rationals (B2); strings UTF-16 (B1); functions appear as `Const` only via `Equals(<interned function value>)`-style constancy — lambdas construct, `Const` embeds what construction produced.

**`Ref(b)`** — a reference to a binding. Three resolved flavors, matching value-identity layer 1 (C§12.3, F3): an **immutable-binding reference** (canonicalizes positionally, de-Bruijn-style, for the cache keys of C§13.4); a **μ-marker** for self/group references still under initialization (rational-tree comparison; the marker, not a back-pointer, keeps code acyclic); a **location marker** for Box-binding references — evaluation is a dynamic read of current content (B4), and the marker participates in function identity (same-body closures over distinct locations are distinct values, B1/1.0.2).

**`Lambda(paramsPattern, body, actKind)`** — the only function form. `paramsPattern` is a **pattern over the complete argument tuple** (the arity model, E3): integer arity is the exact-tuple special case; rest, nesting, and destructuring are ordinary pattern structure (§3). `body` is an `Expr` or a `Match` block-form (§1's Match). **`actKind ∈ {pure, mutator, effect}`** — pure by default; set by the `@`-declaration that binds the lambda (E13/E14); a component of **shape**, inherited by instances, checked at application seats against the world admission matrix (B5, 1.0.3). Reactive-layer kinds (`@reactive`, `@computed`) are G1's fence; the kernel sees them as extension-point act kinds (§7).

**`Apply(callee, args)`** — application; `args` is a sequence of `Expr | Spread(Expr)` (multiple spreads legal, strict left-to-right evaluation, E3). One node for all calls; the operation rule is C§7's n-ary `analyzeOperation(application, …)` carrying the input-obligation check, conservative row selection, act-kind admission [1.0.2], and the expecting-seat completion demand [1.0.2].

**`PrimOp(op, args)`** — the built-in operation node: unary/binary arithmetic (`+ - * / % **`, unary `-`), comparisons, `==`/`!=`, string concat. Each op is a row in the `analyzeOperation` tables (C§7); division is total via Indeterminate values; **no truthiness, logic, or conditional op exists here** — those desugar to `Match` (§4).

**`Match(scrutinee?, items)`** — **the sole control node** (E10: a block is a match with implicit scrutinee; one kernel node). `scrutinee` optional; `items` is an ordered sequence of `Bind | Stmt | Arm(pattern?, guard?, result)`. Semantics: items run in order; an `Arm` tests (pattern against scrutinee when both exist; guard as a strict-Boolean tested seat, E10) and on success **exits the node** with `result`; each later arm sees exactly the remainder — the accumulated Difference (E9); exhaustiveness is the subcontract call; guarded arms consume pattern-region ∩ guard-contract, opaque guards consume nothing (uncertainty selects). **Completion outcome** (E10, 1.0.2): evaluating a `Match` yields `Produced(value) | CompletedWithoutValue | DidNotComplete` — the middle outcome is not a value and never becomes one; expecting seats add the all-completing-paths-produce demand.

**`TupleCons(items)`** — `items`: `Expr | Spread(Expr)`; middle spreads legal; no elision (E5). Feeds the tuple-length/concatenation rule family (C§17 owed).

**`RecordCons(fields)`** — `fields`: `Field(key, Expr) | ComputedField(keyExpr, Expr) | Spread(Expr)`; evaluation later-wins; literal-literal duplicate keys are rejected upstream (E5); computed keys demand proven-finite string sets (E5, fork 12 = R).

**`Access(target, form, total)`** — the one access node (E6): `form ∈ { Field(name), Index(Expr), Slice(lo?, hi?) }`. `total = false` is the **demand form** (receiver provably non-null; field provably present / index provably in bounds — compile error at the hop otherwise); `total = true` is the **`?.` family** (one-step null conversion — the produced null travels as an ordinary value). `Slice` ignores `total` — slices are clamped-total always (E7); negative indexes/bounds address from the end. **`?.` must be a kernel mode, not sugar**: absent-field totalization has no userland probe (E6's one-nothing doctrine), so it cannot desugar.

**`Template(parts)`** — `parts`: interleaved string segments and `Expr` interpolations. Kept as a kernel node **[representation choice — tagged]**: interpolation stringification is B2's rational-printing rule and its kin, which is runtime semantics, not a userland call; normalization may fold adjacent literal segments. Interpolations are pure by jurisdiction (E1).

**`Write(slotRef, Expr)`** — the mutation primitive; legal only inside `mutator`-kind bodies (world jurisdiction, E14); `slotRef` is a location marker for a `@state`/`@mutable` binding. All compound and path/slice mutation forms desugar to `Write` of a functionally-updated value (§4). Runtime semantics: pending-set staging, read-your-writes, publication at outermost completion, the interning-exact equality guard (B5, B7, G1).

**`Spread(Expr)`** — not an expression itself; the element wrapper used inside `Apply`/`TupleCons`/`RecordCons` args (the three roles of `...`; the pattern-side rest is §3's, the slice form is `Access`'s).

## 2. Node inventory — declarations and module structure

**`Module(name?, items)`** — `name` present iff anything exports (E12); `items` ordered. Module top level is pure world: `Bind`, `SlotDecl`, `ActBind`, `Import`, `Where` only — **no act calls** (E12; `SlotDecl` is declarative allocation, ruled legal [user]).

**`Bind(target, Expr, exported?)`** — `target` is a name or an irrefutable pattern (destructuring binding; irrefutability policed by the analyzer, E9). Late binding governs references (B4).

**`SlotDecl(reactive, name, initExpr, exported?)`** — declares a Box location: `reactive = true` for `@state`, `false` for `@mutable` (the 2×2, B7); `initExpr` pure. Exported slots export the **binding** — importers get live reads (E12, corrected); the location is never a value.

**`ActBind(kind, name, Lambda, exported?)`** — binds a mutator or effect declaration (`@mutate`, `@effect`); sets the lambda's `actKind`; statement-position only (E13). The default mutator (B7) is an analyzer/runtime-derived `ActBind`, not a distinct node.

**`Import(names?, moduleName)`** — binds imported names to the source module's **bindings** (aliasing; live for slots); the bare form aliases the namespace (E12). Static whole-program resolution (C§14); no runtime node semantics — imports are link structure.

**`Where(name, inputContract, returnContract)`** — the name-level signature assertion (E11): verified `DeclaredInput ⊑ InferredAcceptedDomain`, `DerivedReturn ⊑ DeclaredReturn`; never trusted, never a mode; analyzer-facing metadata, no evaluation behavior.

**`Stmt(Expr)`** — a bare expression statement (goes-nowhere warning in pure positions; the normal statement form for act calls in act bodies, B5).

## 3. Kernel patterns

`Pat :=` **`PConst(v)`** (literals and prelude constants) · **`PBind(name)`** (fresh binding; may shadow) · **`PWild`** · **`PTuple(elems, rest?)`** · **`PRecord(fields, rest?, exact)`** · **`PContract(ref)`** (matches value ⊑ contract, consumes by intersection — contracts-as-patterns, E9/E11; Kind patterns, user contracts, Indeterminate and Failure discharge all this one form).

Invariants: patterns are **exact by default** — `rest` opens (captured or ignored); **one rest per level**, middle position legal in tuples; record rest-capture is record subtraction with the three-tier contract account (E9). **Pins do not exist in the kernel** — `^name` desugars to an equality guard (E9: "equality-guard sugar"). **Alternation does not exist in the kernel** — `p₁ | p₂` desugars to arm expansion (§4), sound because alternatives are binding-free (E9) and interned results deduplicate. Hask escapes (`^_n`) desugar with their hask. Parameter patterns are this same grammar minus pins/alternation by construction.

---

## 4. The desugaring catalog (surface → kernel; closed and normative)

Every surface form not named in §§1–3 lowers here, **before identity and contract analysis** — the analyzer never sees sugar.

| Surface | Kernel |
|---|---|
| `# expr` (hask) | `Lambda` over the hole positions; fresh numbering per nested `#`; `^_n` escapes rebind to the enclosing generated lambda's parameters (E4) |
| `x \|> f` · `f <\| x` | `Apply(f, [x])` — application, nothing else (E2) |
| `c ? t : e` | `Match(∅, [Arm(guard: c, t), Arm(e)])` — **the condition is a strict tested seat** [RULED — user, 2026-07-22]: guard-based and scrutinee-less, so a non-Boolean traps **tested-seat immediately, regardless of result position** |
| `a && b` | `Match(∅, [Arm(guard: a, b), Arm(Const(false))])` (E10's `a ? b : false`) [RULED — user, 2026-07-22] |
| `a \|\| b` | `Match(∅, [Arm(guard: a, Const(true)), Arm(b)])` [RULED — user, 2026-07-22] |
| `~a \|\| b` · `~a && b` | selection matches over the exact falsy set: `Match(a, [Arm(PConst(false), …), Arm(PConst(null), …), Arm(PBind(x), …)])` — the truthy arm's narrowing **is** the accumulated Difference `Difference(C, {Equals(false), Equals(null)})`; no truthiness primitive exists (E10) |
| `!x` | `Match(∅, [Arm(guard: x, Const(false)), Arm(Const(true))])` [RULED — user, 2026-07-22] |
| `!~x` | the falsy-set match emitting Booleans |
| `a ?? b` | `Match(a, [Arm(PConst(null), b), Arm(PBind(v), Ref(v))])` — scrutinee evaluated once; differs from `~a \|\| b` exactly on `false` (E10) |
| block bodies | the same `Match` node, scrutinee absent, bindings/statements interleaved (E10 — one kernel node) |

**The strict-tested-seat lowering [RULED — user, 2026-07-22; resolves the T-10/D-01 conflict].** The general recipe is
**bind-then-guard**: bind the tested operand to a temporary, then guard on it — the binding is what preserves single
evaluation for lowerings that reference the tested value *again* in a result. In the four rows above the recipe is
**degenerate**: each tested operand occurs exactly once, in the guard, and the results are branch expressions or Boolean
constants — so no temporary is needed and none is emitted. Recorded here so the simplification is visibly the same law
rather than a shortcut. **Behavioral delta from the superseded PConst-arm rows:** a non-Boolean operand previously fell
through every arm to `CompletedWithoutValue`, surfacing as an **expecting-seat** error only at a demanding seat and not at
all at a statement seat; it now traps **tested-seat** at the operand, immediately, in every position — which is what C§E10
requires ("tested seats demand `Kind(Boolean)` **on arrival**, checked and propagated like every operation demand") and what
C§7's fire-even-when-unused discipline requires. Boolean operands are observably unchanged. **The escaped `~` forms and
`??` keep their falsy-set / null-set matches** — they are not tested seats; only the four rows above are.

| `p₁ \| p₂ => e` | arm expansion: `Arm(p₁, e); Arm(p₂, e)` — remainder = union of consumptions, unchanged |
| `^name` in a pattern | equality guard on the arm |
| `x +:= e` (and family) | `Write(x, PrimOp(op, [Ref(x), e]))` |
| `a.b.c := v` | `Write(a, ⟨functional update of read a with b.c ↦ v⟩)` — read → pure update → one Write, atomic in the transaction (B5) |
| `items[a...b] := r` | `Write(items, ⟨spread-composed splice⟩)` (E7) |
| `[name, age] = e` | `Bind(PTuple…, e)` — kernel keeps pattern bindings; no accessor expansion (preserves exactness contracts) |
| string escapes, numeric forms | resolved at lexing; kernel sees interned values |

**Not sugar (kernel-resident, with the reason):** `?.` totals (no userland absence probe); slices (window semantics + length contracts); spreads in construction/calls (tuple-concat transfer rules need them); `Template` (printing semantics); `Match` remainder/exhaustiveness; `Write` (the act primitive); patterns' exactness/rest structure.

## 5. Canonicalization and identity

Kernel forms intern like every value: construct → shallow hash → probe (F1). Canonical bodies replace immutable-binding names with positional (de-Bruijn-style) references — the C§13.4 cache keys' "de-Bruijn-ordered free-variable contract tuple" presumes exactly this; μ-markers canonicalize rational-tree style (C§9, F3); location markers canonicalize per fork 13's binding-identity (same binding ⇒ may intern equal; distinct bindings ⇒ distinct). **Act-kind is part of the shape key** [1.0.2]. Statement-sequence normalization inside act bodies respects the Mutator barrier — box reads never move across it (B5 dep 3; prose owed, J3). Normalization laws the harness enforces from day one (Part I): `eval ∘ normalize = eval`; idempotence; brute-forced per-rule checks against the oracle.

## 6. Worlds, completion, and evaluation hooks

A body's **world** derives from its `Lambda.actKind` (never from lexical nesting of ordinary lambdas — E14's world model): `Write` legal only in mutator world; `Apply` of an act-kind callee legal only where the admission matrix admits it (B5, 1.0.3): pure→{pure}; mutator→{pure, mutator — joining the transaction}; effect→{pure, mutator, effect}. **Completion** is §1's triple on `Match`; act bodies complete vacuously (no coverage obligation); Mutator completion is the publication point (B5). Evaluation order is strictly as written, left to right, spreads included (E3); act occurrences fire when evaluation reaches them (B5) — the kernel has **no** occurrence-moving transformation.

## 7. Extension points (parked; land as additive node/kind entries)

New `ActBind` kinds for the reactive fence (`@reactive`, `@computed`) and any future residents; the `require`-shaped entry prohibition as a declaration-attached demand node; gray-acknowledgment / strict-mode / `@suppress` / `@proof` as declaration metadata (suppression pre-constrained: grounding only, Part A); guarded-act arm semantics as an `Arm` variant in act bodies if ruled; a Mutator-return channel on `ActBind(mutator)` if the leaning stamps; module value-seat reification if the narrow open (E12) is ever defined. None disturbs §§1–6.

## 8. Conformance

A conforming pipeline: parser (grammar v0.1) → **desugar (§4, closed)** → intern (§5) → oracle evaluation (§6 semantics; the truth source) and, later, analysis (Parts C/D) over the same canonical forms. The oracle implements: interned values (closures shallow-keyed), late binding, the falsy-set matches, one-step `?.` totals, clamped slices, staging/publication for mutator bodies, Failure values as plain data, the completion triple. Conformance seeds join Part I's suite: every §4 row as a desugar-equivalence case; `x = [() => x]` interning; `y/z` μ-equality; the `?? vs ~||` false-distinction pair; a `Write` equality-guard no-op case; a `CompletedWithoutValue`-at-statement-seat vs expecting-seat pair.

*End of Kernel AST Specification v0.1. The semantics companion is the remaining pre-code artifact.*
