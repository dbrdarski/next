# NEXT — Conformance & Regression Test Suite Specification v0.1

**Date:** 2026-07-17. **Status:** the owed **A/B regression suite** (C§17/J3), assembled as a specification Claude Code implements as test files, phase by phase. The oracle is the judge for every runtime claim; the analyzer (later) is judged *against* the oracle via the trap concordance. **Verdict vocabulary:** `VALUE v` (evaluates to v — for data values, pointer-equal to v) · `TRAP class` (semantics §6) · `DIVERGES` (fuel-limited by harness) · `PARSE-ERROR` / `LEX-ERROR` · `DESUGAR≡` (surface form and hand-built kernel form are structurally identical post-desugar AND eval-equal) · `ACCEPT` / `REJECT(witness)` / `GRAY` / `LINT name` (analyzer phase) · tags `PENDING-§5`, `PENDING-F7`, `PIN-UNICODE`, `PROVISIONAL`, `RECOVER`. Test IDs are stable; never delete a case — supersede with a note.

---

## Phase 0 — Value layer (numbers, interning)

| ID | Case | Expected |
|---|---|---|
| N-01 | `0.1 + 0.2 == 0.3` | VALUE true — the exactness flagship |
| N-02 | `(1/3) * 3 == 1` | VALUE true |
| N-03 | printing: `1/2`→`"0.5"` · `3/20`→`"0.15"` · `1/8`→`"0.125"` · `1/3`→`"1/3"` · `-1/2`→`"-0.5"` · `5`→`"5"` | per B2 (primes ⊆ {2,5} rule) |
| N-04 | `1e-2 == 1/100` · `.5 == 1/2` · `0xFF == 255` · `1_000 == 1000` | VALUE true each |
| N-05 | `123n` · `017` · `5.` | LEX-ERROR each, hinted |
| I-01 | `[1,2] == [1,2]` and harness `ptr_eq` | true, same pointer |
| I-02 | `{a:1, b:2} == {b:2, a:1}` | true, same pointer (field order ∉ identity) |
| I-03 | `2/4` and `1/2` | same pointer (canonical reduction) |
| I-04 | equal strings; equal nested structures share subtrees | same pointers; structural sharing observable in harness |
| FE-01 | `f = x => x + 1; g = f; f == g` | VALUE true |
| FE-02 | `makeAdder = n => x => x + n; makeAdder(1) == makeAdder(1)` | VALUE true (same code object + equal capture); `makeAdder(1) == makeAdder(2)` false |
| FE-03 | `x => x + 1` vs `y => y + 1` (two source sites) | interim false — **PENDING-§5** flips to true |
| FE-04 | `y = [() => y]; z = [() => z]; y == z` | **PENDING-§5** (F7 flag retired — closures intern) |
| FE-05 | group pair: `a = [() => b]; b = [() => a]; a2 = [() => b]; a == a2` | VALUE true **[RULED — shape identity, 2026-07-17]**; PENDING-§5 mechanism |
| FE-06 | symmetric collapse: the same group plus `y = [() => y]`: `a == b` and `a == y` | VALUE true, true **[RULED — the two-steps-of-y principle]**; PENDING-§5 |
| FE-07 | same parameter pattern, body, and captures, different `actKind` (`pure () => 1` vs `effect () => 1`) | VALUE **unequal** — actKind is part of the canonical Lambda key [companion review 2026-07-21] |

## Phase 1 — Lexer & parser (grammar v0.1)

**P-01…P-15 — the E2 worked parses**, each asserting the exact grouping: `a |> f |> g ≡ g(f(a))` · `f <| g <| x ≡ f(g(x))` · `a |> f <| b` PARSE-ERROR (mixing ban) · `values |> # f(_, k) |> g(_)` two whole hask stages · `# _ * 2 + 1` · `# _ > 0 ? "pos" : "neg"` binds whole · `#( _ :: { … } )` grouped match-hask · `(# f(_))(x)` · `a |> b :: {…} ≡ (a |> b) :: {…}` · `x :: {…} |> f` pipes the match result · `a ?? b || c ≡ (a ?? b) || c` · `-x ** 2 ≡ -(x ** 2)` · `2 ** -3` legal · `t[-2...]` · `u?.name.first` parses (semantics judged later).

| ID | Case | Expected |
|---|---|---|
| P-16 | `a ?.5 : b` | ternary with `.5` (T1 lookahead — no `?.` token) |
| P-17 | `t[1...3]` | slice — lexes `1` `...` `3` (trailing-dot ban synergy) |
| P-18 | `x => {}` | arrow returning empty Record |
| P-19 | `@effect f = () => { }` | empty act **Block** (1.0.3 brace exception) |
| P-20 | two statements on one line | PARSE-ERROR (L1) |
| P-21 | two arms on one line in an arm block | PARSE-ERROR (L2) |
| P-22 | `when = 5` and `where = 2` as plain bindings | ACCEPT — zero reserved words; contextual only in their seats |
| P-23 | multi-line pipeline (operator-leading continuation) | one expression; leading-`-` case flagged LINT later |
| P-24 | `` `a${ {b: "}"} }c` `` | template brace-depth: one interpolation |
| P-25 | `/* /* */` | one comment (non-nesting), then code |
| P-26 | `[a, , c]` | PARSE-ERROR (no elision); `{ x: 1, x: 2 }` PARSE-ERROR (duplicate literal keys) |
| P-27 | `import { area } from Geometry` · `import Oddo.Utils` · headerless file with `export` | third: PARSE/PROJECT error (header required iff exports) |
| P-28 | `name = @effect (x) => {}` | PARSE-ERROR (value-side @ does not exist) |
| P-29 | pattern `[_, x, ..._, y]` | legal (middle rest, one per level); `[...a, ...b]` PARSE-ERROR |
| P-30 | `p₁ | p₂` with a named capture inside an alternative | REJECT (binding-free rule; may be parse- or analyzer-phase — either, with the right message) |

## Phase 2 — Desugar equivalences (AST §4, one per row)

D-01 `c ? t : e` ≡ Match true/false arms · D-02 `a && b` · D-03 `a || b` · D-04 `~a || b` ≡ falsy-set match · D-05 `~a && b` · D-06 `!x` · D-07 `!~x` · D-08 `a ?? b` ≡ null-arm match (scrutinee once — side-effect counter proves single evaluation) · D-09 block body ≡ scrutinee-less Match · D-10 `p₁ | p₂ => e` ≡ two arms · D-11 `^name` ≡ equality guard · D-12 `x +:= e` ≡ `Write(x, PrimOp(+,…))` (each compound) · D-13 `a.b.c := v` ≡ read→update→one Write · D-14 `items[1...3] := r` ≡ splice Write · D-15 hask forms: `# f(_, k)` · `# _1 + _1` (hole reuse) · `#([..._1])` · `^_` escape from arm block · nested `#` fresh numbering · D-16 `x |> f` ≡ `Apply(f,[x])`, `f <| x` same.

Each row: structural equality of desugar output with the hand-built kernel term, plus oracle eval-equality on sample inputs.

## Phase 3 — Oracle semantics

**T-01…T-13 — one minimal program per trap class [renumbered — erratum 2026-07-18]:** unbound-evaluation (`f()` before `f = …` at same level... via forward *call* at evaluation; **and, under Option A, observation of an open group member — MU-18** [companion review 2026-07-21, pending the author's ratification]) · world-admission (`fetch(url)` in a pure function; `Write` outside mutator; effect called from mutator) · expecting-seat (`x = m()` where m's Match falls through) · argument-obligation (`((a, b) => a)(1)`) · operation-safety (`1 + "a"`) · undischarged-Indeterminate (`(1/0) < 3`) · null-receiver (`null.x`) · absent-field (`{a:1}.b`) · index-bounds (`[1,2][5]`, `[1,2][-3]`) · tested-seat (`5 ? a : b` post-desugar guard) · refuted-binding (`[a, b] = [1]`) · spread-kind (`f(...5)`, `{ ...[1] }`) · computed-key (`{ [5]: v }`). *(The former fourteenth class, unprintable-interpolation, is deleted — interpolation ruled total [user, 2026-07-18]; see PR-01…05.)*

| ID | Case | Expected |
|---|---|---|
| PR-01 | `` `${[1, 1/3]}` `` | VALUE `"[1, 1/3]"` — literal rendering, B2 numbers |
| PR-02 | `` `${{b: 2, a: 1}}` `` | VALUE `"{a: 1, b: 2}"` — canonical sorted-key order |
| PR-03 | `` `${["x"]}` `` | VALUE `"[\"x\"]"` — strings quoted-and-escaped inside structures |
| PR-04 | `` `${f}` `` for any function · `` `${1/0}` `` and `` `${2/0}` `` | `"<Function>"` · both `"<Indeterminate _/0>"` — determinism under interning |
| PR-05 | property: parse ∘ print = identity on the **source-renderable fragment** (Boolean, Null, Number, nested-seat String, and Tuple/Record recursively over those) | harness law [scoped, companion review 2026-07-21] |
| PR-06 | `` `${"abc"}` `` — top-level String interpolates raw | VALUE `"abc"` (no quotes); **explicitly outside PR-05's property** |
| PR-07 | `` `${{a: 1, ["a-b"]: 2, ["two words"]: 3}}` `` — non-IDENT keys | VALUE uses computed-key syntax, keys in UTF-16 code-unit order; reparses to the same pointer |
| PR-08 | quoted rendering of a String holding a lone surrogate unit | the unit is escaped individually (`\uD800`), never U+FFFD — lossless UTF-16 round-trip |
| PR-09 | `` `${[1, () => 1]}` `` — aggregate containing a Function | VALUE deterministic display text; **not** claimed parseable (no PR-05 assertion) |
| O-01 | `{a: null}.a` then `.b` on the result | first VALUE null; then TRAP null-receiver — stored null is data (E6) |
| O-02 | `u?.name` with u null · `{a:1}?.b` · `[1]?.[9]` | VALUE null each — one step |
| O-03 | `u?.name.first`, null arriving | TRAP null-receiver at the second hop (one-step rule) |
| O-04 | slices: `t[...10]` on 3-tuple · `t[5...]` · `t[2...2]` · `t[-2...]` · `t[...]` | clamp / `[]` / `[]` / last two / same pointer |
| O-05 | partition: `[...t[...k], ...t[k...]] == t` | VALUE true, same pointer |
| O-06 | `t[-1]` on `[1,2,3]` · on `[]` | VALUE 3 · TRAP index-bounds |
| S-01 | `String.length("👨‍👩‍👧")` = 1 · `s[0]` whole cluster · `s[-1]` last grapheme | **PIN-UNICODE** |
| S-02 | `String.units(s)` / `String.points(s)` lengths differ from grapheme length on astral/ZWJ cases | **PIN-UNICODE** |
| S-03 | slicing never splits a surrogate pair or combining sequence | **PIN-UNICODE** |
| X-01 | `~0 \|\| b` | VALUE 0 — zero is truthy (falsy = {false, null} exactly) |
| X-02 | `a ?? b` vs `~a \|\| b` with `a = false` | null-coalesce keeps false; escaped-or selects b — the ruled distinction |
| M-01 | read-your-writes: mutator writes then reads same slot | sees pending value |
| M-02 | nested join: outer mutator → inner mutator writes → harness inspects σ before outer completes | committed store unchanged until outermost completion; then one publish |
| M-03 | equality-guard: write an equal value | committed pointer unchanged (harness ptr check) |
| M-04 | outer mutator diverges after inner completed (fuel) | DIVERGES; σ unchanged — never-completed publishes nothing |
| M-05 | `x = someMutator()` | TRAP expecting-seat (current return-nothing law); bare call at statement seat fine |
| M-06 | effect: mutator statement then read | subsequent statements see published state |
| FL-01 | host fetch-double returns Failure; `data.body` unguarded | TRAP absent-field — the runtime face of the analyzer's union rejection |
| FL-02 | `then`/`catch` prelude over `\|>`: happy chain · failing chain · catch-collapse to plain value | VALUEs per B6; failure passes stages untouched |
| FL-03 | bind a Failure, keep executing, match it later | failure is inert data — no control transfer |
| MOD-01 | act call at module top level | REJECT (world/parse per grammar §2.1) |
| MOD-02 | entry-file top level calls effects | runs (effect world — the derived rule) |
| MOD-03 | `import { count }` from a store module; invoke its mutator; read | live — sees new value |
| MOD-04 | `m = Counter; m.count` after mutation | live, equals `Counter.count` (aliasing) |
| MOD-05 | two files declaring `module X` | one project-wide error naming both |

## Phase 4 — Normalization harness (property-based, from day one)

| ID | Law | Method |
|---|---|---|
| H-01 | `eval ∘ normalize = eval` | every normalization rule; generated expression space, oracle both sides |
| H-02 | `normalize ∘ normalize = normalize` (idempotence) | same generator |
| H-03 | per-rule brute force | enumerate small expressions per rule shape; oracle-check each rewrite |
| H-04 | Mutator barrier | a program whose meaning would change if a box read moved across a `Write`; eval equal pre/post normalization — the barrier held |
| H-05 | polynomial NF | `x => x + x` and `x => 2 * x` normalize to one canonical body (feeds §5 function equality — PENDING-§5 for the `==` observation) |

## Phase A — Analyzer verdict suite (specified now; runs when the analyzer exists)

**A-NEG — the negative battery (Part D§6): verdicts must never change, under any future families/analysis work.** factorial · countdown−2 · broken fibonacci → **REJECT** · collatz → **GRAY** · the −4 trap → excluded per battery record · McCarthy 91 → **proven, all reals** · Ackermann · isEven/isOdd (both variants) · non-tail mutual · Hofstadter → **GRAY** · gcd. Verdict details as recorded in D§6; this battery is the anti-regression tripwire for the entire recursion arc.

**A-ACC — the acceptance battery (D§6), two layers each:** the *runtime trace* (oracle-checkable now — e.g. `x = makeLinkedList(1,2,3,4)`: `x.next.next.next.value == 4`; `x.next.next.next.next == null`; `.value` on that null TRAPs — the same case the analyzer must refute with witness `(null, "value")`) and the *contract claim* (analyzer-phase: proven facts per the battery — builder, map incl. parametric, reverse incl. `rev ∘ rev` interning to input, zip, level-regular tree, fold BOUNDED, filter depth-Range, cyclic mutual builders incl. 3-cycles, cross-axis mutual, insert/delete, append, flatMap rectangular, merge/sort depth-exact, walkers, `pairUp` ×3, `rotate` (`r.next⁷.top ⊑ Equals("y")`), UniformFamily guard arithmetic).

**A-SND — soundness harness (the C§16 pattern):** (1) generate programs from the accepted subset → analyzer ACCEPTs → oracle runs → **zero traps**, per trap class; (2) sample values from operation input contracts → run the op through the oracle → every result within the claimed output contract, per `analyzeOperation` row; (3) gray programs may diverge but must not trap.

**A-VER — verdict cases:** `a < b < c` → REJECT with the chain hint · `(a == b) == c` legal iff c Boolean · exhaustiveness proofs over the E9 remainder semantics · computed keys: finite union ACCEPT / `Kind(String)` REJECT · destructuring irrefutability · `data.body` on `Union(Response, Failure)` → REJECT until narrowed · Failure-overlap wrapper demand at an adapter boundary · act-kind admission over a union of callees (possibly-effect in mutator world → REJECT) · the E5 discharge: `Indeterminate(_/0) => fallback` arm ACCEPTs the division consumer.

**A-LNT — lint tier, one case each:** goes-nowhere bare pure expression · discarded fallible-effect result · identity slice `t[...]` · redundant `?.` · redundant `~` · non-Boolean right of unescaped `||` · leading-`-` continuation · self-prefix module reference.

**A-WRK — worked-example grids [RECOVER]:** the factorial grids, drift pairs, and the even/odd fact-cycle pair are named in Part I with full program text and expected contract tables in the project transcripts (see `journal.txt` catalog); recover verbatim at implementation time — do not reconstruct from memory. The environment-transforming factory (C§13.3's `make`) is fully specified in-document: instance-chain cutoff → the recorded verdict, unchanged by any families work (deferred-claim form, D§9). **DISCHARGED (2026-07-21):** recovered verbatim into `next-phase-a-worked-examples-recovered.md` (grids 1–9 with per-item transcript provenance); the transcript pointer is superseded for repo purposes — `journal.txt` was the drafting agent's transcript-mount catalog, never a repo file.

## Registers

- **MU-18 / MU-19 [companion review 2026-07-21]:** MU-18 — an unrelated statement observing an open group member (`a = [() => b]; seen = a == a; b = [() => a]`) is **rejected** by the analyzer, and the oracle traps it under the ratified class (Option A: `unbound-evaluation`). MU-19 — a *same-group construction* reference stays **legal** (internal μ edge, never a read); the pair fixes the boundary in both directions.
- **PENDING-§5:** FE-03, FE-04, FE-05, FE-06, H-05's `==` observation — flip to positive when the canonicalizer lands; until then expected-fail, and no test may assert the interim inequality as desired behavior.
- **PENDING-F7:** retired 2026-07-17 — universal interning restored (closures shallow-keyed); FE-04 is PENDING-§5 only.
- **PROVISIONAL:** empty — FE-05 ruled 2026-07-17; register retained for future items.
- **PIN-UNICODE:** S-01…S-03 — pinned to the `unicode-segmentation` version; a Unicode upgrade is a semantics-version event (C§13.4): re-pin deliberately, never silently.
- **RECOVER:** A-WRK grid texts from transcripts.

## Coverage map (comprehensiveness check)

Grammar v0.1 §§1–8 → P-01…P-30 (every lexical rule T1–T3, L1–L2, brace/`_`/`...` disambiguation). Kernel AST §4 → D-01…D-16 (every desugar row). Semantics §3 → O/S/X/M/FL/MOD (every node's rules) and §6 → T-01…T-13 (every trap class, bijectively — thirteen since the interpolation ruling). Compendium B2 → N-01…N-05; B5/B7 → M-01…M-06; B6 → FL-01…FL-03; E6/E7/E8 → O-01…O-06, S-01…S-03; E10 → X-01/X-02, T (tested-seat, expecting-seat); E12 → MOD-01…MOD-05; Part D → A-NEG/A-ACC; C§7/C§16 → A-SND; lints → A-LNT. Gaps are bugs in this document — file them against it.

*End of Test Suite Specification v0.1. Implementation note for Claude Code: phases 0–4 are buildable immediately alongside their build-order steps; Phase A files compile as `#[ignore]`d stubs with their expected verdicts recorded, activated when the analyzer phase opens.*
