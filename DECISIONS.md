# DECISIONS.md — NEXT implementation changelog

Provenance discipline (CLAUDE.md § Process): what the specs **mandated**, what I
**chose** where a representation was left open, and what I'm **asking** the author.
Status tags mirror the compendium's vocabulary. Newest entries first.

---

## 2026-07-19 — Build-order step 4: normalization + property harness — **BUILD ORDER COMPLETE (the gate)**

`src/normalize/` (mod.rs, tests.rs). Kernel AST §5 + Part I harness laws. 5
normalize tests green (incl. the property harness over a 22-program corpus); full
suite 132 (+2 ignored); clippy clean.

- **Mandated (Part I), the deliverable:** the property harness enforces, against
  the oracle, `eval ∘ normalize = eval` and idempotence
  (`normalize(normalize(m)) == normalize(m)`) over a corpus spanning every node
  kind. This is the machine-checked link between the normalizer and the truth
  source.
- **Chosen — active rule set (small, spec-named, clearly eval-preserving):**
  - Template **adjacent-segment folding** (§4).
  - **Literal template → constant**: a template with no interpolations is the
    string it denotes.
  Everything else is a structure-preserving recursive map, so further rules bolt
  on in one place.
- **Deferred (consistent with the §5 sign-off):** the heavy §5 canonicalization —
  de-Bruijn free-variable ordering and μ-binder canonicalization — is *not* built
  here; it lands with canonical function identity. The harness is designed so
  those rules, once added, are checked by the same `eval ∘ normalize = eval` law.
- **Chosen — outcome comparison:** the harness runs original and normalized forms
  in the *same interner*, so produced values compare by pointer and traps by
  class (`Result<ValueRef, TrapClass>`), giving an exact "same outcome" check.
- **`// [ask-author]`:** none.

### Build-order status: **gate reached.**
Steps 1–4 (value layer → lexer/parser/desugar → oracle → normalization + harness)
are complete and green. Per Part I we **stop here**: contracts / the three-valued
checker / demand core / recursion analysis are the explicitly-gated later phase,
not to be started until the author opens it. Outstanding within the completed
scope: the two `#[ignore]`d §5 function-identity seeds, and the small B6 tail
already noted (all logged).

---

## 2026-07-19 — Build-order step 3 (part 3): B6 effect harness — **oracle complete**

`src/value.rs`, `src/interner.rs`, `src/oracle/` (harness.rs new; eval.rs,
mtch.rs). Semantics companion §4 + B6. 6 effect seeds green; full suite 126
(+2 ignored); clippy clean. **This completes build-order step 3 — the oracle.**

- **Mandated (§4/B6), implemented and tested:**
  - New value kind `ValueData::Native` (pointer-identity `NativeRef`): a
    host-callable that runs Rust when applied — the only way host effects (which
    aren't expressible in NEXT) can exist. `eval_apply` dispatches native-vs-
    closure; natives honour the world admission matrix (effect-kind ⇒ effect world
    only).
  - Host-effect doubles injected by the harness: `println`/`exit` (record into an
    observable `HostIo` buffer) and a fallible `readFile` (returns a Failure).
  - `Failure` is the one prelude Record shape (`path` + `reason`); the `Failure`
    contract pattern matches it structurally (E9 — Failure discharge dissolves
    into contract-as-pattern). A failed effect returns a Failure that flows as
    ordinary data — nothing unwinds.
  - **`then`/`catch` proven to be NEXT library code:** the seed defines them in
    NEXT source (over `Match`) and shows a success flowing through `then` while a
    Failure short-circuits it and is recovered by `catch` — no interpreter
    builtins.
- **Chosen — entry programs need not end in a value:** `run_module_in` now returns
  null when the last statement completes without a value (an entry may end in an
  effect statement), rather than trapping. The expecting-seat demand still fires
  in genuine value positions (bindings, operands, …), which the seeds check.
- **Chosen — line-leading `[`/`(` starts a new statement** (parser): a postfix
  index/call only attaches on the same line as its target; a `[`/`(` opening a
  fresh line begins a new statement (the greedy-continuation hazard, §1.1). `.` /
  `?.` still continue across lines (unambiguous). This is the same class of fix as
  the arrow `=>` line rule.
- **`// [ask-author]`:** none. `exit` as a double records the code and returns
  rather than terminating (the real host limit is outside the semantics, §4).

---

## 2026-07-18 — Build-order step 3 (part 2): worlds + mutator staging

`src/oracle/` (mod.rs, eval.rs). Semantics companion §3 (Apply/Write) + §5
staging theorems. 6 new mutation seeds green; full suite 118 (+2 ignored);
clippy clean. Covers task 3c.

- **Mandated (§3), implemented and tested:**
  - `Write` legal only in mutator world (else `world-admission` trap); stages into
    the pending set π.
  - Slot reads use **read-your-writes** (π if staged, else σ).
  - Mutator application: from mutator world **join** the current transaction (same
    π, no publish); from effect world **begin** (π := ∅), run, and **publish** at
    completion. Mutator Apply outcome is `CompletedWithoutValue` (return-nothing
    law).
  - **Publish** commits only staged slots whose value differs by pointer (the
    interning-exact equality guard, B7/G1); a trap publishes nothing (§5).
  - Effect application runs the body in effect world; the world admission matrix
    (pure→{pure}; mutator→{pure,mutator}; effect→all) is enforced with
    `world-admission` traps on violation.
- **Chosen — commit counter on the store:** the equality guard's "fires nothing"
  is otherwise unobservable without the (fenced) reactive layer, so `Store` counts
  *actual* commits and a `run_program_commits` test helper asserts an equal write
  commits zero times. Test-only observability; no semantic effect.
- **Chosen — "invisible until outermost completion" is tested via join
  accumulation:** in the sequential oracle, σ is only inspectable post-transaction,
  so the nested-join seed asserts the accumulated result (inner write visible to
  outer read via shared π, single publish) rather than mid-transaction σ.
- **Deferred to a small follow-on (B6 effect harness):** host effects (test
  doubles for `println`/`exit`), `Failure` records as plain data, and the
  `then`/`catch` prelude functions. These need a native-callable value kind; the
  mutation core (the delicate part) and effect-world mutator invocation are done.
- **`// [ask-author]`:** none.

---

## 2026-07-18 — Build-order step 3 (part 1): pure oracle core + Match

`src/env.rs`, `src/oracle/` (`mod.rs`, `eval.rs`, `mtch.rs`, `tests.rs`).
Semantics companion §3, the pure fragment. 29 oracle seeds green; full suite 112;
clippy clean. Covers tasks 3a + 3b.

- **Mandated (§3), implemented and tested:** exact rational arithmetic; total
  division (`x/0` ⇒ Indeterminate) with left-most Indeterminate propagation
  through arithmetic; `==`/`!=` as pointer equality (Indeterminate is an ordinary
  value); ordering comparisons trap `undischarged-Indeterminate`; late binding via
  a runtime environment (direct + mutual recursion work); `Match` as the sole
  control node with the completion triple; construction (tuple/record, later-wins,
  spreads); access (field/index/slice, demand vs `?.` totals, from-end,
  clamped-total slices); grapheme string index/slice (pinned `unicode-segmentation`);
  template stringification by B2 rules. Nine trap classes fire end-to-end.
- **Chosen — runtime environment (not §5 resolution):** `Scope` chain with names;
  a binding is marked `UnderInit` while its RHS evaluates, so `x = x` traps
  `unbound-evaluation` while a self/mutually-recursive lambda is fine (its body
  isn't evaluated at bind time). This is the agreed approach (see the §5 deferral
  entry below).
- **Chosen — closures capture the environment by reference** (`Rc<Scope>`), which
  is what makes late binding / mutual recursion fall out. Function identity is
  `ClosureRef` pointer identity (the conservative approximation already signed
  off).
- **Chosen, spec-faithful clarifications:**
  - `tested-seat` trap is **guard-only** (companion §3). A non-Boolean *ternary
    condition* desugars to a Boolean-exhaustive match, matches no arm at runtime,
    and surfaces as `expecting-seat` (the analyzer rejects it up front). Both are
    tested.
  - Contract-as-pattern: the runtime-decidable **Kind** checks (`Number`,
    `String`, `Boolean`, `Null`, `Tuple`, `Record`, `Function`) and
    `Indeterminate` are implemented; user-defined contract patterns trap (they
    need the contract engine — analyzer phase).
  - `%` on rationals is the truncation-toward-zero remainder; `**` supports
    **integer exponents only** (irrational-producing ops are omitted from the PoC,
    B2) — a non-integer exponent traps `operation-safety`.
  - Entry-file top level evaluates in **effect world** (the one derivation the
    companion makes, §2).
- **Deferred to step 3c (part 2):** mutator/effect *application* (worlds admission
  is checked, but a mutator/effect call currently traps a placeholder), `Write`
  evaluation, the pending-set/read-your-writes/publish staging, host effects, and
  Failure records. `DidNotComplete` (divergence) is genuine non-termination, not a
  represented value.
- **`// [ask-author]`:** none.

---

## 2026-07-18 — Decision [user-approved]: defer §5 canonicalization; approximate function identity

Sign-off recorded before starting the oracle (step 3). **What the oracle does:**
evaluates kernel AST by resolving names against a runtime environment (late
binding, B4 / semantics §1 `ρ`) — no de-Bruijn/§5 canonicalization pass is built
yet. **What that costs, in full (nothing else):**

- Function-value identity is *approximate*. Same-meaning functions with different
  written shape (α-equivalent, or equivalent-but-differently-written bodies) may
  intern distinct instead of equal. This propagates to values that *contain*
  functions; pure data (numbers/strings/tuples/records of data) stays exact.
- Observably, only `==` on functions (and function-containing structures) is
  affected. The approximation is **conservative**: it can only *fail to merge two
  equal functions*, never merge two different ones — so no wrong `true`, and no
  effect on any produced non-function value, control flow, world/mutation
  semantics, trap, or completion outcome. Soundness is untouched.
- The `y = [() => y]` / `z = [() => z]` interning seed and the §7 group-identity
  pair stay `#[ignore]`d with a note pointing here, until §5 lands.
- Function-value interning is confined to one place (a `ClosureRef` pointer
  identity for now); swapping in §5's canonical-body key later is a localized
  change and does not touch the oracle's evaluation logic.

**User: "consider it settled."**

---

## 2026-07-18 — Build-order step 2c: desugar to kernel AST

`src/desugar/` (`mod.rs`, `hask.rs`, `tests.rs`). Kernel AST spec §4 (the closed
catalog) + E10. 27 desugar-equivalence seeds green; full suite 83; clippy clean.
**This completes build-order step 2.**

- **Mandated (§4 rows), all implemented and tested:** pipes → `Apply`;
  `? :`/`&&`/`||`/`!` → `Match`; `??` → null-arm `Match` (scrutinee once); `~a||b`
  / `~a&&b` → falsy-set selection matches; `!~x` → falsy Boolean match; hasks →
  `Lambda` over holes; alternation → arm expansion; pins → equality guard; block
  bodies → scrutinee-less `Match`; compound/path mutation → `Write` of a
  functional update; arrows → pure `Lambda` over the argument-tuple pattern (the
  arity model). The `?? vs ~||` false distinction is verified structurally (2 arms
  vs 3).
- **Chosen — output is *pre-canonicalization* kernel AST:** `Ref`s carry
  `BindingRef::Name` and `Write` carries `SlotRef::Name` (added this step). Name →
  positional/location/μ resolution and de-Bruijn canonicalization are §5/analyzer
  work, deliberately not done here — desugar is purely syntactic.
- **Chosen — synthetic names use a `%` prefix** (e.g. `%h0`, `%pin1`, `%hrest0`),
  which no surface identifier can contain (identifiers are `_`/`$`-free
  alphanumerics), so generated bindings never collide with user names.
- **Chosen — hask holes collected on the fly** via a scope stack rather than a
  separate rewrite pass: a `#` pushes a scope, holes register synthetic params,
  popping builds the parameter tuple. Nested `#` opens a fresh scope (E4). v0.1
  supports all-anon, all-indexed, and single-rest shapes.
- **Deferred with a clear `DesugarError` (not silently guessed):** mixing plain
  `_` and indexed `_n` holes; index/slice *mutation* targets (field-path updates
  are done); nested pins and nested alternation; `@computed`/`@reactive` and
  anonymous `@` forms (the fenced reactive layer, G1). Each returns a specific
  error message. These are the honest v0.1 boundaries; none is a semantic
  invention.
- **`// [ask-author]`:** none. Every deferral is either a fenced subsystem or a
  syntactic corner that errors cleanly rather than guessing.

---

## 2026-07-18 — Build-order step 2b: surface parser

`src/parse/` (`surface.rs`, `parser.rs`, `mod.rs`, `tests.rs`). Grammar §§2–5.
30 seed tests green (E2 worked parses + §10); full suite 56; clippy clean.

- **Chosen — two-stage pipeline (surface AST then desugar):** the parser emits a
  faithful *surface* AST that keeps all sugar; lowering to the kernel form is a
  separate pass (2c). The kernel spec calls the desugar catalog "closed and
  normative", so keeping it a standalone, separately-tested pass is the right
  seam. The analyzer still never sees sugar.
- **Mandated (§3 ladder):** full precedence ladder as recursive descent, with the
  settled associativities — pipes `|>` left / `<|` right with the **unparenthesized
  mixing ban** (parse error); `**` right-assoc admitting unary on the right
  (`-x ** 2 ≡ -(x ** 2)`, `2 ** -3` legal); ternary right-assoc; `??`/`||` shared
  tier; unary `-`/`!`/`~` stacking. Hasks as loose prefix (tier 4) with the
  grouped `#(...)` primary for below-tier positions.
- **Mandated (§8):** brace rule (record vs block by first token) applied at arrow
  bodies, with the `@`-arrow forced-Block exception threaded via a parser flag.
  `x => {}` is the empty record.
- **Chosen — statement separation by greedy termination, not line pre-splitting:**
  the parser consumes each statement as far as the grammar allows (the documented
  greedy-continuation behavior), then the next statement begins naturally. Strict
  L1/L2 line *enforcement* (rejecting two statements on one line) is deferred to a
  later diagnostic pass; token lines are preserved for it.
- **Chosen — arrow `=>` must be on the same line as its params.** This is the one
  place L2 is load-bearing for *correctness*, not just diagnostics: without it,
  `x = n` ⏎ `=> x` inside a block greedily reads `n => x` as an arrow and swallows
  the else-arm exit. Requiring the `=>` to sit with its params (bare ident, or the
  matching `)`) resolves it. A `=>` opening a fresh line is a block-body arm.
  Flag: this rejects the unusual `(a, b)` ⏎ `=> body` split-arrow; confirm that's
  acceptable.
- **Chosen — binding/mutation/expression disambiguation** via the statement-only
  operators `=` and `:=`/compounds (which never appear in the expression grammar):
  try a bind target then `=`; else a path then a mutation op; else an expression.
  Save/restore on the token index makes the attempts cheap.
- **Chosen — contextual keywords** (`module`/`import`/`export`/`from`/`when`/
  `where`) committed by seat shape; `import` in particular only commits when a `{`
  or a name follows. A variable literally named after a contextual word in an
  ambiguous head position is a known unsupported edge — flag if it matters.
- **Chosen — pattern classification at parse time (§4/§8):** `true`/`false`/`null`
  → prelude-constant patterns; capitalized identifier → contract pattern; else a
  fresh binding. Alternation `|` and pins `^` parsed structurally (they desugar in
  2c).
- **`// [ask-author]`:** none blocking. The two "flag" items (split-arrow across
  lines; contextual-word-as-variable in head position) are the only confirmations.

---

## 2026-07-17 — Build-order step 2a: lexer

`src/lex/` (`token.rs`, `lexer.rs`, `tests.rs`). Grammar spec §1. 14 seed tests
green; full suite 27; clippy clean.

- **Mandated (§1.4 / §4 desugar):** literals resolved at lex time — `Number`
  carries an exact `Rational`, `Str` carries UTF-16, escapes processed. Numeric
  bans implemented: no BigInt `n` suffix, no legacy octal / leading zeros, no
  trailing-dot. Bases `0x`/`0o`/`0b`, exponents, `_` separators.
- **Mandated (§1.1):** no newline tokens; each token records its line so the
  parser can enforce L1/L2. Maximal munch with T1 (`?.` not before a digit — the
  `a ?.5 : b` seed), T2 (`...` beats `.`), T3 (compound mutation ops are single
  tokens).
- **Chosen — leading-dot number disambiguation:** `.5` is a number unless the
  previous token can end a postfix target (ident/`)`/`]`/`}`/number/string/
  hole), in which case `.` is member access. Tracks one token of history.
- **Chosen — trailing-dot ban scope:** `5.` erroring is required; refined so
  `5.foo` lexes as `5 . foo` (member access) and only a *dangling* dot (before
  whitespace/operator/EOF) errors. Numbers having no fields is left to the
  analyzer, not pre-judged by the lexer. Flag if the author wants `5.<ident>` to
  also be a lexical error.
- **Chosen — templates:** interpolations are captured as *pre-lexed* token
  sub-streams (`TemplateElem::Interp(Vec<Token>)`); the parser parses each as an
  Expression. Brace-depth is handled by reusing the main token loop (nested
  string/record braces are consumed as whole tokens, so a `}` inside a nested
  literal never closes the interpolation).
- **Chosen — string escape set:** the JS-standard set (`\n \t \r \0 \b \f \v \\
  \" \'`), `\xHH`, `\uXXXX` (one UTF-16 unit, surrogate halves allowed), `\u{…}`
  (astral → surrogate pair); templates add `` \` `` and `\${`. Matches §1.5's
  "JS standard set plus `\u{…}`".
- **Chosen — identifier classes:** std `is_alphabetic`/`is_alphanumeric` as an
  approximation of Unicode XID_Start/XID_Continue, excluding `_` and `$` per
  §1.3 (so `_`-holes and `$`-interpolation never collide). A `unicode-ident`
  dependency would make this exact; deferred as not worth a dep at v0.1. Flag if
  strict XID conformance is wanted.
- **Minor — `_0`:** grammar says indexed holes are `_n`, n ≥ 1. `_0` currently
  lexes as `IndexedHole(0)`; rejecting n = 0 is left to the parser/analyzer.
- **`// [ask-author]`:** none blocking. The two "flag if…" items above (strict
  XID; `5.<ident>` strictness) are the only choices worth a confirmation.

---

## 2026-07-17 — Build-order step 1: repo + value layer

### Preconditions
- All four normative documents present and read: design compendium v1.0,
  grammar spec v0.1 (added by the author this session), kernel AST spec v0.1,
  semantics companion v0.1. The grammar spec was initially missing; once added,
  its own closing line ("`cargo init` is ungated") plus Part I §365 confirmed the
  gate is open.
- **Chosen — toolchain:** no Rust was installed on the machine. Installed via
  `rustup` (author-approved) → stable `1.97.1`. Pinned in `rust-toolchain.toml`
  for reproducible conformance runs (the oracle is the truth source).

### Dependencies (Cargo.toml)
- **Mandated (Part I step-0):** `num-rational` `BigRational`; fixed-precision
  decimal crates rejected. Added `num-bigint`, `num-integer`, `num-traits`.
- **Chosen — `num-bigint = "0.4"`:** `cargo add` first resolved 0.5.1, which put
  *two* `BigInt` types in the tree (0.5 direct vs the 0.4 that `num-rational`'s
  `BigRational = Ratio<BigInt>` uses). Pinned our direct dep to 0.4 so there is
  one `BigInt`. Not a semantic decision; a tree-hygiene fix.
- **Mandated + Chosen — `unicode-segmentation = "=1.13.3"`:** grapheme ops must
  pin the Unicode table version (CLAUDE.md step 3 / semantics §3 E8). Pinned
  *exactly*. Not yet used (grapheme string ops are step 3); declared now so the
  version is fixed from the start.

### Value layer (`src/rational.rs`, `src/value.rs`, `src/interner.rs`)
- **Mandated (B1):** immutable, eagerly interned values; `==` is pointer
  comparison for every type; locations are not values.
  - **Chosen — hash-consing representation:** `ValueRef = Rc<ValueData>` with
    pointer-based `Hash`/`Eq`; `ValueData` derives structural `Hash`/`Eq`. Because
    children are already canonical, comparing children by pointer *is* structural
    comparison, so the derived key is exact. The interner is
    `HashMap<ValueData, ValueRef>`. This is a standard hash-cons; the compendium
    names the semantics (pointer equality), not the mechanism.
- **Mandated (B2):** exact rationals; decimal-iff-terminating printing. B2's
  printing predicate ("reduced denominator's primes ⊆ {2,5}") implemented exactly
  via `power_of_ten_factors`; scaling to `10^max(twos,fives)` yields no spurious
  trailing zeros (proof sketch in code comment). Flagship seed `0.1+0.2==0.3`
  green.
  - **Chosen — integer rendering:** an integer rational (`denom == 1`) prints with
    no decimal point (`3`, not `3.0`). B2 gives round-trip examples for fractions
    but is silent on the integer spelling; `3` is the natural canonical form and
    the grammar bans the trailing-dot `3.` form anyway. Low-risk; flag if the
    print doctrine later says otherwise.
  - **Chosen — `Rational::from_decimal` helper:** a value-layer convenience/B2
    demonstrator (handles sign, leading-dot, exponent, `_` separators). The lexer
    (step 2) owns *real* literal diagnostics; this is not that.
- **Mandated (semantics §1):** value kinds Boolean, Null, Number, String (UTF-16
  storage), Tuple, Record, Function, Indeterminate(form). All present.
  - **Chosen — record canonical form:** fields stored sorted by UTF-16 key, keys
    unique. Record field order is not observable (structural `==`), so `{a,b}` and
    `{b,a}` intern equal. Construction applies later-wins on duplicate keys (E5
    RecordCons); literal-literal duplicate rejection is an upstream (parser)
    concern, not enforced here.
  - **Chosen — `Indeterminate` forms:** modeled the two the semantics names
    (`_/0`, `0/0`) as an enum. Interned like any value (§3: a plain value, not a
    trap).
  - **Deferred — `FunctionValue` captures:** type defined as `(lambda, capture
    map)` with captures = value / μ-marker / location per semantics §1, but left
    empty; function *construction* and capture resolution are the oracle's job
    (step 3). Consequently the `y = [() => y]` / `z = [() => z]` interning seed is
    **deferred to step 3** — it needs μ-markers and evaluation, which do not exist
    yet. Recorded so the seed is not forgotten.

### Kernel AST (`src/ast.rs`)
- **Mandated (kernel AST spec §§1–3):** full node inventory — expressions,
  declarations/module structure, patterns — with **no source spans** (B4 side
  table) and every node deriving `Hash`/`Eq` so kernel forms intern (§5). Types
  only this pass; no evaluation, no desugaring, no canonicalization yet.
  - **Chosen — `BindingRef { Name | Positional }`:** the spec says canonical
    bodies replace immutable-binding names with positional (de-Bruijn) refs (§5),
    but the parser emits names first. Modeled both lifecycle forms in one enum;
    the normalizer (§5) will rewrite `Name → Positional`. Faithful to the spec's
    stated canonicalization, not an invented representation.
  - **Chosen — pattern rests encoded inline** as `PatElem`/`PatField` variants
    (rather than a separate `rest?` field) so a tuple's *middle* rest keeps its
    position. The "one rest per level" invariant is an analyzer/parser check, not
    a type-level constraint.
  - **Followed — extension points omitted:** reactive-fence act kinds
    (`@reactive`, `@computed`) and other §7 parked forms are deliberately absent;
    `ActKind` is `{Pure, Mutator, Effect}` only.

### Open items carried forward (implement as stated; do not resolve)
- Mutator returns = return-nothing (current law); returns-leaning is an extension
  point.
- Open-value group identity: strict-openness-with-statement-group-windows
  (semantics §7) — to be isolated behind one module when the oracle lands.
- Module in a value seat: unimplemented → clear error (later).
- Template interpolation of non-printable structures: trap (later).

### `// [ask-author]`
None this pass. No unavoidable judgment calls beyond the tagged representation
choices above, all of which the specs already sanction.

### State
`cargo test` green (13 tests): exactness flagship, B2 printing (terminating /
non-terminating / integer / negative / round-trip), interning pointer-equality
(leaves, nested tuples, record order-independence, later-wins). `cargo clippy`
clean.
