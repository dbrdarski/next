# DECISIONS.md — NEXT implementation changelog

Provenance discipline (CLAUDE.md § Process): what the specs **mandated**, what I
**chose** where a representation was left open, and what I'm **asking** the author.
Status tags mirror the compendium's vocabulary. Newest entries first.

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
