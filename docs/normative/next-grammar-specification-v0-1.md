# NEXT — Grammar Specification v0.1

**Date:** 2026-07-17. **Status:** the surface grammar of the official syntax, drafted whole from the Design Compendium v1.0 — every production cites settled rulings; no flags remain (the hask glyph `#` and newline arm-separation stamped [user, 2026-07-17]). **Authority:** the kernel AST and its semantics are the normative language (Compendium Part A: *semantics over form*); this grammar defines the official-but-one syntax. Parked act-cluster items appear only as named **extension points** (§9) — additive forms that bolt on without changing anything below. This document gates `cargo init`.

**Notation.** EBNF: `X := …` productions; `{X}` repetition (zero+); `[X]` optional; `A / B` alternation (slash, since `|` is a token); `"lit"` literal tokens; UPPERCASE token classes. Semantic constraints that the grammar cannot express are marked **⟦sem⟧** and cite the Compendium.

---

## 1. Lexical structure

### 1.1 Input, whitespace, lines
Source is Unicode text. Whitespace and line breaks are lexer-skipped — **no newline tokens exist** — but the lexer records each token's line, and the parser enforces two line-sensitive rules: **(L1) one statement per line** — a statement may not begin on the line where the previous statement's last token sits; **(L2) one arm per line** — each arm in an arm block begins on a new line. Expressions continue greedily across lines (multi-line pipelines need no continuation syntax). **Stated hazard (inherited knowingly):** greedy continuation gives `x = a` ⏎ `- b` the parse `x = a - b`; nearly harmless — no meaningful statement begins with an operator — but normative and diagnosable by a lint when the continuation line starts with `-`.

### 1.2 Comments
`//` to end of line; `/* … */` non-nesting; both skipped. `///` opens a **doc comment** (reserved; content format is tooling-era).

### 1.3 Identifiers and contextual words
`IDENT := IdentStart {IdentPart}` (Unicode identifier classes; `_` and `$`-free — `$` appears only in template interpolation). **Zero reserved words:** `true`, `false`, `null` are predeclared prelude bindings (ordinary IDENTs); `module`, `import`, `export`, `from`, `when`, `where` are **contextual** — they act as keywords only in the seats §§2–5 define and are ordinary identifiers everywhere else; `@`-names are sigil-shielded and never intersect the identifier namespace. Any future word-shaped construct must state its de-reservation mechanism or be rejected.

**Hole tokens (hask scope):** `_` (plain hole / pattern wildcard — role decided by position, ⟦sem: pattern-position `_` is always the wildcard; hole-`_` is expression grammar⟧); `_n` for decimal n ≥ 1 (indexed hole). Lexed as identifier-class tokens; their special roles are syntactic.

### 1.4 Numeric literals
The JS numeric-literal grammar imports whole — decimal, leading-dot fractions (`.5`), exponent forms, `0x`/`0o`/`0b` bases, `_` separators (token-internal; never colliding with the hole `_`) — with three normative amendments: **no BigInt `n` suffix** (`123n` is a lexical error with a hint); **no legacy octal / leading zeros** (`017` errors); **no trailing-dot form** (`5.` errors — write `5` or `5.0`). Every literal denotes an exact rational. The trailing-dot ban is load-bearing for slices: `1...3` lexes cleanly as `1` `...` `3`.

### 1.5 String and template literals
`STRING := " {char / escape} "` — double quotes only, **single-line** (a raw line break in a quoted string is a lexical error). `TEMPLATE` — backtick-delimited, multiline, with interpolation `${ Expression }` (brace-depth-aware: the interpolation closes on the matching `}`); template escapes include `` \` `` and `\${`. Escape set (both forms): the JS standard set plus `\u{…}` producing UTF-16 code units (astral escapes yield surrogate pairs). No raw strings; no tagged templates (rejected v1).

### 1.6 Token inventory (operators and punctuation)
```
=>   ::   |>   <|   #   ?   :   ??   ||   &&   ==   !=
<=   >=   <   >   +   -   *   /   %   **   !   ~
.    ?.   ...  [   ]   (   )   {   }   ,   =   @   ^   |
:=   +:=  -:=  *:=  /:=  %:=  **:=  &&:=  ||:=  ??:=
```
**Maximal munch** with three normative lookaheads: **(T1)** `?.` is not formed when the next character is a decimal digit — `a ?.5 : b` lexes `?` `.5` (the JS rule, adopted); **(T2)** `...` always wins over `.` sequences; **(T3)** compound mutation tokens are single tokens (statement-level only, §2.4). Non-collisions on record: `<|` is safe — no expression-level `|` exists (bitwise discarded; `|` lives only in pattern alternation, where `<` cannot appear); `::` is safe — no construct begins with `:`.

---

## 2. Program, modules, statements

### 2.1 Program
```
Program        := [ModuleHeader] {Statement}
ModuleHeader   := "module" DottedName            // first statement; REQUIRED iff the
DottedName     := IDENT {"." IDENT}              //   file contains any ExportStatement
```
A file with no exports carries no header and is unimportable (an entry point / script). ⟦sem: duplicate module-name declarations are one project-wide error; project-prefix namespacing, resolution, and the modules-are-records semantics per Compendium E12⟧. **Module top-levels are pure bindings only** — no act calls at top level ⟦sem: modules define, never do⟧.

### 2.2 Imports and exports
```
ImportStatement := "import" "{" IDENT {"," IDENT} [","] "}" "from" DottedName
                 / "import" DottedName
ExportStatement := "export" Binding
```
`from` takes a module name — never a path or expression. The bare form binds the module namespace locally (an alias; entries resolve as bindings) ⟦sem: local-name rule (final segment) is a semantics-side footnote, not grammar⟧. `export` prefixes a binding — one way only; no export lists, no default exports.

### 2.3 Statements
```
Statement := Binding / ExpressionStatement / ImportStatement / ExportStatement
           / AtDeclaration / MutationStatement / ArmStatement
Binding             := BindTarget "=" Expression
BindTarget          := IDENT / TuplePattern / RecordPattern      // destructuring binding
ExpressionStatement := Expression
```
⟦sem: destructuring bindings require the pattern proven irrefutable for the source contract — otherwise explicit match; bare pure-expression statements are legal with the goes-nowhere warning; act calls are the normal statement in act bodies; `=` is statement-only — no assignment-in-expression exists⟧.

### 2.4 Mutation statements — mutation world only
```
MutationStatement := Path MutOp Expression
Path              := IDENT {"." IDENT / "[" IndexOrSlice "]"}
MutOp             := ":=" / "+:=" / "-:=" / "*:=" / "/:=" / "%:=" / "**:=" / "&&:=" / "||:=" / "??:="
```
Legal only inside `@mutate` bodies ⟦sem: world jurisdiction, Compendium E14; compounds are sugar over `:=`; path and slice targets are read → pure update/splice → box write, atomic at publication⟧.

### 2.5 `@` declarations — statements, never expressions
```
AtDeclaration := "@" IDENT Binding          // bound:      @effect name = (...) => { }
               / "@" IDENT ArrowFunction    // anonymous:  @reactive () => { ... }
```
The value-side spelling (`name = @x …`) does not exist. The resident inventory and each statute are spec-closed (Compendium E13); `@` followed by a non-resident IDENT is an error naming the inventory. The Oddo block form (`@state:` batch) is **not** in this grammar (unruled; extension point §9).

### 2.6 Arm statements — block bodies
```
ArmStatement := "when" Expression "=>" Expression      // guarded exit
              / "=>" Expression                        // unconditional exit
```
Legal inside function block bodies, interleaved with bindings and statements; each on its own line (L2 applies to blocks' arm statements as to arm blocks). ⟦sem: a block is a match with implicit scrutinee — one kernel node; guarded exits consume their region; coverage policed at expecting seats; Mutator/Effect bodies have no coverage obligation⟧.

---

## 3. Expressions — the precedence ladder as productions

Layered productions, loosest first (Compendium E2 is the authority; associativity in comments).

```
Expression   := ArrowExpr
ArrowExpr    := Params "=>" ArrowBody / MatchExpr            // right-assoc; greedy body
Params       := IDENT / "(" [ParamList] ")"
ParamList    := Param {"," Param} [","]
Param        := IDENT / TuplePattern / RecordPattern / "..." IDENT
ArrowBody    := Expression / Block
Block        := "{" {Statement} "}"

MatchExpr    := PipeExpr {"::" ArmBlock}                     // special form; left-fold —
                                                             //   each :: takes the value so far
ArmBlock     := "{" Arm {Arm} "}"                            // one arm per line (L2)
Arm          := [Pattern] ["when" Expression] "=>" Expression

PipeExpr     := HaskExpr { ("|>" / "<|") HaskExpr }          // |> left-assoc, <| right-assoc;
                                                             //   MIXED CHAIN WITHOUT PARENS = ERROR
HaskExpr     := "#" TernaryExpr / TernaryExpr                // loose prefix: body spans ternary
                                                             //   and tighter; #( Expression ) groups
TernaryExpr  := NullOrExpr ["?" TernaryExpr ":" TernaryExpr] // right-assoc; condition = tested seat
NullOrExpr   := AndExpr { ("??" / "||") AndExpr }            // one tier, left-assoc, ordinary mixing
AndExpr      := EqExpr { "&&" EqExpr }
EqExpr       := RelExpr { ("==" / "!=") RelExpr }
RelExpr      := AddExpr { ("<" / "<=" / ">" / ">=") AddExpr }  // chains self-refute ⟦sem⟧
AddExpr      := MulExpr { ("+" / "-") MulExpr }
MulExpr      := UnaryExpr { ("*" / "/" / "%") UnaryExpr }
UnaryExpr    := ("-" / "!" / "~") UnaryExpr / PowerExpr      // prefixes stack right-to-left (!~x)
PowerExpr    := PostfixExpr ["**" UnaryExpr]                 // right-assoc; -x ** 2 ≡ -(x ** 2);
                                                             //   right operand admits unary: 2 ** -3
PostfixExpr  := Primary {PostfixOp}
PostfixOp    := "." IDENT / "?." IDENT
             / "[" IndexOrSlice "]" / "?." "[" Expression "]"
             / "(" [ArgList] ")"
IndexOrSlice := Expression / [Expression] "..." [Expression]   // t[i]; t[a...b]; t[...n]; t[k...]; t[...]
ArgList      := Arg {"," Arg} [","]
Arg          := Expression / "..." Expression                  // spreads mix; left-to-right evaluation

Primary      := NUMBER / STRING / TEMPLATE / IDENT / Hole
             / "(" Expression ")" / "#(" Expression ")"
             / TupleLit / RecordLit
Hole         := "_" / "_n"                                     // hask scope only ⟦sem⟧
TupleLit     := "[" [Element {"," Element} [","]] "]"
Element      := Expression / "..." Expression                  // middle spreads legal; no elision
RecordLit    := "{" [Field {"," Field} [","]] "}"
Field        := IDENT ":" Expression / IDENT                   // shorthand { name }
             / "[" Expression "]" ":" Expression               // computed key ⟦sem: proven-finite⟧
             / "..." Expression                                // spread; later-wins
```

**Ladder notes carried normatively:** the `::` right operand is exactly one ArmBlock — a closed form; operators after the block attach to the completed match (so `x :: {…} |> f` pipes the result, and `a |> b :: {…}` matches the pipeline's result). The pipe-mixing ban is a parse-time error demanding parentheses. The hask body terminates at pipes, `::`, commas, closing brackets, and statement end; immediate invocation requires grouping (`(# f(_))(x)`); a nested `#` opens a fresh hole-numbering scope; `#([..._1])` passes rest values as one tuple. Identity slice `t[...]` is legal, linted. `{}` is **always** the empty record (§8's brace rule). Comparison-chain and `==`-chain misuse surface as contract refutations, not parse errors.

---

## 4. Patterns

```
Pattern       := AltPattern
AltPattern    := SeqPattern {"|" SeqPattern}      // alternation: binding-free ⟦sem⟧
SeqPattern    := LiteralPat / "_" / IDENT         // IDENT binds fresh; may shadow
              / "^" IDENT                         // pin: equality to existing binding
              / "^" ("_" / "_n")                  // hask escape — arm blocks in hasks only
              / ContractPat                       // capitalized IDENT ⟦sem: must resolve
              / TuplePattern / RecordPattern      //   to a contract; matches value ⊑ C⟧
LiteralPat    := NUMBER / STRING / "-" NUMBER     // plus prelude true/false/null as IDENTs
TuplePattern  := "[" [PatElem {"," PatElem} [","]] "]"
PatElem       := Pattern / Rest
RecordPattern := "{" [PatField {"," PatField} [","]] "}"
PatField      := IDENT [":" Pattern] / Rest
Rest          := "..." "_" / "..." IDENT          // opens; ignores / captures; ONE per level;
                                                  //   bare "..." disallowed; middle rests legal
```
Patterns are **exact by default**; rests open them. Unified across arm patterns, destructuring bindings, and parameters — with the scoped exceptions: pins and hask escapes are **arm-pattern only** (parameters stay pin-free); parameter and binding positions require irrefutability ⟦sem⟧. Record rest-capture is record subtraction; one rest per pattern level makes ambiguous splits unconstructible.

---

## 5. `where` — the name-level signature assertion

```
WhereClause := IDENT "where" "(" [ContractList] ")" "=>" Expression
ContractList := Expression {"," Expression}
```
Attaches at name level only (function-entry `where` rejected); a verified assertion about inference — never trusted, never a mode ⟦sem: Compendium E11⟧. `when` inside blocks/arms is the demand mechanism; `where` never appears there.

---

## 6. World jurisdiction (parse-adjacent law)

The grammar parses uniformly; **worlds** assign legality ⟦sem: Compendium E14⟧: pure world (module bodies, plain functions) — no act calls at any depth, no `:=`; mutation world (`@mutate` bodies) — MutationStatements live here; pure expressions available; effect world (`@effect` bodies) — act calls legal inline and as statements, evaluation strictly as written; `:=` absent. Worlds switch at `@` declarations and never re-nest to pure. Diagnostics name the world, not a position rule.

---

## 7. Line-sensitivity summary

L1 one statement per line; L2 one arm per line (arm blocks and block-body arm statements); greedy expression continuation otherwise; the leading-`-` continuation lint. Trailing commas legal in every comma-separated list; commas are separators, never an operator.

---

## 8. Disambiguation appendix (normative)

- **Brace rule.** After `=>` and in any expression seat: `{` opens a **record** when the first token is `}`, `IDENT :`, `IDENT` followed by `,`/`}` (shorthand), `[` (computed key), or `...`; otherwise it opens a **block**. `x => {}` returns the empty record. Exception [1.0.3]: inside an `@`-declaration's arrow, `{` always opens a **Block** — act bodies are statement sequences — so `@effect f = () => { }` is an empty act body; the empty-Record reading applies everywhere else.
- **`_` position rule.** Pattern position: wildcard, always. Expression position: a hole — legal only within a hask's reach; a compile error outside ⟦sem⟧.
- **`...` roles by position.** Element/argument position: spread. Pattern/parameter position: rest. Inside access brackets: slice. No fourth role exists.
- **`?.` digit lookahead (T1);** `...` maximal munch (T2) — sound because trailing-dot numerals are banned.
- **Contextual words.** `module` (file-first statement head), `import`/`from`, `export` (statement heads), `when` (arm/blocks, before `=>`), `where` (after a name, §5) — each is an ordinary IDENT in every other seat; the parser commits only on the full seat shape.
- **Capitalized pattern names** must resolve to contracts — the convention's one job; error otherwise.
- **`@` sigil.** `@` binds to the following IDENT as a privileged-operation reference; statement head only (§2.5).

---

## 9. Extension points (parked; additive)

Reserved, named, and absent from the grammar until their sessions rule them: the `require`-shaped entry prohibition (uniform across act kinds; prosody must sound like an error); gray-acknowledgment, strict-mode, `@suppress`/`@proof` spellings; the default-mutator spelling (three seeds on record); guarded acts / per-act-kind arm semantics and any binding-position discharge form; the `@`-block batch form; Mutator-return surface (if the leaning stamps). then/catch and exit are prelude *names*, not grammar. Each lands as a new production or resident without disturbing §§1–8.

---

## 10. Conformance

A conforming parser accepts exactly this grammar plus ⟦sem⟧-deferred checks in the analyzer; produces the kernel AST (the normative form — its specification is the next artifact); and reports the normative diagnostics named here (pipe-mixing parens demand; inventory-naming `@` errors; the brace, `_`, and `...` rules; the continuation lint; identity-slice and redundant-`?.`/`~` lints). E2's worked parses are this grammar's seed conformance suite, joined by: `x :: {…}` with newline-separated arms; `#([..._1])`; `a ?.5 : b`; `1...3` slice lexing; `{}`-after-arrow; a mixed-pipe chain rejection.

*End of Grammar Specification v0.1. `cargo init` is ungated.*
