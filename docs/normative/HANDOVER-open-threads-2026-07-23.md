# NEXT — Handover: open threads as of 2026-07-23

> **SUCCESSOR RECORD — read alongside this one.**
> `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md` (2026-07-24) continues **Thread C** and
> supersedes parts of it. In particular it records the author's rejection of the generic
> `Indeterminate(_/0)` model, the *"derive the contracts first, then canonicalize the body"* principle,
> and the intended future Number as a canonical mathematical DAG. **Where the two records conflict, the
> 07-24 record is later.** Threads A and B below are unaffected.

**Purpose.** Three design questions were opened and deliberately left unresolved. All are
upstream of rulings already written into documents, so the documents currently carry provisional text
with pending flags. This record states what is settled, what is open, what was argued and *retracted*,
and what each option costs — so the threads can be picked up cold.

**Nothing here blocks implementation.** The threads concern rare or not-yet-built behavior
(mutual-group construction windows; closure `==` on spelling variants, which is PENDING-§5 in code;
canonicalization strength, which is a design question ahead of the canonicalizer itself).

---

## Part 1 — Status snapshot

**Frozen / closed, unchanged by this session:**
- Compendium v1.0 patch **1.0.8 — FROZEN** (design-closed master; changes only by errata or the runtime-doc pointer).
- Four design-closed packages: μ v0.5 · recursive contracts v0.2 (+0.2.1–0.2.2) · application/induction v0.8 (+0.8.1) · tuple family v0.3 (+0.3.1).
- Record openness ruled and stamped (exact where users write; open only as analyzer-derived demand; `HasField(k)` ≡ `Record({k: Top}, Open)`).

**Completed this session:**
- **A-WRK register discharged** — `next-phase-a-worked-examples-recovered.md` (grids 1–9, verbatim from transcripts, per-item provenance); the test-suite spec's RECOVER line now points at it. `journal.txt` was the drafting agent's transcript-mount catalog, never a repo file — that pointer is superseded.
- **Semantics-companion review round integrated.** Findings 1–9 were already applied (actKind in the closure key; the print/parse law split into display rendering vs source-literal rendering; frozen record-key rule with UTF-16 ordering; lossless surrogate escaping; open-member observation operationalized; μ-spec §§5–6 cross-reference corrected). Finding **§10 was outstanding and is now registered** in the test-suite spec: **PR-06…PR-09** (raw top-level String outside the round-trip law; non-IDENT record keys; lone-surrogate losslessness; deterministic-but-unparseable aggregates), **FE-07** (actKind distinguishes closure values), **MU-18/MU-19** (open-member observation traps / same-group construction reference stays legal). PR-05's wording scoped to the source-renderable fragment. Companion seeds line synced. `MANIFEST.sha256.txt` refreshed.

**Still owed elsewhere (unchanged):** Part F hostile round → runtime design document (the last companion); the optional combined review round on the four working docs; the parked-by-choice opens.

---

## Part 2 — OPEN THREAD A: should observing an open group member be illegal?

### The rule as currently written

μ package (B4, contagious openness + observation prohibition), companion §3, MU-09/MU-18:
during a mutual-group construction window, a member may be *referenced from within the construction
of another member of the same group* (a legal internal μ edge), but any other observation —
`==`, ordinary call argument, export, return beyond the window, or an unrelated interleaved
statement — is a compile error.

```
a = [() => b]        // window opens
seen = (a == c)      // ← currently rejected
b = [() => a]        // window closes; group canonicalizes jointly
```

**Rejection phase:** binding & openness resolution — the analyzer's ordered statement walk carrying
per-name state *unbound → open → closed*. Structural; needs no contracts, no demand graph. Note it is a
**different check** from the ordinary boundness rule: `a` *is* bound by an earlier statement and passes
that one; what catches it is the openness state.

**Runtime failure moment (if an unaccepted program is executed):** evaluating `Ref(a)` in statement 2 —
the environment returns an under-initialization marker. The `==` operator is never reached.

### The author's challenge (2026-07-23)

1. `a == a` — the reviewer's illustrating example — is **reflexive**, true under every possible closure
   of the group. It demonstrates no hazard. Conceded: bad example.
2. **In JS this is legal** and `seen` is `true` (reference identity exists at construction; TDZ never
   fires because the closure isn't called). NEXT differs only because reference identity was removed
   and *shape is identity* — the prohibition is that ruling's shadow, not an independent law.
3. **The program is static.** The analyzer can fold the group and answer correctly.
4. **Canonicalization/interning is semantics, not an optimization** (Principle 5: equivalence-under-rules
   *is* pointer comparison). So framing this as "legality can't depend on whether an optimization ran"
   was an invented problem. II.7's compile-time interning pass concerns *when* the work happens, never
   *whether* the identity holds.

### Arguments offered and retracted (logged, per project discipline)

| Argument | Status |
|---|---|
| "The answer would be unstable — same expression, two answers depending on position" | **Weak.** True for `a == c`, false for reflexive cases; not a general justification. |
| "No pointer exists yet, so `==` has nothing to compare" | **Partially retracted.** True under the general mechanism; but a statically pre-interned group *would* have a pointer. |
| "Legality can't depend on whether an optimization ran" | **Retracted.** Interning is semantics here, not optimization. |

What survives: **for the general mechanism** (window opens at first binding, closes at the last), a
member's captures are unresolved mid-window, joint minimization has not run, and no canonical value
exists to compare. The question is whether the general mechanism must be the *only* mechanism.

### The live options

- **(i) Keep the uniform prohibition.** One structural rule, no analysis, cheap. Costs only programs
  that observe a member mid-window — rare, and typically dead code. Status quo; all current text assumes it.
- **(ii) Permit when the group is statically pre-internable.** Promote compile-time interning from
  optimization to *semantic guarantee* for a defined class: all captures compile-time known, any
  construction-time computation pure and terminating under C§12.2's advance-bound rule. Then the values
  demonstrably exist before the observing statement runs and the observation is legal. **Cost:** the class
  boundary becomes normative language spec, including its diagnostic; the compiler *must* pre-intern for
  that class. Two known blockers to hoisting in general (both must be excluded from the class):
  a later member depending on a binding that sits *between* the statements (`a = [() => b]; m = 5;
  b = [() => a, m]`), and member construction containing calls that can trap or diverge (moving when a
  trap fires is observable in an act world).
- **(iii) Permit only "stable" observations** (those whose answer is invariant over how the group closes).
  Legalizes `a == a`. Needs a stability judgment in the static rules — cheap for reflexivity, awkward in
  general. Weakest of the three; recorded for completeness.

### Downstream and blocked: the trap-class ruling (A vs B)

Only matters for whatever stays illegal. The companion currently carries **Option A with a pending flag**.

- **Option A** — fold open-member observation into `unbound-evaluation`. One sentence, no new machinery;
  **thirteen trap classes hold**; frozen master needs nothing. Justification: an open graph is construction
  state, not yet a language value. **Cost:** the trap↔compile-error concordance goes many-to-one for this
  pair; two mistakes with different remedies share one class (message text can still distinguish them).
- **Option B** — a fourteenth class, `open-value-observation`. Clean bijection, diagnostic names the real
  problem. **Cost:** restates the count across companion §6, suite T-01…T-13, and the **frozen** compendium
  — the first erratum against the freeze, landing on the statement just corrected.

Reviewer recommends A. Assistant's read leaned slightly to B (concordance bijection is load-bearing;
buying it back later costs more than the erratum now). **Author's call, not yet made.**

---

## Part 3 — OPEN THREAD B: function equality under the freeze slice

Opened with this example; the author's own conclusion was **not yet stated** when the session paused.

```
a = x => x + 3
b = x => x + 2 + 1
c = x => x + 4
```

### Established facts

- **`a == b` is true.** `(x + 2) + 1` → associative reordering → literal constant folding → `x + 3`,
  identical canonical body, identical pointer. Both rewrites are in the μ spec §8 enumerated
  equality-freeze slice.
- **`a == c` is false** (`x + 3` vs `x + 4`).
- **`x + x == 2 * x` is true** — like-term coefficient combining is in the slice (the H-05 commitment).
- **`x * 2 == x * 3 - x` is false** — cancellation is *permanently excluded*, and must be:
  `expensive(x) − expensive(x)` may not erase a call. Same for zero-annihilation (`0 * loop(x)`) and
  demand-dropping identity elimination (`x + 0`).
- **Analyzer awareness: yes by design, no in code today.** Same canonicalization, same interning table,
  so contracts see one pointer and `Equals(<interned fn>)` proves it. In the current implementation this
  does not hold — the universal-interning re-architecture is **PENDING-§5**; MU-12's register states it
  exactly: same-code closures immediate, *spelling variants* pend on §5.

### The consequence in view when the session paused

The `==`-determining set is enumerated and frozen (amending it is a semantics-version event), and its
exclusions are motivated by semantics preservation rather than convenience. But from a user's algebraic
intuition the resulting boundary is **jagged**: some algebraically-equal functions compare equal
(`x+3` / `x+2+1`, `x+x` / `2*x`), others do not (`x*2` / `x*3−x`), and the only way to predict which is to
read the enumerated list. Whether that is acceptable, needs documentation, needs a different slice, or
needs `==` on functions restricted in some way — **is the open question. The author had not yet stated
their position.**

---

## Part 2b — OPEN THREAD C: the equality-freeze exclusions were never ratified

**Raised by the author 2026-07-23. Nothing has been changed in any document; this is a record only.**

> **CONTINUED AND PARTLY SUPERSEDED (2026-07-24)** by
> `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md`. Still current below: the provenance
> finding, the five-part inventory of what the round-one decision removed, MU-10/H-05 as the tests that
> move, and the `==`-set-vs-analyzer-NF scope defect. **Overtaken:** the framing that the identity set
> has no second channel for demands — §27.4 of the successor records the author's principle that
> **contracts are derived and retained first, and the body then canonicalizes freely**, so function
> identity becomes *canonical body + retained semantic envelope*. Under that principle the exclusion
> trio's rationale largely dissolves, and the open work becomes defining the envelope (§9 there) rather
> than choosing which rewrites to ban.

### Provenance finding

The exclusion list lives in exactly two normative places and **carries no author provenance in either**:

- `next-mu-canonicalization-specification-v0-5.md` **§8**, headed *"The equality freeze — narrowed and
  enumerated"* and marked **"[rewritten round 1]"**, citing *"the review's counterexamples"*.
- `next-design-compendium-v1-0.md` **C§11** summary line — no tag at all; reads as settled design.

It is therefore **reviewer-originated, absorbed as settled, never ruled by the author.** Logged as an
extrapolated-ruling instance. The author's stated position (2026-07-23): annihilation is *expected
behavior*, was never ruled out, and its removal may defeat the purpose of canonicalization.

### What exactly was excluded — the full list, one decision

Removed from the `==`-determining set, in the same round-one sentence:

1. **Zero-annihilation** — `0 * e → 0`
2. **Cancellation** — `e − e → 0`
3. **Demand-dropping identity elimination** — `x + 0 → x`
4. **A catch-all:** *"any rewrite erasing a call or potentially-diverging operand"* — the broadest clause,
   and the one that would swallow further rewrites case-by-case (`e * 1`, `e && false`, dead ternary arms,
   unused-let elimination) without them ever being listed.

5. **The narrowing itself** — the section is titled *"narrowed and enumerated"*: the slice went from
   open-ended ("polynomial NF") to a **closed list**, so **everything unlisted is excluded by default**,
   including rewrites nobody discussed — distributivity, power/exponent rules, double negation,
   constant-condition ternary folding, boolean simplification. This is the largest effect of the decision
   and the least visible, because no rewrite had to be named to be lost.

Each named exclusion is nailed down by a suite case asserting the rewrite **does not fire** — **MU-10, "the exclusion trio"**
(`0 * loop(x)` stays divergent through normalization; `e − e` and `x + 0` unrewritten; demands intact).
Reverting the exclusions means MU-10 changes or goes.

### What was *kept* in the slice (for contrast)

Commutative/associative reordering of retained operands · literal constant folding (no variable erased) ·
like-term coefficient combining with every occurrence surviving (`x + x → 2 * x`, the H-05 commitment) ·
α/positional conversion · μ-laws 1–8. **Amending the list is declared a semantics-version event.**

### The stated justification, and its scope defect

The master law: a rewrite in the `==` set must preserve, for all inputs — produced value, **completion vs
divergence**, operation-safety demands, and accepted domain (`eval ∘ normalize = eval` read strictly).
Under that law the three exclusions follow, because `x => 0 * loop(x)` and `x => 0` differ on termination,
and `x => 0 * x` and `x => 0` differ on accepted domain (one rejects non-Numbers).

**The defect is scope.** μ §8 confines the exclusion to the **`==`-determining set** — which function
*values* intern to one pointer. The compendium's C§11 line lumps it into the canonicalization description
generally, so it can be read as barring the fold from the **analyzer's normal form** as well. That reading
would cost region tables, polynomial NF, and guard comparison their constant folding through zero, for no
benefit — and nothing requires it, because **C§7 already carries the demand on a separate channel**: the
operation's safety verdict is checked independently of its output contract (`0 * x` → safety "x must be
Number", output `Equals(0)`). The demand-preservation argument bites only in the identity set, where the
canonical body is the sole carrier.

### The author's live considerations (2026-07-23, not resolved)

- Annihilation may be admissible **when the erased operand is a pure expression without effects**; in a
  non-pure function the effects could still matter.
- Unresolved worry: a recursive call in the erased operand that **may not terminate**, or that returns an
  exceptional value which should still affect the result — the divergence case the reviewer's
  counterexample targets. The author's assessment: *"it's a tough call."*
- ~~*Assistant's mapping of that second worry:* NEXT has no Infinity — `1/0` is `Indeterminate(_/0)`,
  C§7 specifies Indeterminate union-propagation, so `0 * Indeterminate` must propagate and never fold;
  a fifth preservation clause the master law does not name.~~ **DEMOTED 2026-07-24 — do not carry
  forward as a constraint.** It describes the *current spec text* accurately, but its premise is the
  generic-Indeterminate model, which the author has since **rejected** (successor record §3, §27.3).
  Under the no-generic-Indeterminate direction `1/0` and `2/0` are distinct canonical values, there is no
  generic marker to propagate, and what `0 * (1/0)` yields is a question for the future zero-denominator
  algebra (successor §§19, 26, 28) — not a preservation clause. **What survives from the author's
  original worry:** an erased operand that may diverge, or that carries mathematical content the fold
  would destroy, still blocks annihilation; the divergence half is unaffected by any of this.

### Decision shape when resumed

1. Does annihilation belong in the **analyzer's NF**? (Assistant's read: yes, and nothing blocks it —
   likely just an erratum stating the scope. Cheap, independent of 2 and 3.)
2. Does it belong in the **`==`-determining set**? Price: `x => 0 * loop(x)` and `x => 0` become one value
   despite differing on termination; `x => 0 * x` and `x => 0` become one value despite differing on
   accepted domain.
3. If admitted **conditionally** (pure + provably total operand), the condition becomes normative language
   spec, and the analyzer must decide totality before it can decide identity — note the ordering
   dependency: identity would then rest on a proof that can land *unproven*.

**Affected if changed:** μ spec §8 (the enumerated slice) · compendium C§11 (frozen — erratum) ·
suite MU-10 · possibly H-05/PENDING-§5 expectations.

---

## Part 4 — Where things live

- Frozen master: `next-design-compendium-v1-0.md` (patch 1.0.8) — B4, C§11, C§12.3, E1, E14.
- Observation prohibition + freeze slice: `next-mu-canonicalization-specification-v0-5.md` §8, MU-09…MU-17.
- Oracle-side trap text and the A/B pending flag: `next-semantics-companion-v0-1.md` §3 (`Ref`), §6 (concordance).
- Registered cases: `next-test-suite-specification-v0-1.md` — PR-05…PR-09, FE-06/FE-07, MU-18/MU-19, T-01…T-13, PENDING-§5 register.
- Thread C's continuation: `HANDOVER-indeterminate-canonical-number-dag-2026-07-24.md` (Indeterminate
  identity, derive-then-canonicalize, the future canonical-DAG Number, the mathematical research agenda).
- Verification of repo copies: `MANIFEST.sha256.txt` (regenerate after any edit).

**Pick-up order when resuming:** Thread A option (i/ii/iii) → then the A/B trap ruling (it depends on
what stays illegal). Threads B and C are independent of A. **Thread C now resumes in the successor
record's Part X**, whose order supersedes anything implied here: do not edit the spec yet → formalize the
specific-`a/0` ruling if still wanted → decide whether `Numeric` is needed now → revisit the exclusion
trio under *derive-contracts-then-canonicalize* → define the minimum semantic envelope for function
identity. The C§11 scope erratum (`==`-set only, not analyzer NF) remains cheap and can be applied at any
time without waiting for any of it. Thread B's jagged-boundary question is partly downstream of where C
lands.
