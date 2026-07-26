# Implementation finding — body safety is built in the wrong layer

**From:** the implementation side (Claude Code), 2026-07-26
**Status:** a question for the author, not a decision taken. Nothing has been
re-architected on the strength of it.
**Trigger:** a reader asked why the analyzer needs call-site machinery to reject
`bad = () => 1 + "x"`, "because we're adding to a string — the program should not
compile. Simple."

That question is correct, and following it up exposed a divergence between what the
normative documents specify and what I have been building across review rounds
Archive(6)–Archive(10).

---

## 1. The observation

```next
bad = () => 1 + "x"
```

`Number + String` is an operation-safety trap (Semantics Companion §3, PrimOp: *"Kind
mismatches (`Number + String`) → **trap: operation-safety**"*). The body takes no
arguments and has no captures. It traps on every possible invocation, in every possible
environment. There is no input that redeems it.

So it should be rejected **at its definition**. It needs no call-site reasoning at all.

**Measured, current implementation:**

```
analyze(() => 1 + "x")   →   accepted = true, findings = [], contract = Top
```

`Expr::Lambda` falls through `analyze`'s catch-all to `Top`; the body is never analyzed
at its definition site. The trap is only ever found because something *calls* `bad`, and
the call site walks into the callee's body.

That is why five review rounds have been about propagating traps from callee bodies out
to call sites.

---

## 2. What the documents actually specify

The normative texts describe a different mechanism — the function's **inferred accepted
domain**, derived from its body:

- **E11:** *"`name where (InputContract) => ReturnContract` … **DeclaredInput ⊑
  InferredAcceptedDomain** (the declared input satisfies every demand **the body
  derives**; it may be stricter — C§12.1's split variance)"*
- **C§12.1:** *"Input preconditions may be stricter than **the body's domain**; return
  postconditions must contain all outputs."*
- **E3 (rest parameters):** *"**body-derived domain** — uses of the rest tuple narrow
  accepted lengths (`first = (...values) => values[0]` rejects `first()`)"*

"The demands the body derives", "the body's domain", "body-derived domain" — the design
assumes each function body is analyzed to yield **the set of inputs for which it is
safe**, and that call sites are then checked against that set (the C§13.2 input
obligation).

Under that design:

| program | verdict | where |
|---|---|---|
| `() => 1 + "x"` | accepted domain is **empty** → rejected | at the definition |
| `(x) => x + 1` | accepted domain is `Number` | definition is **fine** |
| `f("hello")` | `Equals("hello") ⋢ Number` → rejected | at the call site |

The second row is the case that genuinely *requires* call-site, domain-sensitive
reasoning: the body is unimpeachable, and only the caller is wrong.

## 3. What I built instead

`obligation.rs::accepted_domain` derives the accepted set from the **parameter pattern
only** — it never looks at the body. The `InferredAcceptedDomain` that E11 names does
not exist in the implementation.

In its place, `induction::instance_body_summary` analyzes the callee's body **per call
site, indexed by the call-site argument domain**, and propagates the body's proven traps
outward to the caller.

It finds real traps and it is sound. But it is a different mechanism from the one the
documents describe, and it has a different cost structure.

---

## 4. Why this matters: the recurring blockers are artifacts of the layer

| Round | Built | Next review found |
|---|---|---|
| A6 | `body_safety` over `reachable_closures` | misses parameter/local callees; wrong domain |
| A7 | edge-following + `SAFETY_STACK` | shape key aliases distinct instances |
| A8 | `(instance, domain)` + `InstanceBodySummary` | widening unsound; alternatives dropped; non-terminating |
| A9 | `domain_admitted`, `kind_abstraction`, downgrade, `CalleeAlt` | downgrade incomplete; admitted-unions infinite; inhabitance |
| A10 | *(fixes applied — see §6)* | — |

Every round's flaw is **created by** the previous round's fix, and every fix grows the
same mechanism. Each review is sound in itself; the reviews compare each diff against
the previous diff, so none has asked whether the mechanism should exist in this shape.

The two hardest Archive(10) blockers are **structural consequences of analyzing bodies
per call-site domain**, not of anything in NEXT:

- **Widened-domain evidence** (§6–§9) exists only because a recursive body is re-analyzed
  under a *different* domain than the one demanded, so its evidence has to be projected
  back down.
- **Advance-bounded domain universes** (§11–§13) exist only because call-site domains
  form a chain that must be kept finite.

Under body-derived accepted domains, a body is analyzed **once**, and neither situation
arises. To be precise about what does *not* vanish: `f`'s accepted domain still depends
on `f`'s when `f` is recursive. But that is **one lattice element per function**, settled
by the SCC/hypothesis machinery already built and already terminating (the return-fact
induction) — not a fresh body walk per call-site domain requiring its own
advance-bounded state universe.

---

## 5. The question

**Is `InferredAcceptedDomain` (E11 / C§12.1 / E3) the intended mechanism for body
safety, with per-call-site body analysis reserved for what it cannot express?**

If yes, the implementation should move to:

```
per function instance:   analyze body once
                              ↓
                    accepted input domain   (the inputs for which it is safe)
                  + return contract         (already built — the induction)
                              ↓
per call site:      args ⊑ accepted domain  (the C§13.2 input obligation)
```

and much of the Archive(6)–(10) machinery would be **subsumed rather than extended** —
including, I believe, both remaining Archive(10) structural blockers.

Two sub-questions if the answer is yes:

1. **Is an uncalled function with an empty accepted domain a compile error?** Accepting
   it is *sound* (the program never traps if it is never called), but it is dead code
   with a proven type error. E11's `where` machinery implies the domain is derived
   regardless of call sites; whether emptiness is itself an error is a ruling.
2. **What is the accepted domain of a body whose safety depends on a capture rather than
   an input?** (`make = (s) => () => s + 1`; `make("x")()` traps.) Per-instance
   derivation appears to cover it — the instance for `s = "x"` has an empty accepted
   domain over its empty argument tuple — but it should be confirmed.

## 6. State of the code as of this document

The three Archive(10) findings are all technically correct and the load-bearing one was
verified empirically before acting on it (`f = (x, b) => f(b ? x : 0, b)` overflowed the
stack — my "finite admitted basis" argument was invalid, because contract keys are
compared structurally and unions are not canonicalized). Three **small** corrections are
applied — each tightens or *shrinks* the existing mechanism rather than growing it:

- **Termination:** unions are no longer admitted as exact recursive domains (Archive10
  Option A). Admitted domains are atoms only, so the exact state space per position is
  bounded by `|literals| + |Kinds| + 3`. The counterexample now terminates in 0.00s and
  is a permanent regression test.
- **Completion variance:** a widened body's `FallsThrough` drops to `MayFallThrough`,
  matching the rule already applied to findings — both existential channels obey the same
  evidence direction.
- **Inhabitance:** `NotAFunction` carries whether a represented inhabitant exists;
  disjointness alone now warns rather than refutes.

Everything **larger** that Archive(10) recommends — a canonical union basis, the
preconstructed candidate-domain inventory, full witness plumbing — is deliberately **not**
done, pending the answer above. Those are further scaffolding on the mechanism this
document is asking about.

Suite: 323 lib + 111 conformance (13 ignored), clippy clean.

---

*Raised under CLAUDE.md hard rule 3 — "Do not invent semantics. Any gap is either an
extension point, a tagged [open], or a question for the author. Stop and ask; never fill
silently." The divergence here is not an invented semantics, but it is a structural
choice large enough that continuing to build on it without a ruling would be filling
silently.*
