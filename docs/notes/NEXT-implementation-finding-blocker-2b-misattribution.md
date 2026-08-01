> ## 📘 STATUS: **CURRENT** — an implementation finding, raised for the author
> Nothing has been re-architected on the strength of it. The correction to
> `IMPLEMENTATION-STATUS.md` §4 and to the `#[ignore]` text is **proposed, not applied**.
> Design authority remains with the manifest-verified normative specifications.

# Implementation finding — blocker 2b is misattributed to μ-canonicalization

**From:** the implementation side (Claude Code), 2026-08-01
**Status:** a measured finding plus an ordering recommendation. The author's ruling is owed
on the ordering; the document corrections are mechanical and can be applied on request.
**Trigger:** asked whether the μ-grouping I had proposed as the next work item was
*"really necessary in NEXT or an import"*, with the intuition that *"existing mechanisms
already cover this"*.

The intuition is correct. μ-grouping is **not** an import — it is normative, in the
compendium — but the job I assigned it (releasing blocker 2b) is already done by a
different, existing, passing mechanism. This document records the measurement, locates
the error, and states what follows for the queue.

---

## 1. The measurement

Two tests in the tree run the **same program**:

```next
f = (x) => x == 0 ? g("x") : x + 1
g = (y) => f(y)
```

`f(0)` calls `g("x")`, which calls `f("x")`, which reaches `"x" + 1` — an
operation-safety trap. A correct analyzer must reject `f(0)`.

| Path | Entry point | Verdict | Test state |
|---|---|---|---|
| Fact graph (C§13.2a) | `safety::prove` | **Refuted** ✓ | `safety::graph_tests::mutual_recursion_closes_via_the_joint_vector_pass` — **live and passing** |
| Quarantined checker | `bodycheck::body_summary` | **false accept** ✗ | `bodycheck::tests::mutual_domain_changing_recursion_is_caught` — **`#[ignore]`d as blocker 2b** |

Measured 2026-08-01, both run individually rather than inferred from the suite total.

**The mutual-recursion case blocker 2b is filed against is already caught**, by machinery
that exists, is tested, and passes today. No part of μ-canonicalization participates.

---

## 2. The error, located

I claimed layer-2 μ-grouping is what releases 2b. That conflates two distinct structures
that are both strongly-connected-component decompositions:

| | Graph | Nodes | Produces |
|---|---|---|---|
| **μ-grouping** (μ-spec §2, C§11) | a **scope's reference graph** | bindings — which definition mentions which | **code identity**: `GroupTemplate` + slot numbering |
| **C§13.2a** | the **fact dependency graph** | facts `(instance, I, claim)` | the **induction schedule**: reverse-topological order, one joint vector pass per component |

Different graphs, different jobs. The second is what makes a mutual edge resolvable during
analysis — proving `f` alone cannot discharge its call to `g`, because only `f`'s own fact
would be assumed; the joint pass assumes every member of the component. That is exactly
what `analyzer::safety` implements, and exactly why it refutes the program above.

### Provenance of the wrong claim

It comes from `IMPLEMENTATION-STATUS.md` §4's blocker table (2b's *"actual blocker"* column:
*"μ-canonicalization Algorithm A — the group/SCC layer"*) and from the `#[ignore]` string on
`bodycheck.rs:432`. Both were written before the fact graph landed and were never reconciled
with it.

**The same document already contains the correct answer.** §3 says of the candidate graph:
*"Not the wired path — `analyze_apply` still calls `bodycheck::body_summary`, which is why
nine pins are unmoved."* §3 and §4 disagree, and I propagated §4.

---

## 3. What μ-grouping is actually for

It is normative and it is not redundant — the redundancy was in the purpose I gave it.

Compendium **B4, identity layer (2)**:

> **Function shape** = canonical lambda body + μ-structure — for group members,
> `(GroupTemplatePointer, EntrySlot)` with capture routing in the template (the μ package,
> C§11) […] keys the **symbolic summary template**.

And **C§13.4**, the proven-return-fact cache: `(analysis instance, row-set I, demanded C)`,
where the analysis instance is *shape + annotated captured-environment contract tuple*, and
*"Every key interned pointers."*

So the specified job is **identity and dedup**:

1. **Value identity (layer 1).** `y = [() => y]` and `z = [() => z]` must intern to one value
   — the flagship equality case (MU-17, FE-04). Two spellings of one self-referential shape
   are one value.
2. **Template sharing (layer 2).** Two spellings of one mutual group share a summary
   template, so a fact proven of one member is reusable for the other.

Both are about **not doing work twice**, and about the MU/FE equality claims. Neither can
produce a wrong verdict: the failure direction is a **missed cache hit** — false negatives
only. That direction was recorded correctly when the fact cache landed (DECISIONS,
2026-08-01, *"Correction: the fact cache keys on the layer-1 shape"*); the *"it releases 2b"*
inference was not.

---

## 4. Consequence for the queue

The working queue was: (1) layer-2 μ-shape as the fact-cache key, (2) wire grounding,
(3) global phase-separated discovery, (4) T1.4 the wiring.

On the evidence, that is backwards for anything that moves a pinned gate.

- **T1.4, the wiring, is what moves the blockers.** The correct verdict already exists behind
  `safety::prove`; `analyze_apply` is not asking it.
- **Global, phase-separated discovery is the wiring's real prerequisite.** Per the 2026-08-01
  record, the second wiring attempt failed on non-termination because nested settlements are
  unmemoized — a discovery-structure problem, not a canonicalization one.
- **μ-grouping is independent of both.** It should be sequenced by when the MU/FE equality
  claims and cache-hit rate matter, not ahead of the wiring.

**Recommended order:** global discovery → wiring → (grounding, μ-grouping) as independent
items.

### One caution against this document's own conclusion

`IMPLEMENTATION-STATUS.md` §6a records that *"a probe through the new entry point answered
all four blockers correctly, but the pinned tests still failed — the probe was measuring two
cutoffs composing."* This finding shows the fact graph gets 2b's **program** right. Whether
2b's **pinned test** flips is to be verified on the wiring, not assumed. The standing rule
applies: when a pinned gate goes green, report the mechanism, not the outcome.

Note also that this finding speaks only to **2b**. The other three blockers are filed against
different causes (1b: grounding §4 exact-singleton fact chains; 2a: region-table §5
argument-tuple projection; 3: completion carried on the fact) and are **not** re-examined
here. It would be a mistake to generalize from one corrected row to the whole table.

---

## 5. Proposed corrections (not applied)

1. `IMPLEMENTATION-STATUS.md` §4, blocker 2b row — replace the *"actual blocker"* cell with
   the wiring, and cross-reference §3's already-correct statement. Optionally note that §3
   and §4 disagreed, so the reconciliation is visible rather than silent.
2. `src/analyzer/bodycheck.rs:432` `#[ignore]` text — it currently asserts the join between
   `mu::canonicalize_group` and `make_closure` is what blocks 2b. The *description* of that
   join is accurate and worth keeping (it is why `oracle::mu` is dead code); the *attribution*
   to 2b is what fails. Re-file the join description under μ-grouping's own item.
3. Nothing in the manifest-verified specifications changes. B4 layer (2) and C§13.4 are
   correct as written; the implementation simply has not built layer 2 yet, and that remains a
   recorded false-negative gap in `analyzer::factcache`'s module docs.

---

*End of finding.*
