> ## 📗 STATUS: **HISTORICAL** — record of a past review/audit; not current guidance
> The current implementation-status authority is **`IMPLEMENTATION-STATUS.md`**. Left unedited.

# NEXT Analyzer Core Checkpoint Review — 8.1a through 8.1c

**Review basis:** current repository snapshot in `Archive(2).zip`  
**Scope:** focused architecture-to-code review before opening the return-induction tail.

> **Executive verdict**  
> 8.1c is architecturally sound and implements the §4a shape-repeat cutoff correctly. However, I would not open the SCC return-induction tail yet. The current analyzer domain does not yet implement the specification's joint/correlated operand state or structural survival of function metadata through tuples/records. That is a load-bearing gap because the induction tail must reason over jointly represented callee/argument alternatives without inventing false cross-pairs.

## 1. Checkpoint status

| Area | Assessment | Checkpoint status |
|---|---|---|
| 8.1a — AnalysisContract core | Sound-looking scalar/top-level metadata core, but not yet the full §2 correlated/structural annotated domain. | **PARTIAL** |
| 8.1b — ApplicationOutcome algebra | Good tri-state completion and evidence-preserving outcome combinators. | **APPROVE CORE** |
| 8.1c — admitted-instance inventory | Matches §4a: repeat a shape on the active path → no new admission; induction handles the cycle later. | **APPROVE** |
| Ready for return-induction tail | Not yet. First land the joint/correlated annotated operand representation and witness discipline. | **HOLD** |

## 2. Main finding: the joint/correlated operand state is not implemented yet

The application specification is explicit that application analysis receives one joint correlated `AnalysisContract` denoting `[callee, …arguments]` tuples, and that processing occurs per live correlated alternative. A projected implementation is allowed only if cross-pair failures that arise solely from projection degrade to **unproven** rather than **refuted**.  
*Spec: `next-application-induction-specification-v0-8.md:7–13`*

The current implementation instead defines the abstract-domain element as:

```rust
pub struct AnalysisContract {
    pub contract: Contract,
    pub metadata: InstanceMetadata,
}
```

The concretization logic applies metadata only when the runtime value itself is a function. Non-functions are accepted by the ordinary contract alone. Therefore function metadata nested inside a tuple/record/correlated alternative is not represented by this structure.  
*Implementation: `src/analyzer/domain.rs:62–67, 139–151`*

For example:

```next
choice = cond
    ? [numFn, 5]
    : [strFn, "hello"]

choice[0](choice[1])
```

The required state is effectively:

```text
(numFn, 5)
OR
(strFn, "hello")
```

A positional projection instead produces independent possibilities for callee and argument and can synthesize the impossible cross-pairs:

```text
(numFn, "hello")
(strFn, 5)
```

The spec exists specifically to prevent those synthesized pairs from becoming false refutations.

## 3. Test-name mismatch: current AP-24 is not the specification's AP-24

The test named `ap24_union_join_is_componentwise_and_evidence_preserving` currently verifies outcome joining: produced-contract union, completion-evidence precedence, and `may_not_complete` OR-combination.  
*Implementation: `src/analyzer/tests.rs:827–844`*

But specification AP-24 is the correlated `numFn`/`strFn` application case. AP-29 is the explicit false-cross-pair rule, and AP-30 is the completion/fall-through version of the same joint-realization discipline.  
*Spec: `next-application-induction-specification-v0-8.md:58`*

Recommended actions:

- Rename or renumber the current outcome-join test so it does not appear to discharge the correlated AP-24 case.
- Add the real AP-24 correlated application test.
- Add AP-29: projected cross-pair failure → `unproven`, never `refuted`.
- Add AP-30: cross-pair fall-through without joint inhabitance → `UnprovenPossible`; with proved joint inhabitance → `ProvenPresent(witness)`.

## 4. 8.1c review: the inventory algorithm itself is correct

The implementation carries exactly the intended state: `(instance, active shape sequence)`. A target whose shape is not active is admitted; a target whose shape already appears on the active path is cut off and is not admitted through that path. The cutoff makes no claim that recursion is safe or productive; it only prevents minting another analysis instance. Return induction remains responsible for the recursive proof.  
*Implementation: `src/analyzer/inventory.rs:31–44, 46–72`*

```text
A → A
cutoff immediately → inventory {A}

A → B → A
cutoff on repeated A → inventory {A, B}

A → {B, C}; B → D; C → D
no shape repeat → inventory {A, B, C, D}; D deduplicated
```

This division of responsibility is the right one:

```text
shape repeats
≠ "recursion is proven"

shape repeats
= "do not mint another instance; §6 induction owns this cycle"
```

## 5. Smaller 8.1c issue: order-independent as a set, not necessarily as the returned `Vec`

The module comments say the inventory is order-independent and “verified across seed orders in the suite,” but `build_inventory` returns a discovery-ordered `Vec<Instance>`. The semantic inventory **set** is order-independent, but different root or transition iteration order can produce a different vector order unless the output is canonicalized.  
*Implementation: `src/analyzer/inventory.rs:46–72`*

Recommended actions:

- Either document the returned `Vec` as an unordered-set representation, or canonicalize its final ordering.
- Add tests for reversed root order and reversed transition enumeration before candidate IDs/SCC/cache identity depend on this result.

## 6. Spec ↔ implementation mismatch around `Known(∅)`

The specification currently normalizes `(C, Known(∅)) → Bottom` for the function-position `AnalysisContract` semantics. The implementation deliberately only collapses to `Bottom` when `C` is function-only; off function positions, metadata is treated as vacuous.  
*Spec: `next-application-induction-specification-v0-8.md:19`; Implementation: `src/analyzer/domain.rs:80–109`*

```text
(Kind(Function), Known(∅)) → Bottom

(Kind(Number), Known(∅)) → Number   // implementation interpretation
```

I think the implementation's generalized interpretation is defensible if `AnalysisContract` is allowed to represent arbitrary values: non-function members can remain inhabited while function alternatives are empty. But this must be made explicit in the spec before the structural/correlated domain is built.

This is a **document-integration mismatch**, not evidence of an unsound architecture.

## 7. Strengthen the witness interface before real application wiring

The current completion algebra stores:

```rust
ProvenPresent(ValueRef)
```

The module documentation correctly says this must represent a jointly represented completing execution, but the unit tests currently use arbitrary values as witness tokens. That is adequate for testing the algebra alone; it is too weak for the real application/induction tail.  
*Implementation: `src/analyzer/application.rs:22–35`; `src/analyzer/tests.rs:791–804`*

Before real row selection and induction, the witness representation should make the required joint realization difficult to fake, conceptually something like:

```text
ApplicationWitness {
    callee,
    arguments,
    // and, where needed, realized environment / alternative provenance
}
```

The precise representation can differ, but the invariant should be structural: a refutation witness is a represented callee/argument execution, not an argument token or two independently plausible values.

## 8. What already looks strong

- `Known` vs `Unknown` metadata is explicit rather than conflated.
- γ membership is checked recursively through annotated captured environments.
- Metadata coverage is semantic rather than raw instance-key equality.
- The implementation allows narrower captured environments to be covered by broader ones when the annotated subcontract proves it.
- `intersectA` / meet logic is deliberately containment-sound rather than pretending complete exact meets.
- The outcome algebra preserves the completion tri-state instead of collapsing “witnessed” and “merely possible”.
- 8.1c does not smuggle a recursion proof into the shape cutoff.

## 9. Recommended next implementation sequence

### Step 1 — Land a bridge increment for the joint/correlated annotated operand domain

- Represent `[callee, …arguments]` as one correlated analyzer state.
- Preserve function instance metadata inside Tuple/Record/Union alternatives.
- Implement structural annotated subcontract/meet behavior needed by that representation.
- Add the real AP-24, AP-29 and AP-30 batteries.

### Step 2 — Resolve the small interface/document issues

- Resolve/document the `Known(∅)` generalized semantics.
- Resolve/document the inventory ordering contract.

### Step 3 — Freeze the interfaces

Freeze the interfaces of 8.1a–c plus the correlation bridge.

### Step 4 — Open the interlocked induction tail

```text
μ-aware body walk
    ↓
candidate fact graph
    ↓
SCC/vector return induction
    ↓
analyze_apply wiring
    ↓
Phase A batteries
```

Overall sequence:

```text
8.1a core AnalysisContract / γ / metadata coverage
    ↓
8.1b core ApplicationOutcome / completion algebra
    ↓
8.1c finite admitted-instance inventory
    ↓
BRIDGE correlated annotated operand state + joint witnesses
    ↓
TAIL μ body walk → candidate graph → SCC return induction
    ↓
analyze_apply → Phase A
```

## 10. Final checkpoint verdict

> **8.1c: APPROVED.**  
> It correctly implements §4a admission/cutoff and keeps induction responsibility separate.
>
> **8.1a: CORE APPROVED, FULL §2 NOT YET COMPLETE.**  
> The top-level `AnalysisContract` machinery is sound-looking, but the joint/correlated structural domain required by the application spec is absent.
>
> **8.1b: APPROVED AS OUTCOME ALGEBRA.**  
> Real witness construction still needs the joint operand representation.
>
> **Return-induction tail: HOLD FOR ONE BRIDGE INCREMENT.**  
> Fixing the correlation layer now is much cheaper than writing SCC induction around a projected callee/argument abstraction and repairing it later.

## Source references

- `next-application-induction-specification-v0-8.md:7–13` — joint correlated operand state and per-alternative application processing.
- `next-application-induction-specification-v0-8.md:19` — `AnalysisContract` γ semantics and `Known(∅)` normalization statement.
- `next-application-induction-specification-v0-8.md:23` — correlated metadata and annotated subcontract requirements.
- `next-application-induction-specification-v0-8.md:58` — AP-24, AP-29, AP-30 test definitions.
- `src/analyzer/domain.rs:62–67, 80–109, 139–151` — current `AnalysisContract` shape, `Known(∅)` normalization, γ membership.
- `src/analyzer/application.rs:1–15, 22–49` — current outcome-algebra scope and completion witness representation.
- `src/analyzer/inventory.rs:1–26, 31–72` — §4a closure algorithm, cutoff condition, finiteness claim and returned inventory.
- `src/analyzer/tests.rs:791–844, 890 onward` — current completion/outcome tests and 8.1c inventory tests.

**Review limitation:** this is a source/spec review of the supplied snapshot. The environment used for the review did not provide Cargo/Rust tooling, so the test suite was not independently executed during this checkpoint.
