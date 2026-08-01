# NEXT — Phase A Worked Examples, Recovered Verbatim

**Date:** 2026-07-21. **Discharges the test-suite spec's A-WRK RECOVER register.** Every grid below is
extracted **verbatim** from the project's design-session transcripts (the register's instruction: recover,
do not reconstruct). `journal.txt` is the transcript-mount catalog on the drafting agent's side, not a repo
file — this document replaces the transcript pointer for repo purposes. Sources:
**[T1]** = transcript 2026-07-15-07-57-25-next-language-design-sessions.txt (the battery + numeric inventory);
**[T2]** = transcript 2026-07-15-10-43-01 (candidate v0.2–v0.4 texts, pairUp/rotate grids).
Prose context is trimmed; code blocks and derivation lines are untouched.

## 1. factorial — drift, point base, the grid condition, and `where` [T1]

```
const factorial = (n) => match n {
    0 => 1
    _ => n * factorial(n - 1)
}
```
- Recursive argument update: `n - 1` → drift is `+Equals(-1)`, strictly decreasing
- Base pattern: `Equals(0)`
- The orbit n, n-1, n-2, ... hits 0 iff n is a non-negative integer

Derived input contract: `Intersection(GreaterOrEqual(0), Mod(1, 0))`

```
factorial(5)      // Equals(5) ⊑ GreaterOrEqual(0) ∧ Mod(1,0) ✓ compiles
factorial(-3)     // Equals(-3) fails GreaterOrEqual(0) ✗ compile error
factorial(2.5)    // Equals(2.5) fails Mod(1,0) ✗ compile error

const x = someInput            // unknown contract
factorial(x)                   // ✗ compile error — nothing proven about x

match x {
    k when k >= 0 && k % 1 == 0 => factorial(k)   // ✓ guard establishes both
    _ => 0
}
```

The `where` triple (Case 3):
```
const factorial = (n where n >= 0 && n % 1 == 0) => match n { ... }
// ✓ exactly matches derived contract — pure documentation, zero behavior change

const factorial = (n where n >= 1 && n % 1 == 0) => match n { ... }
// ✓ stricter than derived — legal, callers now can't pass 0

const factorial = (n where n >= -5) => match n { ... }
// ✗ compile error — promises to accept -5, but the body's recursion
//    can't ground out for negatives. Explicit contract exceeds derived.
```

## 2. countdown by 2 — the drift pair's second half [T1]

```
const countdown = (n) => match n {
    0 => "done"
    _ => countdown(n - 2)
}
```
Drift is -2, base is `Equals(0)`. The orbit n, n-2, n-4, ... hits 0 iff n is a non-negative **even**
integer. Derived contract: `Intersection(GreaterOrEqual(0), Mod(2, 0))`.
```
countdown(10)   // ✓
countdown(7)    // ✗ compile error — Equals(7) fails Mod(2,0); would skip past 0 forever
```

## 3. broken fibonacci — the rejection smoke test [T1]

```
const f = (n) => match n {
    0 => 1
    _ => f(n - 1) + f(n - 2)    // two calls, different drifts (-1 and -2)
}
```
Drift -2 needs `Mod(2,0)`, drift -1 needs `Mod(1,0)`, and they interleave — n-1 feeds back into both
branches. The correct derived contract here is `GreaterOrEqual(0) ∧ Mod(1,0)` but *also* needs a second
base case (`1 => 1`) or `f(1)` recurses to `f(-1)`. As written, the compiler should reject it — the orbit
from n=1 misses the base.

## 4. collatz — the gray-zone flagship [T1]

```
const collatz = (n) => match n {
    1 => 1                                  // exit A: Equals(1)
    k when k % 2 == 0 => collatz(k / 2)     // B: Mod(2,0)
    _ => collatz(3 * k + 1)                 // C: Mod(2,1) ∧ NotEquals(1)
}
```
Edge from C (step `3k + 1`), via the Mod scaling rule (`Mod(N, R) × Equals(c) = Mod(N·c, R·c)` for c > 0):
```
Mod(2,1) × Equals(3) = Mod(6,3)
Mod(6,3) + Equals(1) = Mod(6,4)
Mod(6,4) ⊑ Mod(2,0)                    // existing divides rule: 2 | 6, 4 mod 2 = 0
→ edge C → B, proven ("odd → even" is derived)
```
Edge from B (step `k / 2`): `Mod(2,0) × Equals(1/2) = Mod(1,0)`: integers, parity gone. `Mod(1,0)`
intersects A, B, and C: a **fork** the arithmetic cannot prune. Refining B into `Mod(4,0)` / `Mod(4,2)`
resolves one level and recreates the fork one level deeper — an infinite regress into the 2-adic structure
of the input. No finite refinement resolves it; division is the one operation in the body that destroys
Mod information. Cycles: B → B (drift ÷2, toward 1 — a good cycle) and C → B → C (net step
n → (3n+1)/2; `(3n+1)/2 < n ⟺ n < −1` — never, for n ≥ 1: provably away from base). Derived provable
sublanguage:
```
Pow2 = Equals(1) ∪ (Equals(2) × Pow2)
```
`collatz(64)` compiles; `collatz(7)` is unproven for the symbolic rule — the gray tier's origin case.

## 5. the −4 trap variant — provably-doesn't-ground tier [T1]

Changing −3 to −4 makes odd → odd a self-loop (Mod(2,1) preserved), net −4 away from base → trap.
Inputs that can enter the trap are removed via backward propagation, producing the derived input contract:
```
(Mod(2,1) ∧ GreaterThan(100)) ∪ (Mod(2,0) ∧ GreaterThan(89))
```
(Odds must exit immediately; evens must clear 100 in one +11 step to avoid landing on a trapped odd.)
The function remains legal; dangerous call sites are compile errors.

## 6. McCarthy 91 — landing zones; point vs range bases [T1]

Nested recursion `m(m(n + 11))`; the circularity is broken in closed form:
1. **Landing zone.** Base region boundary T, drift d toward it: every climb from below arrives in
   `(T, T + d]`. McCarthy 91: zone `(100, 111]`.
2. **Candidate return contract.** Exit branch applied to the landing zone: `− 10` → candidate `Range(90, 101]`.
3. **Feed-back check.** One F(C) ⊑ C induction, licensed by the grounding bound ⌈distance/d⌉.

**McCarthy 91 is proven for all reals, unconditionally.** From any real n ≤ 100 the distance to the exit
region is 101 − n — finite — and the climb depth is ⌈(101 − n)/11⌉; feed-back laps net +1 per lap and are
likewise finite. Because the exit is a region, no grid condition arises. The candidate `Range(90, 101]`
soundly over-approximates the pointwise truth (`Equals(91)` for n ≤ 100).

| | factorial | McCarthy 91 |
|---|---|---|
| base | `Equals(0)` — a point | `k > 100` — a region |
| can you skip it? | yes (off-grid inputs) | no (it's a half-line) |
| grid condition | `Mod(1, 0)` required | none |
| derived input contract | `GreaterOrEqual(0) ∧ Mod(1,0)` | none — all reals |

## 7. isEven/isOdd — the even/odd cycles, both variants [T1]

**Same bases (0⇒true / 0⇒false):**
```
const isEven = (n) => match n {
    0 => true
    _ => isOdd(n - 1)      // isEven calls isOdd
}
const isOdd = (n) => match n {
    0 => false
    _ => isEven(n - 1)     // isOdd calls isEven
}
```
SCC treatment: the two-step lap isEven→isOdd→isEven has drift −1 per hop, bases {0} in both — deriving
`GE(0) ∧ Mod(1,0)` for both functions, exactly factorial's contract.

**Different bases (0⇒true / 1⇒true) — the threading example:**
```
isEven: 0 => true          otherwise => isOdd(n − 1)
isOdd:  1 => true          otherwise => isEven(n − 1)
```
Trace isEven(4): →isOdd(3)→isEven(2)→isOdd(1) ✓ grounds. Trace isEven(3): →isOdd(2)→isEven(1)→isOdd(0)
→isEven(−1)→... **diverges** — it threads between both bases forever. After k hops the state is
(isEven if k even else isOdd, n−k); grounding needs ∃k with (k even ∧ n−k=0) ∨ (k odd ∧ n−k=1) — both
disjuncts solve to **n even, n ≥ 0**. Per-(exit, position) grids: exit (isEven, 0) needs n − k = 0 with
k even → n even; exit (isOdd, 1) needs n − k = 1 with k odd → n even. Derived: **isEven requires
`GE(0) ∧ Mod(2, 0)`**; symmetrically **isOdd requires `GE(1) ∧ Mod(2, 1)`**. `isEven(3)` is a compile
error naming the threading. The lap-composed step (one full cycle: −2) plays the role single-function
drift played. Cycle classification is minimum-mean-cycle on the graph — bound computable in advance.
(The *return-fact* twin — vector induction `F(C_E, C_O) ⊑ (C_E, C_O)` — is the application spec's AP-06.)

## 8. makeLinkedList — the canonical family trace (the author's acceptance test) [T1/T2]

```
nums = [1, 2, 3, 4]
makeLinkedList = (value, ...rest) =>
    { value, next: rest.length > 0 ? makeLinkedList(...rest) : null }
x = makeLinkedList(...nums)

F_LL = (group, depth, d, args) => Record(
           value: args[d],
           next:  d < depth - 1 ? group[0] : Equals(null) )

x                      ⊑ Recursion({ depth: 4, position: 0, args: A, formula: F_LL })
x.value                ⊑ Equals(1)
x.next                 ⊑ Recursion({ depth: 4, position: 1, args: A, formula: F_LL })
x.next.next.next.value ⊑ Equals(4)
x.next.next.next.next  ⊑ Equals(null)
x.next.next.next.next.value → refuted, witness (null, "value")
```

## 9. pairUp ×3 and rotate — the σ-reading grids [T2]

```
── pairUp(...rest)      out = (2,3,…)   σ: j↦j+2   drift −2
   F: first: args[2d], second: args[2d+1]      // disjoint pairs
── pairUp(b, ...rest)   out = (1,2,…)   σ: j↦j+1   drift −1
   F: first: args[d],  second: args[d+1]       // sliding window
── pairUp(a, ...rest)   out = (0,2,3,…) σ: 0↦0, j↦j+1
   σᵈ: 0↦0, j↦j+d → F: first: args[0], second: args[d+1]   // anchor/pivot
── rotate(b, c, a, rest−1)   len-diff 0 (counter grounds);  σ = 3-cycle
   σᵈ(0) = d mod 3 → F: top: args[d mod 3]
   r.next⁷.top ⊑ Equals("y")   // 7 mod 3 = 1 — foresight through permutation
```

*Phase-A note: grids 1–7 are oracle-verifiable today (numeric machinery); grids 8–9 seed the Part-D
candidate's future battery and stay expectation-only until that gate opens. Every block above is a
transcript quotation; discrepancies against a spec are resolved by the spec, with the discrepancy logged.*
