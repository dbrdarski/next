//! The proven-fact cache — C§13.4.
//!
//! > **Proven-return-fact cache** ((analysis instance, row-set I, demanded C) → verdict;
//! > unproven entries per-compilation). Every query is interned; every entry a fact or
//! > an appropriately-scoped shrug.
//!
//! **Why this is part of the T1.4 boundary.** Moving `analyze_apply` onto the settled facts
//! means a settlement analyzes bodies whose calls reach `analyze_apply` again. Guarding
//! that with a *global* "am I settling?" flag is unsound: it answers every nested query from
//! the hypotheses, including for callees that are not members of the graph and hold no
//! hypothesis, which silently drops their traps. Measured on 2026-08-01: ten lib failures,
//! one of them `Proven` where the suite demands a refutation — a false accept.
//!
//! The key is therefore the **fact node**, not a flag. A re-entrant query on *the same*
//! node is a recursive reference and resolves through its hypothesis (correct vector
//! induction, C§13.2a); a query on a *different* node is genuinely settled.
//!
//! **The instance half of the key is the canonical applied function value.** Closure
//! conversion has already reduced lexical scope to positional immutable captures, recursive
//! construction has already tied those positions into a closed rational graph, and universal
//! interning has already assigned that graph one [`ValueRef`]. Reconstructing source sibling
//! names or serializing a second group identity here would reverse that canonicalization.
//!
//! The complete [`FactKey`] is itself **interned**; its function value and contract components
//! are canonical pointers too. Structural hashing therefore happens once when the query is
//! formed; every memo lookup after that is one pointer comparison.
//!
//! This concrete key deliberately makes no claim about future symbolic instances. If those
//! arrive, their identity is canonical code applied to positional capture contracts; no
//! source-level group template is reintroduced.
//!
//! **Pure memoization.** A settled entry is a deterministic fact of the complete semantic key
//! and is owned by the same [`Interner`] that owns every identity in it. Sharing that owner
//! shares the memo; dropping it reclaims both together. In particular, the complete
//! named-contract environment is an explicit key argument: the same shape under `N = String`
//! and `N = Number` is not the same fact. A compilation-bound clear would only hide an omitted
//! dependency; it cannot make an incomplete key correct.
//!
//! **Only top-level settlements are cached.** A settlement running inside another one sees
//! ambient hypotheses, so its verdict is hypothesis-relative and must not be recorded as a
//! fact. `begin`/`finish` still maintain dynamic recursion state in that case, but do not
//! publish the nested answer; this costs hits and never soundness.

use std::cell::{Cell, RefCell};
use std::collections::HashSet;

use crate::analyzer::induction::Claim;
use crate::analyzer::safety::BodySafety;
use crate::analyzer::{Analysis, domain::Instance};
use crate::contract::{Contract, ContractEnv};
use crate::intern::Interned;
use crate::interner::Interner;
use crate::value::ValueRef;

/// A fact node: (analysis instance, row-set `I`, demanded `C`).
///
/// The instance is the canonical applied function value. The complete named-contract
/// environment is a further analyzer input until named contracts become ordinary captures.
/// The claim carries the demanded contract for a return fact and discriminates
/// safety/completion facts.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct FactKey {
    instance: ValueRef,
    named_contracts: Interned<NamedContractEnvironment>,
    input: Vec<Interned<Contract>>,
    claim: MemoClaim,
}

/// The domain-indexed query for a symbolic function application. Its identity is
/// the canonical code/capture-contract application, never the source lambda or a
/// recursive declaration group. The answer is the immutable body analysis for
/// these arrived arguments and named-contract meanings.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct SymbolicFactKey {
    instance: Instance,
    named_contracts: Interned<NamedContractEnvironment>,
    input: Vec<Interned<Contract>>,
}

thread_local! {
    /// Dynamic settlement state, not memoized knowledge. A recursive query sees its
    /// active hypothesis; only a completed outer settlement publishes an immutable answer.
    static ACTIVE: RefCell<HashSet<Interned<FactKey>>> = RefCell::new(HashSet::new());
    static DEPTH: Cell<usize> = const { Cell::new(0) };
    /// Dynamic symbolic settlement state. The complete key, rather than a raw
    /// code-shape flag, decides whether a recursive edge is an admitted hypothesis.
    static ACTIVE_SYMBOLIC: RefCell<Vec<Interned<SymbolicFactKey>>> = const { RefCell::new(Vec::new()) };
    static SYMBOLIC_DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// A canonical snapshot of `ContractEnv`. Sorting removes `HashMap` iteration order; interning
/// makes the fact key itself compare one pointer. Including the complete environment is a
/// conservative dependency key: an unrelated binding may cost a hit, but can never reuse a fact
/// under a different meaning of a referenced contract such as `N`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct NamedContractEnvironment(Vec<(String, Interned<Contract>)>);

pub(crate) fn named_environment(
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Interned<NamedContractEnvironment> {
    let mut named: Vec<(&String, &Contract)> = cenv.iter().collect();
    named.sort_by_key(|(name, _)| *name);
    let environment = NamedContractEnvironment(
        named
            .into_iter()
            .map(|(name, contract)| (name.clone(), interner.contract(contract.clone())))
            .collect(),
    );
    interner.intern_enum(environment)
}

/// The claim component of a memo key. A demanded return contract is interned just like
/// every other contract in the key; safety and completion are nullary discriminators.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum MemoClaim {
    Safety,
    Return(Interned<Contract>),
    Completes,
}

/// What the cache knows about a node.
pub(crate) enum Cached {
    /// Currently being settled — a query for it is a **recursive reference**, which never
    /// unfolds (C§13.2) and must resolve through the node's hypothesis instead.
    InProgress,
    /// Immutable answer published in this identity universe.
    Settled(BodySafety),
}

/// The node for a call, or `None` when the callee is not a resolvable function instance
/// (nothing to key on — the caller settles uncached).
pub(crate) fn key(
    callee: &ValueRef,
    args: &[Contract],
    claim: &Claim,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Interned<FactKey>> {
    callee.as_fn()?;
    callee.as_closure()?;
    let named_contracts = named_environment(cenv, interner);
    let input = args.iter().map(|c| interner.contract(c.clone())).collect();
    let claim = match claim {
        Claim::Safety => MemoClaim::Safety,
        Claim::Return(c) => MemoClaim::Return(interner.contract(c.clone())),
        Claim::Completes => MemoClaim::Completes,
    };
    Some(interner.memo_query(FactKey {
        instance: callee.clone(),
        named_contracts,
        input,
        claim,
    }))
}

pub(crate) fn symbolic_key(
    instance: &Instance,
    args: &[Contract],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Interned<SymbolicFactKey> {
    let named_contracts = named_environment(cenv, interner);
    let input = args.iter().map(|c| interner.contract(c.clone())).collect();
    interner.memo_query(SymbolicFactKey {
        instance: instance.clone(),
        named_contracts,
        input,
    })
}

pub(crate) enum SymbolicCached {
    /// The active fact's input covers this recursive arrival, so induction—not
    /// re-entry—answers the safety edge.
    Hypothesis,
    /// One complete, hypothesis-independent immutable body answer.
    Settled(std::rc::Rc<Analysis>),
    /// The same code shape repeated through a different instance or uncovered
    /// input. Shape repetition bounds discovery but proves nothing.
    UncoveredRepeat,
    Missing,
}

pub(crate) fn symbolic_lookup(
    key: &Interned<SymbolicFactKey>,
    interner: &mut Interner,
) -> SymbolicCached {
    let active = ACTIVE_SYMBOLIC.with(|held| held.borrow().clone());
    for candidate in &active {
        if candidate.instance == key.instance
            && candidate.named_contracts == key.named_contracts
            && candidate.input.len() == key.input.len()
        {
            let covered = key
                .input
                .iter()
                .zip(&candidate.input)
                .all(|(asked, assumed)| {
                    matches!(
                        crate::contract::subcontract(asked, assumed, interner),
                        crate::contract::Verdict::Proven
                    )
                });
            if covered {
                return SymbolicCached::Hypothesis;
            }
        }
    }
    if active
        .iter()
        .any(|candidate| candidate.instance.code_handle() == key.instance.code_handle())
    {
        return SymbolicCached::UncoveredRepeat;
    }
    if let Some(answer) = interner.memo_get::<SymbolicFactKey, Analysis>(key) {
        return SymbolicCached::Settled(answer);
    }
    SymbolicCached::Missing
}

pub(crate) fn symbolic_begin(key: &Interned<SymbolicFactKey>) {
    ACTIVE_SYMBOLIC.with(|active| active.borrow_mut().push(key.clone()));
    SYMBOLIC_DEPTH.with(|depth| depth.set(depth.get() + 1));
}

pub(crate) fn symbolic_finish(
    key: &Interned<SymbolicFactKey>,
    answer: &Analysis,
    tainted: bool,
    interner: &mut Interner,
) {
    let removed = ACTIVE_SYMBOLIC.with(|active| {
        let mut active = active.borrow_mut();
        let held = active.pop();
        held.is_some_and(|held| held == *key)
    });
    debug_assert!(removed, "symbolic finish pairs with the latest begin");
    let outer = SYMBOLIC_DEPTH.with(|depth| {
        let next = depth.get() - 1;
        depth.set(next);
        next == 0
    }) && !tainted;
    if outer {
        interner.memo_publish(key.clone(), answer.clone());
    }
}

/// What is known about `key`, if anything.
pub(crate) fn lookup(key: &Interned<FactKey>, interner: &Interner) -> Option<Cached> {
    if ACTIVE.with(|active| active.borrow().contains(key)) {
        return Some(Cached::InProgress);
    }
    interner
        .memo_get::<FactKey, BodySafety>(key)
        .map(|answer| Cached::Settled((*answer).clone()))
}

/// Resolution by **coverage** [author, 2026-08-03]: a demanded fact is answered by any
/// settled **Proven** fact of the same instance, named-contract environment, and claim
/// whose input domain *contains* the demanded one — the subcontract test *is* the
/// resolution, in the same step; the exact-pointer hit is merely its trivial case.
/// Only `Proven` transfers down: a refutation's witness may lie outside the narrower
/// domain, and unproven says nothing about it.
pub(crate) fn covering(key: &Interned<FactKey>, interner: &mut Interner) -> Option<BodySafety> {
    let candidates: Vec<Vec<Interned<Contract>>> = interner
        .memo_entries::<FactKey, BodySafety>()
        .into_iter()
        .filter(|(k, v)| {
            k.instance == key.instance
                && k.named_contracts == key.named_contracts
                && k.claim == key.claim
                && k.input.len() == key.input.len()
                && matches!(&**v, BodySafety::Proven)
        })
        .map(|(k, _)| k.input.clone())
        .collect();
    for domain in candidates {
        let contains = key.input.iter().zip(&domain).all(|(asked, held)| {
            matches!(
                crate::contract::subcontract(asked, held, interner),
                crate::contract::Verdict::Proven
            )
        });
        if contains {
            return Some(BodySafety::Proven);
        }
    }
    None
}

/// Mark a node as being settled, and enter a settlement. Always paired with [`finish`].
pub(crate) fn begin(key: &Interned<FactKey>) {
    let inserted = ACTIVE.with(|active| active.borrow_mut().insert(key.clone()));
    debug_assert!(inserted, "a settled query begins only once");
    DEPTH.with(|depth| depth.set(depth.get() + 1));
}

/// Record a settled verdict and leave the settlement.
///
/// At depth > 1 the verdict was reached with ambient hypotheses in scope, so it is
/// **removed** rather than recorded — a hypothesis-relative answer is not a fact.
/// `tainted` covers the hypotheses DEPTH cannot see: a vector pass installs its
/// hypotheses without a `begin` (return inference, `check_return_claim`,
/// `run_pass` verification), so a settlement launched from inside one starts at
/// depth 0 yet may still have consulted those ambient assumptions. The caller
/// samples `induction::any_hypotheses_active()` **at `begin` time** and passes it
/// here; a tainted settlement is discarded exactly like a nested one.
pub(crate) fn finish(
    key: &Interned<FactKey>,
    verdict: &BodySafety,
    tainted: bool,
    interner: &mut Interner,
) -> bool {
    let removed = ACTIVE.with(|active| active.borrow_mut().remove(key));
    debug_assert!(removed, "finish pairs with begin");
    let outer = DEPTH.with(|depth| {
        let next = depth.get() - 1;
        depth.set(next);
        next == 0
    }) && !tainted;
    if outer {
        interner.memo_publish(key.clone(), verdict.clone());
    }
    outer
}

/// Publish another verdict settled by the same outermost graph pass. Dependency
/// components are facts too: retaining only the seed would force later completion/
/// return analysis to settle the graph again. The caller may use this only after
/// [`finish`] reports that no ambient hypotheses remain.
pub(crate) fn record_settled(key: Interned<FactKey>, verdict: BodySafety, interner: &mut Interner) {
    interner.memo_publish(key, verdict);
}

/// Drop the fact memo family, for test isolation or explicit memory reclamation.
///
/// Correctness does not depend on this: a `FactKey` determines its verdict. That claim
/// used to be made here *and* be false one module over — `region`'s instance-table query
/// erased source spelling while its cached rows kept it, so one program's table answered
/// another's query. Keeping this note honest means the same discipline has to hold for every
/// memo: **if clearing can change an answer, the query is incomplete.**
#[allow(dead_code)]
pub(crate) fn clear(interner: &mut Interner) {
    interner.memo_clear::<FactKey, BodySafety>();
    interner.memo_clear::<SymbolicFactKey, Analysis>();
    ACTIVE.with(|active| active.borrow_mut().clear());
    DEPTH.with(|depth| depth.set(0));
    ACTIVE_SYMBOLIC.with(|active| active.borrow_mut().clear());
    SYMBOLIC_DEPTH.with(|depth| depth.set(0));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner::Interner;
    use crate::oracle::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    /// The code half of function identity is itself interned. The complete fact key uses
    /// the already-canonical function value, so no lookup walks or reconstructs source code.
    #[test]
    fn identical_functions_share_one_interned_code_pointer() {
        let mut i = Interner::new();
        let a = f("g = (n) => n + 1\ng", &mut i);
        let b = f("h = (n) => n + 1\nh", &mut i);
        assert!(
            a.as_fn()
                .unwrap()
                .shape_rc()
                .ptr_eq(&b.as_fn().unwrap().shape_rc()),
            "same code must be one interned allocation"
        );
    }

    /// And the reason canonicalization comes first: bound names are not part of a function's
    /// identity, so α-variants must reach the *same* pointer. A key built on parsed code
    /// (the interim your notes describe) would miss this pair.
    #[test]
    fn alpha_variants_share_one_interned_code_pointer() {
        let mut i = Interner::new();
        let a = f("g = (n) => n + 1\ng", &mut i);
        let b = f("h = (x) => x + 1\nh", &mut i);
        assert!(
            a.as_fn()
                .unwrap()
                .shape_rc()
                .ptr_eq(&b.as_fn().unwrap().shape_rc()),
            "alpha-variants are the same shape"
        );
    }

    /// The complement — pointer equality must not over-collapse.
    #[test]
    fn different_functions_do_not_share_a_code_pointer() {
        let mut i = Interner::new();
        let a = f("g = (n) => n + 1\ng", &mut i);
        let b = f("h = (n) => n + 2\nh", &mut i);
        assert!(
            !a.as_fn()
                .unwrap()
                .shape_rc()
                .ptr_eq(&b.as_fn().unwrap().shape_rc()),
            "different code is different shapes"
        );
    }

    /// Two closures over the same code but different captures are the same *shape* and
    /// different canonical function values, hence different fact instances.
    #[test]
    fn same_shape_different_captures_are_distinct_fact_nodes() {
        let mut i = Interner::new();
        let a = f("k = 1\ng = (n) => n + k\ng", &mut i);
        let b = f("k = 2\nh = (n) => n + k\nh", &mut i);
        assert!(
            a.as_fn()
                .unwrap()
                .shape_rc()
                .ptr_eq(&b.as_fn().unwrap().shape_rc()),
            "same code, so one shape"
        );
        let args = [Contract::Top];
        let cenv = ContractEnv::new();
        let ka = key(&a, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        let kb = key(&b, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        assert_ne!(ka, kb, "different captures are different fact nodes");
    }

    #[test]
    fn repeated_fact_query_is_one_shared_identity() {
        let mut i = Interner::new();
        let closure = f("limit = 5\ng = (n) => n <= limit ? n : 0\ng", &mut i);
        let args = [Contract::Top];
        let cenv = ContractEnv::new();
        let first = key(&closure, &args, &Claim::Safety, &cenv, &mut i).expect("fact key");
        let second = key(&closure, &args, &Claim::Safety, &cenv, &mut i).expect("fact key");

        assert!(
            first.ptr_eq(&second),
            "one immutable fact query must reuse one allocation"
        );
        assert_eq!(
            i.interned_count::<FactKey>(),
            1,
            "the complete fact identity is stored once"
        );
    }
}

#[cfg(test)]
mod interning_tests {
    use super::*;
    use crate::contract::Kind;
    use crate::oracle::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    /// Equal contracts are one allocation, so a key holding them compares by pointer.
    #[test]
    fn equal_contracts_intern_to_one_handle() {
        let mut i = Interner::new();
        let a = i.contract(Contract::Kind(Kind::Number));
        let b = i.contract(Contract::Kind(Kind::Number));
        assert!(a.ptr_eq(&b), "same contract must be one interned term");
        assert!(!a.ptr_eq(&i.contract(Contract::Kind(Kind::String))));
    }

    /// Compound contracts dedup through their parts, so the fact-graph's repeated domains
    /// (`I` appears on every node of a component) cost one allocation, not one per node.
    #[test]
    fn compound_contracts_dedup() {
        let mut i = Interner::new();
        let mk = |i: &mut Interner| {
            let u = Contract::union(
                Contract::Kind(Kind::Number),
                Contract::Kind(Kind::String),
                i,
            );
            i.contract(u)
        };
        let (a, b) = (mk(&mut i), mk(&mut i));
        assert!(a.ptr_eq(&b), "structurally equal compounds share one term");
        // Three terms, not one: children-first interning stores `Kind(Number)` and
        // `Kind(String)` as well as the `Union` over them. Under the earlier root-only
        // scheme this read `1`, because the children were `Box`ed inside the root and
        // had no identity of their own — which is what `shared_subterms_are_one_allocation`
        // now exercises directly.
        assert_eq!(
            i.interned_count::<Contract>(),
            3,
            "the union and both children"
        );
    }

    /// **The property children-first interning exists for**: a subterm shared between two
    /// otherwise-different contracts is stored **once**, and both parents point at it.
    ///
    /// Root-only interning could not give this. With `Box<Contract>` children the subterm had
    /// no identity — each parent carried its own copy, so `n` contracts mentioning one domain
    /// cost `n` copies of that domain's whole tree, and comparing them was a deep walk every
    /// time. This is not a micro-optimization in the fact graph: `I` appears on every node of
    /// a component (C§13.2a), and the cache key is specified to hold *interned pointers*.
    #[test]
    fn shared_subterms_are_one_allocation() {
        let mut i = Interner::new();
        // A domain of some depth, so a copy would be visible rather than incidental.
        let domain = {
            let inner = Contract::intersection(
                Contract::Kind(Kind::Number),
                Contract::Greater(0.into()),
                &mut i,
            );
            Contract::union(inner, Contract::Kind(Kind::Null), &mut i)
        };
        let before = i.interned_count::<Contract>();

        // Two different parents over the *same* subterm.
        let lhs = Contract::tuple([domain.clone(), Contract::Kind(Kind::String)], &mut i);
        let rhs = Contract::record([("d".to_string(), domain.clone())], &mut i);

        // Exactly two new terms: the domain's own handle (minted by the first parent) and
        // `Kind(String)`. The second parent added nothing at all — it reused the handle.
        // A constructor returns an un-interned root holding interned children, so the
        // `Tuple` and `Record` themselves are not counted here.
        assert_eq!(
            i.interned_count::<Contract>() - before,
            2,
            "the shared domain costs one allocation for both parents, not one each"
        );

        // And they hold the *same pointer*, which is the claim that matters: identity, not
        // merely equality. `Interned::ptr_eq` is address comparison, so this cannot pass by
        // accident of structural equality.
        let (Contract::Tuple(elems), Contract::Record(fields)) = (&lhs, &rhs) else {
            panic!("constructed a Tuple and a Record");
        };
        assert!(
            elems[0].ptr_eq(&fields[0].1),
            "the shared subterm is one allocation reached from both parents"
        );

        // Re-deriving the same domain hands back that same allocation rather than a new one.
        let again = {
            let inner = Contract::intersection(
                Contract::Kind(Kind::Number),
                Contract::Greater(0.into()),
                &mut i,
            );
            Contract::union(inner, Contract::Kind(Kind::Null), &mut i)
        };
        assert!(
            i.contract(again).ptr_eq(&elems[0]),
            "an equal domain re-interns to the same term"
        );
    }

    /// The key's whole point: two calls at the same fact node produce the *same* key, so the
    /// second is a cache hit rather than a re-settlement.
    #[test]
    fn the_same_call_produces_the_same_key() {
        let mut i = Interner::new();
        let g = f("g = (n) => n + 1\ng", &mut i);
        let args = [Contract::Kind(Kind::Number)];
        let cenv = ContractEnv::new();
        let ka = key(&g, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        let kb = key(&g, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        assert_eq!(ka, kb, "same node, same key");
    }

    /// A different demanded contract is a different node, even for the same function and
    /// domain — the `C` in (instance, I, C).
    #[test]
    fn a_different_demand_is_a_different_node() {
        let mut i = Interner::new();
        let g = f("g = (n) => n + 1\ng", &mut i);
        let args = [Contract::Kind(Kind::Number)];
        let cenv = ContractEnv::new();
        let ka = key(&g, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        let kb = key(&g, &args, &Claim::Completes, &cenv, &mut i).expect("keyed");
        assert_ne!(ka, kb);
    }

    /// The contract environment is not ambient metadata: a named contract read by the
    /// root or a statically reachable helper is an argument to the analysis fact.
    #[test]
    fn named_contract_environment_is_part_of_fact_identity() {
        let mut i = Interner::new();
        let f = f(
            "g = (x) => x :: {\n N => 1 + \"s\"\n _ => 1\n }\n\
             f = (x) => g(x)\n\
             f",
            &mut i,
        );
        let args = [Contract::Kind(Kind::Number)];
        let strings = ContractEnv::from([("N".to_string(), Contract::Kind(Kind::String))]);
        let numbers = ContractEnv::from([("N".to_string(), Contract::Kind(Kind::Number))]);

        let string_key = key(&f, &args, &Claim::Safety, &strings, &mut i).expect("keyed");
        let same_string_key = key(&f, &args, &Claim::Safety, &strings, &mut i).expect("keyed");
        let number_key = key(&f, &args, &Claim::Safety, &numbers, &mut i).expect("keyed");

        assert_eq!(
            string_key, same_string_key,
            "same contract dependency, same fact"
        );
        assert_ne!(
            string_key, number_key,
            "changing helper pattern N from String to Number changes the root fact"
        );
    }

    /// `ContractEnv` is a `HashMap`, whose iteration order is not semantic. Canonical sorting
    /// must produce one interned environment pointer for the same bindings in any insert order.
    #[test]
    fn named_contract_environment_order_does_not_change_fact_identity() {
        let mut i = Interner::new();
        let g = f("g = (n) => n + 1\ng", &mut i);
        let args = [Contract::Kind(Kind::Number)];
        let mut first = ContractEnv::new();
        first.insert("N".to_string(), Contract::Kind(Kind::String));
        first.insert("M".to_string(), Contract::Kind(Kind::Number));
        let mut reversed = ContractEnv::new();
        reversed.insert("M".to_string(), Contract::Kind(Kind::Number));
        reversed.insert("N".to_string(), Contract::Kind(Kind::String));

        let first_key = key(&g, &args, &Claim::Safety, &first, &mut i).expect("keyed");
        let reversed_key = key(&g, &args, &Claim::Safety, &reversed, &mut i).expect("keyed");
        assert_eq!(
            first_key, reversed_key,
            "map insertion order is not fact identity"
        );
    }
}

#[cfg(test)]
mod recursive_instance_tests {
    use super::*;
    use crate::oracle::run_source_in;

    /// Recursive fact identity is exactly the canonical applied function value:
    /// spelling variants in one identity universe share it, genuinely different
    /// members do not, and a symmetric cycle collapsed by value interning shares it.
    #[test]
    fn recursive_fact_keys_follow_canonical_function_values() {
        let mut i = Interner::new();
        let even_a = run_source_in(
            "isEven = (n) => n == 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n == 0 ? false : isEven(n - 1)\n\
             isEven",
            &mut i,
        )
        .unwrap()
        .0;

        let even_b = run_source_in(
            "even = (k) => k == 0 ? true : odd(k - 1)\n\
             odd = (k) => k == 0 ? false : even(k - 1)\n\
             even",
            &mut i,
        )
        .unwrap()
        .0;
        assert!(even_a.ptr_eq(&even_b), "spelling variants are one value");

        let args = [Contract::Top];
        let cenv = ContractEnv::new();
        let ka = key(&even_a, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        let kb = key(&even_b, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        assert!(ka.ptr_eq(&kb), "one function value is one fact instance");

        // The sibling is a *different* member of the same group.
        let odd_a = {
            let function = even_a.as_fn().unwrap();
            match function.capture_binding("isOdd") {
                Some(crate::env::Binding::Value(v)) => v,
                other => panic!("isOdd must be captured: {other:?}"),
            }
        };
        assert!(!even_a.ptr_eq(&odd_a));
        let ko = key(&odd_a, &args, &Claim::Safety, &cenv, &mut i).expect("keyed");
        assert_ne!(ka, ko, "different function values are different facts");

        let pair = run_source_in("a = () => b()\nb = () => a()\n[a, b]", &mut i)
            .unwrap()
            .0;
        let pair = pair.as_tuple().expect("symmetric pair");
        assert!(pair[0].ptr_eq(&pair[1]), "the value graph collapses first");
        let left = key(&pair[0], &[], &Claim::Safety, &cenv, &mut i).expect("keyed");
        let right = key(&pair[1], &[], &Claim::Safety, &cenv, &mut i).expect("keyed");
        assert!(
            left.ptr_eq(&right),
            "facts consume the collapsed value identity"
        );
    }
}

#[cfg(test)]
mod symbolic_instance_tests {
    use super::*;
    use crate::analyzer::domain::{AnalysisContract, Instance};
    use crate::contract::Kind;
    use crate::oracle::run_source_in;

    fn captured_code(interner: &mut Interner) -> crate::intern::Interned<crate::ast::Lambda> {
        run_source_in("k = 0\nf = (n) => n + k\nf", interner)
            .unwrap()
            .0
            .as_fn()
            .expect("function")
            .shape_rc()
    }

    #[test]
    fn symbolic_facts_use_full_instance_and_domain_coverage() {
        let mut i = Interner::new();
        let code = captured_code(&mut i);
        let numeric = Instance::new(
            code.clone(),
            vec![AnalysisContract::of_contract(Contract::Kind(Kind::Number))],
            &mut i,
        );
        let textual = Instance::new(
            code,
            vec![AnalysisContract::of_contract(Contract::Kind(Kind::String))],
            &mut i,
        );
        let cenv = ContractEnv::new();
        let assumed = symbolic_key(&numeric, &[Contract::Kind(Kind::Number)], &cenv, &mut i);
        let one = i.integer(1);
        let covered = symbolic_key(&numeric, &[Contract::Equals(one)], &cenv, &mut i);
        let other_instance = symbolic_key(&textual, &[Contract::Kind(Kind::Number)], &cenv, &mut i);

        symbolic_begin(&assumed);
        assert!(matches!(
            symbolic_lookup(&covered, &mut i),
            SymbolicCached::Hypothesis
        ));
        assert!(matches!(
            symbolic_lookup(&other_instance, &mut i),
            SymbolicCached::UncoveredRepeat
        ));

        let answer = Analysis::produced(Contract::Kind(Kind::Number), Vec::new());
        symbolic_finish(&assumed, &answer, false, &mut i);
        assert!(matches!(
            symbolic_lookup(&assumed, &mut i),
            SymbolicCached::Settled(_)
        ));
    }
}
