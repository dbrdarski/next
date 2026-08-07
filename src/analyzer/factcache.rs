//! The proven-fact cache — C§13.4.
//!
//! > **Proven-return-fact cache** ((analysis instance, row-set I, demanded C) → verdict;
//! > unproven entries per-compilation). Every key interned pointers; every entry a fact or
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
//! **The instance half of the key is the canonical shape** — `FnValue::shape()`, produced by
//! `oracle::canon` — paired with the de-Bruijn-ordered capture contracts. Runtime closures are
//! universally interned, but a fact depends on the *abstract contracts* of its captures rather
//! than only their concrete value pointers; spelling variants must therefore meet at canonical
//! code plus those contract arguments.
//!
//! The shape is **interned** (`Interner::intern_code`) and the key compares it by pointer,
//! per "every key interned pointers". Structural hashing happens once per distinct shape at
//! closure construction, never per lookup. Value-capture, named-contract-environment, input,
//! and demanded-return contracts are interned too, so every semantic component compares by
//! pointer.
//!
//! **The layer-2 join (2026-08-04):** the shape half of the key is [`ShapeKey`] — a lone
//! acyclic function keys by its canonical per-lambda shape, and a member of a recursive
//! reference SCC keys by its **canonical member key within the serialized group template**
//! (`oracle::mu`'s Algorithm A — positional μ-refs, canonical slot order), which is
//! spelling- and interner-independent; sibling references route inside the serialization
//! and are excluded from the capture tuple. Where the member names cannot be derived
//! unambiguously from the sibling environments, the key falls back to the per-lambda
//! `Solo` shape — sound, at worst a missed shared hit. Still deferred: the μ package's
//! law 2 (nested-binder merge) and law 4 (partition-refinement slot merging), and fact
//! keys for **symbolic** (non-concrete) instances, which are not yet constructed at all.
//!
//! **Pure memoization.** A settled entry is a deterministic fact of the complete semantic key.
//! Reusing the table across compilations is therefore sound. In particular, the complete
//! named-contract environment is an explicit key argument: the same shape under `N = String`
//! and `N = Number` is not the same fact. A compilation-bound clear would only hide an omitted
//! dependency; it cannot make an incomplete key correct.
//!
//! **Only top-level settlements are cached.** A settlement running inside another one sees
//! ambient hypotheses, so its verdict is hypothesis-relative and must not be recorded as a
//! fact. `begin`/`finish` are no-ops in that case, which costs hits and never soundness.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::analyzer::induction::Claim;
use crate::analyzer::safety::BodySafety;
use crate::ast::Lambda;
use crate::contract::{Contract, ContractEnv};
use crate::intern::Interned;
use crate::interner::Interner;
use crate::value::ValueRef;

/// A fact node: (analysis instance, row-set `I`, demanded `C`).
///
/// The instance is `(layer-2 shape, value-capture contracts)`. The complete named-contract
/// environment is a further analyzer input until named contracts become ordinary annotated
/// captures. The claim carries the demanded contract for a return fact and is the discriminator
/// for safety/completion facts.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct FactKey {
    shape: ShapeKey,
    captures: Vec<Interned<Contract>>,
    named_contracts: Interned<NamedContractEnvironment>,
    input: Vec<Interned<Contract>>,
    claim: MemoClaim,
}

/// The **layer-2 shape** (C§12.3 layer 2 / C§13.4): a lone acyclic function keys by
/// its canonical per-lambda shape; a member of a recursive reference SCC keys by its
/// **canonical member key within the serialized group template** (Algorithm A —
/// positional μ-refs, canonical slot order), which is spelling- and
/// interner-independent. Sibling references live inside the group serialization, so
/// they are excluded from the instance's capture tuple.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum ShapeKey {
    Solo(Interned<Lambda>),
    Group(String),
}

/// A closure's layer-2 identity plus the free-variable names that resolve to its
/// own SCC siblings (excluded from capture tuples — the template routes them).
#[derive(Clone)]
pub(crate) struct Layer2 {
    pub(crate) shape: ShapeKey,
    pub(crate) siblings: std::collections::HashSet<String>,
}

thread_local! {
    /// Memo: closure value → its layer-2 identity. The group canonicalization
    /// enumerates slot permutations, so it runs once per closure, never per key.
    static LAYER2: RefCell<HashMap<ValueRef, Layer2>> = RefCell::new(HashMap::new());
}

/// The layer-2 identity of a closure (memoized). Falls back to the per-lambda
/// `Solo` shape — always sound, only ever costing a shared hit — when the group's
/// member names cannot be derived unambiguously from the sibling environments.
pub(crate) fn layer2(callee: &ValueRef) -> Option<Layer2> {
    callee.as_fn()?;
    if let Some(hit) = LAYER2.with(|m| m.borrow().get(callee).cloned()) {
        return Some(hit);
    }
    let computed = compute_layer2(callee)?;
    LAYER2.with(|m| m.borrow_mut().insert(callee.clone(), computed.clone()));
    Some(computed)
}

fn compute_layer2(callee: &ValueRef) -> Option<Layer2> {
    use crate::analyzer::bodywalk::{callee_targets, reachable_closures};
    let function = callee.as_fn()?;
    let solo = |f: &crate::value::FnValue| Layer2 {
        shape: ShapeKey::Solo(f.shape_rc()),
        siblings: std::collections::HashSet::new(),
    };

    let group = reachable_closures(callee.clone());
    let adj: Vec<Vec<usize>> = group
        .iter()
        .map(|g| {
            let targets = callee_targets(g);
            (0..group.len())
                .filter(|&j| targets.contains(&group[j]))
                .collect()
        })
        .collect();
    let me = group.iter().position(|g| g == callee)?;
    let components = crate::analyzer::induction::scc_reverse_topo(&adj);
    let component = components.iter().find(|c| c.contains(&me))?;
    let cyclic = component.len() > 1 || adj[me].contains(&me);
    if !cyclic {
        return Some(solo(function));
    }

    // Derive each member's binding name: the free-variable name under which any
    // member's environment (its own included — late-bound self-reference) resolves
    // to it. Ambiguity or a nameless member falls back to the per-lambda shape.
    let members: Vec<&ValueRef> = component.iter().map(|&i| &group[i]).collect();
    let mut names: Vec<Option<String>> = vec![None; members.len()];
    for holder in &members {
        let (Some(hf), Some(hc)) = (holder.as_fn(), holder.as_closure()) else {
            continue;
        };
        for free in hf.free_vars() {
            if let Some(crate::env::Binding::Value(v)) = hc.env.lookup(free)
                && let Some(k) = members.iter().position(|m| **m == v)
            {
                match &names[k] {
                    None => names[k] = Some(free.clone()),
                    Some(existing) if existing == free => {}
                    Some(_) => return Some(solo(function)), // two names, one member
                }
            }
        }
    }
    let names: Option<Vec<String>> = names.into_iter().collect();
    let Some(names) = names else {
        return Some(solo(function));
    };
    if names.iter().collect::<std::collections::HashSet<_>>().len() != names.len() {
        return Some(solo(function)); // one name, two members
    }

    let bindings: Vec<(String, crate::ast::Expr)> = members
        .iter()
        .zip(&names)
        .map(|(m, n)| {
            let lambda = m
                .as_closure()
                .expect("a member is a closure")
                .lambda
                .clone();
            (n.clone(), crate::ast::Expr::Lambda(lambda))
        })
        .collect();
    let keys = crate::oracle::canonical_group_keys(&bindings);
    let mine = component.iter().position(|&i| i == me)?;
    let my_key = keys.get(&names[mine])?.clone();
    Some(Layer2 {
        shape: ShapeKey::Group(my_key),
        siblings: names.into_iter().collect(),
    })
}

/// A canonical snapshot of `ContractEnv`. Sorting removes `HashMap` iteration order; interning
/// makes the fact key itself compare one pointer. Including the complete environment is a
/// conservative dependency key: an unrelated binding may cost a hit, but can never reuse a fact
/// under a different meaning of a referenced contract such as `N`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct NamedContractEnvironment(Vec<(String, Interned<Contract>)>);

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
    /// Settled this compilation.
    Settled(BodySafety),
}

thread_local! {
    static CACHE: RefCell<HashMap<FactKey, Option<BodySafety>>> = RefCell::new(HashMap::new());
    /// Depth of active settlements — non-zero means ambient hypotheses are in scope, so
    /// nothing settled right now is a fact.
    static DEPTH: RefCell<usize> = const { RefCell::new(0) };
}

/// The node for a call, or `None` when the callee is not a resolvable function instance
/// (nothing to key on — the caller settles uncached).
pub(crate) fn key(
    callee: &ValueRef,
    args: &[Contract],
    claim: &Claim,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<FactKey> {
    let f = callee.as_fn()?;
    let closure = callee.as_closure()?;
    let layer2 = layer2(callee)?;
    // De-Bruijn order: `free_vars` is the ordered capture-slot list `shape`'s `@cap`i
    // refer to, so iterating it gives a positional tuple independent of name spelling.
    // Sibling references of a recursive group are routed inside the group
    // serialization and excluded here (the layer-2 discipline).
    let capture_terms: Vec<Contract> = f
        .free_vars()
        .iter()
        .filter(|n| !layer2.siblings.contains(*n))
        .map(|n| match closure.env.lookup(n) {
            Some(crate::env::Binding::Value(v)) => Contract::Equals(v),
            _ => Contract::Top,
        })
        .collect();
    let captures = capture_terms
        .into_iter()
        .map(|c| interner.contract(c))
        .collect();
    let mut named_contracts: Vec<(&String, &Contract)> = cenv.iter().collect();
    named_contracts.sort_by_key(|(name, _)| *name);
    let named_contracts = NamedContractEnvironment(
        named_contracts
            .into_iter()
            .map(|(name, contract)| (name.clone(), interner.contract(contract.clone())))
            .collect(),
    );
    let named_contracts = interner.intern_enum(named_contracts);
    let input = args.iter().map(|c| interner.contract(c.clone())).collect();
    let claim = match claim {
        Claim::Safety => MemoClaim::Safety,
        Claim::Return(c) => MemoClaim::Return(interner.contract(c.clone())),
        Claim::Completes => MemoClaim::Completes,
    };
    Some(FactKey {
        shape: layer2.shape,
        captures,
        named_contracts,
        input,
        claim,
    })
}

/// What is known about `key`, if anything.
pub(crate) fn lookup(key: &FactKey) -> Option<Cached> {
    CACHE.with(|c| {
        c.borrow().get(key).map(|e| match e {
            None => Cached::InProgress,
            Some(v) => Cached::Settled(v.clone()),
        })
    })
}

/// Resolution by **coverage** [author, 2026-08-03]: a demanded fact is answered by any
/// settled **Proven** fact of the same instance, named-contract environment, and claim
/// whose input domain *contains* the demanded one — the subcontract test *is* the
/// resolution, in the same step; the exact-pointer hit is merely its trivial case.
/// Only `Proven` transfers down: a refutation's witness may lie outside the narrower
/// domain, and unproven says nothing about it.
pub(crate) fn covering(key: &FactKey, interner: &mut Interner) -> Option<BodySafety> {
    let candidates: Vec<Vec<Interned<Contract>>> = CACHE.with(|c| {
        c.borrow()
            .iter()
            .filter(|(k, v)| {
                k.shape == key.shape
                    && k.captures == key.captures
                    && k.named_contracts == key.named_contracts
                    && k.claim == key.claim
                    && k.input.len() == key.input.len()
                    && matches!(v, Some(BodySafety::Proven))
            })
            .map(|(k, _)| k.input.clone())
            .collect()
    });
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
pub(crate) fn begin(key: &FactKey) {
    CACHE.with(|c| c.borrow_mut().insert(key.clone(), None));
    DEPTH.with(|d| *d.borrow_mut() += 1);
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
pub(crate) fn finish(key: &FactKey, verdict: &BodySafety, tainted: bool) -> bool {
    let outer = DEPTH.with(|d| {
        let mut d = d.borrow_mut();
        *d -= 1;
        *d == 0
    }) && !tainted;
    CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if outer {
            c.insert(key.clone(), Some(verdict.clone()));
        } else {
            c.remove(key);
        }
    });
    outer
}

/// Publish another verdict settled by the same outermost graph pass. Dependency
/// components are facts too: retaining only the seed would force later completion/
/// return analysis to settle the graph again. The caller may use this only after
/// [`finish`] reports that no ambient hypotheses remain.
pub(crate) fn record_settled(key: FactKey, verdict: BodySafety) {
    CACHE.with(|c| c.borrow_mut().insert(key, Some(verdict)));
}

/// TEMPORARY probe: (settled entries, in-progress markers, depth).
/// Drop everything memoized, for test isolation or memory reclamation.
///
/// Correctness does not depend on this: a `FactKey` determines its verdict. That claim
/// used to be made here *and* be false one module over — `region`'s instance-table key
/// erased parameter spelling while its cached rows kept it, so one program's table
/// answered another's query. Keeping this note honest means the same discipline has to
/// hold for every memo: **if clearing can change an answer, the key is incomplete.**
#[allow(dead_code)]
pub(crate) fn clear() {
    CACHE.with(|c| c.borrow_mut().clear());
    DEPTH.with(|d| *d.borrow_mut() = 0);
    LAYER2.with(|m| m.borrow_mut().clear());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interner::Interner;
    use crate::oracle::run_source_in;

    fn f(src: &str, i: &mut Interner) -> ValueRef {
        run_source_in(src, i).unwrap().0
    }

    /// The property the key rests on: identical canonical code is **one allocation**, so
    /// shape identity is a pointer comparison. Without this the key would silently fall back
    /// to walking a syntax tree on every lookup, which is what it did before 2026-08-01.
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
    /// different *instances* — which is exactly why the key carries capture contracts
    /// alongside the code pointer.
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
mod layer2_tests {
    use super::*;
    use crate::oracle::run_source_in;

    /// The join's whole content: a mutual group's member keys come from the
    /// serialized group canonicalization, so they are **spelling- and
    /// interner-independent** — two α-variant spellings built in *separate*
    /// interners (where value-pointer collapse cannot apply) produce the same
    /// `ShapeKey::Group`; the two members of one group stay distinct; a lone
    /// function stays `Solo`.
    #[test]
    fn group_member_keys_are_spelling_and_interner_independent() {
        let mut a = Interner::new();
        let even_a = run_source_in(
            "isEven = (n) => n == 0 ? true : isOdd(n - 1)\n\
             isOdd = (n) => n == 0 ? false : isEven(n - 1)\n\
             isEven",
            &mut a,
        )
        .unwrap()
        .0;

        let mut b = Interner::new();
        let even_b = run_source_in(
            "even = (k) => k == 0 ? true : odd(k - 1)\n\
             odd = (k) => k == 0 ? false : even(k - 1)\n\
             even",
            &mut b,
        )
        .unwrap()
        .0;

        let la = layer2(&even_a).expect("a closure");
        let lb = layer2(&even_b).expect("a closure");
        assert!(matches!(la.shape, ShapeKey::Group(_)), "a mutual member");
        assert_eq!(
            la.shape, lb.shape,
            "the group serialization sees through spelling and interner"
        );

        // The sibling is a *different* member of the same group.
        let odd_a = {
            let closure = even_a.as_closure().unwrap();
            match closure.env.lookup("isOdd") {
                Some(crate::env::Binding::Value(v)) => v,
                other => panic!("isOdd must be captured: {other:?}"),
            }
        };
        let lodd = layer2(&odd_a).expect("a closure");
        assert!(matches!(lodd.shape, ShapeKey::Group(_)));
        assert_ne!(la.shape, lodd.shape, "two members, two keys");

        // A lone acyclic function keys by its per-lambda shape.
        let mut c = Interner::new();
        let solo = run_source_in("f = (n) => n + 1\nf", &mut c).unwrap().0;
        let ls = layer2(&solo).expect("a closure");
        assert!(matches!(ls.shape, ShapeKey::Solo(_)));
    }
}
