//! Return induction — §6, the joint vector pass (the induction step).
//!
//! A **return candidate** claims that a function, applied over an argument domain,
//! returns values in a contract `C`. The induction: **assume** every candidate in a
//! recursive component (SCC) returns its claimed `C`, then verify that each member's
//! body actually produces a subcontract of its `C`. If every member verifies, the
//! component closes — the returns are proven; a **vector failure** (any member
//! unproven) leaves the whole component unproven (per-compilation, §6).
//!
//! The hypotheses are installed as a **dynamic-scope** table that `analyze_apply`
//! consults: a recursive/mutual call whose callee shape is under an active hypothesis
//! returns the assumed contract instead of the coarse `Top` (step 3's fallback). This
//! is what turns `f = (n) => n == 0 ? 1 : n * f(n-1)`'s coarse `Union(Equals(0), Top)`
//! into a proof that `f` returns `Number` under the hypothesis `f: Number`.
//!
//! This module lands three layers. **The joint vector pass** ([`joint_vector_pass`])
//! settles one component. **The multi-SCC driver** ([`prove_facts`]) decomposes the
//! candidates' call graph into strongly-connected components, processes them in
//! **reverse-topological order** (dependencies first), and carries each proven
//! component's return facts as hypotheses for its dependents — so a dependent proves
//! what it could not alone. **Return-fact inference** ([`infer_return_fact`]) closes
//! the loop autonomously: from a callee it reaches the call graph, *proposes* a return
//! claim per function (base-generalization, [`Contract::generalize`]), and runs the
//! driver — so the claim need not be supplied. AP-30's `ProvenPresent` half, the
//! realized-witness refutation, and the `analyze_apply` rewiring onto `infer_return_fact`
//! are the wiring that follows.

use std::cell::{Cell, RefCell};

use crate::analyzer::bodywalk::{callee_targets, reachable_closures};
use crate::analyzer::obligation::accepted_domain;
use crate::analyzer::outcome::summarize_instance;
use crate::contract::{Contract, ContractEnv, Verdict, subcontract};
use crate::interner::Interner;
use crate::value::ValueRef;

thread_local! {
    /// Dynamic-scope return-induction hypotheses, consulted by `analyze_apply` during a
    /// vector pass. A `Vec` (linear lookup) — components are small.
    static HYPOTHESES: RefCell<Vec<Hypothesis>> = const { RefCell::new(Vec::new()) };

    /// Set while an [`infer_return_fact`] run is in progress — the **re-entrancy
    /// guard**. A driver pass analyzes bodies, whose calls reach `analyze_apply` again;
    /// this flag stops that inner `analyze_apply` from launching a *nested* inference
    /// (its calls resolve through the pass's hypotheses or coarse `Top` instead), so one
    /// call site drives exactly one bounded inference.
    static INFERRING: Cell<bool> = const { Cell::new(false) };

}

/// Whether a return-fact inference is currently running (the re-entrancy guard).
/// `analyze_apply` consults this before launching one.
pub(crate) fn currently_inferring() -> bool {
    INFERRING.with(Cell::get)
}

/// Run `body` with the inference guard set (save/restore, so it composes). Used by
/// [`summarize_instance`] so **all body analysis during fact-proving stays coarse** —
/// its calls resolve through the pass's hypotheses or coarse `Top`, never a nested
/// inference. Inference thereby fires only at genuine top-level `analyze` call sites,
/// not inside the machinery that inference itself drives.
pub(crate) fn without_inference<R>(body: impl FnOnce() -> R) -> R {
    let saved = INFERRING.with(|f| f.replace(true));
    let out = body();
    INFERRING.with(|f| f.set(saved));
    out
}

/// An active return-induction hypothesis (§6 / C§13.2), keyed by the **concrete
/// instance** (`callee` — a closure value, which carries its captured environment) and
/// the **input domain** (`input`) it is assumed over. Shape alone never suffices: two
/// closures of one shape with different captures (`make(1)` vs `make("s")`) hold
/// distinct facts, and a fact proved over one domain must not be reused on a wider one.
/// This is the interim of the spec's `(shape, annotated env, input domain)` key —
/// instance identity subsumes shape+env, `input` is I.
#[derive(Clone)]
pub(crate) struct Hypothesis {
    pub(crate) callee: ValueRef,
    pub(crate) input: Vec<Contract>,
    pub(crate) claim: Claim,
}

/// The assumed return contract for a call to `callee` over `args`, if a live hypothesis
/// applies: **the same instance** (`hyp.callee == callee`) **and** the call's argument
/// domain **contained in** the fact's input domain (`args ⊑ hyp.input`). Consulted by
/// the analyzer's application rule for recursive/mutual calls — the aliasing guard the
/// v0.8.1 domain-indexed-fact rule requires.
pub(crate) fn hypothesis_for(callee: &ValueRef, args: &[Contract], interner: &mut Interner) -> Option<Contract> {
    // Collect the same-instance hypotheses first (dropping the borrow before the
    // subcontract check, which may itself want the interner but never HYPOTHESES).
    let same_instance: Vec<Hypothesis> = HYPOTHESES.with(|h| {
        h.borrow()
            .iter()
            .filter(|hyp| hyp.callee == *callee && matches!(hyp.claim, Claim::Return(_)))
            .cloned()
            .collect()
    });
    same_instance.into_iter().find(|hyp| args_within(args, &hyp.input, interner)).and_then(|hyp| {
        match hyp.claim {
            Claim::Return(c) => Some(c),
            Claim::Safety | Claim::Completes => None,
        }
    })
}

/// Whether an assumed **completion** fact covers a call — the same instance and
/// `args ⊑ I`. A cycle assumption may only claim production when a fact *for that
/// call's own domain* says so; this replaces `BodySummary::cycle()`'s unconditional
/// `Produces`, which asserted rather than settled it.
pub(crate) fn completes_assumed(callee: &ValueRef, args: &[Contract], interner: &mut Interner) -> bool {
    let domains: Vec<Vec<Contract>> = HYPOTHESES.with(|h| {
        h.borrow()
            .iter()
            .filter(|hyp| hyp.callee == *callee && matches!(hyp.claim, Claim::Completes))
            .map(|hyp| hyp.input.clone())
            .collect()
    });
    domains.into_iter().any(|input| args_within(args, &input, interner))
}

/// Whether an assumed **safety** fact discharges a call to `callee` over `args` — the
/// same instance and `args ⊑ I`. This is what lets a recursive reference resolve through
/// a fact instead of re-entering the body (C§13.2), and it reads the **same** hypothesis
/// table the return facts use.
pub(crate) fn safety_assumed(callee: &ValueRef, args: &[Contract], interner: &mut Interner) -> bool {
    let domains: Vec<Vec<Contract>> = HYPOTHESES.with(|h| {
        h.borrow()
            .iter()
            .filter(|hyp| hyp.callee == *callee && matches!(hyp.claim, Claim::Safety))
            .map(|hyp| hyp.input.clone())
            .collect()
    });
    domains
        .into_iter()
        .any(|input| args_within(args, &input, interner))
}

/// Whether a call's argument domain `args` is contained in a fact's `domain` — the
/// per-tuple subcontract `Tuple(args) ⊑ Tuple(domain)`.
fn args_within(args: &[Contract], domain: &[Contract], interner: &mut Interner) -> bool {
    let call = Contract::tuple(args.to_vec(), interner);
    let dom = Contract::tuple(domain.to_vec(), interner);
    matches!(subcontract(&call, &dom, interner), Verdict::Proven)
}

/// Run `body` with `hyps` installed as the active hypotheses, restoring the previous
/// table afterward (so nested/stacked passes compose). `pub(crate)` so the analyzer
/// suite can lock the lookup law directly.
pub(crate) fn with_hypotheses<R>(hyps: Vec<Hypothesis>, body: impl FnOnce() -> R) -> R {
    let saved = HYPOTHESES.with(|h| std::mem::replace(&mut *h.borrow_mut(), hyps));
    let out = body();
    HYPOTHESES.with(|h| *h.borrow_mut() = saved);
    out
}

/// Whether a safety-component verification is currently in progress. During that
/// pass, a call not covered by an installed safety fact is an unresolved graph
/// dependency (for example a shape-cutoff node); recursively launching the legacy
/// body summary would silently bypass the graph's `Unproven` verdict.
pub(crate) fn safety_context_active() -> bool {
    HYPOTHESES.with(|h| h.borrow().iter().any(|hyp| matches!(hyp.claim, Claim::Safety)))
}

/// A return candidate: the closure `callee`, applied over arguments described by
/// `args`, claimed to return values in `contract`.
#[derive(Clone)]
pub struct Candidate {
    pub callee: ValueRef,
    pub args: Vec<Contract>,
    pub claim: Claim,
    /// C§13.3(2)'s instance-chain cutoff: this candidate's shape already appeared on the
    /// discovery path, so it was not expanded. It resolves as the ladder's **(c) rung**
    /// — unproven — and never acquires an invented covering domain.
    pub cutoff: bool,
}

/// What a fact node claims. C§13.2a's node is `(instance, row-set I, demanded C)`; a
/// **safety** fact is the kind with no demanded `C`. Both kinds live in **one** graph
/// because dependency cycles cross them — *"the graph and its SCC collapse are global."*
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Claim {
    /// `BodySafe(instance, I)` — every operation the body reaches over `I` discharges.
    Safety,
    /// `ReturnFact(instance, I, C)` — the return is contained in `C`.
    Return(Contract),
    /// **Completion** (E10 / C§13.4's *"produced + completion evidence"*): every path
    /// through the body over `I` produces a value. Settled inductively like the others —
    /// a recursive call resolves through the assumed fact **for its own domain**, which
    /// is exactly why `f = (x) => x :: { 0 => f(1) }` cannot prove it: `f(1)` is a
    /// *different* node, and under `Equals(1)` no arm matches.
    Completes,
}

/// One **joint vector pass** over a recursive component (§6). Installs every member's
/// claim as a hypothesis, then verifies each member's body produces a subcontract of
/// its claimed contract. Returns `true` iff **all** members verify — a vector failure
/// leaves the whole component unproven.
pub fn joint_vector_pass(members: &[Candidate], cenv: &ContractEnv, interner: &mut Interner) -> bool {
    run_pass(&[], members, cenv, interner)
}

/// A vector pass over `members` with `base` hypotheses already in force — the return
/// facts of dependency components the driver has already settled (§6). Installs `base`
/// plus every member's own claim, then verifies each member's body produces a
/// subcontract of its claimed contract. `true` iff **all** members verify.
fn run_pass(base: &[Hypothesis], members: &[Candidate], cenv: &ContractEnv, interner: &mut Interner) -> bool {
    let mut hyps = base.to_vec();
    hyps.extend(member_hypotheses(members));

    members.iter().all(|c| {
        if c.cutoff {
            return false; // ladder rung (c) — not expanded, so never proven
        }
        let hyps = hyps.clone();
        match &c.claim {
            // A return claim holds when the body's produced contract is contained in it.
            Claim::Return(want) => {
                // Evaluated by the §5 partition (C§13.2's region-table walk), falling back
                // to the whole-body summary where the partition does not apply. Analyzing
                // the body whole loses each row's narrowing, which is exactly what a
                // recursive return claim needs to stay inside its declared domain.
                let produced = with_hypotheses(hyps, || {
                    crate::analyzer::safety::produced_by_partition(
                        &c.callee, &c.args, cenv, interner,
                    )
                    .or_else(|| {
                        summarize_instance(&c.callee, &c.args, cenv, interner)
                            .map(|o| o.produced.erase(interner))
                    })
                });
                match produced {
                    Some(p) => matches!(subcontract(&p, want, interner), Verdict::Proven),
                    None => false,
                }
            }
            // A safety claim holds when the body raises no finding over `I` — verified by
            // the partition rule (each region-table row under `I ∩ row.region`).
            Claim::Safety => {
                with_hypotheses(hyps, || crate::analyzer::safety::verify(&c.callee, &c.args, cenv, interner))
                    .is_empty()
            }
            Claim::Completes => {
                with_hypotheses(hyps, || {
                    crate::analyzer::safety::verify_completes(&c.callee, &c.args, cenv, interner)
                })
            }
        }
    })
}

/// Each member's claim as an instance-and-domain-keyed hypothesis ([`hypothesis_for`]'s
/// form): the concrete callee, the input domain the claim is over (`c.args`), and the
/// claimed return.
fn member_hypotheses(members: &[Candidate]) -> Vec<Hypothesis> {
    members
        .iter()
        .map(|c| Hypothesis { callee: c.callee.clone(), input: c.args.clone(), claim: c.claim.clone() })
        .collect()
}

/// The outcome of the multi-SCC driver: the candidates partitioned into those whose
/// component **closed** (proven, per-compilation) and those a vector failure left
/// **unproven**. A component's members share their fate (§6), so the partition is by
/// component even though it is flattened here.
#[derive(Clone)]
pub struct FactResult {
    pub proven: Vec<Candidate>,
    pub unproven: Vec<Candidate>,
}

/// The **multi-SCC driver** (§6 / C§13.2a). Decomposes the candidates' call graph into
/// strongly-connected components, processes them in **reverse-topological order**
/// (dependencies first), and carries each proven component's return facts as
/// hypotheses for its dependents. A self- or mutually-recursive nest is one component
/// settled by a joint vector pass; a non-recursive candidate is a singleton component
/// whose body sees the already-proven facts of everything it calls.
///
/// This is what lets a dependent prove what it cannot alone: `quad = (n) => double(n)
/// + double(n)` returns `Number` **only** once `double : Number` is a fact — the
/// reverse-topological order guarantees `double` is settled first, so its fact is in
/// force when `quad`'s body is summarized.
///
/// Edges are the **direct** calls among candidate closures ([`callee_targets`]); an
/// indirect dependency through a non-candidate helper is not an edge, so that helper's
/// call coarsens to `Top` — sound (the dependent lands unproven), never a false proof.
/// The result is order-independent: SCC membership and the condensation order depend
/// on the call graph alone, not the candidate-list order.
pub fn prove_facts(candidates: Vec<Candidate>, cenv: &ContractEnv, interner: &mut Interner) -> FactResult {
    let adj = call_edges(&candidates);
    settle_components(candidates, &adj, cenv, interner)
}

/// The settlement half of the driver, over **caller-supplied edges** — so a discovery
/// pass that knows its own domain-specific edges (the safety graph) reuses this one
/// driver instead of running a second SCC of its own. C§13.2a's graph is *global*; this
/// is the single place components are settled.
pub fn settle_components(
    candidates: Vec<Candidate>,
    adj: &[Vec<usize>],
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> FactResult {
    let components = scc_reverse_topo(adj);

    let mut settled: Vec<Hypothesis> = Vec::new();
    let mut proven = Vec::new();
    let mut unproven = Vec::new();
    for comp in components {
        let members: Vec<Candidate> = comp.iter().map(|&i| candidates[i].clone()).collect();
        if run_pass(&settled, &members, cenv, interner) {
            settled.extend(member_hypotheses(&members));
            proven.extend(members);
        } else {
            unproven.extend(members);
        }
    }
    FactResult { proven, unproven }
}

/// **Infer** a callee's return fact autonomously (§6, the demand-free entry). Reaches
/// the whole call graph from `callee`, **proposes** a return claim per function, runs
/// the multi-SCC driver over those candidates, and returns the callee's proven return
/// contract — `None` if nothing informative is proven (→ the coarse `Top` at the call
/// site, sound).
///
/// The claim is proposed by [`Contract::generalize`] applied to each function's body
/// summary with **the whole reachable group pinned to `Bottom`** — so a mutual/identity
/// recursive tail call drops out of the base union (`even`'s `odd(n−1)` → `Bottom`,
/// leaving the base `true` → `Boolean`), while an arithmetic use still types
/// (`factorial`'s `n * f(n−1)` → `Number`, since `*` outputs `Number` and `Bottom` is
/// absorbed). The proposal is **never trusted**: the driver re-verifies `F(C) ⊑ C`
/// over real hypotheses, so a too-tight or too-loose proposal simply fails or lands
/// coarse — never a false proof.
///
/// **`root_args`** are the root callee's argument contracts — the **call-site**
/// domain: `Some([Number])` for `factorial(k)` with `k : Number` sharpens the fact to
/// pure `Number`; `None` proposes over the root's
/// accepted domain too (the autonomous, call-site-independent form). The reachable
/// helpers/mutual members always use their accepted domains.
///
/// **Scope of this cut.** A function whose only base contribution is a **non-recursive
/// helper call** proposes `Top`/`Bottom` (the helper is Bottom-pinned too) and so
/// yields no fact — a precision gap, sound; the reverse-topological *proposal* that
/// would close it is owed. There is no persistent cache yet: one call site drives one
/// bounded inference (the C§13.4 evaluation cache is owed).
pub fn infer_return_fact(
    callee: &ValueRef,
    root_args: Option<&[Contract]>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Contract> {
    if currently_inferring() {
        return None; // re-entrancy guard — a driver pass never nests inference
    }
    without_inference(|| infer_inner(callee, root_args, cenv, interner))
}

fn infer_inner(
    callee: &ValueRef,
    root_args: Option<&[Contract]>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Contract> {
    let with_args = group_domains(callee, root_args, cenv, interner);

    // Bottom-pin the whole group over their own domains, so a mutual/identity recursive
    // tail call (in-domain) drops out of the base union. The instance+domain key means
    // an out-of-domain recursive call is *not* pinned — it coarsens to `Top`, and the
    // proposal then yields no informative claim (sound).
    let bottoms: Vec<Hypothesis> = with_args
        .iter()
        .map(|(g, args)| Hypothesis {
            callee: g.clone(),
            input: args.clone(),
            claim: Claim::Return(Contract::Bottom),
        })
        .collect();

    let candidates: Vec<Candidate> = with_args
        .iter()
        .filter_map(|(f, args)| {
            let produced = with_hypotheses(bottoms.clone(), || {
                summarize_instance(f, args, cenv, interner)
            })?
            .produced
            .erase(interner);
            let claim = produced.generalize(interner);
            // Top proves trivially (no information); Bottom claims no value (a baseless
            // recursion) — neither is an informative fact.
            if matches!(claim, Contract::Top | Contract::Bottom) {
                return None;
            }
            Some(Candidate {
                callee: f.clone(),
                args: args.clone(),
                claim: Claim::Return(claim),
                cutoff: false,
            })
        })
        .collect();

    let result = prove_facts(candidates, cenv, interner);
    result
        .proven
        .iter()
        .find(|c| c.callee == *callee)
        .and_then(|c| match &c.claim {
            Claim::Return(x) => Some(x.clone()),
            Claim::Safety | Claim::Completes => None,
        })
}

/// A callee's accepted input domain as per-position argument contracts, or `None` when
/// no sound domain is derivable (a rest parameter — §4 owed — or a non-tuple domain).
fn domain_args(
    callee: &ValueRef,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Option<Vec<Contract>> {
    match accepted_domain(callee, cenv, interner)? {
        Contract::Tuple(parts) => Some(parts.iter().map(|c| (**c).clone()).collect()),
        _ => None,
    }
}

/// Every function reachable from `callee` paired with the domain it is analyzed over.
/// The root takes the call-site domain (`root_args` when supplied); so do **same-arity
/// partners**, so a mutual group is analyzed over one consistent domain (else a partner
/// over its wider accepted domain feeds the root wider-domain
/// args that the domain-indexed hypothesis then declines — the [interim] same-arity
/// propagation, to be replaced by call-edge-derived domains, v0.8.1 §5). A function with
/// no sound domain (a rest param) drops out — a call to it coarsens to `Top`, sound.
fn group_domains(
    callee: &ValueRef,
    root_args: Option<&[Contract]>,
    cenv: &ContractEnv,
    interner: &mut Interner,
) -> Vec<(ValueRef, Vec<Contract>)> {
    let mut out = Vec::new();
    for g in reachable_closures(callee.clone()).iter() {
        let args = match root_args {
            Some(a) if g == callee => a.to_vec(),
            Some(a) => match domain_args(g, cenv, interner) {
                Some(dom) if dom.len() == a.len() => a.to_vec(),
                Some(dom) => dom,
                None => continue,
            },
            None => match domain_args(g, cenv, interner) {
                Some(dom) => dom,
                None => continue,
            },
        };
        out.push((g.clone(), args));
    }
    out
}

/// Whether `cv` participates in a call cycle (is recursive/mutual) — a back-edge to `cv`
/// exists somewhere in its reachable call graph. A recursive return needs the induction
/// (`call_return`); a non-recursive return is its body's exact contract.
pub fn is_recursive(cv: &ValueRef) -> bool {
    reachable_closures(cv.clone())
        .iter()
        .any(|g| callee_targets(g).contains(cv))
}

/// The direct-call adjacency among candidates: `i → j` iff candidate `j`'s closure is
/// a direct callee of candidate `i`'s body. `i → j` means fact `i` depends on fact `j`
/// (C§13.2a's edge orientation), so the driver settles `j` first.
fn call_edges(candidates: &[Candidate]) -> Vec<Vec<usize>> {
    candidates
        .iter()
        .map(|c| {
            let targets = callee_targets(&c.callee);
            (0..candidates.len())
                .filter(|&j| targets.contains(&candidates[j].callee))
                .collect()
        })
        .collect()
}

/// Tarjan's SCC over the adjacency list, returning components in **reverse
/// topological order** — a component is emitted before every component that depends on
/// it (dependencies first), exactly the driver's processing order. The emission order
/// is a property of the graph, not of the traversal, so the driver is
/// order-independent.
pub(crate) fn scc_reverse_topo(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct Tarjan<'a> {
        adj: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        counter: usize,
        comps: Vec<Vec<usize>>,
    }
    impl Tarjan<'_> {
        fn connect(&mut self, v: usize) {
            self.index[v] = Some(self.counter);
            self.low[v] = self.counter;
            self.counter += 1;
            self.stack.push(v);
            self.on_stack[v] = true;

            for w in self.adj[v].clone() {
                match self.index[w] {
                    None => {
                        self.connect(w);
                        self.low[v] = self.low[v].min(self.low[w]);
                    }
                    Some(iw) if self.on_stack[w] => self.low[v] = self.low[v].min(iw),
                    Some(_) => {}
                }
            }

            // A component root: pop the stack down to `v`.
            if self.low[v] == self.index[v].unwrap() {
                let mut comp = Vec::new();
                loop {
                    let w = self.stack.pop().unwrap();
                    self.on_stack[w] = false;
                    comp.push(w);
                    if w == v {
                        break;
                    }
                }
                self.comps.push(comp);
            }
        }
    }

    let n = adj.len();
    let mut t = Tarjan {
        adj,
        index: vec![None; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        counter: 0,
        comps: Vec::new(),
    };
    for v in 0..n {
        if t.index[v].is_none() {
            t.connect(v);
        }
    }
    t.comps
}
