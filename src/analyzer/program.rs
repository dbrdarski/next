//! Program-level analysis entry — the missing top of the analyzer (plan T1.1).
//!
//! Every analyzer path below this point answers a question somebody asked. Until now
//! nobody asked: `main.rs` only ran the oracle, and the analyzer was reachable solely from
//! unit tests, which is how ~3000 lines got built without a consumer. This module is the
//! consumer.
//!
//! **The first demand origin is `where` (E11 / E-8).** An author-written signature is the
//! one contract that needs no guessing — its input domain is *declared*. So the program
//! pass verifies, for each `where`, that the named function is safe over the domain the
//! author declared: `BodySafe(instance, DeclaredInput)`, settled through
//! [`crate::analyzer::safety::prove`].
//!
//! **Analysis never evaluates the program.** The oracle's module runner evaluates items
//! eagerly in effect world; calling it here would execute the program at compile time.
//! Instead the pass builds *closures only* ([`make_closure_in`]) — which touches no body
//! and forces no binding — over a module environment assembled by walking the items once.
//! A binding whose value is not a lambda contributes no value, only (where it is a
//! contract expression) a named contract.
//!
//! **Scope — deliberately thin, per the plan's own note.** This pass verifies *safety*
//! over the declared input. It does **not** verify the declared **return** contract: that
//! is a demand (`does this body produce a value satisfying C?`), and the demand core
//! (C§13.1) does not exist yet. Rather than guess at it, the unverified return contract is
//! reported by [`ProgramVerdict::owed_return_checks`] — it is precisely the demand that
//! pulls T1.2, which is the order the plan prescribes.

use std::collections::HashMap;

use super::{Finding, Severity, demand, safety};
use crate::analyzer::TrapClass;
use crate::ast::{Bind, BindTarget, Expr, Item, Lambda, Module, Pat};
use crate::contract::{Contract, ContractEnv, Verdict, eval_contract};
use crate::env::{Binding, Env, Scope};
use crate::interner::Interner;
use crate::oracle::make_closure_in;
use crate::value::ValueRef;

/// The result of analyzing a whole module.
#[derive(Debug, Clone)]
pub struct ProgramVerdict {
    /// Every finding raised, in item order.
    pub findings: Vec<Finding>,
    /// Declared return contracts checked and **proven**, as `(name, contract)`. The
    /// record of what the demand core discharged, kept so a regression to "recorded but
    /// unchecked" is visible rather than silent.
    pub proven_returns: Vec<(String, Contract)>,
}

impl ProgramVerdict {
    /// A module is accepted when nothing was **refuted**. `Warning`s do not reject, and an
    /// `unproven` verdict surfaces as an `Error` finding per the 2026-07-31 severity
    /// ruling — safety-unproven is un-suppressible.
    pub fn accepted(&self) -> bool {
        !self.findings.iter().any(|f| f.severity == Severity::Error)
    }

    /// The rejecting findings only.
    pub fn errors(&self) -> impl Iterator<Item = &Finding> {
        self.findings.iter().filter(|f| f.severity == Severity::Error)
    }
}

/// Analyze a module: collect its function values and named contracts, then verify every
/// `where` as `BodySafe(instance, DeclaredInput)`.
pub fn analyze_program(module: &Module, interner: &mut Interner) -> ProgramVerdict {
    let scope = Scope::root();
    let (values, cenv) = collect(module, &scope, interner);

    let mut findings = Vec::new();
    let mut proven_returns = Vec::new();

    for item in &module.items {
        let Item::Where(w) = item else { continue };

        let Some(callee) = values.get(&w.name) else {
            findings.push(malformed(
                &w.name,
                "names no function binding in this module",
            ));
            continue;
        };
        let Some(declared) = eval_contract(&w.input_contract, &cenv, interner) else {
            findings.push(malformed(
                &w.name,
                "declares an input contract this pass cannot evaluate statically \
                 (C§12.2 computed contract arguments are owed)",
            ));
            continue;
        };

        let Some(args) = spread_input(callee, declared) else {
            findings.push(malformed(
                &w.name,
                "declares an input contract whose arity does not match the function's parameters",
            ));
            continue;
        };

        findings.extend(verdict_findings(
            &w.name,
            safety::prove(callee, &args, &cenv, interner),
        ));

        // The declared **return** contract is a demand (C§13.1): the `where` asks whether
        // the body produces a value satisfying it, adjudicated here, at the ask site.
        if let Some(ret) = eval_contract(&w.return_contract, &cenv, interner) {
            let asker = format!("where {}", w.name);
            match demand::returns(callee, &args, &ret, &asker, &cenv, interner) {
                Verdict::Proven => proven_returns.push((w.name.clone(), ret)),
                // Unproven rejects. A declared return the compiler cannot discharge is not
                // a declaration it may assume — the same discipline as safety-unproven
                // (late-resolution §5), and the reason the third voice is un-suppressible.
                Verdict::Unproven | Verdict::Refuted(_) => findings.push(malformed(
                    &w.name,
                    "declares a return contract that cannot be proven of its body",
                )),
            }
        }
    }

    ProgramVerdict { findings, proven_returns }
}

/// Walk the items once, building the module environment (function values, so that late
/// binding resolves a call to a sibling) and the named-contract environment.
///
/// Two passes over the items would let a `where` precede its function, and a named
/// contract precede its use — but `eval_contract` resolves a reference to an *already
/// evaluated* definition, so contracts stay single-pass and in order (recursive source
/// contracts are a separate increment, plan T2.4). Values get the two passes, since a
/// closure captures `scope` by reference and is order-independent.
fn collect(
    module: &Module,
    scope: &Env,
    interner: &mut Interner,
) -> (HashMap<String, ValueRef>, ContractEnv) {
    let mut values = HashMap::new();
    let mut cenv = ContractEnv::new();

    for item in &module.items {
        match item {
            Item::Bind(Bind {
                target: BindTarget::Name(name),
                value: Expr::Lambda(l),
                ..
            }) => {
                define(name, l, scope, &mut values, interner);
            }
            Item::ActBind(ab) => define(&ab.name, &ab.lambda, scope, &mut values, interner),
            // A non-lambda binding of a contract expression is a **named contract**
            // (`Percent = Range(0, 100)` — C§12.2). Anything else contributes no
            // analyzer-visible value: evaluating it is exactly what this pass must not do.
            Item::Bind(Bind {
                target: BindTarget::Name(name),
                value,
                ..
            }) => {
                if let Some(c) = eval_contract(value, &cenv, interner) {
                    cenv.insert(name.clone(), c);
                }
            }
            _ => {}
        }
    }
    (values, cenv)
}

fn define(
    name: &str,
    lambda: &Lambda,
    scope: &Env,
    values: &mut HashMap<String, ValueRef>,
    interner: &mut Interner,
) {
    let v = make_closure_in(lambda, scope, interner);
    scope.define(name, Binding::Value(v.clone()));
    values.insert(name.to_string(), v);
}

/// Map a declared input contract onto the function's parameters.
///
/// A single-parameter `where` declares that parameter's contract directly; a multi-element
/// one desugars to a tuple over the argument list (desugar `where_clause`), so its parts
/// map positionally. `None` on an arity mismatch — a real authoring error, not a shrug.
///
/// **One mismatch is undetectable here, by construction.** `where_clause` desugars a
/// multi-element list to `TupleCons`, which is the same shape a single tuple-valued
/// parameter produces — so on a one-parameter function, `where (Number, Number)` and
/// `where ((Number, Number))` are indistinguishable by the time this sees a `Contract`.
/// The reading taken is the legal one (the parameter is a 2-tuple). Distinguishing them
/// would need the element count preserved on `Where`, which is an AST change and not this
/// slice's business.
fn spread_input(callee: &ValueRef, declared: Contract) -> Option<Vec<Contract>> {
    let arity = match &callee.as_closure()?.lambda.params {
        Pat::Tuple(elems) => elems.len(),
        _ => 1,
    };
    match declared {
        _ if arity == 1 => Some(vec![declared]),
        Contract::Tuple(parts) if parts.len() == arity => {
            Some(parts.iter().map(|c| (**c).clone()).collect())
        }
        _ => None,
    }
}

/// Turn a settled safety fact into findings.
///
/// `Refuted` and `Unproven` both reject: late-resolution §5 makes safety-unproven a
/// compile error, un-suppressible — a `where` the compiler cannot discharge is not a
/// `where` it may assume. A voice that carries no finding of its own still rejects, with
/// the fact named, so the verdict is never silently empty.
fn verdict_findings(name: &str, v: safety::BodySafety) -> Vec<Finding> {
    let (voice, mut fs) = match v {
        safety::BodySafety::Proven => return Vec::new(),
        safety::BodySafety::Refuted(fs) => ("is refuted over", fs),
        safety::BodySafety::Unproven(fs) => ("cannot be proven over", fs),
    };
    if fs.is_empty() {
        fs.push(malformed(name, &format!("{voice} its declared input domain")));
    }
    fs
}

/// A `where` this pass cannot act on. `ArgumentObligation` is the closest existing class —
/// the declared input *is* the argument obligation — but no trap class names a malformed
/// signature, because a `where` is analyzer-facing metadata with no evaluation behavior
/// (AST `Where`), so it can never trap at runtime and the §6 concordance has no row for it.
// [ask-author] Should a malformed/undischargeable `where` (unknown name, arity mismatch,
// statically un-evaluable contract expression) carry its own diagnostic class rather than
// borrowing `ArgumentObligation`? These are authoring errors in the signature itself, not
// trap-class rejections, and the concordance has no row for them.
fn malformed(name: &str, why: &str) -> Finding {
    Finding {
        class: TrapClass::ArgumentObligation,
        severity: Severity::Error,
        message: format!("`where {name}` {why}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Through the shared front end (`check_source`), so these tests exercise the same
    /// lex/parse/desugar path the CLI does.
    fn check(src: &str) -> (ProgramVerdict, Interner) {
        crate::oracle::harness::check_source(src).expect("lexes, parses, desugars")
    }

    /// The point of the whole pass: an author declares a domain, the body traps somewhere
    /// inside it, and the module is rejected — with no call site anywhere in the program.
    /// Before this entry existed, nothing asked the question.
    #[test]
    fn a_where_whose_body_traps_over_its_declared_domain_is_rejected() {
        let (v, _) = check("f where (Number) => Number\nf = (n) => n + 1\ng where (String) => Number\ng = (s) => s + 1\n");
        assert!(!v.accepted(), "a String input to `+` must reject: {:?}", v.findings);
    }

    /// The complement — and the harder half. A declared domain that *does* discharge must
    /// be accepted, or the pass is just a rejector.
    #[test]
    fn a_where_whose_body_is_safe_over_its_declared_domain_is_accepted() {
        let (v, _) = check("f where (Number) => Number\nf = (n) => n + 1\n");
        assert!(v.accepted(), "a Number input to `+` discharges: {:?}", v.findings);
    }

    /// E-8's whole reason for existing: the declared domain is what makes recursion
    /// provable. `countDown` over `GE(0)` keeps `n - 1` inside the domain, so the fact
    /// closes by induction — no unfolding, no growth.
    #[test]
    fn a_declared_domain_lets_recursion_close_by_induction() {
        // Non-negative **integers**: `n - 1` stays inside the declared domain, so the
        // recursive call discharges against the assumed fact and the body is analyzed once.
        // Integrality surviving `−` is an operation-rulebook (F0) transfer — which is why
        // F0 had to be built before this could work.
        let (v, _) = check(
            "countDown where (Intersection(GreaterEq(0), Mod(1, 0))) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n",
        );
        assert!(v.accepted(), "declared-domain recursion proves by induction: {:?}", v.findings);
    }

    /// The same program over a domain **without** integrality must NOT prove — and this is
    /// the analyzer being right, not a gap to paper over. `GreaterEq(0)` admits `0.5`, which
    /// never satisfies `n == 0` and recurses to `-0.5`, outside the declared domain; no
    /// assumed fact covers that call. The honest verdict is unproven, which rejects.
    ///
    /// Pinned deliberately: making this accept would require growing the domain until it
    /// stabilized, which is the reverted reaching engine. If this test ever flips to
    /// accepted, check `tests/machinery_gate.rs` before believing it.
    #[test]
    fn a_declared_domain_that_omits_integrality_does_not_prove() {
        let (v, _) = check(
            "countDown where (GreaterEq(0)) => Number\n\
             countDown = (n) => n == 0 ? 0 : countDown(n - 1)\n",
        );
        assert!(!v.accepted(), "0.5 leaves the declared domain — unproven, not accepted");
    }

    /// A `where` naming nothing, and one whose arity disagrees with the function, are
    /// authoring errors — they must not pass silently just because there is no body to check.
    #[test]
    fn a_where_that_cannot_be_acted_on_rejects_rather_than_passing_silently() {
        let (v, _) = check("ghost where (Number) => Number\nf = (n) => n\n");
        assert!(!v.accepted(), "a `where` naming no binding rejects: {:?}", v.findings);

        // Detectable only in this direction — see `spread_input`: a *declared* tuple on a
        // one-parameter function is legal (that parameter may be a tuple), so the mismatch
        // that can be caught is a declaration too narrow for the parameter list.
        let (v, _) = check("f where (Number) => Number\nf = (a, b) => a + b\n");
        assert!(!v.accepted(), "an arity mismatch rejects: {:?}", v.findings);
    }

    /// Named contracts are ordinary bindings of contract expressions (C§12.2), so a `where`
    /// may name one — and the declared domain is then the *named* contract, not `Number`.
    #[test]
    fn a_where_may_declare_a_named_contract() {
        let (v, _) = check("Percent = Range(0, 100)\nf where (Percent) => Number\nf = (p) => p + 1\n");
        assert!(v.accepted(), "a named contract resolves as the declared domain: {:?}", v.findings);
    }

    /// A fact depends on every named contract its function body reads. Reusing one pure
    /// memo table is sound only when that dependency is part of the semantic key: changing
    /// `N` changes which arm is reachable even though the canonical function body, value
    /// captures, call input, and claim are otherwise identical.
    #[test]
    fn fact_memo_records_named_contract_dependencies() {
        const SAFE: &str = "N = String\n\
            f where (Number) => Number\n\
            f = (x) => x :: {\n\
             N => 1 + \"s\"\n\
             _ => 1\n\
            }\n";
        const UNSAFE: &str = "N = Number\n\
            f where (Number) => Number\n\
            f = (x) => x :: {\n\
             N => 1 + \"s\"\n\
             _ => 1\n\
            }\n";

        super::super::factcache::clear();
        let mut interner = Interner::new();
        let safe = crate::oracle::harness::check_source_in(SAFE, &mut interner)
            .expect("safe variant parses and checks");
        assert!(safe.accepted(), "String does not select the trapping arm: {safe:?}");
        let unsafe_variant = crate::oracle::harness::check_source_in(UNSAFE, &mut interner)
            .expect("unsafe variant parses and checks");
        assert!(
            !unsafe_variant.accepted(),
            "Number selects the trapping arm; a fact for N=String must not be reused: \
             {unsafe_variant:?}"
        );

        // The reverse order catches the symmetric stale-refutation failure mode too.
        super::super::factcache::clear();
        let mut interner = Interner::new();
        let unsafe_variant = crate::oracle::harness::check_source_in(UNSAFE, &mut interner)
            .expect("unsafe variant parses and checks");
        assert!(!unsafe_variant.accepted(), "the unsafe variant rejects from a cold memo");
        let safe = crate::oracle::harness::check_source_in(SAFE, &mut interner)
            .expect("safe variant parses and checks");
        assert!(
            safe.accepted(),
            "a refutation for N=Number must not be reused when N=String: {safe:?}"
        );
        super::super::factcache::clear();
    }

    /// The declared **return** contract is now checked (demand core, C§13.1). This test
    /// previously asserted the opposite — that the contract was recorded but unverified —
    /// and it is the flip that slice was written to produce.
    #[test]
    fn a_declared_return_contract_that_the_body_does_not_meet_rejects() {
        let (v, _) = check("f where (Number) => String\nf = (n) => n + 1\n");
        assert!(!v.accepted(), "`f` returns a Number where String is declared: {:?}", v.findings);
    }

    /// And the complement: a return contract the body does meet is proven and recorded.
    #[test]
    fn a_declared_return_contract_the_body_meets_is_proven() {
        let (v, _) = check("f where (Number) => Number\nf = (n) => n + 1\n");
        assert!(v.accepted(), "{:?}", v.findings);
        assert_eq!(v.proven_returns.len(), 1, "the discharge is recorded: {v:?}");
    }

    /// Analysis must not run the program. A module whose top level would trap on evaluation
    /// analyzes fine, because no binding is ever forced.
    #[test]
    fn analysis_does_not_evaluate_the_module() {
        let (v, _) = check("boom = 1 + \"x\"\nf where (Number) => Number\nf = (n) => n + 1\n");
        assert!(v.accepted(), "the un-forced trapping binding is not evaluated: {:?}", v.findings);
    }
}
