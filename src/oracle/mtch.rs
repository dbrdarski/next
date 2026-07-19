//! `Match` — the sole control node (Semantics Companion §3) — and pattern
//! matching. Items run in order; an `Arm` tests (pattern against scrutinee, then
//! guard as a strict tested seat) and on success **exits** the node with its
//! result. Items exhausted with no exit ⇒ `CompletedWithoutValue`.

use super::*;
use crate::value::RecordEntry;

impl<'a> Oracle<'a> {
    pub(super) fn eval_match(&mut self, m: &Match, env: &Env, world: World) -> EvalResult {
        let scrutinee = match &m.scrutinee {
            Some(e) => Some(self.eval_value(e, env, world)?),
            None => None,
        };

        // Binds and statements accumulate in a shared frame; each arm tests in a
        // child of it so its bindings are dropped on a miss.
        let body_env = Scope::child(env);
        for item in &m.items {
            match item {
                MatchItem::Bind(b) => self.eval_bind(b, &body_env, world)?,
                MatchItem::Stmt(e) => {
                    self.eval(e, &body_env, world)?; // value discarded (goes-nowhere)
                }
                MatchItem::Arm(arm) => {
                    let arm_env = Scope::child(&body_env);
                    if let Some(pat) = &arm.pattern {
                        let scrut = match &scrutinee {
                            Some(s) => s,
                            None => {
                                return Self::trap(
                                    TrapClass::OperationSafety,
                                    "an arm has a pattern but the match has no scrutinee",
                                );
                            }
                        };
                        if !self.match_pattern(pat, scrut, &arm_env)? {
                            continue;
                        }
                    }
                    if let Some(guard) = &arm.guard {
                        let g = self.eval_value(guard, &arm_env, world)?;
                        match g.as_boolean() {
                            Some(true) => {}
                            Some(false) => continue,
                            None => {
                                return Self::trap(
                                    TrapClass::TestedSeat,
                                    "a guard must be a strict Boolean",
                                );
                            }
                        }
                    }
                    // The arm exits the node with its result's outcome.
                    return self.eval(&arm.result, &arm_env, world);
                }
            }
        }
        Ok(Outcome::CompletedWithoutValue)
    }

    /// Match `value` against `pat`, defining any bindings into `scope`. Returns
    /// whether it matched. A no-match leaves partial bindings in `scope`, which is
    /// harmless because callers use a fresh throwaway scope per attempt.
    pub(super) fn match_pattern(&mut self, pat: &Pat, value: &ValueRef, scope: &Env) -> Result<bool, Trap> {
        match pat {
            Pat::Const(v) => Ok(value.ptr_eq(v)),
            Pat::Wild => Ok(true),
            Pat::Bind(name) => {
                scope.define(name, Binding::Value(value.clone()));
                Ok(true)
            }
            Pat::Tuple(elems) => self.match_tuple(elems, value, scope),
            Pat::Record { fields, exact } => self.match_record(fields, *exact, value, scope),
            Pat::Contract(r) => self.match_contract(r, value),
        }
    }

    fn match_tuple(&mut self, elems: &[PatElem], value: &ValueRef, scope: &Env) -> Result<bool, Trap> {
        let Some(items) = value.as_tuple() else { return Ok(false) };
        let items = items.to_vec(); // detach from `value` so we can borrow self

        let rest_pos = elems.iter().position(|e| matches!(e, PatElem::Rest(_)));
        match rest_pos {
            None => {
                if items.len() != elems.len() {
                    return Ok(false);
                }
                for (pe, item) in elems.iter().zip(&items) {
                    let PatElem::Pat(p) = pe else { unreachable!() };
                    if !self.match_pattern(p, item, scope)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Some(r) => {
                let before = &elems[..r];
                let after = &elems[r + 1..];
                if items.len() < before.len() + after.len() {
                    return Ok(false);
                }
                for (pe, item) in before.iter().zip(&items[..before.len()]) {
                    let PatElem::Pat(p) = pe else { return Ok(false) };
                    if !self.match_pattern(p, item, scope)? {
                        return Ok(false);
                    }
                }
                let back_start = items.len() - after.len();
                for (pe, item) in after.iter().zip(&items[back_start..]) {
                    let PatElem::Pat(p) = pe else { return Ok(false) };
                    if !self.match_pattern(p, item, scope)? {
                        return Ok(false);
                    }
                }
                if let PatElem::Rest(Some(name)) = &elems[r] {
                    let mid = items[before.len()..back_start].to_vec();
                    let captured = self.interner.tuple(mid);
                    scope.define(name, Binding::Value(captured));
                }
                Ok(true)
            }
        }
    }

    fn match_record(
        &mut self,
        fields: &[PatField],
        exact: bool,
        value: &ValueRef,
        scope: &Env,
    ) -> Result<bool, Trap> {
        let Some(entries) = value.as_record() else { return Ok(false) };
        let entries: Vec<RecordEntry> = entries.to_vec();

        let mut matched_keys: Vec<Vec<u16>> = Vec::new();
        let mut rest: Option<&Option<String>> = None;
        for f in fields {
            match f {
                PatField::Field { key, pat } => {
                    let ku: Vec<u16> = key.encode_utf16().collect();
                    let Some(entry) = entries.iter().find(|e| e.key == ku) else {
                        return Ok(false); // absent field ⇒ no match
                    };
                    let entry_value = entry.value.clone();
                    if !self.match_pattern(pat, &entry_value, scope)? {
                        return Ok(false);
                    }
                    matched_keys.push(ku);
                }
                PatField::Rest(name) => rest = Some(name),
            }
        }

        let extras: Vec<&RecordEntry> = entries.iter().filter(|e| !matched_keys.contains(&e.key)).collect();
        if rest.is_none() && exact && !extras.is_empty() {
            return Ok(false); // exact pattern with unaccounted keys
        }
        if let Some(Some(name)) = rest {
            let pairs: Vec<(Vec<u16>, ValueRef)> =
                extras.iter().map(|e| (e.key.clone(), e.value.clone())).collect();
            let captured = self.interner.record(pairs);
            scope.define(name, Binding::Value(captured));
        }
        Ok(true)
    }

    /// A contract-as-pattern: the runtime-decidable Kind and Indeterminate checks
    /// (E9). User-defined contracts need the contract engine (analyzer phase) and
    /// are not yet evaluable here.
    fn match_contract(&mut self, r: &Ref, value: &ValueRef) -> Result<bool, Trap> {
        let Ref::Immutable(BindingRef::Name(name)) = r else {
            return Self::trap(TrapClass::OperationSafety, "unsupported contract reference in a pattern");
        };
        let matched = match name.as_str() {
            "Number" => value.as_number().is_some(),
            "String" => value.as_str_units().is_some(),
            "Boolean" => value.as_boolean().is_some(),
            "Null" => value.is_null(),
            "Tuple" => value.as_tuple().is_some(),
            "Record" => value.as_record().is_some(),
            "Function" => value.as_closure().is_some(),
            "Indeterminate" => value.as_indeterminate().is_some(),
            // The one prelude Failure shape (B6): a Record carrying `path` and
            // `reason`. Failure discharge dissolves into contract-as-pattern (E9).
            "Failure" => value.as_record().is_some_and(|entries| {
                let has = |k: &str| {
                    let ku: Vec<u16> = k.encode_utf16().collect();
                    entries.iter().any(|e| e.key == ku)
                };
                has("path") && has("reason")
            }),
            other => {
                return Self::trap(
                    TrapClass::OperationSafety,
                    format!("user-defined contract pattern `{other}` needs the contract engine (v0.1)"),
                );
            }
        };
        Ok(matched)
    }
}
