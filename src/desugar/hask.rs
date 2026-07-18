//! Hask lowering (E4 / §4): `# body` ⇒ a `Lambda` over the hole positions.
//!
//! Holes are collected on the fly while the body is desugared: entering a `#`
//! pushes a [`HaskScope`], each hole registers a synthetic parameter against the
//! top scope, and popping the scope builds the parameter pattern. A nested `#`
//! pushes its own scope, so inner holes belong to the inner hask (fresh
//! numbering — E4).
//!
//! v0.1 supports the common shapes: all-anon (`# f(_, _)`), all-indexed
//! (`# f(_1, _2)`), and a single rest (`#([..._1])`, `# f(_, ..._)`). Mixing
//! plain and indexed holes, or conflicting rests, returns a `DesugarError`
//! rather than guessing (see DECISIONS.md).

use std::collections::BTreeMap;

use crate::ast::*;
use crate::parse::surface::{Hole, SExpr};

use super::{Desugarer, DesugarError, err};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum RestKind {
    Anon,
    Indexed(u32),
}

/// The holes gathered for one `#` scope.
#[derive(Default)]
pub(super) struct HaskScope {
    /// Plain `_` params — each occurrence is distinct, in source order.
    anon: Vec<String>,
    /// Indexed `_n` params — repeats reuse the same parameter.
    indexed: BTreeMap<u32, String>,
    /// A single rest suffix (`..._` / `..._n`), with its generated name.
    rest: Option<(RestKind, String)>,
}

impl<'a> Desugarer<'a> {
    pub(super) fn hask(&mut self, body: &SExpr) -> Result<Expr, DesugarError> {
        self.hask_stack.push(HaskScope::default());
        let body_expr = self.expr(body)?;
        let scope = self.hask_stack.pop().expect("hask scope was pushed");
        let params = self.build_hask_params(scope)?;
        Ok(Expr::Lambda(Lambda { params, body: Box::new(body_expr), act_kind: ActKind::Pure }))
    }

    /// Register a non-rest hole, returning its parameter name.
    pub(super) fn register_hole(&mut self, h: &Hole) -> Result<String, DesugarError> {
        if self.hask_stack.is_empty() {
            return err("a hole `_`/`_n` is only legal inside a hask `#`");
        }
        match h {
            Hole::Anon => {
                let name = self.fresh("h");
                self.hask_stack.last_mut().unwrap().anon.push(name.clone());
                Ok(name)
            }
            Hole::Indexed(n) => {
                if let Some(existing) = self.hask_stack.last().unwrap().indexed.get(n) {
                    return Ok(existing.clone());
                }
                let name = self.fresh("h");
                self.hask_stack.last_mut().unwrap().indexed.insert(*n, name.clone());
                Ok(name)
            }
        }
    }

    /// Register a rest hole (from a `...<hole>` spread), returning its name.
    pub(super) fn register_rest_hole(&mut self, h: &Hole) -> Result<String, DesugarError> {
        if self.hask_stack.is_empty() {
            return err("a rest hole `..._`/`..._n` is only legal inside a hask `#`");
        }
        let kind = match h {
            Hole::Anon => RestKind::Anon,
            Hole::Indexed(n) => RestKind::Indexed(*n),
        };
        if let Some((existing_kind, name)) = &self.hask_stack.last().unwrap().rest {
            if *existing_kind == kind {
                return Ok(name.clone());
            }
            return err("a hask may have at most one distinct rest hole");
        }
        let name = self.fresh("hrest");
        self.hask_stack.last_mut().unwrap().rest = Some((kind, name.clone()));
        Ok(name)
    }

    fn build_hask_params(&mut self, scope: HaskScope) -> Result<Pat, DesugarError> {
        let HaskScope { anon, indexed, rest } = scope;
        if !anon.is_empty() && !indexed.is_empty() {
            return err("mixing plain `_` and indexed `_n` holes is not supported (v0.1)");
        }

        let mut elems: Vec<PatElem> = Vec::new();
        if !indexed.is_empty() {
            let max = *indexed.keys().max().unwrap();
            for i in 1..=max {
                match indexed.get(&i) {
                    Some(name) => elems.push(PatElem::Pat(Pat::Bind(name.clone()))),
                    None => {
                        // Keep the tuple dense (indexes must be dense — E4).
                        let filler = self.fresh("h");
                        elems.push(PatElem::Pat(Pat::Bind(filler)));
                    }
                }
            }
        } else {
            for name in anon {
                elems.push(PatElem::Pat(Pat::Bind(name)));
            }
        }

        if let Some((kind, name)) = rest {
            if let RestKind::Indexed(n) = kind {
                let need = n.saturating_sub(1) as usize; // fixed params before position n
                if elems.len() > need {
                    return err("a rest hole's position conflicts with the fixed holes");
                }
                while elems.len() < need {
                    let filler = self.fresh("h");
                    elems.push(PatElem::Pat(Pat::Bind(filler)));
                }
            }
            elems.push(PatElem::Rest(Some(name)));
        }

        Ok(Pat::Tuple(elems))
    }
}
