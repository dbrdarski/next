//! The oracle interpreter (Semantics Companion v0.1, §3).
//!
//! The **truth source**: it evaluates kernel AST exactly per the companion, with
//! no contract/analysis code (Part I: interpreter before analyzer). Situations
//! the analyzer must later prove absent manifest here as **oracle traps** — an
//! immediate halt that is *not a value, not a Failure, not catchable* (§6). Each
//! trap class maps one-to-one to a compile-error class, so "accepted programs
//! never trap" becomes the executable soundness claim.
//!
//! This module currently covers the pure fragment: constants, references (late
//! binding), primitive operations (exact rationals, total division via
//! Indeterminate), construction, access, templates, `Match` (the sole control
//! node), and pure application. Worlds, mutator staging, and effects arrive next
//! (build-order step 3c).

use std::collections::HashMap;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use unicode_segmentation::UnicodeSegmentation;

use crate::ast::*;
use crate::env::{Binding, Env, Scope, SlotId};
use crate::interner::Interner;
use crate::rational::Rational;
use crate::value::{Closure, FnValue, IndetForm, ValueData, ValueRef};

mod canon;
mod equal;
mod eval;
pub mod harness;
mod mtch;
mod mu;
mod poly;
#[cfg(test)]
mod tests;

pub use equal::values_equal;
pub use eval::{eval_expr, eval_prim, run_program_commits, run_program_value};
pub use harness::{HostIo, RunError, run_source, run_with_io};

/// An oracle trap: a non-value, non-catchable halt (§6). Its class is the
/// analyzer obligation it mirrors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trap {
    pub class: TrapClass,
    pub message: String,
}

/// The trap classes and their analyzer-obligation mirrors (§6 concordance).
///
/// Thirteen classes, bijective with suite cases T-01…T-14 (the ID range is stable;
/// one case is superseded). The former fourteenth, `unprintable-interpolation`, is
/// **deleted** — structure interpolation was ruled *total* [user, 2026-07-18], so
/// every value renders and no interpolation can halt (suite PR-01…05).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrapClass {
    UnboundEvaluation,
    WorldAdmission,
    ExpectingSeat,
    ArgumentObligation,
    OperationSafety,
    UndischargedIndeterminate,
    NullReceiver,
    AbsentField,
    IndexBounds,
    TestedSeat,
    RefutedBinding,
    SpreadKind,
    ComputedKey,
}

/// The completion triple for a body/expression (§1). `DidNotComplete`
/// (divergence) is genuine non-termination and is not represented as a value;
/// traps travel on the `Err` channel.
#[derive(Clone, Debug)]
pub enum Outcome {
    Produced(ValueRef),
    CompletedWithoutValue,
}

pub type EvalResult = Result<Outcome, Trap>;

/// The world a body evaluates in (semantics §1), derived from `Lambda.actKind`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum World {
    Pure,
    Mutator,
    Effect,
}

impl World {
    /// The admission matrix (B5, 1.0.3): which callee act-kinds are admitted.
    fn admits(self, callee: ActKind) -> bool {
        match self {
            World::Pure => matches!(callee, ActKind::Pure),
            World::Mutator => matches!(callee, ActKind::Pure | ActKind::Mutator),
            World::Effect => true,
        }
    }
}

/// The runtime store σ: committed slot contents, plus a count of *actual*
/// commits (the interning-exact equality guard skips no-op writes — B7/G1). The
/// commit count is test-observable evidence the guard fired.
#[derive(Default)]
pub struct Store {
    committed: Vec<ValueRef>,
    commits: usize,
}

impl Store {
    fn alloc(&mut self, value: ValueRef) -> SlotId {
        let id = SlotId(self.committed.len() as u32);
        self.committed.push(value);
        id
    }

    fn read(&self, slot: SlotId) -> ValueRef {
        self.committed[slot.0 as usize].clone()
    }
}

/// The oracle: owns the interner and the store while evaluating. `pending` is the
/// pending set π — present only inside a mutation transaction (B5).
pub struct Oracle<'a> {
    interner: &'a mut Interner,
    store: Store,
    pending: Option<HashMap<SlotId, ValueRef>>,
}

impl<'a> Oracle<'a> {
    pub fn new(interner: &'a mut Interner) -> Oracle<'a> {
        Oracle { interner, store: Store::default(), pending: None }
    }

    /// Read a slot with **read-your-writes** (B5): the staged value if the
    /// current transaction has one, else the committed value.
    fn read_slot(&self, slot: SlotId) -> ValueRef {
        if let Some(v) = self.pending.as_ref().and_then(|p| p.get(&slot)) {
            return v.clone();
        }
        self.store.read(slot)
    }

    /// Publish the current transaction (B5/B7): commit each staged slot whose
    /// value differs from the committed one (pointer inequality — the
    /// interning-exact guard); equal writes fire nothing. All commits land here,
    /// at the outermost mutator's completion.
    fn publish(&mut self) {
        if let Some(pending) = self.pending.take() {
            for (slot, staged) in pending {
                let committed = self.store.committed[slot.0 as usize].clone();
                if !staged.ptr_eq(&committed) {
                    self.store.committed[slot.0 as usize] = staged;
                    self.store.commits += 1;
                }
            }
        }
    }

    fn trap<T>(class: TrapClass, message: impl Into<String>) -> Result<T, Trap> {
        Err(Trap { class, message: message.into() })
    }

    /// Evaluate an expression in an expecting seat: demand `Produced`.
    fn eval_value(&mut self, e: &Expr, env: &Env, world: World) -> Result<ValueRef, Trap> {
        match self.eval(e, env, world)? {
            Outcome::Produced(v) => Ok(v),
            Outcome::CompletedWithoutValue => Self::trap(
                TrapClass::ExpectingSeat,
                "a value is expected here but the expression completed without one",
            ),
        }
    }
}
