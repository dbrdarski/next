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

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use unicode_segmentation::UnicodeSegmentation;

use crate::ast::*;
use crate::env::{Binding, Env, Scope, SlotId};
use crate::interner::Interner;
use crate::rational::Rational;
use crate::value::{Closure, ClosureRef, IndetForm, ValueData, ValueRef};

mod eval;
mod mtch;
#[cfg(test)]
mod tests;

pub use eval::run_program_value;

/// An oracle trap: a non-value, non-catchable halt (§6). Its class is the
/// analyzer obligation it mirrors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trap {
    pub class: TrapClass,
    pub message: String,
}

/// The trap classes and their analyzer-obligation mirrors (§6 concordance).
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
    UnprintableInterpolation,
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

/// The runtime store σ: committed slot contents (mutator staging arrives in 3c).
#[derive(Default)]
pub struct Store {
    committed: Vec<ValueRef>,
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

/// The oracle: owns the interner and the store while evaluating.
pub struct Oracle<'a> {
    interner: &'a mut Interner,
    store: Store,
}

impl<'a> Oracle<'a> {
    pub fn new(interner: &'a mut Interner) -> Oracle<'a> {
        Oracle { interner, store: Store::default() }
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
