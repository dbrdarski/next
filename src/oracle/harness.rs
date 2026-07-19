//! The host-effect harness (Semantics Companion §4).
//!
//! "The oracle needs a world to touch." Host effects are harness-provided
//! functions with `actKind = effect` — test doubles for IO. This harness injects
//! a `println` (records into a buffer instead of real stdout) and an `exit`
//! (records the code), runs an entry program, and returns what was "printed" so
//! effects are observable in tests. A failing effect returns a `Failure` record
//! (B6) that flows on as ordinary data.

use std::cell::RefCell;
use std::rc::Rc;

use crate::desugar::Desugarer;
use crate::env::{Binding, Env, Scope};
use crate::interner::Interner;
use crate::lex::lex;
use crate::parse::parse_program;
use crate::value::{NativeFn, NativeRef, ValueRef};

use super::{Oracle, Trap};
use crate::ast::ActKind;

/// What the harness captured from a run.
#[derive(Default, Debug)]
pub struct HostIo {
    /// Lines "printed" by `println`, in order.
    pub output: Vec<String>,
    /// The code passed to `exit`, if it was called.
    pub exit_code: Option<i64>,
}

/// Build a `Failure` record value `{ path, reason }` (B6, the one prelude shape).
fn failure(interner: &mut Interner, path: &str, reason: &str) -> ValueRef {
    let p = interner.string(path);
    let r = interner.string(reason);
    interner.record_str(vec![("path", p), ("reason", r)])
}

/// Install the host-effect doubles into `env`, sharing `io` for observation.
fn install_host_effects(interner: &mut Interner, env: &Env, io: &Rc<RefCell<HostIo>>) {
    // println(msg): record `msg` (stringified minimally), return null.
    let io_println = io.clone();
    let println = NativeFn {
        name: "println".into(),
        act_kind: ActKind::Effect,
        imp: Rc::new(move |interner: &mut Interner, args: &[ValueRef]| {
            let line = args
                .first()
                .and_then(|v| v.as_string_lossy())
                .unwrap_or_default();
            io_println.borrow_mut().output.push(line);
            Ok(interner.null())
        }),
    };
    let println = interner.native(NativeRef::new(println));
    env.define("println", Binding::Value(println));

    // exit(code): record the code, return null (the real host limit is outside
    // the semantics — §4; the double does not terminate the process).
    let io_exit = io.clone();
    let exit = NativeFn {
        name: "exit".into(),
        act_kind: ActKind::Effect,
        imp: Rc::new(move |interner: &mut Interner, args: &[ValueRef]| {
            let code = args
                .first()
                .and_then(|v| v.as_number())
                .and_then(|n| n.is_integer().then(|| n.as_ratio().numer().clone()))
                .and_then(|n| n.try_into().ok())
                .unwrap_or(0i64);
            io_exit.borrow_mut().exit_code = Some(code);
            Ok(interner.null())
        }),
    };
    let exit = interner.native(NativeRef::new(exit));
    env.define("exit", Binding::Value(exit));

    // readFile(name): a fallible double — always fails, returning a Failure that
    // flows as plain data (B6). Enough to exercise then/catch chains.
    let read_file = NativeFn {
        name: "readFile".into(),
        act_kind: ActKind::Effect,
        imp: Rc::new(move |interner: &mut Interner, args: &[ValueRef]| {
            let path = args
                .first()
                .and_then(|v| v.as_string_lossy())
                .unwrap_or_default();
            Ok(failure(interner, &path, "not found"))
        }),
    };
    let read_file = interner.native(NativeRef::new(read_file));
    env.define("readFile", Binding::Value(read_file));
}

/// Lex → parse → desugar → run an entry program with host effects installed,
/// returning the final value and the captured IO.
pub fn run_with_io(src: &str) -> Result<(ValueRef, HostIo), Trap> {
    let mut interner = Interner::new();
    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = Desugarer::new(&mut interner).program(&sprogram).expect("desugar ok");

    let io = Rc::new(RefCell::new(HostIo::default()));
    let env = Scope::root();
    install_host_effects(&mut interner, &env, &io);

    let mut oracle = Oracle::new(&mut interner);
    let value = oracle.run_module_in(&module, &env)?;
    // The host-effect closures still hold clones of `io`, so take the contents
    // out of the shared cell rather than unwrapping the `Rc`.
    let captured = std::mem::take(&mut *io.borrow_mut());
    Ok((value, captured))
}
