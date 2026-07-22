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
use crate::desugar::DesugarError;
use crate::lex::LexError;
use crate::parse::ParseError;

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

/// A root environment with the **pure prelude** installed: the `String` record
/// (`length` / `units` / `points` — E8's grapheme machinery views). These are
/// pure natives, callable in every world.
pub fn prelude_env(interner: &mut Interner) -> Env {
    let env = Scope::root();
    install_string_prelude(interner, &env);
    env
}

/// `String.length` counts **grapheme clusters** (UAX #29, the pinned segmenter —
/// E8); `String.units` / `String.points` are the UTF-16-unit and code-point views
/// over the same machinery.
// [ask-author]: the element representation of the `units`/`points` views is not
// pinned by E8 — implemented here as Tuples of Numbers (code units / code points);
// only their *lengths* are asserted by the suite (S-02).
fn install_string_prelude(interner: &mut Interner, env: &Env) {
    use unicode_segmentation::UnicodeSegmentation;

    let demand_str = |args: &[ValueRef]| -> Result<String, String> {
        args.first()
            .and_then(|v| v.as_str_units().map(String::from_utf16_lossy))
            .ok_or_else(|| "String.* expects a String argument".to_string())
    };

    let length = NativeFn {
        name: "String.length".into(),
        act_kind: ActKind::Pure,
        imp: Rc::new(move |interner: &mut Interner, args: &[ValueRef]| {
            let s = demand_str(args)?;
            let n = s.graphemes(true).count();
            Ok(interner.integer(n as i64))
        }),
    };
    let units = NativeFn {
        name: "String.units".into(),
        act_kind: ActKind::Pure,
        imp: Rc::new(move |interner: &mut Interner, args: &[ValueRef]| {
            let s = demand_str(args)?;
            let items: Vec<ValueRef> =
                s.encode_utf16().map(|u| interner.integer(u as i64)).collect();
            Ok(interner.tuple(items))
        }),
    };
    let points = NativeFn {
        name: "String.points".into(),
        act_kind: ActKind::Pure,
        imp: Rc::new(move |interner: &mut Interner, args: &[ValueRef]| {
            let s = demand_str(args)?;
            let items: Vec<ValueRef> =
                s.chars().map(|c| interner.integer(c as i64)).collect();
            Ok(interner.tuple(items))
        }),
    };

    let length_v = interner.native(NativeRef::new(length));
    let units_v = interner.native(NativeRef::new(units));
    let points_v = interner.native(NativeRef::new(points));
    let string_record = interner.record_str(vec![
        ("length", length_v),
        ("units", units_v),
        ("points", points_v),
    ]);
    env.define("String", Binding::Value(string_record));
}

/// Lex → parse → desugar → run an entry program with host effects installed,
/// returning the final value and the captured IO. Panics on a front-end error
/// (for tests, where the source is known-good); use [`run_source`] for a
/// non-panicking driver.
pub fn run_with_io(src: &str) -> Result<(ValueRef, HostIo), Trap> {
    let mut interner = Interner::new();
    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = Desugarer::new(&mut interner).program(&sprogram).expect("desugar ok");

    let io = Rc::new(RefCell::new(HostIo::default()));
    let env = prelude_env(&mut interner);
    install_host_effects(&mut interner, &env, &io);

    let mut oracle = Oracle::new(&mut interner);
    let value = oracle.run_module_in(&module, &env)?;
    // The host-effect closures still hold clones of `io`, so take the contents
    // out of the shared cell rather than unwrapping the `Rc`.
    let captured = std::mem::take(&mut *io.borrow_mut());
    Ok((value, captured))
}

/// A failure at any stage of running a program (for the CLI / user-facing use).
#[derive(Debug)]
pub enum RunError {
    Lex(LexError),
    Parse(ParseError),
    Desugar(DesugarError),
    Trap(Trap),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunError::Lex(e) => write!(f, "lex error (line {}): {}", e.line, e.message),
            RunError::Parse(e) => write!(f, "parse error (line {}): {}", e.line, e.message),
            RunError::Desugar(e) => write!(f, "desugar error: {}", e.message),
            RunError::Trap(t) => write!(f, "trap [{:?}]: {}", t.class, t.message),
        }
    }
}

/// The non-panicking driver: run a program, surfacing every stage's error.
pub fn run_source(src: &str) -> Result<(ValueRef, HostIo), RunError> {
    let toks = lex(src).map_err(RunError::Lex)?;
    let sprogram = parse_program(toks).map_err(RunError::Parse)?;
    let mut interner = Interner::new();
    let module = Desugarer::new(&mut interner)
        .program(&sprogram)
        .map_err(RunError::Desugar)?;

    let io = Rc::new(RefCell::new(HostIo::default()));
    let env = prelude_env(&mut interner);
    install_host_effects(&mut interner, &env, &io);

    let value = Oracle::new(&mut interner)
        .run_module_in(&module, &env)
        .map_err(RunError::Trap)?;
    let captured = std::mem::take(&mut *io.borrow_mut());
    Ok((value, captured))
}
