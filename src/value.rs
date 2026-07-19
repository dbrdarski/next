//! The value layer — interned, immutable NEXT values (Compendium B1, semantics §1).
//!
//! All values are immutable and **eagerly interned**: same value = same pointer,
//! and `==` is pointer comparison for every type (B1). There is no
//! reference-identity operator and no observable reference identity. Locations
//! (slots) are **not** values and can never be named or compared — they live in
//! the store, not here.
//!
//! Interning is hash-consing: a [`ValueRef`] is a shared pointer whose children
//! are themselves canonical `ValueRef`s. Because children are already canonical,
//! comparing a compound value's children *by pointer* is exactly structural
//! comparison — so `ValueData`'s derived `Hash`/`Eq` (which uses the pointer-based
//! `Hash`/`Eq` of `ValueRef` for children and content for leaves) is the correct
//! interning key. Construct values through the [`Interner`](crate::interner).

use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::ast::{ActKind, Lambda};
use crate::env::Env;
use crate::interner::Interner;
use crate::rational::Rational;

/// A canonical, interned value handle. Equality and hashing are by pointer; the
/// interner guarantees that equal values share one pointer, so pointer equality
/// coincides with structural (`==`) equality (B1).
#[derive(Clone, Debug)]
pub struct ValueRef(Rc<ValueData>);

impl ValueRef {
    /// Wrap owned data. **Interner-internal**: constructing a `ValueRef` outside
    /// the interner breaks the canonicalization invariant (would create a second
    /// pointer for an equal value). Use [`Interner`](crate::interner) instead.
    pub(crate) fn from_data(data: ValueData) -> ValueRef {
        ValueRef(Rc::new(data))
    }

    pub fn data(&self) -> &ValueData {
        &self.0
    }

    /// Pointer equality — the language's only equality (B1). Same as `==`.
    pub fn ptr_eq(&self, other: &ValueRef) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    fn as_ptr(&self) -> *const ValueData {
        Rc::as_ptr(&self.0)
    }
}

// Pointer identity is the whole game: two `ValueRef`s are equal iff they point at
// the same interned allocation. The interner makes this coincide with structural
// equality.
impl PartialEq for ValueRef {
    fn eq(&self, other: &ValueRef) -> bool {
        self.ptr_eq(other)
    }
}
impl Eq for ValueRef {}

impl Hash for ValueRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_ptr().hash(state);
    }
}

/// The payload behind a [`ValueRef`]. Derived `Hash`/`Eq` use pointer identity
/// for child `ValueRef`s (canonical ⇒ structural) and content for leaves — the
/// key the interner probes on.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ValueData {
    Boolean(bool),
    Null,
    /// Exact rational (B2).
    Number(Rational),
    /// UTF-16 storage (B1); grapheme semantics for bare index/slice/length are
    /// an oracle concern (E8, build-order step 3).
    Str(Vec<u16>),
    /// Elements are canonical `ValueRef`s, in order.
    Tuple(Vec<ValueRef>),
    /// Fields in canonical form: sorted by UTF-16 key, keys unique (later-wins
    /// resolved at construction). Order is not observable — `{a:1,b:2}` and
    /// `{b:2,a:1}` are the same value.
    Record(Vec<RecordEntry>),
    /// A function value: `(body, captured environment, actKind)` (semantics §1).
    /// A plain allocation (never hash-consed); value equality is a bisimulation
    /// over the rational tree `node(shape, captures)` — see [`FnValue`] and the
    /// μ-Canonicalization Spec (algorithm B).
    Function(FnValue),
    /// A total-division / indeterminate arithmetic result (semantics §3). A plain
    /// interned value, not a trap.
    Indeterminate(IndetForm),
    /// A **host effect** — a native (Rust) callable injected by the harness
    /// (semantics §4): a `println`/`exit` double, "from another dimension" (E13).
    /// Not expressible in NEXT; runs Rust when applied.
    Native(NativeRef),
}

/// A canonical record field. `key` is raw UTF-16 (record keys are always
/// strings); `value` is an interned value.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct RecordEntry {
    pub key: Vec<u16>,
    pub value: ValueRef,
}

/// A closure: a lambda body plus the environment it was constructed in
/// (semantics §1). The environment is captured by reference, so late binding and
/// mutual recursion resolve at call time (B4). Used for **evaluation**.
#[derive(Debug)]
pub struct Closure {
    pub lambda: Lambda,
    pub env: Env,
}

/// A function value (μ-Canonicalization Spec, the interning amendment): a **plain
/// allocation**, never hash-consed. Its identity is its rational tree
/// `node(shape, captures)` — compared lazily by bisimulation (algorithm B), *not*
/// by the interner's pointer test. It carries:
///
/// - `shape` — the canonical code (α/capture-normalized; finite), the node label
///   for equality and the layer-2 cache key;
/// - `free_vars` — the ordered names of the capture slots in `shape`, resolved
///   against `closure.env` at comparison time to get the capture children;
/// - `closure` — lambda + captured environment, for evaluation.
///
/// `Hash`/`Eq` are **pointer identity** so the interner treats functions (and any
/// structure transitively containing one) as distinct allocations; value equality
/// goes through algorithm B instead.
#[derive(Clone)]
pub struct FnValue {
    shape: Rc<Lambda>,
    free_vars: Rc<Vec<String>>,
    closure: Rc<Closure>,
}

impl FnValue {
    pub fn new(shape: Lambda, free_vars: Vec<String>, closure: Closure) -> FnValue {
        FnValue { shape: Rc::new(shape), free_vars: Rc::new(free_vars), closure: Rc::new(closure) }
    }

    /// The canonical code (shape) — the function's node label for equality.
    pub fn shape(&self) -> &Lambda {
        &self.shape
    }

    /// The ordered capture-slot names (`shape`'s `@cap`i corresponds to
    /// `free_vars[i]`).
    pub fn free_vars(&self) -> &[String] {
        &self.free_vars
    }

    pub fn closure(&self) -> &Closure {
        &self.closure
    }

    pub fn closure_rc(&self) -> Rc<Closure> {
        self.closure.clone()
    }

    fn ptr(&self) -> *const Closure {
        Rc::as_ptr(&self.closure)
    }
}

impl PartialEq for FnValue {
    fn eq(&self, other: &FnValue) -> bool {
        std::ptr::eq(self.ptr(), other.ptr())
    }
}
impl Eq for FnValue {}

impl Hash for FnValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.ptr() as *const ()).hash(state);
    }
}

impl std::fmt::Debug for FnValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<function>")
    }
}

/// A native host callable (semantics §4). `imp` runs Rust against the argument
/// values, using the interner to build its result; it returns an ordinary value
/// (a success, or a `Failure` record — B6), or an `Err(msg)` that the oracle
/// turns into an `operation-safety` trap.
pub struct NativeFn {
    pub name: String,
    pub act_kind: ActKind,
    #[allow(clippy::type_complexity)]
    pub imp: Rc<dyn Fn(&mut Interner, &[ValueRef]) -> Result<ValueRef, String>>,
}

/// A pointer-identity handle to a [`NativeFn`] (host effects are unique).
#[derive(Clone)]
pub struct NativeRef(Rc<NativeFn>);

impl NativeRef {
    pub fn new(native: NativeFn) -> NativeRef {
        NativeRef(Rc::new(native))
    }

    pub fn get(&self) -> &NativeFn {
        &self.0
    }
}

impl PartialEq for NativeRef {
    fn eq(&self, other: &NativeRef) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for NativeRef {}

impl Hash for NativeRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Rc::as_ptr(&self.0) as *const ()).hash(state);
    }
}

impl std::fmt::Debug for NativeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native {}>", self.0.name)
    }
}

/// The form label of an Indeterminate value (semantics §3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum IndetForm {
    /// `x / 0` for nonzero `x` — printed `_/0`.
    DivByZero,
    /// `0 / 0` — printed `0/0`.
    ZeroOverZero,
}

impl IndetForm {
    pub fn label(self) -> &'static str {
        match self {
            IndetForm::DivByZero => "_/0",
            IndetForm::ZeroOverZero => "0/0",
        }
    }
}

// ── Convenience read accessors (for the oracle and tests) ────────────────────

impl ValueRef {
    pub fn as_boolean(&self) -> Option<bool> {
        match self.data() {
            ValueData::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self.data(), ValueData::Null)
    }

    pub fn as_number(&self) -> Option<&Rational> {
        match self.data() {
            ValueData::Number(n) => Some(n),
            _ => None,
        }
    }

    pub fn as_str_units(&self) -> Option<&[u16]> {
        match self.data() {
            ValueData::Str(u) => Some(u),
            _ => None,
        }
    }

    /// Decode a string value to a Rust `String` (lossy on unpaired surrogates).
    /// For tests/diagnostics only — not a language operation.
    pub fn as_string_lossy(&self) -> Option<String> {
        self.as_str_units().map(String::from_utf16_lossy)
    }

    pub fn as_tuple(&self) -> Option<&[ValueRef]> {
        match self.data() {
            ValueData::Tuple(items) => Some(items),
            _ => None,
        }
    }

    pub fn as_record(&self) -> Option<&[RecordEntry]> {
        match self.data() {
            ValueData::Record(fields) => Some(fields),
            _ => None,
        }
    }

    /// The closure to evaluate when this function value is applied. Returns a
    /// cloned `Rc<Closure>` so callers can borrow `self` freely afterward.
    pub fn as_closure(&self) -> Option<Rc<Closure>> {
        match self.data() {
            ValueData::Function(f) => Some(f.closure_rc()),
            _ => None,
        }
    }

    pub fn as_indeterminate(&self) -> Option<IndetForm> {
        match self.data() {
            ValueData::Indeterminate(f) => Some(*f),
            _ => None,
        }
    }

    pub fn as_native(&self) -> Option<&NativeRef> {
        match self.data() {
            ValueData::Native(n) => Some(n),
            _ => None,
        }
    }
}
