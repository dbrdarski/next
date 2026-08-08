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

use std::cell::{OnceCell, RefCell};
use std::hash::{Hash, Hasher};
use std::rc::{Rc, Weak};

use crate::ast::{ActKind, Lambda};
use crate::env::{Binding, Env, SlotId};
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

    pub(crate) fn weak(&self) -> Weak<ValueData> {
        Rc::downgrade(&self.0)
    }

    pub(crate) fn matches_weak(&self, weak: &Weak<ValueData>) -> bool {
        weak.upgrade()
            .is_some_and(|held| Rc::ptr_eq(&held, &self.0))
    }

    /// The interned allocation address, as a stable within-process id (used for
    /// canonical serialization of constants — equal interned values share it).
    pub fn addr(&self) -> usize {
        self.as_ptr() as usize
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
    /// A function value: canonical code plus positional captures and `actKind`.
    /// Construction canonicalizes it through the function interner: an acyclic
    /// shallow key when captures are resolved, or a verified rational-graph
    /// bucket at recursive-window close. Source code retained by [`Closure`] is
    /// diagnostic/analyzer metadata, not identity or invocation state.
    Function(FnValue),
    /// An unresolved arithmetic result (Part XII, 2026-08-01): a plain interned
    /// value, not a trap. The form tag and canonical Number operand together are
    /// its complete identity key.
    Indeterminate(IndeterminateForm),
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

/// The source lambda retained as analyzer/diagnostic metadata beside a positional
/// capture vector. Runtime invocation executes [`FnValue::shape`], not this source
/// form. Closed closures retain no lexical environment.
#[derive(Debug)]
pub struct Closure {
    pub lambda: Lambda,
    capture_names: Rc<Vec<String>>,
    captures: Rc<Vec<ClosureCapture>>,
}

impl Closure {
    pub(crate) fn new(lambda: Lambda) -> Closure {
        Closure {
            lambda,
            capture_names: Rc::new(Vec::new()),
            captures: Rc::new(Vec::new()),
        }
    }

    pub(crate) fn capture_binding_at(&self, index: usize) -> Option<Binding> {
        match self.captures.get(index)? {
            ClosureCapture::Value(value) => Some(Binding::Value(value.clone())),
            ClosureCapture::Location(slot) => Some(Binding::Slot(*slot)),
            ClosureCapture::Recursive(edge) => edge.group.target(edge.index).map(Binding::Value),
            ClosureCapture::Deferred { env, name } => env.lookup(name),
        }
    }

    pub(crate) fn capture_binding(&self, name: &str) -> Option<Binding> {
        let index = self.capture_names.iter().position(|free| free == name)?;
        self.capture_binding_at(index)
    }
}

/// One positional capture operand of canonical function code. `Value` is the
/// complete Pure-closure representation. `Location` is retained only for the
/// separate Effect/Mutator implementation path. `Deferred` is a construction-
/// window placeholder and must be eliminated when the graph closes.
#[derive(Clone, Debug)]
pub(crate) enum ClosureCapture {
    Value(ValueRef),
    Location(SlotId),
    Recursive(RecursiveCapture),
    Deferred { env: Env, name: String },
}

/// A positional edge inside one closed recursive construction graph. The current
/// Rust representation keeps the graph's canonical root handles together; the
/// later one-allocation/group-offset representation can replace this ownership
/// detail without changing the capture or invocation model.
#[derive(Clone, Debug)]
pub(crate) struct RecursiveCapture {
    group: Rc<RecursiveGroup>,
    index: usize,
}

#[derive(Debug)]
pub(crate) struct RecursiveGroup {
    draft: RefCell<Vec<Option<ValueRef>>>,
    locked: OnceCell<Rc<Vec<ValueRef>>>,
}

impl RecursiveGroup {
    pub(crate) fn new(len: usize) -> Rc<RecursiveGroup> {
        Rc::new(RecursiveGroup {
            draft: RefCell::new((0..len).map(|_| None).collect()),
            locked: OnceCell::new(),
        })
    }

    pub(crate) fn edge(group: &Rc<RecursiveGroup>, index: usize) -> ClosureCapture {
        ClosureCapture::Recursive(RecursiveCapture {
            group: group.clone(),
            index,
        })
    }

    pub(crate) fn set_target(&self, index: usize, value: &ValueRef) {
        debug_assert!(self.locked.get().is_none());
        self.draft.borrow_mut()[index] = Some(value.clone());
    }

    pub(crate) fn lock(&self) {
        let targets: Vec<ValueRef> = self
            .draft
            .borrow()
            .iter()
            .cloned()
            .map(|target| target.expect("recursive group target is initialized"))
            .collect();
        self.locked
            .set(Rc::new(targets))
            .expect("recursive group locks exactly once");
        self.draft.borrow_mut().clear();
    }

    fn target(&self, index: usize) -> Option<ValueRef> {
        if let Some(locked) = self.locked.get() {
            return locked.get(index).cloned();
        }
        self.draft.borrow().get(index)?.clone()
    }
}

/// A function payload (μ-Canonicalization Specification §6). The enclosing
/// [`ValueRef`] is canonicalized by the interner; this payload carries:
///
/// - `shape` — the canonical code (α/capture-normalized; finite), the node label
///   for equality and the layer-2 cache key;
/// - `free_vars` — source names corresponding positionally to `@cap0`, `@cap1`, …;
/// - `closure` — source metadata plus the explicit capture vector.
///
/// `Hash`/`Eq` here identify the provisional closure allocation only. They keep a
/// half-built graph out of the ordinary bottom-up table; [`Interner`] applies the
/// actual shallow/group key and returns the canonical `ValueRef` before exposure.
/// Language equality compares canonical `ValueRef` pointers, never payloads.
#[derive(Clone)]
pub struct FnValue {
    shape: crate::intern::Interned<Lambda>,
    closure: Rc<Closure>,
}

impl FnValue {
    /// `shape` must come from [`crate::interner::Interner::intern_code`] — the interned
    /// canonical code, so that identical shapes share one allocation and compare by pointer.
    pub(crate) fn new(
        shape: crate::intern::Interned<Lambda>,
        free_vars: Vec<String>,
        captures: Vec<ClosureCapture>,
        closure: Closure,
    ) -> FnValue {
        debug_assert_eq!(free_vars.len(), captures.len());
        let capture_names = Rc::new(free_vars);
        let captures = Rc::new(captures);
        FnValue {
            shape,
            closure: Rc::new(Closure {
                lambda: closure.lambda,
                capture_names,
                captures,
            }),
        }
    }

    /// The interned canonical code, as a pointer. Identical shapes share it, so
    /// `Rc::ptr_eq` on this is exact shape identity — no structural walk.
    pub fn shape_rc(&self) -> crate::intern::Interned<Lambda> {
        self.shape.clone()
    }

    /// The canonical code (shape) — the function's node label for equality.
    pub fn shape(&self) -> &Lambda {
        &self.shape
    }

    /// The ordered capture-slot names (`shape`'s `@cap`i corresponds to
    /// `free_vars[i]`).
    pub fn free_vars(&self) -> &[String] {
        &self.closure.capture_names
    }

    pub(crate) fn captures(&self) -> &[ClosureCapture] {
        &self.closure.captures
    }

    /// Resolve one positional capture. Deferred captures consult the temporary
    /// construction environment; closed Pure closures never take that branch.
    pub(crate) fn capture_binding_at(&self, index: usize) -> Option<Binding> {
        self.closure.capture_binding_at(index)
    }

    pub(crate) fn capture_binding(&self, name: &str) -> Option<Binding> {
        self.closure.capture_binding(name)
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

/// The currently ruled unresolved-arithmetic forms. The operand is an already
/// interned Number value, so derived `Hash`/`Eq` use its canonical pointer.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum IndeterminateForm {
    DivZero(ValueRef),
    ModZero(ValueRef),
}

/// The form-only projection used by `Contract::Indeterminate(F)`: contracts may
/// distinguish the unresolved operation without enumerating every operand.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum IndeterminateFormTag {
    DivZero,
    ModZero,
}

impl IndeterminateForm {
    pub fn tag(&self) -> IndeterminateFormTag {
        match self {
            IndeterminateForm::DivZero(_) => IndeterminateFormTag::DivZero,
            IndeterminateForm::ModZero(_) => IndeterminateFormTag::ModZero,
        }
    }

    pub fn operand(&self) -> &ValueRef {
        match self {
            IndeterminateForm::DivZero(operand) | IndeterminateForm::ModZero(operand) => operand,
        }
    }

    /// The frozen form-only display label. Specific identity retains the operand
    /// internally even when display deliberately hides a nonzero operand.
    pub fn label(&self) -> &'static str {
        let is_zero = self
            .operand()
            .as_number()
            .expect("Indeterminate operands are canonical Numbers")
            .is_zero();
        match (self.tag(), is_zero) {
            (IndeterminateFormTag::DivZero, true) => "0/0",
            (IndeterminateFormTag::DivZero, false) => "_/0",
            (IndeterminateFormTag::ModZero, true) => "0%0",
            (IndeterminateFormTag::ModZero, false) => "_%0",
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

    /// The function value itself (canonical shape + capture-slot names), for the
    /// analyzer's γ realization check. `None` for non-functions.
    pub fn as_fn(&self) -> Option<&FnValue> {
        match self.data() {
            ValueData::Function(f) => Some(f),
            _ => None,
        }
    }

    /// Whether this value is a function (for γ's function-position constraint).
    pub fn is_function(&self) -> bool {
        matches!(self.data(), ValueData::Function(_))
    }

    pub fn as_indeterminate(&self) -> Option<&IndeterminateForm> {
        match self.data() {
            ValueData::Indeterminate(form) => Some(form),
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
