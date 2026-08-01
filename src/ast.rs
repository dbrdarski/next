//! Kernel AST — the analyzer-facing form (Kernel AST Specification v0.1, §§1–3).
//!
//! This is *what exists after parsing and desugaring*: the parser emits it
//! through the closed desugar catalog (spec §4), the oracle evaluates it, the
//! normalizer rewrites it, and (later) the analyzer keys identity on its
//! canonical forms. Surface sugar never reaches here.
//!
//! **No source spans.** Kernel forms are position-free so interned code stays
//! canonical; provenance lives in a separate occurrence→span side table (B4).
//! Every node derives `Hash`/`Eq` so kernel forms intern like any value (§5).
//!
//! This module defines the node *inventory* only. Evaluation is the oracle
//! (build-order step 3); canonicalization/de-Bruijn rewriting is §5's normalizer.

use crate::value::ValueRef;

/// Act-kind — a component of function **shape** (C§13.2). Reactive-fence kinds
/// (`@reactive`, `@computed`) are AST §7 extension points, deliberately absent.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ActKind {
    Pure,
    Mutator,
    Effect,
}

// ── Binding / location / self-reference identity (§1 `Ref` flavors) ──────────

/// An immutable-binding reference. Post-canonicalization it is positional
/// (de-Bruijn-style, for C§13.4 cache keys); pre-canonicalization it carries the
/// surface name. The normalizer (§5) rewrites `Name` → `Positional`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BindingRef {
    Name(String),
    Positional(u32),
}

/// A Box (`@state`/`@mutable`) location marker. Evaluation is a dynamic read of
/// current content (B4); the marker participates in function identity — distinct
/// bindings are distinct (fork 13). Same numbering ⇒ same location.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LocationId(pub u32);

/// A μ-marker for a self/group reference still under initialization. The marker
/// (not a back-pointer) keeps interned code acyclic; canonicalizes rational-tree
/// style (C§9, F3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct MuMarker(pub u32);

/// The three resolved reference flavors — value-identity layer 1 (C§12.3, F3).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Ref {
    Immutable(BindingRef),
    Location(LocationId),
    Mu(MuMarker),
}

// ── Expressions (§1) ─────────────────────────────────────────────────────────

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Expr {
    /// An interned value embedded directly (post-resolution literals, prelude
    /// `true`/`false`/`null`).
    Const(ValueRef),
    /// A reference to a binding (one of three resolved flavors).
    Ref(Ref),
    /// The only function form.
    Lambda(Lambda),
    /// Application — one node for all calls. Strict left-to-right arg eval.
    Apply { callee: Box<Expr>, args: Vec<Arg> },
    /// Built-in operation. No truthiness/logic/conditional op exists here —
    /// those desugar to `Match`. Division/remainder are total via specific
    /// Indeterminate forms.
    PrimOp { op: PrimOp, args: Vec<Expr> },
    /// The sole control node (§1). A block is a `Match` with implicit scrutinee.
    Match(Match),
    /// Tuple construction; middle spreads legal; no elision.
    TupleCons(Vec<Element>),
    /// Record construction; later-wins; computed keys demand finite string sets.
    RecordCons(Vec<Field>),
    /// The one access node. `total = false` is the demand form; `total = true`
    /// is the `?.` family (one-step null conversion). Slices ignore `total`
    /// (always clamped-total). `?.` is a kernel mode, never sugar.
    Access {
        target: Box<Expr>,
        form: AccessForm,
        total: bool,
    },
    /// Interpolated template; a kernel node (printing is runtime semantics).
    Template(Vec<TemplatePart>),
    /// The mutation primitive; legal only inside `mutator`-kind bodies. All
    /// compound/path/slice mutation desugars to `Write` of a functional update.
    Write { slot: SlotRef, value: Box<Expr> },
}

/// A mutation target. Pre-canonicalization it is a name (resolving a name to a
/// slot and confirming the binding is a Box is analyzer work); post-resolution it
/// is a `LocationId`. Mirrors [`BindingRef`].
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SlotRef {
    Name(String),
    Location(LocationId),
}

/// The one function form. `params` is a pattern over the complete argument
/// tuple (the arity model); `body` is an `Expr` (a `Match` when block-form).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Lambda {
    pub params: Pat,
    pub body: Box<Expr>,
    pub act_kind: ActKind,
}

/// An argument in `Apply`; `...e` is `Spread`. Multiple spreads are legal.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Arg {
    Expr(Expr),
    Spread(Expr),
}

/// An element in `TupleCons`; middle spreads legal.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Element {
    Expr(Expr),
    Spread(Expr),
}

/// A field in `RecordCons`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Field {
    /// Static-key field `key: expr`.
    Field { key: String, value: Expr },
    /// Computed-key field `[keyExpr]: expr` (demands a proven-finite string set).
    Computed { key: Expr, value: Expr },
    /// Record spread `...expr` (later-wins).
    Spread(Expr),
}

/// Built-in operations (§1). String concat is `Add` over two Strings.
/// No truthiness/logic/conditional op — those are `Match`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Neg,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

/// Access target shape.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AccessForm {
    Field(String),
    Index(Box<Expr>),
    /// Half-open window; negative bounds address from the end; always clamped.
    Slice {
        lo: Option<Box<Expr>>,
        hi: Option<Box<Expr>>,
    },
}

/// A template part: a literal segment or an interpolation.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TemplatePart {
    Segment(String),
    Interp(Expr),
}

// ── Match (§1) ───────────────────────────────────────────────────────────────

/// The sole control node. `items` run in order; an `Arm` tests and on success
/// exits with `result`; each later item sees the accumulated Difference.
/// Completion outcome is the semantic triple (Produced / CompletedWithoutValue /
/// DidNotComplete) — evaluated by the oracle, not represented here.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Match {
    pub scrutinee: Option<Box<Expr>>,
    pub items: Vec<MatchItem>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum MatchItem {
    Bind(Bind),
    Stmt(Expr),
    Arm(Arm),
}

/// `Arm(pattern?, guard?, result)`. Pattern tests against the scrutinee; guard is
/// a strict tested seat (Boolean). On success the enclosing `Match` exits.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Arm {
    pub pattern: Option<Pat>,
    pub guard: Option<Expr>,
    pub result: Expr,
}

// ── Patterns (§3) ────────────────────────────────────────────────────────────
//
// Pins (`^name`) and alternation (`p1 | p2`) do NOT exist in the kernel — they
// desugar (to an equality guard and to arm expansion). Patterns are exact by
// default; `rest` opens. One rest per level; middle rests legal in tuples.

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pat {
    /// `PConst` — literals and prelude constants.
    Const(ValueRef),
    /// `PBind` — a fresh binding; may shadow.
    Bind(String),
    /// `PWild` — `_`.
    Wild,
    /// `PTuple` — elements with an optional positioned rest (encoded inline).
    Tuple(Vec<PatElem>),
    /// `PRecord` — fields with an optional rest; `exact` unless opened.
    Record { fields: Vec<PatField>, exact: bool },
    /// `PContract` — matches `value ⊑ contract`, consumes by intersection.
    Contract(Ref),
}

/// A tuple-pattern element: a sub-pattern or a rest. `Rest(None)` ignores
/// (`..._`); `Rest(Some(name))` captures.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PatElem {
    Pat(Pat),
    Rest(Option<String>),
}

/// A record-pattern field: `key` bound to a sub-pattern, or a rest (record
/// subtraction).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PatField {
    Field { key: String, pat: Pat },
    Rest(Option<String>),
}

// ── Declarations and module structure (§2) ───────────────────────────────────

/// Module top level is pure world: `Bind`, `SlotDecl`, `ActBind`, `Import`,
/// `Where` only — no act calls. `name` present iff anything exports.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Module {
    pub name: Option<String>,
    pub items: Vec<Item>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Item {
    Bind(Bind),
    SlotDecl(SlotDecl),
    ActBind(ActBind),
    Import(Import),
    Where(Where),
    Stmt(Expr),
}

/// `Bind(target, Expr, exported?)`. `target` is a name or an irrefutable pattern
/// (irrefutability policed by the analyzer). Late binding governs references.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Bind {
    pub target: BindTarget,
    pub value: Expr,
    pub exported: bool,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BindTarget {
    Name(String),
    Pattern(Pat),
}

/// Declares a Box location: `reactive = true` for `@state`, `false` for
/// `@mutable`. `init` is pure. Exported slots export the *binding* (live reads).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SlotDecl {
    pub reactive: bool,
    pub name: String,
    pub init: Expr,
    pub exported: bool,
}

/// Binds a mutator or effect declaration (`@mutate`, `@effect`); sets the
/// lambda's `act_kind`. Statement-position only. (`kind` is `Mutator` or
/// `Effect`; `Pure` bindings are ordinary `Bind`s.)
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ActBind {
    pub kind: ActKind,
    pub name: String,
    pub lambda: Lambda,
    pub exported: bool,
}

/// Binds imported names to the source module's bindings (`names = None` aliases
/// the whole namespace). Static whole-program resolution; no runtime semantics.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Import {
    pub names: Option<Vec<String>>,
    pub module: String,
}

/// The name-level signature assertion (E11). Analyzer-facing metadata; no
/// evaluation behavior.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Where {
    pub name: String,
    pub input_contract: Expr,
    pub return_contract: Expr,
}
