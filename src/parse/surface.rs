//! Surface AST — the faithful parse tree (Grammar Specification v0.1).
//!
//! This preserves **all** surface sugar (hasks, ternary, `&&`/`||`/`??`/`~`,
//! pipes, `::` match, compound mutation, pins, alternation, block bodies,
//! templates). The desugar pass (build-order step 2c) lowers it to the kernel
//! AST via the closed catalog (kernel spec §4); the analyzer never sees this
//! form. Nodes carry no spans yet — diagnostics live with a later side table.

use crate::rational::Rational;

/// A whole compilation unit (§2.1). `header` present iff the file exports.
#[derive(Clone, Debug, PartialEq)]
pub struct SProgram {
    pub header: Option<Vec<String>>,
    pub statements: Vec<SStmt>,
}

// ── Expressions (§3) ─────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq)]
pub enum SExpr {
    Number(Rational),
    Str(Vec<u16>),
    Template(Vec<STemplatePart>),
    /// A bare name (incl. the prelude `true`/`false`/`null` and contextual words
    /// when they land in ordinary seats).
    Ident(String),
    /// An expression-position hole (`_` or `_n`) — legal only within a hask (§8).
    Hole(Hole),
    /// `[ ... ]` tuple literal (middle spreads legal).
    Tuple(Vec<SElem>),
    /// `{ ... }` record literal.
    Record(Vec<SField>),
    /// `{ ... }` block body (statements incl. block-body arms). One kernel node
    /// after desugar.
    Block(Vec<SStmt>),
    /// `( e )` grouping — preserved because it affects hask/pipe scoping.
    Grouping(Box<SExpr>),
    /// `Params => body`.
    Arrow(SArrow),
    /// `# body` (bare, tier 4) or `#( expr )` (grouped primary). The inner is the
    /// hask body over its holes.
    Hask(Box<SExpr>),
    /// `scrutinee :: { arms }`.
    Match { scrutinee: Box<SExpr>, arms: Vec<SArm> },
    /// `l |> r` / `l <| r`.
    Pipe { dir: PipeDir, left: Box<SExpr>, right: Box<SExpr> },
    /// `c ? t : e`.
    Ternary { cond: Box<SExpr>, then: Box<SExpr>, els: Box<SExpr> },
    /// An infix operator application.
    Binary { op: BinOp, left: Box<SExpr>, right: Box<SExpr> },
    /// A prefix operator (`-`, `!`, `~`).
    Unary { op: UnOp, operand: Box<SExpr> },
    /// `target.field`, `target?.field`, `target[i]`, `target?.[i]`, slices.
    Access { target: Box<SExpr>, form: SAccessForm, total: bool },
    /// `callee( args )`.
    Call { callee: Box<SExpr>, args: Vec<SArg> },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Hole {
    /// `_` — a distinct fresh parameter.
    Anon,
    /// `_n` — generated positional parameter n (n ≥ 1).
    Indexed(u32),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PipeDir {
    Forward,  // |>
    Backward, // <|
}

/// Infix operators, excluding pipes/ternary/`::` (which have their own nodes).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BinOp {
    NullOr, // ??
    Or,     // ||
    And,    // &&
    Eq,     // ==
    Ne,     // !=
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow, // **
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum UnOp {
    Neg,    // -
    Not,    // !
    Loosen, // ~  (the tested-seat loosener)
}

#[derive(Clone, Debug, PartialEq)]
pub enum SAccessForm {
    Field(String),
    Index(Box<SExpr>),
    Slice { lo: Option<Box<SExpr>>, hi: Option<Box<SExpr>> },
}

/// A call argument; `...e` is a spread.
#[derive(Clone, Debug, PartialEq)]
pub enum SArg {
    Expr(SExpr),
    Spread(SExpr),
}

/// A tuple element; `...e` is a spread.
#[derive(Clone, Debug, PartialEq)]
pub enum SElem {
    Expr(SExpr),
    Spread(SExpr),
}

/// A record field.
#[derive(Clone, Debug, PartialEq)]
pub enum SField {
    /// `{ name }` ≡ `{ name: name }`.
    Shorthand(String),
    /// `{ key: value }`.
    KeyValue(String, SExpr),
    /// `{ [keyExpr]: value }`.
    Computed(SExpr, SExpr),
    /// `{ ...expr }`.
    Spread(SExpr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum STemplatePart {
    Str(Vec<u16>),
    Interp(SExpr),
}

/// An arrow function `Params => ArrowBody`.
#[derive(Clone, Debug, PartialEq)]
pub struct SArrow {
    pub params: Vec<SParam>,
    pub body: Box<SArrowBody>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SArrowBody {
    Expr(SExpr),
    Block(Vec<SStmt>),
}

/// A parameter (§3 `Param`). Pins are rejected in parameters (§4).
#[derive(Clone, Debug, PartialEq)]
pub enum SParam {
    Ident(String),
    Tuple(Vec<SPatElem>),
    Record(Vec<SPatField>, bool),
    /// `...name` — a rest parameter (final position; policed by the analyzer).
    Rest(String),
}

/// A `::` match arm: `[Pattern] [when guard] => result`.
#[derive(Clone, Debug, PartialEq)]
pub struct SArm {
    pub pattern: Option<SPattern>,
    pub guard: Option<SExpr>,
    pub result: SExpr,
}

// ── Patterns (§4) ────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq)]
pub enum SPattern {
    /// A numeric literal (incl. `-NUMBER`).
    Number(Rational),
    /// A string literal.
    Str(Vec<u16>),
    /// A prelude constant used as a literal pattern: `true`/`false`/`null`.
    Prelude(String),
    /// A fresh binding (lowercase-initial identifier).
    Bind(String),
    /// `_` wildcard.
    Wild,
    /// `^name` pin — equality to an existing binding (arm patterns only).
    Pin(String),
    /// `^_` / `^_n` — the one-level hask escape (arm blocks in hasks only).
    PinHole(Hole),
    /// A contract-as-pattern: a capitalized identifier that must resolve to a
    /// contract (the convention's one job — checked later).
    Contract(String),
    /// `[ ... ]` tuple pattern (middle rests legal).
    Tuple(Vec<SPatElem>),
    /// `{ ... }` record pattern; `exact` unless a rest opens it.
    Record(Vec<SPatField>, bool),
    /// `p1 | p2 | …` — binding-free alternation.
    Alt(Vec<SPattern>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum SPatElem {
    Pat(SPattern),
    /// `..._` ignores, `...name` captures.
    Rest(Option<String>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum SPatField {
    /// `{ key }` (shorthand bind) or `{ key: pat }`.
    Field(String, Option<SPattern>),
    Rest(Option<String>),
}

// ── Statements and declarations (§2) ─────────────────────────────────────────

#[derive(Clone, Debug, PartialEq)]
pub enum SStmt {
    Binding(SBinding),
    Expr(SExpr),
    Import { names: Option<Vec<String>>, module: Vec<String> },
    At(SAt),
    Mutation { path: SPath, op: MutOp, value: SExpr },
    /// Block-body arm `when guard => result`.
    WhenArm { guard: SExpr, result: SExpr },
    /// Block-body arm `=> result`.
    ElseArm { result: SExpr },
    /// Name-level `where` signature assertion (§5).
    Where { name: String, inputs: Vec<SExpr>, ret: SExpr },
}

#[derive(Clone, Debug, PartialEq)]
pub struct SBinding {
    pub target: SBindTarget,
    pub value: SExpr,
    pub exported: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SBindTarget {
    Name(String),
    Tuple(Vec<SPatElem>),
    Record(Vec<SPatField>, bool),
}

/// An `@`-declaration statement (§2.5). `op` is the privileged-operation name
/// (e.g. `effect`, `mutate`, `state`, `reactive`).
#[derive(Clone, Debug, PartialEq)]
pub enum SAt {
    /// `@op name = value` (bound form).
    Binding { op: String, binding: SBinding },
    /// `@op arrow` (anonymous form, e.g. `@reactive () => { ... }`).
    Anon { op: String, arrow: SExpr },
}

/// A mutation target path (§2.4).
#[derive(Clone, Debug, PartialEq)]
pub struct SPath {
    pub root: String,
    pub segments: Vec<SPathSeg>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SPathSeg {
    Field(String),
    Index(SExpr),
    Slice { lo: Option<SExpr>, hi: Option<SExpr> },
}

/// A mutation operator (§2.4). `Assign` is `:=`; the rest are compound.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MutOp {
    Assign, // :=
    Add,    // +:=
    Sub,    // -:=
    Mul,    // *:=
    Div,    // /:=
    Rem,    // %:=
    Pow,    // **:=
    And,    // &&:=
    Or,     // ||:=
    Null,   // ??:=
}
