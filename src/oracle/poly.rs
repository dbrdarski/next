//! Polynomial normal form over pure arithmetic bodies (μ-Canonicalization Spec
//! §6, the frozen `==`-set item H-05: `x => x + x == x => 2 * x`).
//!
//! Applied to a function **shape** (after α/capture canonicalization), this
//! rewrites arithmetic subterms into a canonical polynomial form so that
//! algebraically-equal bodies share a shape and thus compare `==`. It handles
//! `+ - *`, unary `-`, division by a nonzero *constant*, and a nonnegative
//! integer constant power; every other subterm is an **atom** (a variable in the
//! polynomial) whose own children are normalized recursively. This is sound:
//! only total, exact-rational identities are used — `x/x`, `x % y`, `x/0`, and
//! variable/negative powers are left untouched, so no partial operation is
//! equated with a total one.
//!
//! Evaluation is unaffected: shapes drive identity only; closures evaluate their
//! original body.

use std::collections::BTreeMap;

use num_traits::One;

use crate::ast::*;
use crate::interner::Interner;
use crate::rational::Rational;

/// A monomial: canonical atom key → exponent. Empty map = the constant term.
type Mono = BTreeMap<String, u32>;
/// A polynomial: monomial → nonzero rational coefficient.
type Poly = BTreeMap<Mono, Rational>;

/// Normalize the arithmetic subterms of a lambda shape.
pub(super) fn normalize_lambda(l: &Lambda, interner: &mut Interner) -> Lambda {
    let mut p = PolyNorm { interner, atoms: BTreeMap::new() };
    Lambda {
        params: l.params.clone(),
        body: Box::new(p.normalize(&l.body)),
        act_kind: l.act_kind,
    }
}

struct PolyNorm<'a> {
    interner: &'a mut Interner,
    /// Atom key → its canonical expression (for reconstruction).
    atoms: BTreeMap<String, Expr>,
}

impl PolyNorm<'_> {
    /// Normalize one expression: build its polynomial and re-emit canonically.
    fn normalize(&mut self, e: &Expr) -> Expr {
        self.atoms.clear();
        let poly = self.build(e);
        self.emit(&poly)
    }

    // ── Polynomial construction ──────────────────────────────────────────────

    fn build(&mut self, e: &Expr) -> Poly {
        match e {
            Expr::Const(v) if v.as_number().is_some() => {
                constant(v.as_number().unwrap().clone())
            }
            Expr::PrimOp { op: PrimOp::Add, args } if args.len() == 2 => {
                let a = self.build(&args[0]);
                let b = self.build(&args[1]);
                add(a, b)
            }
            Expr::PrimOp { op: PrimOp::Sub, args } if args.len() == 2 => {
                let a = self.build(&args[0]);
                let b = neg(self.build(&args[1]));
                add(a, b)
            }
            Expr::PrimOp { op: PrimOp::Neg, args } if args.len() == 1 => {
                neg(self.build(&args[0]))
            }
            Expr::PrimOp { op: PrimOp::Mul, args } if args.len() == 2 => {
                let a = self.build(&args[0]);
                let b = self.build(&args[1]);
                mul(a, b)
            }
            Expr::PrimOp { op: PrimOp::Div, args } if args.len() == 2 => {
                let denom = self.build(&args[1]);
                match constant_value(&denom) {
                    Some(c) if !c.is_zero() => {
                        let num = self.build(&args[0]);
                        scale(num, Rational::from(1) / c)
                    }
                    // Non-constant or zero divisor: not polynomial — an atom.
                    _ => self.atom(e),
                }
            }
            Expr::PrimOp { op: PrimOp::Pow, args } if args.len() == 2 => {
                match integer_exponent(&args[1]) {
                    Some(k) => {
                        let base = self.build(&args[0]);
                        powi(base, k)
                    }
                    None => self.atom(e),
                }
            }
            _ => self.atom(e),
        }
    }

    /// Treat `e` as an opaque variable — normalize its children, then register it.
    fn atom(&mut self, e: &Expr) -> Poly {
        let canonical = self.normalize_children(e);
        let key = serialize(&canonical);
        self.atoms.entry(key.clone()).or_insert(canonical);
        let mut mono = Mono::new();
        mono.insert(key, 1);
        let mut poly = Poly::new();
        poly.insert(mono, Rational::from(1));
        poly
    }

    // ── Reconstruction ───────────────────────────────────────────────────────

    fn emit(&mut self, poly: &Poly) -> Expr {
        if poly.is_empty() {
            return Expr::Const(self.interner.number(Rational::from(0)));
        }
        let mut terms = poly.iter().map(|(m, c)| self.term_expr(m, c));
        let first = terms.next().unwrap();
        terms.fold(first, |acc, t| prim(PrimOp::Add, acc, t))
    }

    fn term_expr(&mut self, mono: &Mono, coeff: &Rational) -> Expr {
        // Product of atom^exp, atoms in canonical (key) order.
        let mut factors: Vec<Expr> = Vec::new();
        for (key, &exp) in mono {
            let atom = self.atoms[key].clone();
            if exp == 1 {
                factors.push(atom);
            } else {
                let e = Expr::Const(self.interner.number(Rational::from(exp as i64)));
                factors.push(prim(PrimOp::Pow, atom, e));
            }
        }
        let product = factors.into_iter().reduce(|acc, f| prim(PrimOp::Mul, acc, f));
        match product {
            None => Expr::Const(self.interner.number(coeff.clone())),
            Some(p) if coeff.as_ratio().is_one() => p,
            Some(p) => {
                let c = Expr::Const(self.interner.number(coeff.clone()));
                prim(PrimOp::Mul, c, p)
            }
        }
    }

    /// Structurally normalize the children of a non-arithmetic node (so
    /// arithmetic nested inside an atom is still canonicalized).
    fn normalize_children(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::Const(_) | Expr::Ref(_) => e.clone(),
            Expr::Lambda(l) => Expr::Lambda(Lambda {
                params: l.params.clone(),
                body: Box::new(self.normalize(&l.body)),
                act_kind: l.act_kind,
            }),
            Expr::Apply { callee, args } => Expr::Apply {
                callee: Box::new(self.normalize(callee)),
                args: args.iter().map(|a| self.norm_arg(a)).collect(),
            },
            Expr::PrimOp { op, args } => Expr::PrimOp {
                op: *op,
                args: args.iter().map(|a| self.normalize(a)).collect(),
            },
            Expr::Match(m) => Expr::Match(self.norm_match(m)),
            Expr::TupleCons(elems) => Expr::TupleCons(elems.iter().map(|el| self.norm_elem(el)).collect()),
            Expr::RecordCons(fields) => Expr::RecordCons(fields.iter().map(|f| self.norm_field(f)).collect()),
            Expr::Access { target, form, total } => Expr::Access {
                target: Box::new(self.normalize(target)),
                form: self.norm_form(form),
                total: *total,
            },
            Expr::Template(parts) => Expr::Template(
                parts
                    .iter()
                    .map(|p| match p {
                        TemplatePart::Segment(s) => TemplatePart::Segment(s.clone()),
                        TemplatePart::Interp(e) => TemplatePart::Interp(self.normalize(e)),
                    })
                    .collect(),
            ),
            Expr::Write { slot, value } => Expr::Write {
                slot: slot.clone(),
                value: Box::new(self.normalize(value)),
            },
        }
    }

    fn norm_arg(&mut self, a: &Arg) -> Arg {
        match a {
            Arg::Expr(e) => Arg::Expr(self.normalize(e)),
            Arg::Spread(e) => Arg::Spread(self.normalize(e)),
        }
    }
    fn norm_elem(&mut self, el: &Element) -> Element {
        match el {
            Element::Expr(e) => Element::Expr(self.normalize(e)),
            Element::Spread(e) => Element::Spread(self.normalize(e)),
        }
    }
    fn norm_field(&mut self, f: &Field) -> Field {
        match f {
            Field::Field { key, value } => Field::Field { key: key.clone(), value: self.normalize(value) },
            Field::Computed { key, value } => {
                Field::Computed { key: self.normalize(key), value: self.normalize(value) }
            }
            Field::Spread(e) => Field::Spread(self.normalize(e)),
        }
    }
    fn norm_form(&mut self, form: &AccessForm) -> AccessForm {
        match form {
            AccessForm::Field(n) => AccessForm::Field(n.clone()),
            AccessForm::Index(e) => AccessForm::Index(Box::new(self.normalize(e))),
            AccessForm::Slice { lo, hi } => AccessForm::Slice {
                lo: lo.as_ref().map(|e| Box::new(self.normalize(e))),
                hi: hi.as_ref().map(|e| Box::new(self.normalize(e))),
            },
        }
    }
    fn norm_match(&mut self, m: &Match) -> Match {
        Match {
            scrutinee: m.scrutinee.as_ref().map(|e| Box::new(self.normalize(e))),
            items: m
                .items
                .iter()
                .map(|item| match item {
                    MatchItem::Bind(b) => MatchItem::Bind(Bind {
                        target: b.target.clone(),
                        value: self.normalize(&b.value),
                        exported: b.exported,
                    }),
                    MatchItem::Stmt(e) => MatchItem::Stmt(self.normalize(e)),
                    MatchItem::Arm(arm) => MatchItem::Arm(Arm {
                        pattern: arm.pattern.clone(),
                        guard: arm.guard.as_ref().map(|g| self.normalize(g)),
                        result: self.normalize(&arm.result),
                    }),
                })
                .collect(),
        }
    }
}

fn prim(op: PrimOp, a: Expr, b: Expr) -> Expr {
    Expr::PrimOp { op, args: vec![a, b] }
}

// ── Polynomial arithmetic ────────────────────────────────────────────────────

fn constant(c: Rational) -> Poly {
    let mut p = Poly::new();
    if !c.is_zero() {
        p.insert(Mono::new(), c);
    }
    p
}

/// If `p` is a pure constant, return its value (0 for the empty polynomial).
fn constant_value(p: &Poly) -> Option<Rational> {
    match p.len() {
        0 => Some(Rational::from(0)),
        1 => p.get(&Mono::new()).cloned(),
        _ => None,
    }
}

fn integer_exponent(e: &Expr) -> Option<u32> {
    let n = match e {
        Expr::Const(v) => v.as_number()?,
        _ => return None,
    };
    if !n.is_integer() || n.as_ratio().numer().sign() == num_bigint::Sign::Minus {
        return None;
    }
    u32::try_from(n.as_ratio().numer().clone()).ok()
}

fn insert_term(p: &mut Poly, mono: Mono, coeff: Rational) {
    if coeff.is_zero() {
        return;
    }
    let entry = p.entry(mono).or_insert_with(|| Rational::from(0));
    *entry = entry.clone() + coeff;
    // Cancellation to zero is swept up by `prune_zeros` at the end of add/mul.
}

fn add(a: Poly, b: Poly) -> Poly {
    let mut out = a;
    for (m, c) in b {
        insert_term(&mut out, m, c);
    }
    prune_zeros(out)
}

fn neg(a: Poly) -> Poly {
    a.into_iter().map(|(m, c)| (m, -c)).collect()
}

fn scale(a: Poly, factor: Rational) -> Poly {
    if factor.is_zero() {
        return Poly::new();
    }
    a.into_iter().map(|(m, c)| (m, c * factor.clone())).collect()
}

fn mul(a: Poly, b: Poly) -> Poly {
    let mut out = Poly::new();
    for (m1, c1) in &a {
        for (m2, c2) in &b {
            let mut mono = m1.clone();
            for (k, e) in m2 {
                *mono.entry(k.clone()).or_insert(0) += e;
            }
            insert_term(&mut out, mono, c1.clone() * c2.clone());
        }
    }
    prune_zeros(out)
}

fn powi(base: Poly, k: u32) -> Poly {
    let mut acc = constant(Rational::from(1));
    for _ in 0..k {
        acc = mul(acc, base.clone());
    }
    acc
}

fn prune_zeros(p: Poly) -> Poly {
    p.into_iter().filter(|(_, c)| !c.is_zero()).collect()
}

// ── Canonical serialization of atoms ─────────────────────────────────────────

fn serialize(e: &Expr) -> String {
    let mut s = String::new();
    ser(e, &mut s);
    s
}

fn ser(e: &Expr, out: &mut String) {
    match e {
        Expr::Const(v) => out.push_str(&format!("c{}", v.addr())),
        Expr::Ref(r) => match r {
            Ref::Immutable(BindingRef::Name(n)) => out.push_str(&format!("rn{n};")),
            Ref::Immutable(BindingRef::Positional(i)) => out.push_str(&format!("rp{i};")),
            Ref::Location(l) => out.push_str(&format!("rl{};", l.0)),
            Ref::Mu(m) => out.push_str(&format!("rm{};", m.0)),
        },
        Expr::Lambda(l) => {
            out.push_str("L{");
            ser_pat(&l.params, out);
            out.push(';');
            ser(&l.body, out);
            out.push_str(&format!(";{:?}}}", l.act_kind));
        }
        Expr::Apply { callee, args } => {
            out.push_str("A(");
            ser(callee, out);
            for a in args {
                match a {
                    Arg::Expr(e) => ser(e, out),
                    Arg::Spread(e) => {
                        out.push('*');
                        ser(e, out);
                    }
                }
                out.push(',');
            }
            out.push(')');
        }
        Expr::PrimOp { op, args } => {
            out.push_str(&format!("P{op:?}("));
            for a in args {
                ser(a, out);
                out.push(',');
            }
            out.push(')');
        }
        Expr::Match(m) => {
            out.push_str("M(");
            if let Some(s) = &m.scrutinee {
                ser(s, out);
            }
            out.push_str(&format!("#{})", m.items.len()));
        }
        Expr::TupleCons(elems) => {
            out.push_str("T(");
            for el in elems {
                match el {
                    Element::Expr(e) => ser(e, out),
                    Element::Spread(e) => {
                        out.push('*');
                        ser(e, out);
                    }
                }
                out.push(',');
            }
            out.push(')');
        }
        Expr::RecordCons(fields) => {
            out.push_str(&format!("D#{}", fields.len()));
        }
        Expr::Access { target, form, total } => {
            out.push_str(&format!("X{total}("));
            ser(target, out);
            match form {
                AccessForm::Field(n) => out.push_str(&format!(".{n}")),
                AccessForm::Index(e) => {
                    out.push('[');
                    ser(e, out);
                    out.push(']');
                }
                AccessForm::Slice { .. } => out.push_str("[..]"),
            }
            out.push(')');
        }
        Expr::Template(parts) => out.push_str(&format!("S#{}", parts.len())),
        Expr::Write { slot, value } => {
            out.push_str("W(");
            match slot {
                SlotRef::Name(n) => out.push_str(&format!("n{n}")),
                SlotRef::Location(l) => out.push_str(&format!("l{}", l.0)),
            }
            ser(value, out);
            out.push(')');
        }
    }
}

fn ser_pat(p: &Pat, out: &mut String) {
    match p {
        Pat::Const(v) => out.push_str(&format!("pc{}", v.addr())),
        Pat::Bind(n) => out.push_str(&format!("pb{n};")),
        Pat::Wild => out.push('_'),
        Pat::Tuple(elems) => {
            out.push_str("pt(");
            for e in elems {
                match e {
                    PatElem::Pat(p) => ser_pat(p, out),
                    PatElem::Rest(r) => out.push_str(&format!("...{}", r.as_deref().unwrap_or("_"))),
                }
                out.push(',');
            }
            out.push(')');
        }
        Pat::Record { fields, exact } => out.push_str(&format!("pr{}#{}", exact, fields.len())),
        Pat::Contract(r) => {
            out.push_str("pk");
            ser(&Expr::Ref(r.clone()), out);
        }
    }
}
