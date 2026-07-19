//! Per-node evaluation rules (Semantics Companion §3).

use std::collections::HashMap;

use super::canon;
use super::*;

/// Convenience: lex → parse → desugar → evaluate a whole program, returning the
/// value produced by its last statement (used by tests and as the entry shape).
pub fn run_program_value(src: &str) -> Result<ValueRef, Trap> {
    use crate::desugar::Desugarer;
    use crate::lex::lex;
    use crate::parse::parse_program;

    let mut interner = Interner::new();
    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = Desugarer::new(&mut interner).program(&sprogram).expect("desugar ok");

    let mut oracle = Oracle::new(&mut interner);
    oracle.run_module(&module)
}

/// Like [`run_program_value`], but also returns the number of *actual* slot
/// commits — test-observable evidence of the interning-exact equality guard.
pub fn run_program_commits(src: &str) -> Result<(ValueRef, usize), Trap> {
    use crate::desugar::Desugarer;
    use crate::lex::lex;
    use crate::parse::parse_program;

    let mut interner = Interner::new();
    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = Desugarer::new(&mut interner).program(&sprogram).expect("desugar ok");

    let mut oracle = Oracle::new(&mut interner);
    let value = oracle.run_module(&module)?;
    Ok((value, oracle.store.commits))
}

impl<'a> Oracle<'a> {
    /// Evaluate a module's items in order under **effect world** (the entry-file
    /// reading — semantics §2), returning the last statement's produced value.
    pub fn run_module(&mut self, module: &Module) -> Result<ValueRef, Trap> {
        self.run_module_in(module, &Scope::root())
    }

    /// As [`run_module`], but in a caller-supplied environment (so the harness can
    /// pre-install host effects / prelude bindings).
    pub fn run_module_in(&mut self, module: &Module, env: &Env) -> Result<ValueRef, Trap> {
        let mut last = None;
        for item in &module.items {
            last = self.eval_item(item, env, World::Effect)?;
        }
        // An entry program need not end in a value (it may end in an effect
        // statement); report null in that case.
        Ok(last.unwrap_or_else(|| self.interner.null()))
    }

    fn eval_item(&mut self, item: &Item, env: &Env, world: World) -> Result<Option<ValueRef>, Trap> {
        match item {
            Item::Bind(b) => {
                self.eval_bind(b, env, world)?;
                Ok(None)
            }
            Item::SlotDecl(s) => {
                // Allocation is declarative; the initializer is pure (E12).
                let init = self.eval_value(&s.init, env, World::Pure)?;
                let slot = self.store.alloc(init);
                env.define(&s.name, Binding::Slot(slot));
                Ok(None)
            }
            Item::ActBind(ab) => {
                let closure = self.make_closure(&ab.lambda, env);
                env.define(&ab.name, Binding::Value(closure));
                Ok(None)
            }
            Item::Stmt(e) => match self.eval(e, env, world)? {
                Outcome::Produced(v) => Ok(Some(v)),
                Outcome::CompletedWithoutValue => Ok(None),
            },
            Item::Import(_) | Item::Where(_) => Ok(None), // link/metadata only
        }
    }

    /// A binding: mark the name under-initialization, evaluate, then bind. The
    /// under-init marker makes an eager self-reference (`x = x`) trap, while a
    /// lambda that refers to itself is fine (its body is not evaluated yet).
    pub(super) fn eval_bind(&mut self, b: &Bind, env: &Env, world: World) -> Result<(), Trap> {
        if let BindTarget::Name(name) = &b.target {
            env.define(name, Binding::UnderInit);
            let v = self.eval_value(&b.value, env, world)?;
            env.define(name, Binding::Value(v));
            Ok(())
        } else {
            let v = self.eval_value(&b.value, env, world)?;
            let target = match &b.target {
                BindTarget::Pattern(p) => p,
                BindTarget::Name(_) => unreachable!(),
            };
            if !self.match_pattern(target, &v, env)? {
                return Self::trap(
                    TrapClass::RefutedBinding,
                    "destructuring binding did not match its value",
                );
            }
            Ok(())
        }
    }

    // ── Expressions ──────────────────────────────────────────────────────────

    pub(super) fn eval(&mut self, e: &Expr, env: &Env, world: World) -> EvalResult {
        match e {
            Expr::Const(v) => Ok(Outcome::Produced(v.clone())),
            Expr::Ref(r) => self.eval_ref(r, env),
            Expr::Lambda(l) => Ok(Outcome::Produced(self.make_closure(l, env))),
            Expr::PrimOp { op, args } => self.eval_primop(*op, args, env, world),
            Expr::TupleCons(elems) => self.eval_tuple(elems, env, world),
            Expr::RecordCons(fields) => self.eval_record(fields, env, world),
            Expr::Access { target, form, total } => self.eval_access(target, form, *total, env, world),
            Expr::Template(parts) => self.eval_template(parts, env, world),
            Expr::Match(m) => self.eval_match(m, env, world),
            Expr::Apply { callee, args } => self.eval_apply(callee, args, env, world),
            Expr::Write { slot, value } => self.eval_write(slot, value, env, world),
        }
    }

    /// `Write(slot, e)` (§3): legal only in mutator world; evaluate `e` and stage
    /// it into the pending set. Commitment happens at publication.
    fn eval_write(&mut self, slot: &SlotRef, value: &Expr, env: &Env, world: World) -> EvalResult {
        if world != World::Mutator {
            return Self::trap(TrapClass::WorldAdmission, "`:=` is legal only inside a mutator");
        }
        let name = match slot {
            SlotRef::Name(n) => n,
            SlotRef::Location(_) => {
                return Self::trap(TrapClass::UnboundEvaluation, "positional slot refs require §5");
            }
        };
        let slot_id = match env.lookup(name) {
            Some(Binding::Slot(id)) => id,
            Some(_) => return Self::trap(TrapClass::OperationSafety, format!("`{name}` is not a mutable slot")),
            None => return Self::trap(TrapClass::UnboundEvaluation, format!("`{name}` is not bound")),
        };
        let v = self.eval_value(value, env, world)?;
        match &mut self.pending {
            Some(pending) => {
                pending.insert(slot_id, v);
                Ok(Outcome::CompletedWithoutValue)
            }
            None => Self::trap(TrapClass::WorldAdmission, "a write occurred outside a transaction"),
        }
    }

    fn eval_ref(&mut self, r: &Ref, env: &Env) -> EvalResult {
        match r {
            Ref::Immutable(BindingRef::Name(name)) => match env.lookup(name) {
                Some(Binding::Value(v)) => Ok(Outcome::Produced(v)),
                Some(Binding::Slot(slot)) => Ok(Outcome::Produced(self.read_slot(slot))),
                Some(Binding::UnderInit) => Self::trap(
                    TrapClass::UnboundEvaluation,
                    format!("`{name}` is referenced during its own initialization"),
                ),
                None => Self::trap(
                    TrapClass::UnboundEvaluation,
                    format!("`{name}` is not bound"),
                ),
            },
            Ref::Immutable(BindingRef::Positional(_)) | Ref::Location(_) | Ref::Mu(_) => {
                Self::trap(
                    TrapClass::UnboundEvaluation,
                    "canonical/positional references require §5 (not built yet)",
                )
            }
        }
    }

    fn make_closure(&mut self, lambda: &Lambda, env: &Env) -> ValueRef {
        // The identity key: the canonical form if every free variable resolves
        // now, else a unique opaque id (the deferred μ case — see canon.rs).
        let key = match canon::canonicalize(lambda, env) {
            Some(canonical) => FnKey::Canonical(canonical),
            None => {
                self.opaque_counter += 1;
                FnKey::Opaque(self.opaque_counter)
            }
        };
        let closure = Closure { lambda: lambda.clone(), env: env.clone() };
        self.interner.function(FnValue::new(closure, key))
    }

    // ── Primitive operations (§3) ────────────────────────────────────────────

    fn eval_primop(&mut self, op: PrimOp, args: &[Expr], env: &Env, world: World) -> EvalResult {
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            vals.push(self.eval_value(a, env, world)?);
        }

        // Indeterminate propagation: arithmetic with an Indeterminate operand
        // yields the left-most Indeterminate unchanged. Ordering/numeric-demand
        // ops instead trap; `==`/`!=` treat it as an ordinary value.
        let is_arith = matches!(
            op,
            PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Rem | PrimOp::Pow | PrimOp::Neg
        );
        if is_arith
            && let Some(ind) = vals.iter().find(|v| v.as_indeterminate().is_some())
        {
            return Ok(Outcome::Produced(ind.clone()));
        }

        let result = match op {
            PrimOp::Neg => {
                let n = self.demand_number(&vals[0])?;
                self.interner.number(-n)
            }
            PrimOp::Add => return self.eval_add(&vals[0], &vals[1]).map(Outcome::Produced),
            PrimOp::Sub => self.num_binop(&vals, |a, b| a - b)?,
            PrimOp::Mul => self.num_binop(&vals, |a, b| a * b)?,
            PrimOp::Div => return self.eval_div(&vals[0], &vals[1]).map(Outcome::Produced),
            PrimOp::Rem => return self.eval_rem(&vals[0], &vals[1]).map(Outcome::Produced),
            PrimOp::Pow => return self.eval_pow(&vals[0], &vals[1]).map(Outcome::Produced),
            PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge => {
                return self.eval_compare(op, &vals[0], &vals[1]).map(Outcome::Produced);
            }
            PrimOp::Eq => {
                let b = vals[0].ptr_eq(&vals[1]);
                self.interner.boolean(b)
            }
            PrimOp::Ne => {
                let b = !vals[0].ptr_eq(&vals[1]);
                self.interner.boolean(b)
            }
        };
        Ok(Outcome::Produced(result))
    }

    fn demand_number(&self, v: &ValueRef) -> Result<Rational, Trap> {
        match v.as_number() {
            Some(n) => Ok(n.clone()),
            None => Self::trap(TrapClass::OperationSafety, "expected a Number operand"),
        }
    }

    fn num_binop(
        &mut self,
        vals: &[ValueRef],
        f: impl Fn(Rational, Rational) -> Rational,
    ) -> Result<ValueRef, Trap> {
        let a = self.demand_number(&vals[0])?;
        let b = self.demand_number(&vals[1])?;
        Ok(self.interner.number(f(a, b)))
    }

    /// `+`: numeric addition, or string concatenation when both are Strings.
    fn eval_add(&mut self, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        match (a.data(), b.data()) {
            (ValueData::Number(x), ValueData::Number(y)) => {
                Ok(self.interner.number(x.clone() + y.clone()))
            }
            (ValueData::Str(x), ValueData::Str(y)) => {
                let mut units = x.clone();
                units.extend_from_slice(y);
                Ok(self.interner.string_units(units))
            }
            _ => Self::trap(
                TrapClass::OperationSafety,
                "`+` requires two Numbers or two Strings",
            ),
        }
    }

    fn eval_div(&mut self, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        let x = self.demand_number(a)?;
        let y = self.demand_number(b)?;
        if y.is_zero() {
            // Total division: x/0 ⇒ Indeterminate.
            let form = if x.is_zero() { IndetForm::ZeroOverZero } else { IndetForm::DivByZero };
            return Ok(self.interner.indeterminate(form));
        }
        Ok(self.interner.number(x / y))
    }

    fn eval_rem(&mut self, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        let x = self.demand_number(a)?;
        let y = self.demand_number(b)?;
        if y.is_zero() {
            let form = if x.is_zero() { IndetForm::ZeroOverZero } else { IndetForm::DivByZero };
            return Ok(self.interner.indeterminate(form));
        }
        // Exact rational remainder: x - y*trunc(x/y) (truncation toward zero).
        let xr = x.as_ratio().clone();
        let yr = y.as_ratio().clone();
        let q = (xr.clone() / yr.clone()).trunc();
        let r = xr - yr * q;
        Ok(self.interner.number(Rational::from_ratio(r)))
    }

    fn eval_pow(&mut self, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        let base = self.demand_number(a)?;
        let exp = self.demand_number(b)?;
        // PoC supports integer exponents only (irrational-producing ops omitted).
        if !exp.is_integer() {
            return Self::trap(
                TrapClass::OperationSafety,
                "non-integer exponents are outside the PoC (would be irrational)",
            );
        }
        let e = exp.as_ratio().numer().clone();
        let result = pow_int(base.as_ratio(), &e);
        match result {
            Some(r) => Ok(self.interner.number(Rational::from_ratio(r))),
            None => Self::trap(TrapClass::OperationSafety, "0 raised to a negative power is undefined"),
        }
    }

    fn eval_compare(&mut self, op: PrimOp, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        if a.as_indeterminate().is_some() || b.as_indeterminate().is_some() {
            return Self::trap(
                TrapClass::UndischargedIndeterminate,
                "an ordering comparison received an Indeterminate operand",
            );
        }
        let x = self.demand_number(a)?;
        let y = self.demand_number(b)?;
        let ord = x.as_ratio().cmp(y.as_ratio());
        let b = match op {
            PrimOp::Lt => ord.is_lt(),
            PrimOp::Le => ord.is_le(),
            PrimOp::Gt => ord.is_gt(),
            PrimOp::Ge => ord.is_ge(),
            _ => unreachable!(),
        };
        Ok(self.interner.boolean(b))
    }

    // ── Construction ─────────────────────────────────────────────────────────

    fn eval_tuple(&mut self, elems: &[Element], env: &Env, world: World) -> EvalResult {
        let mut items = Vec::new();
        for el in elems {
            match el {
                Element::Expr(e) => items.push(self.eval_value(e, env, world)?),
                Element::Spread(e) => {
                    let v = self.eval_value(e, env, world)?;
                    match v.as_tuple() {
                        Some(t) => items.extend_from_slice(t),
                        None => {
                            return Self::trap(TrapClass::SpreadKind, "tuple spread of a non-Tuple");
                        }
                    }
                }
            }
        }
        Ok(Outcome::Produced(self.interner.tuple(items)))
    }

    fn eval_record(&mut self, fields: &[Field], env: &Env, world: World) -> EvalResult {
        let mut pairs: Vec<(Vec<u16>, ValueRef)> = Vec::new();
        for field in fields {
            match field {
                Field::Field { key, value } => {
                    let v = self.eval_value(value, env, world)?;
                    pairs.push((key.encode_utf16().collect(), v));
                }
                Field::Computed { key, value } => {
                    let k = self.eval_value(key, env, world)?;
                    let units = match k.as_str_units() {
                        Some(u) => u.to_vec(),
                        None => {
                            return Self::trap(TrapClass::ComputedKey, "computed record key is not a String");
                        }
                    };
                    let v = self.eval_value(value, env, world)?;
                    pairs.push((units, v));
                }
                Field::Spread(e) => {
                    let v = self.eval_value(e, env, world)?;
                    match v.as_record() {
                        Some(entries) => {
                            for entry in entries {
                                pairs.push((entry.key.clone(), entry.value.clone()));
                            }
                        }
                        None => {
                            return Self::trap(TrapClass::SpreadKind, "record spread of a non-Record");
                        }
                    }
                }
            }
        }
        Ok(Outcome::Produced(self.interner.record(pairs)))
    }

    // ── Access (§3) ──────────────────────────────────────────────────────────

    fn eval_access(
        &mut self,
        target: &Expr,
        form: &AccessForm,
        total: bool,
        env: &Env,
        world: World,
    ) -> EvalResult {
        let recv = self.eval_value(target, env, world)?;
        match form {
            AccessForm::Field(name) => self.access_field(&recv, name, total),
            AccessForm::Index(idx) => {
                let index = self.eval_value(idx, env, world)?;
                self.access_index(&recv, &index, total)
            }
            AccessForm::Slice { lo, hi } => {
                let lo = self.eval_opt(lo, env, world)?;
                let hi = self.eval_opt(hi, env, world)?;
                self.access_slice(&recv, lo, hi)
            }
        }
    }

    fn eval_opt(&mut self, e: &Option<Box<Expr>>, env: &Env, world: World) -> Result<Option<ValueRef>, Trap> {
        match e {
            Some(inner) => Ok(Some(self.eval_value(inner, env, world)?)),
            None => Ok(None),
        }
    }

    fn access_field(&mut self, recv: &ValueRef, name: &str, total: bool) -> EvalResult {
        if recv.is_null() {
            return if total {
                Ok(Outcome::Produced(self.interner.null()))
            } else {
                Self::trap(TrapClass::NullReceiver, format!("null receiver for field `{name}`"))
            };
        }
        let key: Vec<u16> = name.encode_utf16().collect();
        if let Some(entries) = recv.as_record()
            && let Some(entry) = entries.iter().find(|e| e.key == key)
        {
            return Ok(Outcome::Produced(entry.value.clone()));
        }
        if total {
            Ok(Outcome::Produced(self.interner.null()))
        } else {
            Self::trap(TrapClass::AbsentField, format!("field `{name}` is absent"))
        }
    }

    fn access_index(&mut self, recv: &ValueRef, index: &ValueRef, total: bool) -> EvalResult {
        if recv.is_null() {
            return if total {
                Ok(Outcome::Produced(self.interner.null()))
            } else {
                Self::trap(TrapClass::NullReceiver, "null receiver for index")
            };
        }
        // Record with a String key behaves like a field access.
        if let (Some(entries), Some(units)) = (recv.as_record(), index.as_str_units()) {
            if let Some(entry) = entries.iter().find(|e| e.key == units) {
                return Ok(Outcome::Produced(entry.value.clone()));
            }
            return self.index_miss(total, "key is absent");
        }

        let i = match self.as_index(index) {
            Some(i) => i,
            None => {
                return if total {
                    Ok(Outcome::Produced(self.interner.null()))
                } else {
                    Self::trap(TrapClass::IndexBounds, "index is not an integer")
                };
            }
        };

        if let Some(items) = recv.as_tuple() {
            return match normalize_index(i, items.len()) {
                Some(k) => Ok(Outcome::Produced(items[k].clone())),
                None => self.index_miss(total, "tuple index out of bounds"),
            };
        }
        if let Some(units) = recv.as_str_units() {
            let graphemes = grapheme_slices(units);
            return match normalize_index(i, graphemes.len()) {
                Some(k) => {
                    let g = graphemes[k].to_vec();
                    Ok(Outcome::Produced(self.interner.string_units(g)))
                }
                None => self.index_miss(total, "string index out of bounds"),
            };
        }
        self.index_miss(total, "value is not indexable")
    }

    fn index_miss(&mut self, total: bool, msg: &str) -> EvalResult {
        if total {
            Ok(Outcome::Produced(self.interner.null()))
        } else {
            Self::trap(TrapClass::IndexBounds, msg.to_string())
        }
    }

    fn access_slice(&mut self, recv: &ValueRef, lo: Option<ValueRef>, hi: Option<ValueRef>) -> EvalResult {
        // Slices are always total and clamped (E7).
        let lo_i = self.opt_index(&lo)?;
        let hi_i = self.opt_index(&hi)?;

        if let Some(items) = recv.as_tuple() {
            let items = items.to_vec();
            let (a, b) = clamp_window(lo_i, hi_i, items.len());
            return Ok(Outcome::Produced(self.interner.tuple(items[a..b].to_vec())));
        }
        if let Some(units) = recv.as_str_units() {
            let graphemes = grapheme_slices(units);
            let (a, b) = clamp_window(lo_i, hi_i, graphemes.len());
            let joined: Vec<u16> = graphemes[a..b].concat();
            return Ok(Outcome::Produced(self.interner.string_units(joined)));
        }
        Self::trap(TrapClass::OperationSafety, "value is not sliceable")
    }

    fn opt_index(&self, v: &Option<ValueRef>) -> Result<Option<i64>, Trap> {
        match v {
            None => Ok(None),
            Some(v) => match self.as_index(v) {
                Some(i) => Ok(Some(i)),
                None => Self::trap(TrapClass::IndexBounds, "slice bound is not an integer"),
            },
        }
    }

    fn as_index(&self, v: &ValueRef) -> Option<i64> {
        let n = v.as_number()?;
        if !n.is_integer() {
            return None;
        }
        n.as_ratio().numer().to_i64()
    }

    // ── Template (§3) ────────────────────────────────────────────────────────

    fn eval_template(&mut self, parts: &[TemplatePart], env: &Env, world: World) -> EvalResult {
        let mut out: Vec<u16> = Vec::new();
        for part in parts {
            match part {
                TemplatePart::Segment(s) => out.extend(s.encode_utf16()),
                TemplatePart::Interp(e) => {
                    let v = self.eval_value(e, env, world)?;
                    let s = self.stringify(&v)?;
                    out.extend(s.encode_utf16());
                }
            }
        }
        Ok(Outcome::Produced(self.interner.string_units(out)))
    }

    fn stringify(&self, v: &ValueRef) -> Result<String, Trap> {
        match v.data() {
            ValueData::Str(u) => Ok(String::from_utf16_lossy(u)),
            ValueData::Number(n) => Ok(n.to_string()),
            ValueData::Boolean(b) => Ok(b.to_string()),
            ValueData::Null => Ok("null".to_string()),
            _ => Self::trap(
                TrapClass::UnprintableInterpolation,
                "structure interpolation is unruled (deliberately trapped — E11)",
            ),
        }
    }

    // ── Application (pure fragment; worlds/staging in 3c) ─────────────────────

    /// Evaluate call arguments left-to-right, splicing spreads (E3). A spread of
    /// a non-Tuple traps `spread-kind`.
    fn eval_args(&mut self, args: &[Arg], env: &Env, world: World) -> Result<Vec<ValueRef>, Trap> {
        let mut arg_vals = Vec::new();
        for a in args {
            match a {
                Arg::Expr(e) => arg_vals.push(self.eval_value(e, env, world)?),
                Arg::Spread(e) => {
                    let v = self.eval_value(e, env, world)?;
                    match v.as_tuple() {
                        Some(t) => arg_vals.extend_from_slice(t),
                        None => return Self::trap(TrapClass::SpreadKind, "argument spread of a non-Tuple"),
                    }
                }
            }
        }
        Ok(arg_vals)
    }

    fn eval_apply(&mut self, callee: &Expr, args: &[Arg], env: &Env, world: World) -> EvalResult {
        let callee_v = self.eval_value(callee, env, world)?;
        let arg_vals = self.eval_args(args, env, world)?;

        // A host effect: run its native (Rust) body directly (semantics §4).
        if let Some(native) = callee_v.as_native() {
            let native = native.clone();
            let kind = native.get().act_kind;
            if !world.admits(kind) {
                return Self::trap(
                    TrapClass::WorldAdmission,
                    format!("a {kind:?} host effect is not admitted in {world:?} world"),
                );
            }
            return match (native.get().imp)(self.interner, &arg_vals) {
                Ok(v) => Ok(Outcome::Produced(v)),
                Err(msg) => Self::trap(TrapClass::OperationSafety, msg),
            };
        }

        let closure = match callee_v.as_closure() {
            Some(c) => c,
            None => return Self::trap(TrapClass::OperationSafety, "callee is not a function"),
        };

        let callee_kind = closure.lambda.act_kind;
        if !world.admits(callee_kind) {
            return Self::trap(
                TrapClass::WorldAdmission,
                format!("a {callee_kind:?} call is not admitted in {world:?} world"),
            );
        }

        // Bind the complete argument tuple against the parameter pattern (the
        // arity model); parameter binding is pure and happens before any staging.
        let arg_tuple = self.interner.tuple(arg_vals);
        let call_env = Scope::child(&closure.env);
        if !self.match_pattern(&closure.lambda.params, &arg_tuple, &call_env)? {
            return Self::trap(
                TrapClass::ArgumentObligation,
                "arguments do not match the parameter pattern",
            );
        }
        let body = closure.lambda.body.clone();

        match callee_kind {
            ActKind::Pure => self.eval(&body, &call_env, World::Pure),
            ActKind::Effect => self.eval(&body, &call_env, World::Effect),
            ActKind::Mutator => self.apply_mutator(&body, &call_env, world),
        }
    }

    /// Apply a mutator callee (semantics §3): from mutator world **join** the
    /// current transaction; from effect world **begin** one, run the body, and on
    /// completion **publish**. Either way the Apply's own outcome is
    /// `CompletedWithoutValue` (current law: mutator returns are discarded).
    fn apply_mutator(&mut self, body: &Expr, call_env: &Env, world: World) -> EvalResult {
        match world {
            World::Mutator => {
                // Join: same pending set; writes accumulate, no publish here.
                self.eval(body, call_env, World::Mutator)?;
                Ok(Outcome::CompletedWithoutValue)
            }
            World::Effect => {
                // Begin a transaction (π := ∅), run, and publish on completion.
                let saved = self.pending.take();
                self.pending = Some(HashMap::new());
                match self.eval(body, call_env, World::Mutator) {
                    Ok(_) => {
                        self.publish(); // commit staged-and-changed slots as one event
                        self.pending = saved;
                        Ok(Outcome::CompletedWithoutValue)
                    }
                    Err(trap) => {
                        // A trap is a halt, not completion — publish nothing (§5).
                        self.pending = saved;
                        Err(trap)
                    }
                }
            }
            World::Pure => unreachable!("admission matrix rejects mutator-in-pure"),
        }
    }
}

/// Integer power of a rational. Returns `None` for `0` to a negative power.
fn pow_int(base: &num_rational::BigRational, exp: &BigInt) -> Option<num_rational::BigRational> {
    use num_traits::One;
    if exp.is_zero() {
        return Some(num_rational::BigRational::one());
    }
    let neg = exp.is_negative();
    let mut n = exp.abs();
    let mut acc = num_rational::BigRational::one();
    let mut b = base.clone();
    let two = BigInt::from(2);
    while n > BigInt::zero() {
        if (&n % &two) == BigInt::one() {
            acc *= &b;
        }
        b = &b * &b;
        n /= &two;
    }
    if neg {
        if acc.is_zero() {
            return None;
        }
        Some(num_rational::BigRational::one() / acc)
    } else {
        Some(acc)
    }
}

/// Normalize a possibly-negative index against a length; `None` if out of bounds.
fn normalize_index(i: i64, len: usize) -> Option<usize> {
    let len = len as i64;
    let k = if i < 0 { len + i } else { i };
    if k >= 0 && k < len { Some(k as usize) } else { None }
}

/// Normalize and clamp a half-open slice window `[lo, hi)` to `[0, len]`.
fn clamp_window(lo: Option<i64>, hi: Option<i64>, len: usize) -> (usize, usize) {
    let len_i = len as i64;
    let norm = |x: i64| if x < 0 { len_i + x } else { x };
    let mut a = lo.map(norm).unwrap_or(0).clamp(0, len_i);
    let mut b = hi.map(norm).unwrap_or(len_i).clamp(0, len_i);
    if b < a {
        b = a; // empty window
    }
    a = a.min(len_i);
    (a as usize, b as usize)
}

/// Split a UTF-16 unit string into grapheme clusters (UAX #29), each as its own
/// unit vector. The pinned `unicode-segmentation` fixes the table version.
fn grapheme_slices(units: &[u16]) -> Vec<Vec<u16>> {
    let s = String::from_utf16_lossy(units);
    s.graphemes(true).map(|g| g.encode_utf16().collect()).collect()
}
