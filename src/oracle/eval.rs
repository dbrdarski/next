//! Per-node evaluation rules (Semantics Companion §3).

use std::collections::HashMap;
use std::rc::Rc;

use super::canon;
use super::*;

/// Convenience: lex → parse → desugar → evaluate a whole program, returning the
/// value produced by its last statement (used by tests and as the entry shape).
pub fn run_program_value(src: &str) -> Result<ValueRef, Trap> {
    use crate::lex::lex;
    use crate::parse::parse_program;

    let mut interner = Interner::new();
    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = crate::desugar::lower_program(&sprogram, &mut interner).expect("desugar ok");

    let env = super::harness::prelude_env(&mut interner);
    let mut oracle = Oracle::new(&mut interner);
    oracle.run_module_in(&module, &env)
}

/// Apply a primitive operation to concrete operand values, returning the produced
/// value or a [`Trap`]. This exposes the oracle's value-level primop semantics as
/// the truth source for the analyzer's operation rules (C§7): the analyzer's
/// `analyze_operation` is brute-tested to over-approximate this and to agree on
/// operation-safety. Primops always produce (never suspend), so a non-`Produced`
/// outcome is unreachable.
pub fn eval_prim(op: PrimOp, args: &[ValueRef], interner: &mut Interner) -> Result<ValueRef, Trap> {
    let mut oracle = Oracle::new(interner);
    match oracle.apply_prim(op, args)? {
        Outcome::Produced(v) => Ok(v),
        _ => unreachable!("primops always produce a value"),
    }
}

/// Evaluate a single closed kernel expression in an empty environment under the
/// **pure world**, returning its outcome or a [`Trap`]. This is the truth source
/// the analyzer's pure-fragment checker (§6 concordance) is tested against: an
/// accepted expression must not trap.
pub fn eval_expr(expr: &Expr, interner: &mut Interner) -> EvalResult {
    let mut oracle = Oracle::new(interner);
    oracle.eval(expr, &crate::env::Scope::root(), World::Pure)
}

/// The outcome of a **fuel-bounded** pure evaluation ([`eval_expr_bounded`]) — the
/// completion triple plus the two halts a bounded run distinguishes: a genuine language
/// `Trapped` (§6) and `OutOfFuel` (a non-completing input the bound cut off — a machine
/// limit, never a witness against a return bound, §6).
#[derive(Clone, Debug)]
pub enum BoundedOutcome {
    Produced(ValueRef),
    CompletedWithoutValue,
    Trapped(Trap),
    OutOfFuel,
}

/// Evaluate a closed pure expression under a `fuel`-step bound. Used by the analyzer's
/// realized-witness refutation to run a concrete input to completion *safely*: a
/// diverging input exhausts the bound and yields `OutOfFuel` rather than hanging.
pub fn eval_expr_bounded(expr: &Expr, fuel: u64, interner: &mut Interner) -> BoundedOutcome {
    let mut oracle = Oracle::new_fueled(interner, fuel);
    match oracle.eval(expr, &crate::env::Scope::root(), World::Pure) {
        _ if oracle.out_of_fuel => BoundedOutcome::OutOfFuel,
        Ok(Outcome::Produced(v)) => BoundedOutcome::Produced(v),
        Ok(Outcome::CompletedWithoutValue) => BoundedOutcome::CompletedWithoutValue,
        Err(t) => BoundedOutcome::Trapped(t),
    }
}

/// A fuel-bounded whole-program run (the M-04 harness verdict). `Diverged` is the
/// **machine-limit** reading of fuel exhaustion (Part A's trap clause — a harness
/// verdict, never a semantic one; fuel stays out of all normative analysis).
/// `commits` counts actual slot publishes, so the row's σ-unchanged claim — a
/// never-completed outer mutator publishes nothing, its joined inner included — is
/// directly observable.
#[derive(Debug)]
pub enum BoundedRun {
    /// Completed with a value, carried as its **canonical literal form** (the total
    /// B2 renderer) — the runner executes on a dedicated big-stack thread, and the
    /// printed form is what crosses it (values are thread-local by design).
    Completed {
        value: String,
        commits: usize,
    },
    Trapped(Trap),
    Diverged {
        commits: usize,
    },
}

/// The bounded runner's recursion allowance, paired with [`BOUNDED_RUN_STACK`]:
/// ≈21 KiB of interpreter stack per call level (measured 2026-08-04, debug build)
/// × 4096 ≈ 86 MiB — a 3× margin under the 256 MiB dedicated thread stack. This is
/// the **harness** calibration; the refutation sampler keeps its own far-lower cap
/// ([`super::FUELED_MAX_CALL_DEPTH`]) on ordinary test threads.
const BOUNDED_RUN_MAX_CALL_DEPTH: u32 = 4096;
const BOUNDED_RUN_STACK: usize = 256 * 1024 * 1024;

/// Run an entry program under a `fuel`-step bound (the test-suite's DIVERGES
/// harness — T3.5). Panics on front-end errors; test-only by design. Runs on a
/// dedicated big-stack thread so recursion depth up to
/// [`BOUNDED_RUN_MAX_CALL_DEPTH`] is real evidence; `Diverged` means **resource
/// exhaustion** (fuel or depth) — not completed, not trapped — never a semantic
/// verdict.
pub fn run_program_bounded(src: &str, fuel: u64) -> BoundedRun {
    let src = src.to_string();
    std::thread::Builder::new()
        .name("bounded-oracle".into())
        .stack_size(BOUNDED_RUN_STACK)
        .spawn(move || run_program_bounded_here(&src, fuel))
        .expect("spawn bounded-oracle thread")
        .join()
        .expect("bounded-oracle thread completes")
}

fn run_program_bounded_here(src: &str, fuel: u64) -> BoundedRun {
    use crate::lex::lex;
    use crate::parse::parse_program;

    let mut interner = Interner::new();
    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = crate::desugar::lower_program(&sprogram, &mut interner).expect("desugar ok");

    let env = super::harness::prelude_env(&mut interner);
    let mut oracle = Oracle::new_fueled_with_depth(&mut interner, fuel, BOUNDED_RUN_MAX_CALL_DEPTH);
    let result = oracle.run_module_in(&module, &env);
    let commits = oracle.store.commits;
    if oracle.out_of_fuel {
        return BoundedRun::Diverged { commits };
    }
    match result {
        Ok(value) => BoundedRun::Completed {
            value: render_value(&value, false),
            commits,
        },
        Err(trap) => BoundedRun::Trapped(trap),
    }
}

/// Like [`run_program_value`], but also returns the number of *actual* slot
/// commits — test-observable evidence of the interning-exact equality guard.
pub fn run_program_commits(src: &str) -> Result<(ValueRef, usize), Trap> {
    use crate::lex::lex;
    use crate::parse::parse_program;

    let mut interner = Interner::new();
    let toks = lex(src).expect("lex ok");
    let sprogram = parse_program(toks).expect("parse ok");
    let module = crate::desugar::lower_program(&sprogram, &mut interner).expect("desugar ok");

    let env = super::harness::prelude_env(&mut interner);
    let mut oracle = Oracle::new(&mut interner);
    let value = oracle.run_module_in(&module, &env)?;
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
        // The C§9 pre-pass (T2.4): recursive named contracts are ordinary static
        // bindings whose references are late-bound within their group, so they are
        // recognized over the whole module before item order runs — mirroring the
        // checker's collect. Only an **admissible** group is consumed (the
        // recursive membership walk terminates on admissible groups only); an
        // inadmissible definition is the checker's rejection, and here the name
        // simply stays unresolved. The in-order item handler skips a bind whose
        // name is already a contract definition.
        {
            let mut pass1 = crate::contract::ContractEnv::new();
            let mut deferred: Vec<(String, Expr)> = Vec::new();
            for item in &module.items {
                if let Item::Bind(b) = item
                    && let crate::ast::BindTarget::Name(name) = &b.target
                    && !matches!(b.value, Expr::Lambda(_))
                {
                    if let Some(c) = crate::contract::eval_contract(&b.value, &pass1, self.interner)
                    {
                        pass1.insert(name.clone(), c);
                    } else {
                        deferred.push((name.clone(), b.value.clone()));
                    }
                }
            }
            if let Ok(defs) =
                crate::contract::eval_recursive_contract_bindings(&deferred, &pass1, self.interner)
            {
                for (name, c) in defs {
                    self.cenv.insert(name, c);
                }
            }
        }
        // A window whose members are all pre-passed contract definitions is not a
        // value-construction group at all — the "self-reference" it saw is the
        // contract's own late-bound Ref, already resolved statically above.
        let groups: Vec<mu::GroupWindow> = module_group_windows(module)
            .into_iter()
            .filter(|group| {
                !group
                    .members
                    .iter()
                    .all(|(_, name)| self.cenv.contains_key(name))
            })
            .collect();
        let mut last = None;
        for (index, item) in module.items.iter().enumerate() {
            for group in groups.iter().filter(|group| group.start == index) {
                self.begin_group(group, env);
            }
            last = if groups
                .iter()
                .any(|group| group.members.iter().any(|(member, _)| *member == index))
            {
                self.eval_open_item(item, env, World::Effect)?
            } else {
                self.eval_item(item, env, World::Effect)?
            };
            for group in groups.iter().filter(|group| group.end == index).rev() {
                self.close_group(group, env)?;
            }
        }
        self.ensure_scope_closed(env)?;
        // An entry program need not end in a value (it may end in an effect
        // statement); report null in that case.
        Ok(last.unwrap_or_else(|| self.interner.null()))
    }

    fn eval_item(
        &mut self,
        item: &Item,
        env: &Env,
        world: World,
    ) -> Result<Option<ValueRef>, Trap> {
        match item {
            Item::Bind(b) => {
                // A non-lambda `Name = <contract expression>` is a **named contract**
                // (E11) — a static binding, evaluated per C§12.2, never a runtime
                // evaluation. Mirrors the checker's rule exactly; the name lives in
                // the oracle's contract environment for contract-as-pattern matching.
                if let crate::ast::BindTarget::Name(name) = &b.target
                    && !matches!(b.value, Expr::Lambda(_))
                {
                    // Already defined by the recursive pre-pass — a static
                    // definition, never a runtime evaluation.
                    if self.cenv.contains_key(name) {
                        return Ok(None);
                    }
                    if let Some(c) =
                        crate::contract::eval_contract(&b.value, &self.cenv, self.interner)
                    {
                        self.cenv.insert(name.clone(), c);
                        return Ok(None);
                    }
                }
                self.eval_bind(b, env, world)?;
                Ok(None)
            }
            Item::SlotDecl(s) => {
                // Allocation is declarative; the initializer is pure (E12).
                let init = self.eval_value(&s.init, env, World::Pure)?;
                let slot = self.store.alloc(init);
                env.define(&s.name, Binding::Slot(slot));
                self.retry_pending_values();
                Ok(None)
            }
            Item::ActBind(ab) => {
                let closure = self.make_closure(&ab.lambda, env);
                self.finish_binding(&ab.name, closure, env);
                Ok(None)
            }
            Item::Stmt(e) => match self.eval(e, env, world)? {
                Outcome::Produced(v) => Ok(Some(v)),
                Outcome::CompletedWithoutValue => Ok(None),
            },
            Item::Import(_) | Item::Where(_) => Ok(None), // link/metadata only
        }
    }

    /// Evaluate one member of a recursive construction group without exposing
    /// the provisional graph as a value. Observation remains illegal because
    /// ordinary references to `Binding::Open` trap until [`close_group`].
    fn eval_open_item(
        &mut self,
        item: &Item,
        env: &Env,
        world: World,
    ) -> Result<Option<ValueRef>, Trap> {
        match item {
            Item::Bind(
                binding @ Bind {
                    target: BindTarget::Name(_),
                    ..
                },
            ) => {
                self.eval_open_bind(binding, env, world)?;
                Ok(None)
            }
            Item::ActBind(ab) => {
                let raw = self.make_closure(&ab.lambda, env);
                env.define(&ab.name, Binding::Open(raw));
                Ok(None)
            }
            _ => self.eval_item(item, env, world),
        }
    }

    pub(super) fn eval_open_bind(
        &mut self,
        binding: &Bind,
        env: &Env,
        world: World,
    ) -> Result<(), Trap> {
        let BindTarget::Name(name) = &binding.target else {
            return self.eval_bind(binding, env, world);
        };
        let raw = self.eval_value(&binding.value, env, world)?;
        env.define(name, Binding::Open(raw));
        Ok(())
    }

    /// A binding: mark the name under-initialization, evaluate, then bind. The
    /// under-init marker makes an eager self-reference (`x = x`) trap, while a
    /// lambda that refers to itself is fine (its body is not evaluated yet).
    pub(super) fn eval_bind(&mut self, b: &Bind, env: &Env, world: World) -> Result<(), Trap> {
        if let BindTarget::Name(name) = &b.target {
            env.define(name, Binding::UnderInit);
            let v = self.eval_value(&b.value, env, world)?;
            self.finish_binding(name, v, env);
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
        // Fuel bound (analyzer refutation only; unlimited by default). Exhaustion is a
        // machine limit, surfaced via `out_of_fuel` and checked at the bounded entry —
        // never a language trap (Part A).
        if self.burn_fuel() {
            return Err(Trap {
                class: TrapClass::OperationSafety,
                message: "evaluation fuel exhausted".into(),
            });
        }
        match e {
            Expr::Const(v) => Ok(Outcome::Produced(v.clone())),
            Expr::Ref(r) => self.eval_ref(r, env),
            Expr::Lambda(l) => Ok(Outcome::Produced(self.make_closure(l, env))),
            Expr::PrimOp { op, args } => self.eval_primop(*op, args, env, world),
            Expr::TupleCons(elems) => self.eval_tuple(elems, env, world),
            Expr::RecordCons(fields) => self.eval_record(fields, env, world),
            Expr::Access {
                target,
                form,
                total,
            } => self.eval_access(target, form, *total, env, world),
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
            return Self::trap(
                TrapClass::WorldAdmission,
                "`:=` is legal only inside a mutator",
            );
        }
        let name = match slot {
            SlotRef::Name(n) => n,
            SlotRef::Location(_) => {
                return Self::trap(
                    TrapClass::UnboundEvaluation,
                    "positional slot refs require §5",
                );
            }
        };
        let slot_id = match env.lookup(name) {
            Some(Binding::Slot(id)) => id,
            Some(_) => {
                return Self::trap(
                    TrapClass::OperationSafety,
                    format!("`{name}` is not a mutable slot"),
                );
            }
            None => {
                return Self::trap(
                    TrapClass::UnboundEvaluation,
                    format!("`{name}` is not bound"),
                );
            }
        };
        let v = self.eval_value(value, env, world)?;
        match &mut self.pending {
            Some(pending) => {
                pending.insert(slot_id, v);
                Ok(Outcome::CompletedWithoutValue)
            }
            None => Self::trap(
                TrapClass::WorldAdmission,
                "a write occurred outside a transaction",
            ),
        }
    }

    fn eval_ref(&mut self, r: &Ref, env: &Env) -> EvalResult {
        match r {
            Ref::Immutable(BindingRef::Name(name)) => match env.lookup(name) {
                Some(Binding::Value(v)) => Ok(Outcome::Produced(v)),
                Some(Binding::Slot(slot)) => Ok(Outcome::Produced(self.read_slot(slot))),
                Some(Binding::Open(_)) | Some(Binding::UnderInit) => Self::trap(
                    TrapClass::UnboundEvaluation,
                    format!("`{name}` is observed before its construction window closes"),
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
        make_closure_in(lambda, env, self.interner)
    }

    pub(super) fn begin_group(&self, group: &mu::GroupWindow, env: &Env) {
        for (_, name) in &group.members {
            env.define(name, Binding::UnderInit);
        }
    }

    pub(super) fn close_group(&mut self, group: &mu::GroupWindow, env: &Env) -> Result<(), Trap> {
        let mut roots = Vec::with_capacity(group.members.len());
        for (_, name) in &group.members {
            let value = match env.lookup(name) {
                Some(Binding::Open(value)) | Some(Binding::Value(value)) => value,
                _ => {
                    return Self::trap(
                        TrapClass::UnboundEvaluation,
                        format!("recursive member `{name}` did not finish construction"),
                    );
                }
            };
            roots.push((name.clone(), value));
        }

        // Resolve every internal marker simultaneously before probing the
        // interner. No member is observable between this promotion and the
        // canonical rebinding below.
        for (name, value) in &roots {
            env.define(name, Binding::Value(value.clone()));
        }
        if roots
            .iter()
            .any(|(_, value)| !self.interner.value_is_closed(value))
        {
            for (name, value) in roots {
                env.define(&name, Binding::Open(value));
            }
            return Self::trap(
                TrapClass::UnboundEvaluation,
                "a recursive construction window closed with an unresolved capture",
            );
        }
        for (name, value) in roots {
            let canonical = self.interner.close_value_graph(value);
            env.define(&name, Binding::Value(canonical));
        }
        self.retry_pending_values();
        Ok(())
    }

    fn finish_binding(&mut self, name: &str, value: ValueRef, env: &Env) {
        if self.interner.value_is_closed(&value) {
            let canonical = self.interner.close_value_graph(value);
            env.define(name, Binding::Value(canonical));
            self.retry_pending_values();
        } else {
            env.define(name, Binding::Open(value.clone()));
            self.pending_values.push(PendingValue {
                name: name.to_string(),
                env: env.clone(),
                value,
            });
        }
    }

    fn retry_pending_values(&mut self) {
        while let Some(index) = self
            .pending_values
            .iter()
            .position(|pending| self.interner.value_is_closed(&pending.value))
        {
            let pending = self.pending_values.remove(index);
            pending
                .env
                .define(&pending.name, Binding::Value(pending.value.clone()));
            let canonical = self.interner.close_value_graph(pending.value);
            pending.env.define(&pending.name, Binding::Value(canonical));
        }
    }

    pub(super) fn ensure_scope_closed(&self, env: &Env) -> Result<(), Trap> {
        if self
            .pending_values
            .iter()
            .any(|pending| Rc::ptr_eq(&pending.env, env))
        {
            return Self::trap(
                TrapClass::UnboundEvaluation,
                "an open value escaped its construction scope",
            );
        }
        Ok(())
    }

    // ── Primitive operations (§3) ────────────────────────────────────────────

    fn eval_primop(&mut self, op: PrimOp, args: &[Expr], env: &Env, world: World) -> EvalResult {
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            vals.push(self.eval_value(a, env, world)?);
        }
        self.apply_prim(op, &vals)
    }

    /// Apply a primitive operation to already-evaluated operand values. This is the
    /// value-level truth source the analyzer's operation rules (C§7) are tested
    /// against — see [`eval_prim`].
    pub(crate) fn apply_prim(&mut self, op: PrimOp, vals: &[ValueRef]) -> EvalResult {
        // Part XII fixes specific Indeterminate identity but leaves its consuming
        // algebra open. Until that algebra is ruled, every consuming numeric seat
        // must demand an ordinary Number. Equality remains total because these are
        // ordinary values.
        if !matches!(op, PrimOp::Eq | PrimOp::Ne)
            && vals.iter().any(|value| value.as_indeterminate().is_some())
        {
            return Self::trap(
                TrapClass::UndischargedIndeterminate,
                "a strict Number operation received an Indeterminate value",
            );
        }

        let result = match op {
            PrimOp::Neg => {
                let n = self.demand_number(&vals[0])?;
                self.interner.number(-n)
            }
            PrimOp::Add => self.num_binop(vals, |a, b| a + b)?,
            PrimOp::Concat => {
                return self.eval_concat(&vals[0], &vals[1]).map(Outcome::Produced);
            }
            PrimOp::Sub => self.num_binop(vals, |a, b| a - b)?,
            PrimOp::Mul => self.num_binop(vals, |a, b| a * b)?,
            PrimOp::Div => return self.eval_div(&vals[0], &vals[1]).map(Outcome::Produced),
            PrimOp::Rem => return self.eval_rem(&vals[0], &vals[1]).map(Outcome::Produced),
            PrimOp::Pow => return self.eval_pow(&vals[0], &vals[1]).map(Outcome::Produced),
            PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge => {
                return self
                    .eval_compare(op, &vals[0], &vals[1])
                    .map(Outcome::Produced);
            }
            PrimOp::Eq => {
                let b = super::equal::values_equal(&vals[0], &vals[1]);
                self.interner.boolean(b)
            }
            PrimOp::Ne => {
                let b = !super::equal::values_equal(&vals[0], &vals[1]);
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

    /// `++`: String concatenation, and only that. Numeric `+` is a separate operator
    /// [author, 2026-08-07] — one token across both rails made commutative reordering
    /// unsound, since concatenation does not commute.
    fn eval_concat(&mut self, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        match (a.data(), b.data()) {
            (ValueData::Str(x), ValueData::Str(y)) => {
                let mut units = x.clone();
                units.extend_from_slice(y);
                Ok(self.interner.string_units(units))
            }
            _ => Self::trap(TrapClass::OperationSafety, "`++` requires two Strings"),
        }
    }

    fn eval_div(&mut self, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        let x = self.demand_number(a)?;
        let y = self.demand_number(b)?;
        if y.is_zero() {
            // Total division: the form tag and canonical operand retain identity.
            return Ok(self.interner.div_zero(x));
        }
        Ok(self.interner.number(x / y))
    }

    fn eval_rem(&mut self, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
        let x = self.demand_number(a)?;
        let y = self.demand_number(b)?;
        if y.is_zero() {
            return Ok(self.interner.mod_zero(x));
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
            None => Self::trap(
                TrapClass::OperationSafety,
                "0 raised to a negative power is undefined",
            ),
        }
    }

    fn eval_compare(&mut self, op: PrimOp, a: &ValueRef, b: &ValueRef) -> Result<ValueRef, Trap> {
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
                            return Self::trap(
                                TrapClass::SpreadKind,
                                "tuple spread of a non-Tuple",
                            );
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
                            return Self::trap(
                                TrapClass::ComputedKey,
                                "computed record key is not a String",
                            );
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
                            return Self::trap(
                                TrapClass::SpreadKind,
                                "record spread of a non-Record",
                            );
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

    fn eval_opt(
        &mut self,
        e: &Option<Box<Expr>>,
        env: &Env,
        world: World,
    ) -> Result<Option<ValueRef>, Trap> {
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
                Self::trap(
                    TrapClass::NullReceiver,
                    format!("null receiver for field `{name}`"),
                )
            };
        }
        let key: Vec<u16> = name.encode_utf16().collect();
        if let Some(entry) = recv
            .as_record()
            .and_then(|entries| entries.iter().find(|e| e.key == key))
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

    fn access_slice(
        &mut self,
        recv: &ValueRef,
        lo: Option<ValueRef>,
        hi: Option<ValueRef>,
    ) -> EvalResult {
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
                    let s = self.stringify(&v);
                    out.extend(s.encode_utf16());
                }
            }
        }
        Ok(Outcome::Produced(self.interner.string_units(out)))
    }

    /// **Structure interpolation is total** [user, 2026-07-18]: every value renders.
    /// A top-level String interpolates raw; strings *inside* structures are quoted
    /// and escaped, so literal-formed values round-trip (`parse ∘ print = identity`,
    /// the PR-05 harness law). Functions and Indeterminate values render as visibly
    /// non-parseable angle-bracket forms. The frozen renderer intentionally hides a
    /// nonzero numerator even though the value retains it, so `1/0` and `2/0` render
    /// identically while remaining distinct (PR-04 / R-1).
    fn stringify(&self, v: &ValueRef) -> String {
        render_value(v, false)
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
                        None => {
                            return Self::trap(
                                TrapClass::SpreadKind,
                                "argument spread of a non-Tuple",
                            );
                        }
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

        // Call-depth bound (fueled runs only): a diverging call would otherwise deepen
        // the interpreter's own stack without limit. Exhaustion is `out_of_fuel` — a
        // machine limit, not a trap (Part A).
        if let Some(max) = self.max_call_depth
            && self.call_depth >= max
        {
            self.out_of_fuel = true;
            return Err(Trap {
                class: TrapClass::OperationSafety,
                message: "call-depth bound exceeded".into(),
            });
        }
        self.call_depth += 1;
        let result = match callee_kind {
            ActKind::Pure => self.eval(&body, &call_env, World::Pure),
            ActKind::Effect => self.eval(&body, &call_env, World::Effect),
            ActKind::Mutator => self.apply_mutator(&body, &call_env, world),
        };
        self.call_depth -= 1;
        result
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
    if k >= 0 && k < len {
        Some(k as usize)
    } else {
        None
    }
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
    s.graphemes(true)
        .map(|g| g.encode_utf16().collect())
        .collect()
}

// ── Value rendering (structure interpolation is total — [user, 2026-07-18]) ───

/// Render `v` as its canonical literal form. `nested` is true inside a Tuple or
/// Record, where Strings are quoted and escaped so the form round-trips; a
/// top-level String renders raw.
fn render_value(v: &ValueRef, nested: bool) -> String {
    match v.data() {
        ValueData::Str(u) => {
            // Nested: quoted and losslessly escaped, so it round-trips (PR-03/08).
            // Top level: raw — explicitly outside the round-trip law (PR-06).
            if nested {
                quote_units(u)
            } else {
                String::from_utf16_lossy(u)
            }
        }
        ValueData::Number(n) => n.to_string(), // B2 printing
        ValueData::Boolean(b) => b.to_string(),
        ValueData::Null => "null".to_string(),
        ValueData::Tuple(items) => {
            let parts: Vec<String> = items.iter().map(|x| render_value(x, true)).collect();
            format!("[{}]", parts.join(", "))
        }
        ValueData::Record(entries) => {
            // Canonical order: **UTF-16 code-unit order** on the raw key (field
            // order ∉ identity, I-02; the frozen record-key rule). Identifier keys
            // render bare; any other key uses computed-key syntax so it round-trips
            // (PR-07).
            let mut fields: Vec<_> = entries.iter().collect();
            fields.sort_by(|a, b| a.key.cmp(&b.key));
            let parts: Vec<String> = fields
                .iter()
                .map(|e| {
                    let key = if is_render_ident(&e.key) {
                        String::from_utf16_lossy(&e.key)
                    } else {
                        format!("[{}]", quote_units(&e.key))
                    };
                    format!("{key}: {}", render_value(&e.value, true))
                })
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
        // Visibly non-parseable forms.
        ValueData::Function(_) | ValueData::Native(_) => "<Function>".to_string(),
        // The display is form-only even though the operand remains in identity.
        ValueData::Indeterminate(form) => {
            format!("<Indeterminate {}>", form.label())
        }
    }
}

/// Whether a record key renders as a bare identifier (grammar: `$`/`_`-free
/// alphanumerics, alphabetic first — mirrors `lex::is_ident_start/continue`).
/// Anything else needs computed-key syntax (PR-07).
fn is_render_ident(key: &[u16]) -> bool {
    let Ok(s) = String::from_utf16(key) else {
        return false;
    }; // lone surrogate ⇒ not an ident
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c != '_' && c != '$' && c.is_alphabetic() => {}
        _ => return false,
    }
    chars.all(|c| c != '_' && c != '$' && c.is_alphanumeric())
}

/// Quote and escape a UTF-16 string for the literal fragment (JS standard
/// escapes), **losslessly**: a lone surrogate unit is escaped as `\uXXXX` (never
/// U+FFFD, PR-08), so `parse ∘ print = identity` holds on the source-renderable
/// fragment (PR-03/05).
fn quote_units(units: &[u16]) -> String {
    let mut out = String::with_capacity(units.len() + 2);
    out.push('"');
    let mut i = 0;
    while i < units.len() {
        let u = units[i];
        // A well-formed high+low surrogate pair decodes to one scalar.
        let pair = (0xD800..=0xDBFF).contains(&u)
            && matches!(units.get(i + 1), Some(&lo) if (0xDC00..=0xDFFF).contains(&lo));
        if pair {
            let cp = 0x10000 + (((u as u32) - 0xD800) << 10) + ((units[i + 1] as u32) - 0xDC00);
            push_escaped(&mut out, char::from_u32(cp).expect("valid astral scalar"));
            i += 2;
            continue;
        }
        if (0xD800..=0xDFFF).contains(&u) {
            // A lone surrogate has no scalar value — escape the unit itself.
            out.push_str(&format!("\\u{u:04X}"));
            i += 1;
            continue;
        }
        push_escaped(&mut out, char::from_u32(u as u32).expect("BMP scalar"));
        i += 1;
    }
    out.push('"');
    out
}

fn push_escaped(out: &mut String, c: char) {
    match c {
        '"' => out.push_str("\\\""),
        '\\' => out.push_str("\\\\"),
        '\n' => out.push_str("\\n"),
        '\r' => out.push_str("\\r"),
        '\t' => out.push_str("\\t"),
        c => out.push(c),
    }
}

fn module_group_windows(module: &Module) -> Vec<mu::GroupWindow> {
    let bindings: Vec<(usize, String, Expr)> = module
        .items
        .iter()
        .enumerate()
        .filter_map(|(index, item)| match item {
            Item::Bind(Bind {
                target: BindTarget::Name(name),
                value,
                ..
            }) => Some((index, name.clone(), value.clone())),
            Item::ActBind(binding) => Some((
                index,
                binding.name.clone(),
                Expr::Lambda(binding.lambda.clone()),
            )),
            _ => None,
        })
        .collect();
    mu::group_windows(&bindings)
}

/// Build a closure value from a lambda and its defining environment.
///
/// Compute the canonical shape (α + capture slots + polynomial NF). A closure
/// whose captures are resolved takes the interner's shallow fast path
/// immediately; an open closure receives a provisional construction handle and
/// is canonicalized when its dependency/group window closes.
///
/// Free-standing (rather than an `Oracle` method) because the **analyzer** needs closures
/// too — `analyze_program` must reach a top-level function's value to verify its `where`
/// — and it must do so *without evaluating the module*, which would run the program at
/// compile time. Building a closure evaluates nothing: the body is untouched and the
/// environment is captured by reference under late binding.
/// The canonical free-variable list of a lambda (the capture-slot order) — what a
/// constructor must resolve before [`make_closure_in`] can take the closed fast
/// path. Canonicalization is idempotent and interned, so this is cheap to ask.
pub(crate) fn lambda_free_vars(lambda: &Lambda, interner: &mut Interner) -> Vec<String> {
    canon::canonicalize(lambda, interner).free_vars
}

pub(crate) fn make_closure_in(lambda: &Lambda, env: &Env, interner: &mut Interner) -> ValueRef {
    let shape = canon::canonicalize(lambda, interner);
    let closure = Closure {
        lambda: lambda.clone(),
        env: env.clone(),
    };
    let code = interner.intern_code(shape.code);
    interner.function(FnValue::new(code, shape.free_vars, closure))
}
