//! Lift each flow node into Lua statements over web variables.
//!
//! Variables are written as `Expr::Name("@v<id>")`; pseudo-statements that
//! later stages consume use other `@` names:
//! - `@fornum(from, to, step)` / `@forgen(f, s, c)`: init of a for loop,
//! - `@setlist(t, first, multret, items...)`: SETLIST,
//! - `@closure(idx, captures...)`: a closure, filled in after naming.

use disassembler::{LuaConstant, LuaNumber, Proto};
use lua_ast::{is_lua_ident, BinOp, Expr, Stat, TableField, UnOp};

use crate::flow::{Flow, Op, Term};
use crate::ir::{Cap, CmpOp, Decoded, Ins, Rk};
use crate::webs::{Analysis, OpInfo, VarId};

pub fn var(v: VarId) -> Expr {
    Expr::Name(format!("@v{}", v))
}

pub fn var_id(e: &Expr) -> Option<VarId> {
    match e {
        Expr::Name(n) => n.strip_prefix("@v").and_then(|s| s.parse().ok()),
        _ => None,
    }
}

pub fn pseudo(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Call { func: Box::new(Expr::Name(name.to_string())), args }
}

/// If `e` is a call to the pseudo-function `name`, its arguments.
pub fn pseudo_args<'a>(e: &'a Expr, name: &str) -> Option<&'a Vec<Expr>> {
    match e {
        Expr::Call { func, args } if matches!(func.as_ref(), Expr::Name(n) if n == name) => Some(args),
        _ => None,
    }
}

pub fn const_expr(c: Option<&LuaConstant>) -> Expr {
    match c {
        None | Some(LuaConstant::Null) => Expr::Nil,
        Some(LuaConstant::Bool(b)) => if *b { Expr::True } else { Expr::False },
        Some(LuaConstant::Number(LuaNumber::Integer(i))) => Expr::Integer(*i),
        Some(LuaConstant::Number(LuaNumber::Float(f))) => Expr::Float(*f),
        Some(LuaConstant::String(s)) => Expr::Str(s.to_vec()),
        Some(_) => Expr::Nil,
    }
}

#[derive(Clone, Debug, Default)]
pub struct IrBlock {
    pub stmts: Vec<Stat>,
    /// Branch condition for `Term::Cond` (true → `succs[0]`).
    pub cond: Option<Expr>,
    /// Loop variables declared by a for-loop header.
    pub loop_vars: Vec<VarId>,
}

pub struct Lifter<'a> {
    pub proto: &'a Proto,
    pub d: &'a Decoded,
    pub flow: &'a Flow,
    pub an: &'a Analysis,
    /// Resolved names of this function's upvalues.
    pub upnames: &'a [String],
    /// Which upvalues are the global environment.
    pub is_env: &'a [bool],
    /// Captured variables kept in one-element tables (flat functions, see
    /// [`Lifter::box_op`]).  Empty for structured functions.
    pub boxed_vars: std::collections::BTreeSet<VarId>,
    /// Which of this function's upvalues hold such boxes.
    pub boxed_up: &'a [bool],
    /// Next free variable id (for temporaries created here).
    pub next_var: usize,
    /// Per closure prototype: which captured values are boxes.
    pub closure_boxes: std::collections::BTreeMap<usize, Vec<bool>>,
    /// SELF instructions folded into the following call (`obj:m()`).
    pub skip_pc: std::collections::BTreeSet<usize>,
    /// Call pc → (receiver variable, method name).
    pub method_at: std::collections::BTreeMap<usize, (VarId, String)>,
}

impl<'a> Lifter<'a> {
    pub fn lift_all(&mut self) -> Vec<IrBlock> {
        (0..self.flow.nodes.len()).map(|b| {
            if self.flow.reachable(b) { self.lift_node(b) } else { IrBlock::default() }
        }).collect()
    }

    fn k(&self, k: u32) -> Expr {
        let e = const_expr(self.proto.constants.get(k as usize));
        // Before 5.3 every number is a float; whole ones read better as
        // integer literals and mean the same thing.
        if self.proto.version < 0x53 {
            if let Expr::Float(f) = e {
                if f.fract() == 0.0 && f.abs() < 1e15 { return Expr::Integer(f as i64); }
            }
        }
        e
    }

    /// The upvalue as a variable (for reads and writes).
    fn upval(&self, up: u16) -> Expr {
        let raw = self.upval_raw(up);
        if self.boxed_up.get(up as usize).copied().unwrap_or(false) {
            return Expr::Index { table: Box::new(raw), key: Box::new(Expr::Integer(1)) };
        }
        raw
    }

    /// The upvalue's own name (a box, if boxed).
    fn upval_raw(&self, up: u16) -> Expr {
        if self.is_env.get(up as usize).copied().unwrap_or(false) {
            return Expr::Name("_ENV".to_string());
        }
        Expr::Name(self.upnames.get(up as usize).cloned().unwrap_or_else(|| format!("_upv{}", up)))
    }

    /// The call made by CALL/TAILCALL at `pc` (a method call if its SELF
    /// was fused).
    fn call_expr(&self, pc: usize, info: &OpInfo) -> Expr {
        let uv = |k: usize| var(info.use_var[k]);
        match self.method_at.get(&pc) {
            Some((obj, m)) => Expr::Method {
                obj: Box::new(var(*obj)),
                method: m.clone(),
                args: (2..info.uses.len()).map(uv).collect(),
            },
            None => Expr::Call {
                func: Box::new(uv(0)),
                args: (1..info.uses.len()).map(uv).collect(),
            },
        }
    }

    fn fresh_var(&mut self) -> VarId {
        self.next_var += 1;
        self.next_var - 1
    }

    /// Rewrite the statements produced by one op for boxed variables:
    /// reads become `V[1]`; a fresh definition creates a new box
    /// (`V = {e}`), a definition while the upvalue is open writes through
    /// (`V[1] = e`); closures capture a `do local b = V` copy of the box.
    fn box_op(&mut self, stmts: &mut Vec<Stat>, start: usize, cond: Option<&mut Expr>, info: &OpInfo) {
        if self.boxed_vars.is_empty() { return; }
        let boxed = self.boxed_vars.clone();
        if let Some(c) = cond { unbox_uses(c, &boxed); }
        let produced: Vec<Stat> = stmts.drain(start..).collect();
        for mut s in produced {
            // Closures capturing boxed variables.
            let mut caps: Vec<(VarId, VarId)> = Vec::new(); // (boxed var, copy)
            visit_closures(&mut s, &mut |idx, args| {
                let flags = self.closure_boxes.entry(idx).or_insert_with(|| vec![false; args.len()]);
                for (k, a) in args.iter_mut().enumerate() {
                    if let Some(v) = var_id(a) {
                        if boxed.contains(&v) {
                            let copy = match caps.iter().find(|(b, _)| *b == v) {
                                Some(&(_, c)) => c,
                                None => { let c = self.next_var; self.next_var += 1; caps.push((v, c)); c }
                            };
                            *a = var(copy);
                            if k < flags.len() { flags[k] = true; }
                        }
                    }
                }
            });
            // Reads.
            match &mut s {
                Stat::Assign { lhs, rhs } => {
                    for l in lhs.iter_mut() {
                        if let Expr::Index { table, key } = l { unbox_uses(table, &boxed); unbox_uses(key, &boxed); }
                    }
                    for e in rhs.iter_mut() { unbox_uses(e, &boxed); }
                }
                Stat::Call(e) => unbox_uses(e, &boxed),
                Stat::Return(v) => { for e in v.iter_mut() { unbox_uses(e, &boxed); } }
                _ => {}
            }
            // Writes.
            if let Stat::Assign { lhs, rhs } = &mut s {
                let fresh = |v: VarId| info.def_var.iter().position(|&d| d == v).map_or(true, |k| info.def_fresh.get(k).copied().unwrap_or(true));
                let targets: Vec<Option<VarId>> = lhs.iter().map(|l| var_id(l).filter(|v| boxed.contains(v))).collect();
                if targets.iter().any(|t| t.is_some()) {
                    if lhs.len() == 1 && rhs.len() == 1 {
                        let v = targets[0].unwrap();
                        if fresh(v) {
                            let e = rhs.pop().unwrap();
                            rhs.push(Expr::Table(vec![TableField::ValueField(e)]));
                        } else {
                            lhs[0] = box_slot(v);
                        }
                    } else {
                        // Multiple targets: assign through temporaries.
                        let mut after = Vec::new();
                        for (k, t) in targets.iter().enumerate() {
                            if let Some(v) = *t {
                                if fresh(v) {
                                    let tmp = self.fresh_var();
                                    lhs[k] = var(tmp);
                                    after.push(Stat::Assign { lhs: vec![var(v)], rhs: vec![Expr::Table(vec![TableField::ValueField(var(tmp))])] });
                                } else {
                                    lhs[k] = box_slot(v);
                                }
                            }
                        }
                        let first = std::mem::replace(&mut s, Stat::Break);
                        stmts.push(first);
                        stmts.extend(after);
                        continue;
                    }
                }
            }
            if caps.is_empty() {
                stmts.push(s);
            } else {
                let mut body: Vec<Stat> = caps.iter().map(|&(v, c)| Stat::Assign { lhs: vec![var(c)], rhs: vec![var(v)] }).collect();
                body.push(s);
                stmts.push(Stat::Do(body));
            }
        }
    }

    fn lift_node(&mut self, b: usize) -> IrBlock {
        let flow = self.flow;
        let an = self.an;
        let node = &flow.nodes[b];
        let mut out = IrBlock::default();
        let cond_pc = match node.term {
            Term::Cond { cond_pc } => Some(cond_pc),
            _ => None,
        };
        // `SELF A obj "m"` ... `CALL A`: when the two SELF results are only
        // used by that call, emit `obj:m(args)`.
        for (i, &op) in node.ops.iter().enumerate() {
            let Op::Pc(pc) = op else { continue };
            let Ins::SelfOp { a, key: Rk::K(k), .. } = &self.d.ins[pc] else { continue };
            let Some(Expr::Str(name)) = Some(self.k(*k)) else { continue };
            let Ok(name) = String::from_utf8(name) else { continue };
            if !is_lua_ident(&name) { continue; }
            let info = &an.ops[b][i];
            let single = |v: VarId| an.vars[v].uses == 1 && an.vars[v].defs == 1 && !self.boxed_vars.contains(&v);
            let (Some(va), Some(va1)) = (info.def_of(*a), info.def_of(a + 1)) else { continue };
            if !single(va) || !single(va1) { continue; }
            for (j, &op2) in node.ops.iter().enumerate().skip(i + 1) {
                let Op::Pc(pc2) = op2 else { break };
                match &self.d.ins[pc2] {
                    Ins::Call { a: ca, .. } | Ins::TailCall { a: ca, .. } if ca == a => {
                        let ci = &an.ops[b][j];
                        if ci.use_var.first() == Some(&va) && ci.use_var.get(1) == Some(&va1) {
                            self.skip_pc.insert(pc);
                            self.method_at.insert(pc2, (info.use_var[0], name.clone()));
                        }
                        break;
                    }
                    other => {
                        // Argument setup may only touch registers above a+1.
                        let touches = an.ops[b][j].defs.iter().any(|&r| r == *a || r == a + 1);
                        if touches || matches!(other, Ins::Jmp { .. }) { break; }
                    }
                }
            }
        }
        for (i, &op) in node.ops.iter().enumerate() {
            let info = &an.ops[b][i];
            let start = out.stmts.len();
            let had_cond = out.cond.is_some();
            self.lift_op(b, op, info, cond_pc, &mut out);
            let cond = if !had_cond { out.cond.as_mut() } else { None };
            self.box_op(&mut out.stmts, start, cond, info);
        }
        match node.term {
            Term::NumFor { pc, .. } | Term::GenFor { pc, .. } => {
                let i = node.ops.iter().position(|o| *o == Op::Pc(pc)).unwrap();
                out.loop_vars = an.ops[b][i].def_var.clone();
            }
            _ => {}
        }
        out
    }

    fn lift_op(&mut self, b: usize, op: Op, info: &OpInfo, cond_pc: Option<usize>, out: &mut IrBlock) {
        let flow = self.flow;
        let node = &flow.nodes[b];
        {
            let uv = |k: usize| var(info.use_var[k]);
            let u = |r: u16| info.use_of(r).map(var).unwrap_or(Expr::Nil);
            let dv = |r: u16| info.def_of(r).map(var).unwrap_or(Expr::Nil);
            let rk = |x: Rk| match x {
                Rk::R(r) => u(r),
                Rk::K(k) => self.k(k),
                Rk::Int(v) => Expr::Integer(v),
                Rk::Flt(bits) => Expr::Float(f64::from_bits(bits)),
            };
            let assign = |l: Expr, r: Expr| Stat::Assign { lhs: vec![l], rhs: vec![r] };
            match op {
                Op::Copy { dst, src } => out.stmts.push(assign(dv(dst), u(src))),
                Op::NumForInit { .. } => {
                    out.stmts.push(Stat::Call(pseudo("@fornum", (0..3).map(uv).collect())));
                }
                Op::GenForInit { n, .. } => {
                    out.stmts.push(Stat::Call(pseudo("@forgen", (0..n as usize).map(uv).collect())));
                }
                Op::Pc(pc) => {
                    let ins = &self.d.ins[pc];
                    if self.skip_pc.contains(&pc) { return; }
                    if Some(pc) == cond_pc {
                        out.cond = Some(match ins {
                            Ins::Cmp { op, l, r, .. } => {
                                let bop = match op { CmpOp::Eq => BinOp::Eq, CmpOp::Lt => BinOp::Lt, CmpOp::Le => BinOp::Le };
                                Expr::BinOp { op: bop, lhs: Box::new(rk(*l)), rhs: Box::new(rk(*r)) }
                            }
                            Ins::Test { a, .. } => u(*a),
                            Ins::TestSet { b, .. } => u(*b),
                            Ins::TForLoop { src, .. } => ne_nil(u(*src)),
                            Ins::TForLoop51 { a, nvars } => {
                                // Lowered: call, then test the first result.
                                let lhs: Vec<Expr> = (a + 3..a + 3 + nvars).map(dv).collect();
                                let call = Expr::Call { func: Box::new(u(*a)), args: vec![u(a + 1), u(a + 2)] };
                                out.stmts.push(Stat::Assign { lhs, rhs: vec![call] });
                                ne_nil(dv(a + 3))
                            }
                            _ => Expr::True,
                        });
                        return;
                    }
                    let s: Option<Stat> = match ins {
                        Ins::Move { a, b } => Some(assign(dv(*a), u(*b))),
                        Ins::LoadK { a, k } => Some(assign(dv(*a), self.k(*k))),
                        Ins::LoadImm { a, v } => Some(assign(dv(*a), rk(*v))),
                        // The register is used by `astpass::scope_tbc`, which
                        // leaves `@tbc(x)` (printed as `local x <close>`).
                        Ins::Tbc { a } => Some(Stat::Call(pseudo("@tbc", vec![u(*a), Expr::Integer(*a as i64)]))),
                        // Printed as `if x ~= nil then error(...) end`.
                        Ins::ErrNNil { a, name } => {
                            let name = name.map(|k| self.k(k)).unwrap_or(Expr::Str(b"?".to_vec()));
                            Some(Stat::Call(pseudo("@errnnil", vec![u(*a), name])))
                        }
                        // Where a block with to-be-closed variables ends.
                        Ins::Close { a } if self.proto.version >= 0x54
                            && self.d.ins.iter().any(|i| matches!(i, Ins::Tbc { .. })) =>
                        {
                            Some(Stat::Call(pseudo("@close", vec![Expr::Integer(*a as i64)])))
                        }
                        Ins::LoadBool { a, val, .. } => Some(assign(dv(*a), if *val { Expr::True } else { Expr::False })),
                        Ins::LoadNil { a, last } => {
                            for r in *a..=*last { out.stmts.push(assign(dv(r), Expr::Nil)); }
                            None
                        }
                        Ins::GetUpval { a, up } => Some(assign(dv(*a), self.upval(*up))),
                        Ins::GetTabUp { a, up, key } => {
                            let key = rk(*key);
                            let e = if self.is_env.get(*up as usize).copied().unwrap_or(false) {
                                global(key, "_ENV")
                            } else {
                                Expr::Index { table: Box::new(self.upval(*up)), key: Box::new(key) }
                            };
                            Some(assign(dv(*a), e))
                        }
                        Ins::GetGlobal { a, k } => {
                            let e = global(self.k(*k), "_G");
                            Some(assign(dv(*a), e))
                        }
                        Ins::GetTable { a, t, key } => {
                            Some(assign(dv(*a), Expr::Index { table: Box::new(u(*t)), key: Box::new(rk(*key)) }))
                        }
                        Ins::SetTabUp { up, key, val } => {
                            let key = rk(*key);
                            let l = if self.is_env.get(*up as usize).copied().unwrap_or(false) {
                                global(key, "_ENV")
                            } else {
                                Expr::Index { table: Box::new(self.upval(*up)), key: Box::new(key) }
                            };
                            Some(assign(l, rk(*val)))
                        }
                        Ins::SetGlobal { a, k } => {
                            let l = global(self.k(*k), "_G");
                            Some(assign(l, u(*a)))
                        }
                        Ins::SetUpval { a, up } => Some(assign(self.upval(*up), u(*a))),
                        Ins::SetTable { t, key, val } => {
                            Some(assign(Expr::Index { table: Box::new(u(*t)), key: Box::new(rk(*key)) }, rk(*val)))
                        }
                        Ins::NewTable { a } => Some(assign(dv(*a), Expr::Table(vec![]))),
                        Ins::SelfOp { a, obj, key } => {
                            out.stmts.push(assign(dv(a + 1), u(*obj)));
                            Some(assign(dv(*a), Expr::Index { table: Box::new(u(*obj)), key: Box::new(rk(*key)) }))
                        }
                        Ins::Arith { a, op, l, r } => {
                            Some(assign(dv(*a), Expr::BinOp { op: op.clone(), lhs: Box::new(rk(*l)), rhs: Box::new(rk(*r)) }))
                        }
                        Ins::Unary { a, op, b } => {
                            Some(assign(dv(*a), Expr::UnOp { op: op.clone(), operand: Box::new(u(*b)) }))
                        }
                        Ins::Concat { .. } => {
                            let parts: Vec<Expr> = (0..info.uses.len()).map(uv).collect();
                            let e = parts.into_iter().rev().reduce(|acc, x| {
                                Expr::BinOp { op: BinOp::Concat, lhs: Box::new(x), rhs: Box::new(acc) }
                            }).unwrap_or(Expr::Str(vec![]));
                            Some(assign(var(info.def_var[0]), e))
                        }
                        Ins::Call { nret, .. } => {
                            let call = self.call_expr(pc, info);
                            match nret {
                                Some(0) => Some(Stat::Call(call)),
                                _ => Some(Stat::Assign {
                                    lhs: info.def_var.iter().map(|&v| var(v)).collect(),
                                    rhs: vec![call],
                                }),
                            }
                        }
                        Ins::TailCall { .. } => {
                            let call = self.call_expr(pc, info);
                            Some(Stat::Return(vec![call]))
                        }
                        Ins::Return { .. } => {
                            Some(Stat::Return((0..info.uses.len()).map(uv).collect()))
                        }
                        Ins::SetList { n, first, .. } => {
                            let multret = n.is_none() && self.an.pack_producer.contains_key(&pc);
                            let mut args = vec![uv(0), Expr::Integer(*first as i64), if multret { Expr::True } else { Expr::False }];
                            args.extend((1..info.uses.len()).map(uv));
                            Some(Stat::Call(pseudo("@setlist", args)))
                        }
                        Ins::Closure { idx, caps, .. } => {
                            let mut args = vec![Expr::Integer(*idx as i64)];
                            let mut k = 0;
                            let mut flags = vec![false; caps.len()];
                            for (ci, c) in caps.iter().enumerate() {
                                match c {
                                    Cap::Reg(_) => { args.push(var(info.use_var[k])); k += 1; }
                                    Cap::Up(j) => {
                                        // Pass a boxed upvalue on as the box itself.
                                        flags[ci] = self.boxed_up.get(*j as usize).copied().unwrap_or(false);
                                        args.push(self.upval_raw(*j));
                                    }
                                }
                            }
                            if flags.iter().any(|&f| f) {
                                let e = self.closure_boxes.entry(*idx).or_insert_with(|| vec![false; caps.len()]);
                                for (i, f) in flags.into_iter().enumerate() { if f { e[i] = true; } }
                            }
                            Some(assign(var(info.def_var[0]), pseudo("@closure", args)))
                        }
                        Ins::VarArg { n, .. } => match n {
                            Some(0) => None,
                            _ => Some(Stat::Assign {
                                lhs: info.def_var.iter().map(|&v| var(v)).collect(),
                                rhs: vec![Expr::Vararg],
                            }),
                        },
                        Ins::TForCall { a, nvars, base, ctl } if !matches!(node.term, Term::GenFor { .. }) => {
                            let lhs: Vec<Expr> = (a + base..a + base + nvars).map(dv).collect();
                            let call = Expr::Call { func: Box::new(u(*a)), args: vec![u(a + 1), u(a + ctl)] };
                            Some(Stat::Assign { lhs, rhs: vec![call] })
                        }
                        Ins::ForPrep { .. } | Ins::ForLoop { .. } | Ins::TForCall { .. }
                        | Ins::TForLoop { .. } | Ins::TForLoop51 { .. } | Ins::Jmp { .. }
                        | Ins::Close { .. } | Ins::Data | Ins::Unknown
                        | Ins::Cmp { .. } | Ins::Test { .. } | Ins::TestSet { .. } => None,
                    };
                    if let Some(s) = s { out.stmts.push(s); }
                }
            }
        }
    }
}

fn box_slot(v: VarId) -> Expr {
    Expr::Index { table: Box::new(var(v)), key: Box::new(Expr::Integer(1)) }
}

/// Replace reads of boxed variables with `V[1]`, leaving closure
/// captures (which take the box itself) alone.
fn unbox_uses(e: &mut Expr, boxed: &std::collections::BTreeSet<VarId>) {
    if let Some(v) = var_id(e) {
        if boxed.contains(&v) { *e = box_slot(v); }
        return;
    }
    if pseudo_args(e, "@closure").is_some() { return; }
    match e {
        Expr::Index { table, key } => { unbox_uses(table, boxed); unbox_uses(key, boxed); }
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => { unbox_uses(func, boxed); for a in args { unbox_uses(a, boxed); } }
        Expr::BinOp { lhs, rhs, .. } => { unbox_uses(lhs, boxed); unbox_uses(rhs, boxed); }
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => unbox_uses(operand, boxed),
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::IndexField(k, v) => { unbox_uses(k, boxed); unbox_uses(v, boxed); }
                    TableField::NameField(_, v) | TableField::ValueField(v) => unbox_uses(v, boxed),
                }
            }
        }
        _ => {}
    }
}

/// Call `f(proto index, capture args)` for each `@closure` in a statement.
fn visit_closures(s: &mut Stat, f: &mut impl FnMut(usize, &mut [Expr])) {
    let mut go = |e: &mut Expr| lua_ast::transform_expr(e, &mut |x| {
        if let Expr::Call { func, args } = x {
            if matches!(func.as_ref(), Expr::Name(n) if n == "@closure") {
                let idx = args[0].as_integer().unwrap_or(0) as usize;
                f(idx, &mut args[1..]);
            }
        }
    });
    match s {
        Stat::Assign { lhs, rhs } => { for e in lhs.iter_mut().chain(rhs.iter_mut()) { go(e); } }
        Stat::Call(e) => go(e),
        Stat::Return(v) => { for e in v.iter_mut() { go(e); } }
        _ => {}
    }
}

/// A global variable access: a plain name when the key is an identifier.
fn global(key: Expr, env_name: &str) -> Expr {
    if let Expr::Str(b) = &key {
        if let Ok(s) = std::str::from_utf8(b) {
            if is_lua_ident(s) {
                return Expr::Name(s.to_string());
            }
        }
    }
    Expr::Index { table: Box::new(Expr::Name(env_name.to_string())), key: Box::new(key) }
}

fn ne_nil(e: Expr) -> Expr {
    Expr::BinOp { op: BinOp::Ne, lhs: Box::new(e), rhs: Box::new(Expr::Nil) }
}

/// `not e`, simplified where exact.
pub fn negate(e: Expr) -> Expr {
    match e {
        Expr::UnOp { op: UnOp::Not, operand } => *operand,
        Expr::BinOp { op: BinOp::Eq, lhs, rhs } => Expr::BinOp { op: BinOp::Ne, lhs, rhs },
        Expr::BinOp { op: BinOp::Ne, lhs, rhs } => Expr::BinOp { op: BinOp::Eq, lhs, rhs },
        Expr::True => Expr::False,
        Expr::False | Expr::Nil => Expr::True,
        other => Expr::UnOp { op: UnOp::Not, operand: Box::new(other) },
    }
}
