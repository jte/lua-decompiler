//! Block-local expression folding.
//!
//! Lifted code assigns every intermediate value to a variable.  Here
//! single-use temporaries are substituted into their consumer, but only when
//! that cannot change the order of side effects, and table constructors are
//! rebuilt from NEWTABLE/SETTABLE/SETLIST sequences.

use std::collections::BTreeSet;

use lua_ast::{is_lua_ident, Expr, Stat, TableField};

use crate::lift::{pseudo_args, var, var_id, IrBlock};
use crate::webs::VarId;

/// What evaluating an expression or statement may do.
#[derive(Clone, Copy, Default, Debug)]
pub struct Eff {
    pub calls: bool,
    pub reads_mem: bool,
    pub writes_mem: bool,
}

impl Eff {
    fn add(&mut self, o: Eff) {
        self.calls |= o.calls;
        self.reads_mem |= o.reads_mem;
        self.writes_mem |= o.writes_mem;
    }
}

fn is_pseudo(n: &str) -> bool { n.starts_with('@') }

pub fn expr_eff(e: &Expr) -> Eff {
    let mut eff = Eff::default();
    walk_eff(e, &mut eff);
    eff
}

fn walk_eff(e: &Expr, eff: &mut Eff) {
    match e {
        Expr::Name(n) => if !is_pseudo(n) { eff.reads_mem = true; },
        Expr::Index { table, key } => {
            eff.reads_mem = true;
            walk_eff(table, eff);
            walk_eff(key, eff);
        }
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
            // Pseudo-calls (`@closure`, `@uses`, ...) do nothing at runtime.
            let pseudo = matches!(func.as_ref(), Expr::Name(n) if n.starts_with('@') && !n.starts_with("@v"));
            if !pseudo {
                eff.calls = true;
                walk_eff(func, eff);
            }
            for a in args { walk_eff(a, eff); }
        }
        Expr::BinOp { lhs, rhs, .. } => { walk_eff(lhs, eff); walk_eff(rhs, eff); }
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => walk_eff(operand, eff),
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::IndexField(k, v) => { walk_eff(k, eff); walk_eff(v, eff); }
                    TableField::NameField(_, v) | TableField::ValueField(v) => walk_eff(v, eff),
                }
            }
        }
        _ => {}
    }
}

pub fn expr_vars(e: &Expr, out: &mut BTreeSet<VarId>) {
    lua_ast_walk(e, &mut |x| if let Some(v) = var_id(x) { out.insert(v); });
}

/// Pre-order walk over an expression (not entering function bodies).
pub fn lua_ast_walk(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Index { table, key } => { lua_ast_walk(table, f); lua_ast_walk(key, f); }
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => { lua_ast_walk(func, f); for a in args { lua_ast_walk(a, f); } }
        Expr::BinOp { lhs, rhs, .. } => { lua_ast_walk(lhs, f); lua_ast_walk(rhs, f); }
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => lua_ast_walk(operand, f),
        Expr::Table(fields) => {
            for fl in fields {
                match fl {
                    TableField::IndexField(k, v) => { lua_ast_walk(k, f); lua_ast_walk(v, f); }
                    TableField::NameField(_, v) | TableField::ValueField(v) => lua_ast_walk(v, f),
                }
            }
        }
        _ => {}
    }
}

pub fn count_var(e: &Expr, v: VarId) -> usize {
    let mut n = 0;
    lua_ast_walk(e, &mut |x| if var_id(x) == Some(v) { n += 1; });
    n
}

/// Expressions of a (non-compound) statement in evaluation order.
fn stat_exprs(s: &Stat) -> Vec<&Expr> {
    match s {
        Stat::Assign { lhs, rhs } => {
            let mut v = Vec::new();
            for l in lhs {
                if let Expr::Index { table, key } = l { v.push(table.as_ref()); v.push(key.as_ref()); }
            }
            v.extend(rhs.iter());
            v
        }
        Stat::Local { values, .. } => values.iter().collect(),
        Stat::Call(e) => vec![e],
        Stat::Return(vals) => vals.iter().collect(),
        _ => vec![],
    }
}

/// `a, b, c = iter(...)` directly followed by `@forgen(a, b, c)` becomes
/// `@forgen(iter(...))` (the call's results fill the iterator triple).
pub fn fold_forgen(b: &mut IrBlock, facts: &mut VarFacts) -> bool {
    let n = b.stmts.len();
    if n < 2 { return false; }
    let Stat::Call(init) = &b.stmts[n - 1] else { return false };
    let Some(args) = pseudo_args(init, "@forgen") else { return false };
    let Stat::Assign { lhs, rhs } = &b.stmts[n - 2] else { return false };
    if rhs.len() != 1 || !is_multi(&rhs[0]) || lhs.len() < 2 || lhs.len() > 4 { return false; }
    let vars: Vec<VarId> = lhs.iter().filter_map(var_id).collect();
    if vars.len() != lhs.len() || !vars.iter().all(|&v| facts.foldable(v)) { return false; }
    // The init must read exactly these variables, then (if fewer) nils.
    for (k, a) in args.iter().enumerate() {
        match vars.get(k) {
            Some(&v) => if var_id(a) != Some(v) { return false; },
            None => if !matches!(a, Expr::Nil) && var_id(a).is_none() { return false; },
        }
    }
    if args.len() > vars.len() && args[vars.len()..].iter().any(|a| var_id(a).is_some()) { return false; }
    let call = rhs[0].clone();
    for &v in &vars { facts.defs[v] = 0; facts.uses[v] = 0; }
    b.stmts.truncate(n - 2);
    b.stmts.push(Stat::Call(crate::lift::pseudo("@forgen", vec![call])));
    true
}

/// Effects of a whole statement, and the variables it assigns.
fn stat_eff(s: &Stat) -> (Eff, BTreeSet<VarId>) {
    let mut eff = Eff::default();
    let mut writes = BTreeSet::new();
    for e in stat_exprs(s) { eff.add(expr_eff(e)); }
    match s {
        Stat::Assign { lhs, .. } => {
            for l in lhs {
                match var_id(l) {
                    Some(v) => { writes.insert(v); }
                    None => eff.writes_mem = true,
                }
            }
        }
        Stat::Call(e) => {
            if pseudo_args(e, "@setlist").is_some() { eff.writes_mem = true; }
        }
        _ => {}
    }
    (eff, writes)
}

/// Can an expression with effects `e` (reading `e_vars`) be moved past code
/// with effects `x` (writing `x_writes`)?
fn commutes(e: Eff, e_vars: &BTreeSet<VarId>, x: Eff, x_writes: &BTreeSet<VarId>) -> bool {
    if e.calls && (x.calls || x.reads_mem || x.writes_mem) { return false; }
    if e.reads_mem && (x.calls || x.writes_mem) { return false; }
    if x.calls && (e.calls || e.reads_mem) { return false; }
    e_vars.is_disjoint(x_writes)
}

/// Effects of everything evaluated in `e` before the (single) occurrence of
/// `v`, or None if `v` doesn't occur.
fn eff_before(e: &Expr, v: VarId, acc: &mut Eff) -> bool {
    if var_id(e) == Some(v) { return true; }
    let children: Vec<&Expr> = match e {
        Expr::Index { table, key } => vec![table, key],
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
            let mut c = vec![func.as_ref()];
            c.extend(args.iter());
            c
        }
        Expr::BinOp { lhs, rhs, .. } => vec![lhs, rhs],
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => vec![operand],
        Expr::Table(fields) => {
            let mut c = Vec::new();
            for f in fields {
                match f {
                    TableField::IndexField(k, x) => { c.push(k); c.push(x); }
                    TableField::NameField(_, x) | TableField::ValueField(x) => c.push(x),
                }
            }
            c
        }
        _ => vec![],
    };
    for c in children {
        if count_var(c, v) > 0 {
            return eff_before(c, v, acc);
        }
        acc.add(expr_eff(c));
    }
    false
}

/// Replacement for one variable occurrence.  `single` marks a value that was
/// truncated to one result: a call or `...` landing where Lua would expand
/// all values (`multi` positions) gets parentheses.
struct With {
    expr: Option<Expr>,
    single: bool,
}

fn is_multi(e: &Expr) -> bool {
    matches!(e, Expr::Call { .. } | Expr::Method { .. } | Expr::Vararg) && pseudo_args(e, "@closure").is_none()
}

fn subst(e: &mut Expr, v: VarId, with: &mut With, multi: bool) {
    if var_id(e) == Some(v) {
        if let Some(w) = with.expr.take() {
            *e = if multi && with.single && is_multi(&w) { Expr::Paren(Box::new(w)) } else { w };
        }
        return;
    }
    match e {
        Expr::Index { table, key } => { subst(table, v, with, false); subst(key, v, with, false); }
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
            subst(func, v, with, false);
            let n = args.len();
            for (i, a) in args.iter_mut().enumerate() { subst(a, v, with, i + 1 == n); }
        }
        Expr::BinOp { lhs, rhs, .. } => { subst(lhs, v, with, false); subst(rhs, v, with, false); }
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => subst(operand, v, with, false),
        Expr::Table(fields) => {
            let n = fields.len();
            for (i, f) in fields.iter_mut().enumerate() {
                match f {
                    TableField::IndexField(k, x) => { subst(k, v, with, false); subst(x, v, with, false); }
                    TableField::NameField(_, x) => subst(x, v, with, false),
                    TableField::ValueField(x) => subst(x, v, with, i + 1 == n),
                }
            }
        }
        _ => {}
    }
}

/// Substitute into a statement, knowing which positions expand multiple values.
fn subst_stat(s: &mut Stat, v: VarId, with: &mut With) {
    match s {
        Stat::Assign { lhs, rhs } => {
            for l in lhs.iter_mut() {
                if let Expr::Index { table, key } = l {
                    subst(table, v, with, false);
                    subst(key, v, with, false);
                }
            }
            let expand = lhs.len() > rhs.len();
            let n = rhs.len();
            for (i, e) in rhs.iter_mut().enumerate() { subst(e, v, with, expand && i + 1 == n); }
        }
        Stat::Local { names, values } => {
            let expand = names.len() > values.len();
            let n = values.len();
            for (i, e) in values.iter_mut().enumerate() { subst(e, v, with, expand && i + 1 == n); }
        }
        Stat::Return(vals) => {
            let n = vals.len();
            for (i, e) in vals.iter_mut().enumerate() { subst(e, v, with, i + 1 == n); }
        }
        Stat::Call(e) => {
            // Pseudo-statements: the last item of a SETLIST / for-init expands.
            if let Expr::Call { func, args } = e {
                if matches!(func.as_ref(), Expr::Name(n) if n == "@setlist" || n == "@forgen" || n == "@fornum") {
                    let n = args.len();
                    for (i, a) in args.iter_mut().enumerate() { subst(a, v, with, i + 1 == n); }
                    return;
                }
            }
            subst(e, v, with, false)
        }
        _ => {}
    }
}

/// Per-variable facts the folder needs.
pub struct VarFacts {
    pub defs: Vec<u32>,
    pub uses: Vec<u32>,
    /// May not be folded away (captured, named local, parameter, ...).
    pub pinned: Vec<bool>,
    /// Holds all results of a call / `...` (multret).
    pub pack: Vec<bool>,
}

impl VarFacts {
    fn foldable(&self, v: VarId) -> bool {
        v < self.defs.len() && self.defs[v] == 1 && self.uses[v] == 1 && !self.pinned[v]
    }
}

const LOOKAHEAD: usize = 48;

/// Nesting depth of an expression.  Lua's parser rejects expressions nested
/// more than ~200 levels, so folding stops well before that.
fn depth(e: &Expr) -> usize {
    match e {
        Expr::Index { table, key } => 1 + depth(table).max(depth(key)),
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => 1 + args.iter().map(depth).max().unwrap_or(0).max(depth(func)),
        Expr::BinOp { lhs, rhs, .. } => 1 + depth(lhs).max(depth(rhs)),
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => 1 + depth(operand),
        Expr::Table(fields) => 1 + fields.iter().map(|f| match f {
            TableField::IndexField(k, v) => depth(k).max(depth(v)),
            TableField::NameField(_, v) | TableField::ValueField(v) => depth(v),
        }).max().unwrap_or(0),
        _ => 0,
    }
}

const MAX_DEPTH: usize = 40;

/// Is `v` called directly somewhere in `e` (`v(...)`)?
fn called_in(e: &Expr, v: VarId) -> bool {
    let mut found = false;
    lua_ast_walk(e, &mut |x| {
        if let Expr::Call { func, .. } = x {
            if var_id(func) == Some(v) { found = true; }
        }
    });
    found
}

/// Inlining a function literal where it is called would produce
/// `(function() ... end)(...)`; keep it as a named local instead.
fn closure_called(e: &Expr, v: VarId, target: &[&Expr]) -> bool {
    pseudo_args(e, "@closure").is_some() && target.iter().any(|x| called_in(x, v))
}

fn single_def(s: &Stat) -> Option<(VarId, &Expr)> {
    match s {
        Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => var_id(&lhs[0]).map(|v| (v, &rhs[0])),
        _ => None,
    }
}

/// Fold single-use temporaries in one block.  Returns true if anything changed.
pub fn fold_block(b: &mut IrBlock, facts: &mut VarFacts) -> bool {
    let mut changed = false;
    let mut i = b.stmts.len();
    while i > 0 {
        i -= 1;
        let Some((v, e)) = single_def(&b.stmts[i]) else { continue };
        if v >= facts.defs.len() { continue; }
        // Dead definition.
        if facts.defs[v] == 1 && facts.uses[v] == 0 && !facts.pinned[v] {
            let eff = expr_eff(e);
            if !eff.calls {
                b.stmts.remove(i);
                facts.defs[v] = 0;
                changed = true;
            } else if matches!(e, Expr::Call { .. }) && pseudo_args(e, "@closure").is_none() {
                let e = e.clone();
                b.stmts[i] = Stat::Call(e);
                facts.defs[v] = 0;
                changed = true;
            }
            continue;
        }
        if !facts.foldable(v) || depth(e) > MAX_DEPTH { continue; }
        let e_eff = expr_eff(e);
        let mut e_vars = BTreeSet::new();
        expr_vars(e, &mut e_vars);
        if e_vars.contains(&v) { continue; }

        let mut x_eff = Eff::default();
        let mut x_writes: BTreeSet<VarId> = BTreeSet::new();
        let mut j = i + 1;
        let mut target: Option<usize> = None; // usize::MAX = cond
        while j <= b.stmts.len() && j - i <= LOOKAHEAD {
            if j == b.stmts.len() {
                if let Some(c) = &b.cond {
                    if count_var(c, v) == 1 { target = Some(usize::MAX); }
                }
                break;
            }
            let s = &b.stmts[j];
            let cnt: usize = stat_exprs(s).iter().map(|x| count_var(x, v)).sum::<usize>()
                + match s { Stat::Assign { lhs, .. } => lhs.iter().filter(|l| var_id(l) == Some(v)).count(), _ => 0 };
            if cnt > 0 {
                if cnt == 1 && !matches!(s, Stat::Assign { lhs, .. } if lhs.iter().any(|l| var_id(l) == Some(v))) {
                    target = Some(j);
                }
                break;
            }
            if !matches!(s, Stat::Assign { .. } | Stat::Call(_) | Stat::Local { .. }) { break; }
            let (se, sw) = stat_eff(s);
            x_eff.add(se);
            x_writes.extend(sw);
            if !commutes(e_eff, &e_vars, x_eff, &x_writes) { break; }
            j += 1;
        }
        let Some(t) = target else { continue };
        let target_exprs: Vec<&Expr> = if t == usize::MAX { vec![b.cond.as_ref().unwrap()] } else { stat_exprs(&b.stmts[t]) };
        if closure_called(e, v, &target_exprs) { continue; }
        if depth(e) + target_exprs.iter().map(|x| depth(x)).max().unwrap_or(0) > MAX_DEPTH { continue; }

        // Order inside the target.
        let mut before = x_eff;
        let ok = if t == usize::MAX {
            let mut acc = Eff::default();
            eff_before(b.cond.as_ref().unwrap(), v, &mut acc);
            before.add(acc);
            commutes(e_eff, &e_vars, before, &x_writes)
        } else {
            let mut acc = Eff::default();
            for x in stat_exprs(&b.stmts[t]) {
                if count_var(x, v) > 0 { eff_before(x, v, &mut acc); break; }
                acc.add(expr_eff(x));
            }
            before.add(acc);
            commutes(e_eff, &e_vars, before, &x_writes)
        };
        if !ok { continue; }

        let Stat::Assign { mut rhs, .. } = b.stmts.remove(i) else { unreachable!() };
        let mut with = With { expr: Some(rhs.pop().unwrap()), single: !facts.pack[v] };
        if t == usize::MAX {
            subst(b.cond.as_mut().unwrap(), v, &mut with, false);
        } else {
            subst_stat(&mut b.stmts[t - 1], v, &mut with);
        }
        facts.defs[v] = 0;
        facts.uses[v] = 0;
        changed = true;
    }
    changed
}

/// Rebuild `T = {}` + field assignments + SETLISTs into one constructor.
/// Works from the end of the block so nested constructors are built first.
pub fn build_constructors(b: &mut IrBlock, facts: &mut VarFacts) -> bool {
    let mut changed = false;
    let mut i = b.stmts.len();
    while i > 0 {
        i -= 1;
        let (t, start_fields) = match &b.stmts[i] {
            Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => match (&rhs[0], var_id(&lhs[0])) {
                (Expr::Table(f), Some(t)) => (t, f.clone()),
                _ => continue,
            },
            _ => continue,
        };

        let mut npos: i64 = start_fields.iter().filter(|f| matches!(f, TableField::ValueField(_))).count() as i64;
        let mut fields: Vec<TableField> = start_fields;
        let mut pending: Vec<VarId> = Vec::new();
        // fields, last stmt, folded vars, uses of T consumed
        let mut good: Option<(Vec<TableField>, usize, Vec<VarId>, u32)> = None;
        let mut folded: Vec<VarId> = Vec::new();
        let mut t_uses: u32 = 0;
        let mut j = i + 1;
        while j < b.stmts.len() {
            let refs_t = |e: &Expr| count_var(e, t) > 0;
            match &b.stmts[j] {
                Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => {
                    if let Expr::Index { table, key } = &lhs[0] {
                        if var_id(table) == Some(t) && !refs_t(key) && !refs_t(&rhs[0])
                            && !pending.iter().any(|&p| count_var(key, p) + count_var(&rhs[0], p) > 0)
                        {
                            fields.push(field(key.as_ref().clone(), rhs[0].clone()));
                            t_uses += 1;
                            if pending.is_empty() { good = Some((fields.clone(), j, folded.clone(), t_uses)); }
                            j += 1;
                            continue;
                        }
                        break;
                    }
                    match var_id(&lhs[0]) {
                        Some(p) if facts.foldable(p) && !refs_t(&rhs[0])
                            && !pending.iter().any(|&q| count_var(&rhs[0], q) > 0) =>
                        {
                            fields.push(TableField::ValueField(rhs[0].clone()));
                            pending.push(p);
                            j += 1;
                        }
                        _ => break,
                    }
                }
                Stat::Call(e) => {
                    let Some(args) = pseudo_args(e, "@setlist") else { break };
                    if var_id(&args[0]) != Some(t) { break; }
                    let first = args[1].as_integer().unwrap_or(0);
                    let items = &args[3..];
                    if items.len() < pending.len() || first != npos + 1 { break; }
                    if !items.iter().zip(&pending).all(|(it, &p)| var_id(it) == Some(p)) { break; }
                    if items[pending.len()..].iter().any(|x| refs_t(x)) { break; }
                    for x in &items[pending.len()..] { fields.push(TableField::ValueField(x.clone())); }
                    npos += items.len() as i64;
                    folded.extend(pending.drain(..));
                    t_uses += 1;
                    good = Some((fields.clone(), j, folded.clone(), t_uses));
                    j += 1;
                }
                _ => break,
            }
        }
        if let Some((fields, last, folded, used)) = good {
            b.stmts[i] = Stat::Assign { lhs: vec![var(t)], rhs: vec![Expr::Table(fields)] };
            b.stmts.drain(i + 1..=last);
            for p in folded { facts.defs[p] = 0; facts.uses[p] = 0; }
            if t < facts.uses.len() { facts.uses[t] = facts.uses[t].saturating_sub(used); }
            changed = true;
        }
    }
    changed
}

/// Count definitions and uses of every variable in the lifted blocks, so the
/// folder works from what was actually emitted.
pub fn count_blocks(blocks: &[IrBlock], defs: &mut [u32], uses: &mut [u32]) {
    for d in defs.iter_mut() { *d = 0; }
    for u in uses.iter_mut() { *u = 0; }
    let mut use_e = |e: &Expr, uses: &mut [u32]| {
        lua_ast_walk(e, &mut |x| if let Some(v) = var_id(x) { if v < uses.len() { uses[v] += 1; } });
    };
    for b in blocks {
        for s in &b.stmts {
            if let Stat::Assign { lhs, .. } = s {
                for l in lhs {
                    if let Some(v) = var_id(l) { if v < defs.len() { defs[v] += 1; } }
                }
            }
            for e in stat_exprs(s) { use_e(e, uses); }
        }
        if let Some(c) = &b.cond { use_e(c, uses); }
        for &v in &b.loop_vars { if v < defs.len() { defs[v] += 1; } }
    }
}

// ---------------------------------------------------------------------------
// Folding across structured statements
// ---------------------------------------------------------------------------

/// Recount definitions/uses of variables in a structured body.
pub fn count_ast(b: &[Stat], defs: &mut [u32], uses: &mut [u32], loop_vars: &mut BTreeSet<VarId>) {
    let mut use_e = |e: &Expr, uses: &mut [u32]| {
        lua_ast_walk(e, &mut |x| if let Some(v) = var_id(x) { if v < uses.len() { uses[v] += 1; } });
    };
    let name_var = |n: &str| n.strip_prefix("@v").and_then(|s| s.parse::<usize>().ok());
    for s in b {
        match s {
            Stat::Assign { lhs, rhs } => {
                for l in lhs {
                    match var_id(l) {
                        Some(v) => { if v < defs.len() { defs[v] += 1; } }
                        None => use_e(l, uses),
                    }
                }
                for e in rhs { use_e(e, uses); }
            }
            Stat::Local { values, .. } => { for e in values { use_e(e, uses); } }
            Stat::While { cond, body } | Stat::Repeat { body, cond } => {
                use_e(cond, uses);
                count_ast(body, defs, uses, loop_vars);
            }
            Stat::If { branches, else_body } => {
                for (c, bb) in branches { use_e(c, uses); count_ast(bb, defs, uses, loop_vars); }
                if let Some(e) = else_body { count_ast(e, defs, uses, loop_vars); }
            }
            Stat::NumFor { var, from, to, step, body } => {
                if let Some(v) = name_var(var) { loop_vars.insert(v); if v < defs.len() { defs[v] += 1; } }
                use_e(from, uses);
                use_e(to, uses);
                if let Some(s) = step { use_e(s, uses); }
                count_ast(body, defs, uses, loop_vars);
            }
            Stat::GenFor { vars, iters, body } => {
                for n in vars { if let Some(v) = name_var(n) { loop_vars.insert(v); if v < defs.len() { defs[v] += 1; } } }
                for e in iters { use_e(e, uses); }
                count_ast(body, defs, uses, loop_vars);
            }
            Stat::Do(body) => count_ast(body, defs, uses, loop_vars),
            Stat::Return(v) => { for e in v { use_e(e, uses); } }
            Stat::Call(e) => use_e(e, uses),
            _ => {}
        }
    }
}

/// Header expressions of a compound statement that run once, before
/// anything else in it.
fn head_exprs(s: &Stat) -> Vec<&Expr> {
    match s {
        Stat::If { branches, .. } => vec![&branches[0].0],
        Stat::NumFor { from, to, step, .. } => {
            let mut v = vec![from, to];
            if let Some(s) = step { v.push(s); }
            v
        }
        Stat::GenFor { iters, .. } => iters.iter().collect(),
        _ => vec![],
    }
}

fn subst_head(s: &mut Stat, v: VarId, with: &mut With) {
    match s {
        Stat::If { branches, .. } => subst(&mut branches[0].0, v, with, false),
        Stat::NumFor { from, to, step, .. } => {
            subst(from, v, with, false);
            subst(to, v, with, false);
            if let Some(s) = step { subst(s, v, with, false); }
        }
        Stat::GenFor { iters, .. } => {
            let n = iters.len();
            for (i, e) in iters.iter_mut().enumerate() { subst(e, v, with, i + 1 == n); }
        }
        _ => {}
    }
}

pub fn occurs_in_stat(s: &Stat, v: VarId) -> usize {
    let me = format!("@v{}", v);
    let nm = |n: &String| (n == &me) as usize;
    let blk = |b: &Vec<Stat>| b.iter().map(|s| occurs_in_stat(s, v)).sum::<usize>();
    match s {
        Stat::Assign { lhs, rhs } => lhs.iter().chain(rhs).map(|e| count_var(e, v)).sum(),
        Stat::Local { names, values } => names.iter().map(nm).sum::<usize>() + values.iter().map(|e| count_var(e, v)).sum::<usize>(),
        Stat::While { cond, body } | Stat::Repeat { body, cond } => count_var(cond, v) + blk(body),
        Stat::If { branches, else_body } => {
            branches.iter().map(|(c, b)| count_var(c, v) + blk(b)).sum::<usize>()
                + else_body.as_ref().map_or(0, |b| blk(b))
        }
        Stat::NumFor { var, from, to, step, body } => {
            nm(var) + count_var(from, v) + count_var(to, v) + step.as_ref().map_or(0, |s| count_var(s, v)) + blk(body)
        }
        Stat::GenFor { vars, iters, body } => {
            vars.iter().map(nm).sum::<usize>() + iters.iter().map(|e| count_var(e, v)).sum::<usize>() + blk(body)
        }
        Stat::Do(b) => blk(b),
        Stat::Return(vals) => vals.iter().map(|e| count_var(e, v)).sum(),
        Stat::Call(e) => count_var(e, v),
        _ => 0,
    }
}

/// Fold single-use temporaries across a structured body (and rebuild table
/// constructors whose pieces only became adjacent after structuring).
pub fn fold_ast(b: &mut Vec<Stat>, facts: &mut VarFacts) -> bool {
    let mut changed = false;
    for s in b.iter_mut() {
        crate::astpass::for_each_child_mut(s, &mut |c| { changed |= fold_ast(c, facts); });
    }
    {
        let mut tmp = IrBlock { stmts: std::mem::take(b), cond: None, loop_vars: vec![] };
        changed |= build_constructors(&mut tmp, facts);
        *b = tmp.stmts;
    }
    let mut i = b.len();
    while i > 0 {
        i -= 1;
        let Some((v, e)) = single_def(&b[i]) else { continue };
        if !facts.foldable(v) || depth(e) > MAX_DEPTH { continue; }
        let e_eff = expr_eff(e);
        let mut e_vars = BTreeSet::new();
        expr_vars(e, &mut e_vars);
        if e_vars.contains(&v) { continue; }

        let mut x_eff = Eff::default();
        let mut x_writes: BTreeSet<VarId> = BTreeSet::new();
        let mut target: Option<(usize, bool)> = None; // (stmt, is_head)
        let mut j = i + 1;
        while j < b.len() && j - i <= LOOKAHEAD {
            let s = &b[j];
            let simple = matches!(s, Stat::Assign { .. } | Stat::Call(_) | Stat::Return(_) | Stat::Local { .. });
            let total = occurs_in_stat(s, v);
            if simple {
                if total > 0 {
                    let as_target = matches!(s, Stat::Assign { lhs, .. } if lhs.iter().any(|l| var_id(l) == Some(v)));
                    if total == 1 && !as_target { target = Some((j, false)); }
                    break;
                }
                if matches!(s, Stat::Return(_)) { break; }
                let (se, sw) = stat_eff(s);
                x_eff.add(se);
                x_writes.extend(sw);
                if !commutes(e_eff, &e_vars, x_eff, &x_writes) { break; }
                j += 1;
                continue;
            }
            let in_head: usize = head_exprs(s).iter().map(|x| count_var(x, v)).sum();
            if total == 1 && in_head == 1 { target = Some((j, true)); }
            break;
        }
        let Some((t, is_head)) = target else { continue };

        let mut before = x_eff;
        let exprs: Vec<&Expr> = if is_head { head_exprs(&b[t]) } else { stat_exprs(&b[t]) };
        if closure_called(e, v, &exprs) { continue; }
        if depth(e) + exprs.iter().map(|x| depth(x)).max().unwrap_or(0) > MAX_DEPTH { continue; }
        let mut acc = Eff::default();
        for x in exprs {
            if count_var(x, v) > 0 { eff_before(x, v, &mut acc); break; }
            acc.add(expr_eff(x));
        }
        before.add(acc);
        if !commutes(e_eff, &e_vars, before, &x_writes) { continue; }

        let Stat::Assign { mut rhs, .. } = b.remove(i) else { unreachable!() };
        let mut with = With { expr: Some(rhs.pop().unwrap()), single: !facts.pack[v] };
        if is_head { subst_head(&mut b[t - 1], v, &mut with); } else { subst_stat(&mut b[t - 1], v, &mut with); }
        facts.defs[v] = 0;
        facts.uses[v] = 0;
        changed = true;
    }
    changed
}

fn field(key: Expr, val: Expr) -> TableField {
    if let Expr::Str(b) = &key {
        if let Ok(s) = std::str::from_utf8(b) {
            if is_lua_ident(s) { return TableField::NameField(s.to_string(), val); }
        }
    }
    TableField::IndexField(key, val)
}
