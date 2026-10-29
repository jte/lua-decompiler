//! Safety checks shared by the passes.  They look at the whole subtree,
//! including nested blocks and function bodies, because a closure can read
//! or write any local it captures.

use std::collections::{BTreeMap, BTreeSet};

use lua_ast::{Block, Expr, Stat, TableField};

use crate::walk_expr;

/// Every expression directly in `s` (not inside child blocks).
fn stat_exprs(s: &Stat) -> Vec<&Expr> {
    match s {
        Stat::Assign { lhs, rhs } => lhs.iter().chain(rhs).collect(),
        Stat::Local { values, .. } => values.iter().collect(),
        Stat::While { cond, .. } | Stat::Repeat { cond, .. } => vec![cond],
        Stat::If { branches, .. } => branches.iter().map(|(c, _)| c).collect(),
        Stat::NumFor { from, to, step, .. } => {
            let mut v = vec![from, to];
            if let Some(s) = step { v.push(s); }
            v
        }
        Stat::GenFor { iters, .. } => iters.iter().collect(),
        Stat::Return(v) => v.iter().collect(),
        Stat::Call(e) => vec![e],
        _ => vec![],
    }
}

fn child_blocks(s: &Stat) -> Vec<&Block> {
    match s {
        Stat::Do(b) | Stat::While { body: b, .. } | Stat::Repeat { body: b, .. }
        | Stat::NumFor { body: b, .. } | Stat::GenFor { body: b, .. } => vec![b],
        Stat::If { branches, else_body } => {
            let mut v: Vec<&Block> = branches.iter().map(|(_, b)| b).collect();
            if let Some(e) = else_body { v.push(e); }
            v
        }
        _ => vec![],
    }
}

/// Visit every statement in `b` and in nested blocks and function bodies.
pub fn visit_stats(b: &[Stat], f: &mut impl FnMut(&Stat)) {
    for s in b {
        f(s);
        for e in stat_exprs(s) {
            walk_expr(e, &mut |x| if let Expr::Function(fb) = x { visit_stats(&fb.body, f); });
        }
        for c in child_blocks(s) { visit_stats(c, f); }
    }
}

/// Visit every expression node anywhere in `b` (including function bodies).
pub fn visit_exprs(b: &[Stat], f: &mut impl FnMut(&Expr)) {
    visit_stats(b, &mut |s| {
        for e in stat_exprs(s) { walk_expr(e, &mut |x| f(x)); }
    });
}

/// Number of references to `name` anywhere (reads, writes, declarations).
pub fn count_refs(b: &[Stat], name: &str) -> usize {
    let mut n = 0;
    visit_stats(b, &mut |s| {
        match s {
            Stat::Local { names, .. } => n += names.iter().filter(|x| *x == name).count(),
            Stat::NumFor { var, .. } => n += (var == name) as usize,
            Stat::GenFor { vars, .. } => n += vars.iter().filter(|x| *x == name).count(),
            _ => {}
        }
        for e in stat_exprs(s) {
            walk_expr(e, &mut |x| {
                if matches!(x, Expr::Name(m) if m == name) { n += 1; }
                if let Expr::Function(fb) = x { n += fb.params.iter().filter(|p| *p == name).count(); }
            });
        }
    });
    n
}

/// Names assigned anywhere (`name = ...`), plus names declared more than once
/// (locals, loop variables, parameters).
pub fn assigned_names(b: &[Stat]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut decls: BTreeMap<String, usize> = BTreeMap::new();
    visit_stats(b, &mut |s| match s {
        Stat::Assign { lhs, .. } => { for l in lhs { if let Expr::Name(n) = l { out.insert(n.clone()); } } }
        Stat::Local { names, .. } => { for n in names { *decls.entry(n.clone()).or_default() += 1; } }
        Stat::NumFor { var, .. } => *decls.entry(var.clone()).or_default() += 1,
        Stat::GenFor { vars, .. } => { for v in vars { *decls.entry(v.clone()).or_default() += 1; } }
        _ => {}
    });
    visit_exprs(b, &mut |e| if let Expr::Function(fb) = e {
        for p in &fb.params { *decls.entry(p.clone()).or_default() += 1; }
    });
    out.extend(decls.into_iter().filter(|(_, c)| *c > 1).map(|(n, _)| n));
    out
}

/// No calls anywhere in `e` (function literals are not entered: creating a
/// closure has no effect).
pub fn is_pure(e: &Expr) -> bool {
    let mut pure = true;
    walk_expr(e, &mut |x| if matches!(x, Expr::Call { .. } | Expr::Method { .. }) { pure = false; });
    pure
}

/// Is the local table `t`, declared once in `b`, only ever read as `t[...]`?
/// It must never be assigned, written through, passed anywhere or used as a
/// plain value — anywhere, including closures.
pub fn read_only_table(b: &[Stat], t: &str) -> bool {
    fn ok_expr(e: &Expr, t: &str) -> bool {
        match e {
            Expr::Name(n) => n != t,
            Expr::Index { table, key } => {
                (matches!(table.as_ref(), Expr::Name(n) if n == t) || ok_expr(table, t)) && ok_expr(key, t)
            }
            Expr::Call { func, args } => ok_expr(func, t) && args.iter().all(|a| ok_expr(a, t)),
            Expr::Method { obj, args, .. } => ok_expr(obj, t) && args.iter().all(|a| ok_expr(a, t)),
            Expr::BinOp { lhs, rhs, .. } => ok_expr(lhs, t) && ok_expr(rhs, t),
            Expr::UnOp { operand, .. } | Expr::Paren(operand) => ok_expr(operand, t),
            Expr::Table(fields) => fields.iter().all(|f| match f {
                TableField::IndexField(k, v) => ok_expr(k, t) && ok_expr(v, t),
                TableField::NameField(_, v) | TableField::ValueField(v) => ok_expr(v, t),
            }),
            Expr::Function(fb) => fb.body.iter().all(|s| ok_stat(s, t)),
            _ => true,
        }
    }
    fn ok_stat(s: &Stat, t: &str) -> bool {
        if let Stat::Assign { lhs, rhs } = s {
            return lhs.iter().all(|l| match l {
                Expr::Name(n) => n != t,
                Expr::Index { table, key } if matches!(table.as_ref(), Expr::Name(n) if n == t) => {
                    let _ = key;
                    false
                }
                other => ok_expr(other, t),
            }) && rhs.iter().all(|e| ok_expr(e, t));
        }
        if let Stat::Local { names, values } = s {
            if names.iter().any(|n| n == t) { return false; }
            return values.iter().all(|e| ok_expr(e, t));
        }
        stat_exprs(s).iter().all(|e| ok_expr(e, t)) && child_blocks(s).iter().all(|b| b.iter().all(|s| ok_stat(s, t)))
    }
    let mut decls = 0;
    for s in b {
        if let Stat::Local { names, values } = s {
            if names.iter().any(|n| n == t) {
                decls += 1;
                if !values.iter().all(|e| ok_expr(e, t)) { return false; }
                continue;
            }
        }
        if !ok_stat(s, t) { return false; }
    }
    decls == 1
}
