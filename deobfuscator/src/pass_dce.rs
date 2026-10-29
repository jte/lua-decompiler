/// Pass – dead local elimination.
///
/// Removes, where `x` is a local that is never read anywhere:
///   • `local x = <value without calls>`  (incl. functions and tables)
///   • `x = <value without calls>`
/// and repeats, since removing one may leave others unread.

use std::collections::{BTreeMap, BTreeSet};
use lua_ast::{Block, Expr, Stat};

use crate::util::{is_pure, visit_exprs, visit_stats};

pub fn run(block: &mut Block) {
    for _ in 0..10 {
        if !run_once(block) { break; }
    }
}

fn run_once(block: &mut Block) -> bool {
    // Locals declared exactly once (so a name means one variable).
    let mut locals: BTreeSet<String> = BTreeSet::new();
    visit_stats(block, &mut |s| if let Stat::Local { names, .. } = s {
        for n in names { locals.insert(n.clone()); }
    });
    // A local with an assignment that has to stay (it calls something) keeps
    // its declaration, or that assignment would become a global write.
    let mut kept: BTreeSet<String> = BTreeSet::new();
    visit_stats(block, &mut |s| match s {
        Stat::Assign { lhs, rhs } if !removable(rhs) => {
            for l in lhs { if let Expr::Name(n) = l { kept.insert(n.clone()); } }
        }
        Stat::Local { names, values } if !removable(values) => { for n in names { kept.insert(n.clone()); } }
        _ => {}
    });
    let mut redeclared: BTreeMap<String, usize> = BTreeMap::new();
    visit_stats(block, &mut |s| match s {
        Stat::Local { names, .. } => { for n in names { *redeclared.entry(n.clone()).or_default() += 1; } }
        Stat::NumFor { var, .. } => *redeclared.entry(var.clone()).or_default() += 1,
        Stat::GenFor { vars, .. } => { for v in vars { *redeclared.entry(v.clone()).or_default() += 1; } }
        _ => {}
    });
    visit_exprs(block, &mut |e| if let Expr::Function(fb) = e {
        for p in &fb.params { *redeclared.entry(p.clone()).or_default() += 1; }
    });
    locals.retain(|n| redeclared.get(n) == Some(&1));

    // Reads: every Name occurrence except plain assignment targets.
    let mut reads: BTreeSet<String> = BTreeSet::new();
    visit_stats(block, &mut |s| {
        let mut read = |e: &Expr| crate::walk_expr(e, &mut |x| if let Expr::Name(n) = x { reads.insert(n.clone()); });
        match s {
            Stat::Assign { lhs, rhs } => {
                for l in lhs {
                    if let Expr::Index { table, key } = l { read(table); read(key); }
                    if !matches!(l, Expr::Name(_)) && !matches!(l, Expr::Index { .. }) { read(l); }
                }
                for e in rhs { read(e); }
            }
            Stat::Local { values, .. } => { for e in values { read(e); } }
            Stat::While { cond, .. } | Stat::Repeat { cond, .. } => read(cond),
            Stat::If { branches, .. } => { for (c, _) in branches { read(c); } }
            Stat::NumFor { from, to, step, .. } => { read(from); read(to); if let Some(s) = step { read(s); } }
            Stat::GenFor { iters, .. } => { for e in iters { read(e); } }
            Stat::Return(v) => { for e in v { read(e); } }
            Stat::Call(e) => read(e),
            _ => {}
        }
    });
    let dead: BTreeSet<String> = locals.difference(&reads).filter(|n| !kept.contains(*n)).cloned().collect();
    if dead.is_empty() { return false; }

    let mut changed = false;
    remove(block, &dead, &mut changed);
    changed
}

fn removable(values: &[Expr]) -> bool {
    values.iter().all(is_pure)
}

fn remove(block: &mut Block, dead: &BTreeSet<String>, changed: &mut bool) {
    block.retain(|s| {
        let drop = match s {
            Stat::Local { names, values } => names.iter().all(|n| dead.contains(n)) && removable(values),
            Stat::Assign { lhs, rhs } => {
                lhs.iter().all(|l| matches!(l, Expr::Name(n) if dead.contains(n))) && removable(rhs)
            }
            _ => false,
        };
        if drop { *changed = true; }
        !drop
    });
    for s in block.iter_mut() {
        match s {
            Stat::Do(b) | Stat::While { body: b, .. } | Stat::Repeat { body: b, .. }
            | Stat::NumFor { body: b, .. } | Stat::GenFor { body: b, .. } => remove(b, dead, changed),
            Stat::If { branches, else_body } => {
                for (_, b) in branches.iter_mut() { remove(b, dead, changed); }
                if let Some(b) = else_body { remove(b, dead, changed); }
            }
            _ => {}
        }
        // Function bodies.
        let mut in_fn = |e: &mut Expr| lua_ast::transform_expr(e, &mut |x| {
            if let Expr::Function(fb) = x { remove(&mut fb.body, dead, changed); }
        });
        match s {
            Stat::Assign { lhs, rhs } => { for e in lhs.iter_mut().chain(rhs.iter_mut()) { in_fn(e); } }
            Stat::Local { values, .. } => { for e in values.iter_mut() { in_fn(e); } }
            Stat::Return(v) => { for e in v.iter_mut() { in_fn(e); } }
            Stat::Call(e) => in_fn(e),
            _ => {}
        }
    }
}
