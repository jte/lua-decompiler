//! Place `local` declarations and give variables their final names.

use std::collections::{BTreeMap, BTreeSet};

use lua_ast::{Expr, Stat, TableField};

use crate::astpass::for_each_child_mut;
use crate::lift::{pseudo_args, var_id};
use crate::simplify::count_var;
use crate::webs::VarId;

/// Path from the function body to a statement: `(stmt index, child block)`
/// steps, then the final statement index.
type Path = Vec<(usize, u16)>;

#[derive(Default)]
struct Occ {
    /// (path to the containing block, stmt index in that block)
    sites: Vec<(Path, usize)>,
}

fn visit_expr_vars(e: &Expr, f: &mut impl FnMut(VarId)) {
    crate::simplify::lua_ast_walk(e, &mut |x| if let Some(v) = var_id(x) { f(v); });
}

/// Variables referenced directly by a statement (not inside child blocks).
fn stat_vars(s: &Stat, f: &mut impl FnMut(VarId)) {
    match s {
        Stat::Assign { lhs, rhs } => { for e in lhs.iter().chain(rhs) { visit_expr_vars(e, f); } }
        Stat::Local { names, values } => {
            for n in names { if let Some(v) = name_var(n) { f(v); } }
            for e in values { visit_expr_vars(e, f); }
        }
        Stat::While { cond, .. } => visit_expr_vars(cond, f),
        Stat::If { branches, .. } => { for (c, _) in branches { visit_expr_vars(c, f); } }
        Stat::NumFor { var, from, to, step, .. } => {
            if let Some(v) = name_var(var) { f(v); }
            visit_expr_vars(from, f);
            visit_expr_vars(to, f);
            if let Some(s) = step { visit_expr_vars(s, f); }
        }
        Stat::GenFor { vars, iters, .. } => {
            for n in vars { if let Some(v) = name_var(n) { f(v); } }
            for e in iters { visit_expr_vars(e, f); }
        }
        Stat::Return(v) => { for e in v { visit_expr_vars(e, f); } }
        Stat::Call(e) => visit_expr_vars(e, f),
        _ => {}
    }
}

fn name_var(n: &str) -> Option<VarId> {
    n.strip_prefix("@v").and_then(|s| s.parse().ok())
}

fn collect(b: &[Stat], path: &mut Path, occ: &mut BTreeMap<VarId, Occ>, loop_vars: &mut BTreeSet<VarId>) {
    for (i, s) in b.iter().enumerate() {
        stat_vars(s, &mut |v| occ.entry(v).or_default().sites.push((path.clone(), i)));
        match s {
            Stat::NumFor { var, .. } => { if let Some(v) = name_var(var) { loop_vars.insert(v); } }
            Stat::GenFor { vars, .. } => { for n in vars { if let Some(v) = name_var(n) { loop_vars.insert(v); } } }
            _ => {}
        }
        // `until` sees the loop body's locals: count it as the body's end.
        if let Stat::Repeat { body, cond } = s {
            path.push((i, 0));
            visit_expr_vars(cond, &mut |v| occ.entry(v).or_default().sites.push((path.clone(), body.len())));
            path.pop();
        }
        let mut k = 0u16;
        match s {
            Stat::Do(c) | Stat::While { body: c, .. } | Stat::Repeat { body: c, .. }
            | Stat::NumFor { body: c, .. } | Stat::GenFor { body: c, .. } => {
                path.push((i, 0));
                collect(c, path, occ, loop_vars);
                path.pop();
            }
            Stat::If { branches, else_body } => {
                for (_, c) in branches {
                    path.push((i, k));
                    collect(c, path, occ, loop_vars);
                    path.pop();
                    k += 1;
                }
                if let Some(c) = else_body {
                    path.push((i, u16::MAX));
                    collect(c, path, occ, loop_vars);
                    path.pop();
                }
            }
            _ => {}
        }
    }
}

fn block_at<'a>(b: &'a mut Vec<Stat>, path: &[(usize, u16)]) -> &'a mut Vec<Stat> {
    let Some(&(i, k)) = path.first() else { return b };
    let child = match &mut b[i] {
        Stat::Do(c) | Stat::While { body: c, .. } | Stat::Repeat { body: c, .. }
        | Stat::NumFor { body: c, .. } | Stat::GenFor { body: c, .. } => c,
        Stat::If { branches, else_body } => {
            if k == u16::MAX { else_body.as_mut().unwrap() } else { &mut branches[k as usize].1 }
        }
        _ => unreachable!(),
    };
    block_at(child, &path[1..])
}

/// Insert `local` declarations for every variable except `skip`
/// (parameters).  Returns the declared variables.
pub fn place(body: &mut Vec<Stat>, skip: &BTreeSet<VarId>) -> BTreeSet<VarId> {
    let mut occ: BTreeMap<VarId, Occ> = BTreeMap::new();
    let mut loop_vars = BTreeSet::new();
    collect(body, &mut Vec::new(), &mut occ, &mut loop_vars);

    // Declaration point per variable: (block path, index).
    let mut points: BTreeMap<(Path, usize), Vec<VarId>> = BTreeMap::new();
    for (&v, o) in &occ {
        if skip.contains(&v) || loop_vars.contains(&v) { continue; }
        let mut prefix: Path = o.sites[0].0.clone();
        let mut idx: Option<usize> = None;
        for (p, i) in &o.sites {
            let common = prefix.iter().zip(p.iter()).take_while(|(a, b)| a == b).count();
            prefix.truncate(common);
        }
        for (p, i) in &o.sites {
            let at = if p.len() > prefix.len() { p[prefix.len()].0 } else { *i };
            idx = Some(idx.map_or(at, |x: usize| x.min(at)));
        }
        points.entry((prefix, idx.unwrap())).or_default().push(v);
    }

    let declared: BTreeSet<VarId> = points.values().flatten().copied().collect();
    // Insert from the back so earlier indices stay valid.
    for ((path, idx), vars) in points.into_iter().rev() {
        let blk = block_at(body, &path);
        let vars: BTreeSet<VarId> = vars.into_iter().collect();
        // Merge into the first assignment when it assigns exactly these vars.
        let mut merged: BTreeSet<VarId> = BTreeSet::new();
        if let Some(Stat::Assign { lhs, rhs }) = blk.get(idx) {
            let lv: Vec<Option<VarId>> = lhs.iter().map(var_id).collect();
            let all_vars = lv.iter().all(|x| x.is_some());
            let set: BTreeSet<VarId> = lv.iter().flatten().copied().collect();
            let rhs_clean = rhs.iter().all(|e| set.iter().all(|&v| count_var(e, v) == 0));
            if all_vars && set.len() == lv.len() && set.is_subset(&vars) && rhs_clean {
                let names = lv.iter().map(|x| format!("@v{}", x.unwrap())).collect();
                let rhs = rhs.clone();
                blk[idx] = Stat::Local { names, values: rhs };
                merged = set;
            }
        }
        let rest: Vec<String> = vars.iter().filter(|v| !merged.contains(v)).map(|v| format!("@v{}", v)).collect();
        if !rest.is_empty() {
            blk.insert(idx, Stat::Local { names: rest, values: vec![] });
        }
    }
    remove_uses(body);
    declared
}

/// A `goto` may not jump into the scope of a local, so in every block that
/// contains a label all of its `local` declarations move to the block start.
pub fn hoist_for_labels(b: &mut Vec<Stat>) {
    for s in b.iter_mut() { for_each_child_mut(s, &mut hoist_for_labels); }
    if !b.iter().any(|s| matches!(s, Stat::Label(_))) { return; }
    let mut names: Vec<String> = Vec::new();
    let old = std::mem::take(b);
    for s in old {
        match s {
            Stat::Local { names: ns, values } => {
                names.extend(ns.iter().cloned());
                if !values.is_empty() {
                    b.push(Stat::Assign { lhs: ns.into_iter().map(Expr::Name).collect(), rhs: values });
                }
            }
            other => b.push(other),
        }
    }
    if !names.is_empty() {
        b.insert(0, Stat::Local { names, values: vec![] });
    }
}

/// Lua allows at most 200 active locals per function.  Where a block would
/// exceed that, reuse the name of a dead, non-captured local for a new one
/// (exactly what the VM's register allocation did).
pub fn coalesce(b: &mut Vec<Stat>, outer: usize) {
    const LIMIT: usize = 100;
    let declared = |b: &Vec<Stat>| b.iter().map(|s| match s { Stat::Local { names, .. } => names.len(), _ => 0 }).sum::<usize>();
    if outer + declared(b) > LIMIT {
        coalesce_block(b);
    }
    let here = outer + declared(b);
    for s in b.iter_mut() {
        for_each_child_mut(s, &mut |c| coalesce(c, here));
    }
}

fn vars_in_stat(s: &Stat, out: &mut BTreeSet<VarId>) {
    stat_vars(s, &mut |v| { out.insert(v); });
    let mut sub = |c: &Vec<Stat>| { for x in c { vars_in_stat(x, out); } };
    crate::astpass::for_each_child(s, &mut sub);
    if let Stat::Repeat { cond, .. } = s { visit_expr_vars(cond, &mut |v| { out.insert(v); }); }
}

fn captured_in_stat(s: &Stat, out: &mut BTreeSet<VarId>) {
    let mut look = |e: &Expr| {
        crate::simplify::lua_ast_walk(e, &mut |x| {
            if let Some(args) = pseudo_args(x, "@closure") {
                for a in &args[1..] { if let Some(v) = var_id(a) { out.insert(v); } }
            }
        });
    };
    match s {
        Stat::Assign { lhs, rhs } => { for e in lhs.iter().chain(rhs) { look(e); } }
        Stat::Local { values, .. } => { for e in values { look(e); } }
        Stat::Call(e) => look(e),
        Stat::Return(v) => { for e in v { look(e); } }
        Stat::If { branches, .. } => { for (c, _) in branches { look(c); } }
        Stat::While { cond, .. } | Stat::Repeat { cond, .. } => look(cond),
        Stat::NumFor { from, to, step, .. } => { look(from); look(to); if let Some(s) = step { look(s); } }
        Stat::GenFor { iters, .. } => { for e in iters { look(e); } }
        _ => {}
    }
    let mut sub = |c: &Vec<Stat>| { for x in c { captured_in_stat(x, out); } };
    crate::astpass::for_each_child(s, &mut sub);
}

fn coalesce_block(b: &mut Vec<Stat>) {
    let mut captured = BTreeSet::new();
    for s in b.iter() { captured_in_stat(s, &mut captured); }
    // Last statement index (at this level) mentioning each variable.
    let mut last: BTreeMap<VarId, usize> = BTreeMap::new();
    for (i, s) in b.iter().enumerate() {
        let mut vs = BTreeSet::new();
        vars_in_stat(s, &mut vs);
        for v in vs { last.insert(v, i); }
    }
    let mut live_decl: Vec<VarId> = Vec::new(); // declared here, possibly still live
    let mut alias: BTreeMap<VarId, VarId> = BTreeMap::new();
    for i in 0..b.len() {
        // Apply earlier aliases to this statement.
        if !alias.is_empty() {
            let names: BTreeMap<VarId, String> = alias.iter().map(|(&k, &v)| (k, format!("@v{}", v))).collect();
            let mut one = vec![std::mem::replace(&mut b[i], Stat::Break)];
            rename(&mut one, &names);
            b[i] = one.pop().unwrap();
        }
        let Stat::Local { names, values } = &b[i] else { continue };
        if names.len() != 1 {
            for n in names { if let Some(v) = name_var(n) { live_decl.push(v); } }
            continue;
        }
        let Some(new) = name_var(&names[0]) else { continue };
        // A dead, uncaptured local declared earlier in this block.
        let reuse = live_decl.iter().position(|&old| {
            last.get(&old).map_or(true, |&l| l < i) && !captured.contains(&old) && !captured.contains(&new)
        });
        match reuse {
            Some(p) => {
                let old = live_decl.remove(p);
                let rhs = if values.is_empty() { vec![Expr::Nil] } else { values.clone() };
                b[i] = Stat::Assign { lhs: vec![Expr::Name(format!("@v{}", old))], rhs };
                alias.insert(new, old);
                let l = last.get(&new).copied().unwrap_or(i);
                last.insert(old, l);
                live_decl.push(old);
            }
            None => live_decl.push(new),
        }
    }
}

/// Last resort for the 200-locals limit: move uncaptured locals into slots
/// of one table `S` (variable `spill_var`).  Returns true if anything moved.
pub fn spill(body: &mut Vec<Stat>, nparams: usize, spill_var: VarId) -> bool {
    const BUDGET: usize = 110;
    let mut captured = BTreeSet::new();
    for s in body.iter() { captured_in_stat(s, &mut captured); }
    let mut chosen: Vec<VarId> = Vec::new();
    pick_spills(body, nparams + 1, BUDGET, &captured, &mut chosen);
    if chosen.is_empty() { return false; }
    let slots: BTreeMap<VarId, i64> = chosen.iter().enumerate().map(|(i, &v)| (v, i as i64 + 1)).collect();
    apply_spills(body, &slots, spill_var);
    body.insert(0, Stat::Local { names: vec![format!("@v{}", spill_var)], values: vec![Expr::Table(vec![])] });
    true
}

fn pick_spills(b: &Vec<Stat>, outer: usize, budget: usize, captured: &BTreeSet<VarId>, chosen: &mut Vec<VarId>) {
    let mine: Vec<VarId> = b.iter().flat_map(|s| match s {
        Stat::Local { names, .. } => names.iter().filter_map(|n| name_var(n)).collect::<Vec<_>>(),
        _ => vec![],
    }).collect();
    let mut kept = mine.len();
    if outer + kept > budget {
        for &v in mine.iter().rev() {
            if outer + kept <= budget { break; }
            if captured.contains(&v) { continue; }
            chosen.push(v);
            kept -= 1;
        }
    }
    let here = outer + kept;
    for s in b {
        let mut sub = |c: &Vec<Stat>| pick_spills(c, here, budget, captured, chosen);
        crate::astpass::for_each_child(s, &mut sub);
    }
}

fn apply_spills(b: &mut Vec<Stat>, slots: &BTreeMap<VarId, i64>, s: VarId) {
    lua_ast::transform_block(b, &mut |e: &mut Expr| {
        if let Some(v) = var_id(e) {
            if let Some(&k) = slots.get(&v) {
                *e = Expr::Index { table: Box::new(Expr::Name(format!("@v{}", s))), key: Box::new(Expr::Integer(k)) };
            }
        }
    });
    apply_spills_stats(b, slots, s, true);
}

/// Rewrite the declarations of spilled locals (expressions were already
/// handled).  A declaration without value resets the slot to nil, except at
/// the top of the function body where the table is fresh anyway.
fn apply_spills_stats(b: &mut Vec<Stat>, slots: &BTreeMap<VarId, i64>, s: VarId, root: bool) {
    let slot = |v: VarId| Expr::Index {
        table: Box::new(Expr::Name(format!("@v{}", s))),
        key: Box::new(Expr::Integer(slots[&v])),
    };
    let is_spilled = |n: &String| name_var(n).map_or(false, |v| slots.contains_key(&v));
    let old = std::mem::take(b);
    let mut at_top = root;
    for st in old {
        match st {
            Stat::Local { names, values } if names.iter().any(is_spilled) => {
                let keep: Vec<String> = names.iter().filter(|n| !is_spilled(n)).cloned().collect();
                if !keep.is_empty() { b.push(Stat::Local { names: keep.clone(), values: vec![] }); }
                if values.is_empty() {
                    if !at_top {
                        // Lua's parser recurses per assignment target; keep lists short.
                        let targets: Vec<Expr> = names.iter().filter(|n| is_spilled(n))
                            .map(|n| slot(name_var(n).unwrap())).collect();
                        for chunk in targets.chunks(50) {
                            b.push(Stat::Assign { lhs: chunk.to_vec(), rhs: vec![Expr::Nil] });
                        }
                    }
                } else {
                    let lhs: Vec<Expr> = names.iter().map(|n| match name_var(n) {
                        Some(v) if slots.contains_key(&v) => slot(v),
                        _ => Expr::Name(n.clone()),
                    }).collect();
                    b.push(Stat::Assign { lhs, rhs: values });
                }
            }
            mut other => {
                at_top = at_top && matches!(other, Stat::Local { .. });
                for_each_child_mut(&mut other, &mut |c| apply_spills_stats(c, slots, s, false));
                b.push(other);
            }
        }
    }
}

fn remove_uses(b: &mut Vec<Stat>) {
    b.retain(|s| !matches!(s, Stat::Call(e) if pseudo_args(e, "@uses").is_some()));
    for s in b.iter_mut() { for_each_child_mut(s, &mut remove_uses); }
}

// ---------------------------------------------------------------------------
// Renaming
// ---------------------------------------------------------------------------

pub fn rename(b: &mut Vec<Stat>, names: &BTreeMap<VarId, String>) {
    let ren_name = |n: &mut String| {
        if let Some(v) = name_var(n) { if let Some(x) = names.get(&v) { *n = x.clone(); } }
    };
    for s in b.iter_mut() {
        match s {
            Stat::Assign { lhs, rhs } => { for e in lhs.iter_mut().chain(rhs.iter_mut()) { rename_expr(e, names); } }
            Stat::Local { names: ns, values } => {
                for n in ns.iter_mut() { ren_name(n); }
                for e in values { rename_expr(e, names); }
            }
            Stat::While { cond, .. } => rename_expr(cond, names),
            Stat::Repeat { cond, .. } => rename_expr(cond, names),
            Stat::If { branches, .. } => { for (c, _) in branches.iter_mut() { rename_expr(c, names); } }
            Stat::NumFor { var, from, to, step, .. } => {
                ren_name(var);
                rename_expr(from, names);
                rename_expr(to, names);
                if let Some(s) = step { rename_expr(s, names); }
            }
            Stat::GenFor { vars, iters, .. } => {
                for n in vars.iter_mut() { ren_name(n); }
                for e in iters { rename_expr(e, names); }
            }
            Stat::Return(v) => { for e in v { rename_expr(e, names); } }
            Stat::Call(e) => rename_expr(e, names),
            _ => {}
        }
        for_each_child_mut(s, &mut |c| rename(c, names));
    }
}

fn rename_expr(e: &mut Expr, names: &BTreeMap<VarId, String>) {
    match e {
        Expr::Name(n) => { if let Some(v) = name_var(n) { if let Some(x) = names.get(&v) { *n = x.clone(); } } }
        Expr::Index { table, key } => { rename_expr(table, names); rename_expr(key, names); }
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => { rename_expr(func, names); for a in args { rename_expr(a, names); } }
        Expr::BinOp { lhs, rhs, .. } => { rename_expr(lhs, names); rename_expr(rhs, names); }
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => rename_expr(operand, names),
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::IndexField(k, v) => { rename_expr(k, names); rename_expr(v, names); }
                    TableField::NameField(_, v) | TableField::ValueField(v) => rename_expr(v, names),
                }
            }
        }
        _ => {}
    }
}

/// The value a declared variable is first initialized with (for naming).
pub fn init_kinds(b: &[Stat], out: &mut BTreeMap<VarId, char>) {
    for s in b {
        match s {
            Stat::Local { names, values } if names.len() == 1 && values.len() == 1 => {
                if let Some(v) = name_var(&names[0]) {
                    let k = match &values[0] {
                        Expr::Table(_) => 't',
                        Expr::Function(_) => 'f',
                        e if pseudo_args(e, "@closure").is_some() => 'f',
                        _ => 'v',
                    };
                    out.entry(v).or_insert(k);
                }
            }
            Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => {
                if let Some(v) = var_id(&lhs[0]) {
                    if pseudo_args(&rhs[0], "@closure").is_some() { out.entry(v).or_insert('f'); }
                }
            }
            Stat::NumFor { var, .. } => { if let Some(v) = name_var(var) { out.insert(v, 'i'); } }
            Stat::GenFor { vars, .. } => {
                for (k, n) in vars.iter().enumerate() {
                    if let Some(v) = name_var(n) { out.insert(v, if k == 0 { 'k' } else { 'v' }); }
                }
            }
            _ => {}
        }
        let mut sub = |c: &Vec<Stat>| init_kinds(c, out);
        crate::astpass::for_each_child(s, &mut sub);
    }
}
