/// Pass – constant and identity function inlining, constant field reads.
///
/// Phase 1: `local f = function() return LITERAL end` → every `f()` becomes
///          LITERAL.
/// Phase 2: `local f = function(a, ...) return a end` → `f(x, <pure>...)`
///          becomes `x` (parenthesised if it is a call: one value only).
/// Phase 3: a local table whose every use is `t["k"]` with constant keys and
///          whose fields are each set once (in its constructor or by one
///          top-level `t["k"] = v` with a stable value): later reads of
///          `t["k"]` become `v`.
///
/// Functions and tables are only touched when declared once and never
/// reassigned; declarations are removed when nothing refers to them.

use std::collections::{BTreeMap, BTreeSet};
use lua_ast::{Block, Expr, Stat, TableField};

use crate::for_each_block;
use crate::util::{assigned_names, count_refs, is_pure};

pub fn run(block: &mut Block) {
    let assigned = assigned_names(block);
    for_each_block(block, &mut |b| process_block(b, &assigned));
}

fn process_block(block: &mut Block, assigned: &BTreeSet<String>) {
    for _ in 0..20 {
        let a = inline_const_funcs(block, assigned);
        let b = inline_identity_funcs(block, assigned);
        if !a && !b { break; }
    }
    substitute_table_reads(block, assigned);
}

/// `local f = function(...) <body> end` declared in this block.
fn local_functions(block: &Block, assigned: &BTreeSet<String>) -> Vec<(String, lua_ast::FuncBody)> {
    block.iter().filter_map(|s| match s {
        Stat::Local { names, values } if names.len() == 1 && values.len() == 1 && !assigned.contains(&names[0]) => {
            if let Expr::Function(fb) = &values[0] { Some((names[0].clone(), (**fb).clone())) } else { None }
        }
        _ => None,
    }).collect()
}

fn remove_unused_decls(block: &mut Block, names: &[String]) {
    for n in names {
        if count_refs(block, n) == 1 {
            block.retain(|s| !matches!(s, Stat::Local { names: ns, .. } if ns.len() == 1 && ns[0] == *n));
        }
    }
}

fn inline_const_funcs(block: &mut Block, assigned: &BTreeSet<String>) -> bool {
    let consts: BTreeMap<String, Expr> = local_functions(block, assigned).into_iter().filter_map(|(n, fb)| {
        match fb.body.as_slice() {
            [Stat::Return(v)] if v.len() == 1 && v[0].is_literal() && !fb.has_vararg => Some((n, v[0].clone())),
            _ => None,
        }
    }).collect();
    if consts.is_empty() { return false; }
    let mut changed = false;
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Call { func, args } = e {
            if let Expr::Name(n) = func.as_ref() {
                if let Some(lit) = consts.get(n) {
                    // Arguments are evaluated (and ignored) by the call.
                    if args.iter().all(is_pure) {
                        *e = lit.clone();
                        changed = true;
                    }
                }
            }
        }
    });
    remove_unused_decls(block, &consts.keys().cloned().collect::<Vec<_>>());
    changed
}

fn inline_identity_funcs(block: &mut Block, assigned: &BTreeSet<String>) -> bool {
    let ids: BTreeSet<String> = local_functions(block, assigned).into_iter().filter_map(|(n, fb)| {
        match fb.body.as_slice() {
            [Stat::Return(v)] if v.len() == 1 && !fb.params.is_empty()
                && matches!(&v[0], Expr::Name(p) if *p == fb.params[0]) => Some(n),
            _ => None,
        }
    }).collect();
    if ids.is_empty() { return false; }
    let mut changed = false;
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Call { func, args } = e {
            if let Expr::Name(n) = func.as_ref() {
                if ids.contains(n) && !args.is_empty() && args[1..].iter().all(is_pure) {
                    let a = args[0].clone();
                    *e = match a {
                        Expr::Call { .. } | Expr::Method { .. } | Expr::Vararg => Expr::Paren(Box::new(a)),
                        other => other,
                    };
                    changed = true;
                }
            }
        }
    });
    remove_unused_decls(block, &ids.into_iter().collect::<Vec<_>>());
    changed
}

// ---------------------------------------------------------------------------
// Phase 3
// ---------------------------------------------------------------------------

/// A value that means the same wherever it is read later.
fn stable(e: &Expr, assigned: &BTreeSet<String>) -> bool {
    match e {
        _ if e.is_literal() => true,
        Expr::Name(n) => !assigned.contains(n),
        _ => false,
    }
}

/// Is every reference to `t` in `b` either a constant-key read or one of the
/// allowed top-level writes?
fn only_const_key_uses(b: &Block, t: &str, writes_ok: &BTreeSet<usize>) -> bool {
    fn ok_expr(e: &Expr, t: &str) -> bool {
        match e {
            Expr::Name(n) => n != t,
            Expr::Index { table, key } if matches!(table.as_ref(), Expr::Name(n) if n == t) => {
                matches!(key.as_ref(), Expr::Str(_))
            }
            _ => {
                let mut ok = true;
                match e {
                    Expr::Index { table, key } => ok = ok_expr(table, t) && ok_expr(key, t),
                    Expr::Call { func, args } => ok = ok_expr(func, t) && args.iter().all(|a| ok_expr(a, t)),
                    Expr::Method { obj, args, .. } => ok = ok_expr(obj, t) && args.iter().all(|a| ok_expr(a, t)),
                    Expr::BinOp { lhs, rhs, .. } => ok = ok_expr(lhs, t) && ok_expr(rhs, t),
                    Expr::UnOp { operand, .. } | Expr::Paren(operand) => ok = ok_expr(operand, t),
                    Expr::Table(fields) => ok = fields.iter().all(|f| match f {
                        TableField::IndexField(k, v) => ok_expr(k, t) && ok_expr(v, t),
                        TableField::NameField(_, v) | TableField::ValueField(v) => ok_expr(v, t),
                    }),
                    Expr::Function(fb) => ok = fb.body.iter().all(|s| ok_stat(s, t)),
                    _ => {}
                }
                ok
            }
        }
    }
    fn ok_stat(s: &Stat, t: &str) -> bool {
        match s {
            Stat::Assign { lhs, rhs } => lhs.iter().all(|l| match l {
                Expr::Name(n) => n != t,
                Expr::Index { table, key } if matches!(table.as_ref(), Expr::Name(n) if n == t) => {
                    let _ = key;
                    false
                }
                other => ok_expr(other, t),
            }) && rhs.iter().all(|e| ok_expr(e, t)),
            Stat::Local { names, values } => !names.iter().any(|n| n == t) && values.iter().all(|e| ok_expr(e, t)),
            Stat::While { cond, body } | Stat::Repeat { body, cond } => ok_expr(cond, t) && body.iter().all(|s| ok_stat(s, t)),
            Stat::If { branches, else_body } => {
                branches.iter().all(|(c, b)| ok_expr(c, t) && b.iter().all(|s| ok_stat(s, t)))
                    && else_body.as_ref().map_or(true, |b| b.iter().all(|s| ok_stat(s, t)))
            }
            Stat::NumFor { from, to, step, body, .. } => {
                ok_expr(from, t) && ok_expr(to, t) && step.as_ref().map_or(true, |s| ok_expr(s, t))
                    && body.iter().all(|s| ok_stat(s, t))
            }
            Stat::GenFor { iters, body, .. } => iters.iter().all(|e| ok_expr(e, t)) && body.iter().all(|s| ok_stat(s, t)),
            Stat::Do(b) => b.iter().all(|s| ok_stat(s, t)),
            Stat::Return(v) => v.iter().all(|e| ok_expr(e, t)),
            Stat::Call(e) => ok_expr(e, t),
            _ => true,
        }
    }
    b.iter().enumerate().all(|(i, s)| {
        if writes_ok.contains(&i) {
            // The allowed `t["k"] = v`: only the value is checked.
            if let Stat::Assign { rhs, .. } = s { return rhs.iter().all(|e| ok_expr(e, t)); }
        }
        if let Stat::Local { names, values } = s {
            if names.len() == 1 && names[0] == t { return values.iter().all(|e| ok_expr(e, t)); }
        }
        ok_stat(s, t)
    })
}

fn substitute_table_reads(block: &mut Block, assigned: &BTreeSet<String>) {
    for decl in 0..block.len() {
        let (t, fields) = match &block[decl] {
            Stat::Local { names, values } if names.len() == 1 && values.len() == 1 && !assigned.contains(&names[0]) => {
                match &values[0] { Expr::Table(f) => (names[0].clone(), f.clone()), _ => continue }
            }
            _ => continue,
        };
        // Field values known from the constructor (available from decl on).
        let mut known: BTreeMap<Vec<u8>, (Expr, usize)> = BTreeMap::new();
        let mut set_count: BTreeMap<Vec<u8>, usize> = BTreeMap::new();
        for f in &fields {
            let (k, v) = match f {
                TableField::NameField(k, v) => (k.as_bytes().to_vec(), v),
                TableField::IndexField(Expr::Str(k), v) => (k.clone(), v),
                _ => continue,
            };
            *set_count.entry(k.clone()).or_default() += 1;
            if stable(v, assigned) { known.insert(k, (v.clone(), decl)); }
        }
        // Single top-level writes `t["k"] = v` after the declaration.
        let mut writes_ok = BTreeSet::new();
        for (i, s) in block.iter().enumerate().skip(decl + 1) {
            if let Stat::Assign { lhs, rhs } = s {
                if lhs.len() == 1 && rhs.len() == 1 {
                    if let Expr::Index { table, key } = &lhs[0] {
                        if matches!(table.as_ref(), Expr::Name(n) if *n == t) {
                            if let Expr::Str(k) = key.as_ref() {
                                writes_ok.insert(i);
                                *set_count.entry(k.clone()).or_default() += 1;
                                if stable(&rhs[0], assigned) { known.insert(k.clone(), (rhs[0].clone(), i)); }
                            }
                        }
                    }
                }
            }
        }
        known.retain(|k, _| set_count.get(k) == Some(&1));
        if known.is_empty() || !only_const_key_uses(block, &t, &writes_ok) { continue; }
        // Substitute reads in statements after each field's definition.
        for i in decl + 1..block.len() {
            let avail: BTreeMap<Vec<u8>, Expr> = known.iter()
                .filter(|(_, (_, at))| *at < i)
                .map(|(k, (v, _))| (k.clone(), v.clone()))
                .collect();
            if avail.is_empty() { continue; }
            let mut one = vec![std::mem::replace(&mut block[i], Stat::Break)];
            subst_reads(&mut one, &t, &avail);
            block[i] = one.pop().unwrap();
        }
    }
}

/// Replace `t["k"]` reads (not assignment targets) with known values.
fn subst_reads(b: &mut Block, t: &str, vals: &BTreeMap<Vec<u8>, Expr>) {
    let sub = |e: &mut Expr| lua_ast::transform_expr(e, &mut |node| {
        if let Expr::Index { table, key } = node {
            if let (Expr::Name(n), Expr::Str(k)) = (table.as_ref(), key.as_ref()) {
                if n == t { if let Some(v) = vals.get(k) { *node = v.clone(); } }
            }
        }
    });
    for s in b.iter_mut() {
        match s {
            Stat::Assign { lhs, rhs } => {
                for l in lhs.iter_mut() {
                    if let Expr::Index { table, key } = l {
                        if matches!(table.as_ref(), Expr::Name(n) if n == t) { sub(key); } else { sub(table); sub(key); }
                    }
                }
                for e in rhs.iter_mut() { sub(e); }
            }
            Stat::Local { values, .. } => { for e in values.iter_mut() { sub(e); } }
            Stat::Return(v) => { for e in v.iter_mut() { sub(e); } }
            Stat::Call(e) => sub(e),
            Stat::While { cond, body } | Stat::Repeat { body, cond } => { sub(cond); subst_reads(body, t, vals); }
            Stat::If { branches, else_body } => {
                for (c, b) in branches.iter_mut() { sub(c); subst_reads(b, t, vals); }
                if let Some(b) = else_body { subst_reads(b, t, vals); }
            }
            Stat::NumFor { from, to, step, body, .. } => {
                sub(from); sub(to);
                if let Some(s) = step { sub(s); }
                subst_reads(body, t, vals);
            }
            Stat::GenFor { iters, body, .. } => { for e in iters.iter_mut() { sub(e); } subst_reads(body, t, vals); }
            Stat::Do(b) => subst_reads(b, t, vals),
            _ => {}
        }
    }
}
