/// Pass 5 – Permutation/lookup-table resolution.
///
/// Finds `local _tN = {v1, v2, ...}` where all entries are leaf expressions
/// (Integer, Float, Str, Name, True, False, Nil).
/// Substitutes every `_tN[K]` reference (K integer or float-integer) with the value.
/// Iterates to fixed-point so nested lookups like `_tN[_tN[k]]` are resolved.

use std::collections::{BTreeMap, BTreeSet};
use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    for _ in 0..20 {
        let tables = collect_leaf_tables(block);
        if tables.is_empty() { return; }
        let before = lua_ast::print_block(block, 0);
        for (tname, entries) in &tables {
            let mut subst_count = 0usize;
            // Use transform_block so substitution reaches all nested blocks.
            lua_ast::transform_block(block, &mut |node| {
                if let Expr::Index { table, key } = node {
                    if matches!(table.as_ref(), Expr::Name(n) if n == tname.as_str()) {
                        if let Some(k) = key_as_usize(key.as_ref()) {
                            // Integer index: look up positional entry.
                            if let Some(val) = entries.get(&k) {
                                *node = val.clone();
                            }
                        } else if let Expr::Str(s) = key.as_ref() {
                            // String-numeric key: the load-loop sets tbl["N"] = N (integer).
                            // Replace tbl["N"] with tbl[N] so the same iteration can resolve it.
                            if let Ok(s_str) = std::str::from_utf8(s) {
                                if let Ok(n) = s_str.parse::<i64>() {
                                    *node = Expr::Index {
                                        table: table.clone(),
                                        key: Box::new(Expr::Integer(n)),
                                    };
                                }
                            }
                        }
                    }
                }
            });
        }
        if lua_ast::print_block(block, 0) == before { break; }
    }
}

/// Extract an integer key from Integer or whole Float.
fn key_as_usize(e: &Expr) -> Option<usize> {
    match e {
        Expr::Integer(n) if *n >= 1 => Some(*n as usize),
        Expr::Float(f) if f.fract() == 0.0 && f.is_finite() && *f >= 1.0 => Some(*f as usize),
        _ => None,
    }
}

/// True if expression is a leaf (safe to inline — no side effects, no mutable state).
fn is_leaf(e: &Expr) -> bool {
    matches!(e, Expr::Integer(_) | Expr::Float(_) | Expr::Str(_)
               | Expr::Name(_) | Expr::True | Expr::False | Expr::Nil)
}

/// Returns { name → { 1-based index → expr } } for all pure-leaf tables.
/// If a table has a `for k in ... do tbl[k] = load("return " .. tbl[k])() end` loop,
/// string entries that parse as Lua literals are evaluated to their actual values.
fn collect_leaf_tables(block: &Block) -> BTreeMap<String, BTreeMap<usize, Expr>> {
    let load_eval = find_load_eval_tables(block);
    let mut result = BTreeMap::new();
    for stat in block {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if let Some(entries) = extract_leaf_table(&values[0]) {
                    if !entries.is_empty() {
                        let tname = &names[0];
                        if load_eval.contains(tname.as_str()) {
                            // Evaluate string-encoded literals.
                            let evaled: BTreeMap<usize, Expr> = entries.into_iter().map(|(k, v)| {
                                let v = if let Expr::Str(ref s) = v {
                                    eval_lua_literal(s).unwrap_or(v)
                                } else { v };
                                (k, v)
                            }).collect();
                            result.insert(tname.clone(), evaled);
                        } else {
                            result.insert(tname.clone(), entries);
                        }
                    }
                }
            }
        }
    }
    result
}

/// Find table names used in `for v1, v2 in ... do tbl[v2] = load(PREFIX .. tbl[v2])() end`
/// where PREFIX is either the literal `"return "` or `tbl[K]` that resolves to `"return "`.
fn find_load_eval_tables(block: &Block) -> BTreeSet<String> {
    // Pre-collect all leaf table entries so we can resolve `tbl[K]` prefixes.
    let leaf_entries: BTreeMap<String, BTreeMap<usize, Expr>> = block.iter().filter_map(|stat| {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if let Some(e) = extract_leaf_table(&values[0]) {
                    return Some((names[0].clone(), e));
                }
            }
        }
        None
    }).collect();

    let mut result = BTreeSet::new();
    for stat in block {
        if let Stat::GenFor { vars, body, .. } = stat {
            if vars.len() >= 2 {
                let key_var = &vars[1];
                for bstat in body {
                    if let Stat::Assign { lhs, rhs } = bstat {
                        if lhs.len() == 1 && rhs.len() == 1 {
                            if let Expr::Index { table, key } = &lhs[0] {
                                if let (Expr::Name(tbl), Expr::Name(kv)) = (table.as_ref(), key.as_ref()) {
                                    if kv == key_var && is_load_concat_call_ex(&rhs[0], tbl, key_var, &leaf_entries) {
                                        result.insert(tbl.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    // Propagate load-eval status through aliases: if `local X = Y` and X is load-eval, Y is too.
    let mut extra: BTreeSet<String> = BTreeSet::new();
    for stat in block {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Name(alias_target) = &values[0] {
                    if result.contains(names[0].as_str()) {
                        extra.insert(alias_target.clone());
                    }
                }
            }
        }
    }
    result.extend(extra);
    result
}

/// True if `e` is a reference to Lua's `load` function: bare `load`, or `_upvN.load`,
/// or `_upvN["load"]` (before pass9_desugar has run).
fn is_load_func(e: &Expr) -> bool {
    match e {
        Expr::Name(n) => n == "load",
        Expr::Index { table, key } => {
            if let Expr::Str(kb) = key.as_ref() {
                if kb.as_slice() == b"load" {
                    return matches!(table.as_ref(), Expr::Name(n) if n.starts_with("_upv"));
                }
            }
            false
        }
        _ => false,
    }
}

/// Match `load(PREFIX .. tbl[key_var])()` where PREFIX is `"return "` as a literal
/// string OR as `tbl[K]` that resolves to `"return "` in `leaf_entries`.
fn is_load_concat_call_ex(
    e: &Expr,
    tbl_name: &str,
    key_var: &str,
    leaf_entries: &BTreeMap<String, BTreeMap<usize, Expr>>,
) -> bool {
    if let Expr::Call { func, args } = e {
        if args.is_empty() {
            if let Expr::Call { func: load_func, args: load_args } = func.as_ref() {
                if load_args.len() == 1 {
                    if is_load_func(load_func.as_ref()) {
                        if let Expr::BinOp { op, lhs, rhs } = &load_args[0] {
                            if matches!(op, lua_ast::BinOp::Concat) {
                                let prefix_ok = match lhs.as_ref() {
                                    Expr::Str(s) => s.as_slice() == b"return ",
                                    Expr::Index { table, key } => {
                                        if let Expr::Name(t) = table.as_ref() {
                                            if let Some(k) = key_as_usize(key.as_ref()) {
                                                leaf_entries.get(t)
                                                    .and_then(|m| m.get(&k))
                                                    .map_or(false, |v| matches!(v, Expr::Str(s) if s.as_slice() == b"return "))
                                            } else { false }
                                        } else { false }
                                    }
                                    _ => false,
                                };
                                if prefix_ok {
                                    if let Expr::Index { table, key } = rhs.as_ref() {
                                        return matches!(table.as_ref(), Expr::Name(n) if n == tbl_name)
                                            && matches!(key.as_ref(), Expr::Name(k) if k == key_var);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

/// Evaluate a string-encoded Lua literal to its actual expression.
fn eval_lua_literal(s: &[u8]) -> Option<Expr> {
    let s = std::str::from_utf8(s).ok()?;
    match s {
        "nil" => Some(Expr::Nil),
        "true" => Some(Expr::True),
        "false" => Some(Expr::False),
        _ => {
            if let Ok(n) = s.parse::<i64>() { return Some(Expr::Integer(n)); }
            if s.contains('.') {
                if let Ok(f) = s.parse::<f64>() { return Some(Expr::Float(f)); }
            }
            None
        }
    }
}

fn extract_leaf_table(e: &Expr) -> Option<BTreeMap<usize, Expr>> {
    if let Expr::Table(fields) = e {
        let mut map = BTreeMap::new();
        for (i, field) in fields.iter().enumerate() {
            match field {
                TableField::ValueField(v) if is_leaf(v) => {
                    map.insert(i + 1, v.clone());
                }
                _ => return None, // Non-leaf entry → not a pure leaf table
            }
        }
        Some(map)
    } else {
        None
    }
}

fn subst_stat(stat: &mut Stat, tname: &str, entries: &BTreeMap<usize, Expr>) {
    match stat {
        Stat::Local { values, .. } => {
            for v in values.iter_mut() { subst_expr(v, tname, entries); }
        }
        Stat::Assign { lhs, rhs } => {
            for e in lhs.iter_mut().chain(rhs.iter_mut()) { subst_expr(e, tname, entries); }
        }
        Stat::Return(vals) => {
            for v in vals.iter_mut() { subst_expr(v, tname, entries); }
        }
        Stat::Call(e) => subst_expr(e, tname, entries),
        _ => {}
    }
}

fn subst_expr(e: &mut Expr, tname: &str, entries: &BTreeMap<usize, Expr>) {
    lua_ast::transform_expr(e, &mut |node| {
        if let Expr::Index { table, key } = node {
            if matches!(table.as_ref(), Expr::Name(n) if n == tname) {
                if let Some(k) = key_as_usize(key.as_ref()) {
                    if let Some(val) = entries.get(&k) {
                        *node = val.clone();
                    }
                }
            }
        }
    });
}
