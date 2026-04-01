/// Pass 5 – Permutation/lookup-table resolution.
///
/// Finds `local _tN = {v1, v2, ...}` where all entries are leaf expressions
/// (Integer, Float, Str, Name, True, False, Nil).
/// Substitutes every `_tN[K]` reference (K integer or float-integer) with the value.
/// Iterates to fixed-point so nested lookups like `_tN[_tN[k]]` are resolved.

use std::collections::BTreeMap;
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
fn collect_leaf_tables(block: &Block) -> BTreeMap<String, BTreeMap<usize, Expr>> {
    let mut result = BTreeMap::new();
    for stat in block {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if let Some(entries) = extract_leaf_table(&values[0]) {
                    if !entries.is_empty() {
                        result.insert(names[0].clone(), entries);
                    }
                }
            }
        }
    }
    result
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
