/// Table-constructor collapsing pass.
///
/// Converts:
///   local _tN = {}
///   _acc25 = 74            (plain integer assignments, kept for other uses)
///   _tN[1] = _acc25        (sequential integer-keyed table population)
///   _tN[2] = 44
///   ...
///
/// into:
///   local _tN = {74, 44, ...}
///
/// Only collapses when every table entry resolves to an integer literal
/// (either directly or via the most-recently-seen assignment to that name),
/// and the indices form a gap-free sequence starting at 1.

use std::collections::HashMap;
use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut collapse_block);
}

fn collapse_block(block: &mut Block) {
    // Map: name → most-recently-seen integer value (for resolving variables).
    let mut val_ctx: HashMap<String, i64> = HashMap::new();
    // Map: table_name → (decl_index, entries_so_far, entry_indices, bad_flag)
    let mut tables: HashMap<String, TableBuild> = HashMap::new();

    struct TableBuild {
        decl_idx:     usize,
        entries:      Vec<i64>,          // 1-based, in order
        entry_idxs:   Vec<usize>,        // which block indices are entries
        bad:          bool,
    }

    for (i, stat) in block.iter().enumerate() {
        match stat {
            // Table declaration
            Stat::Local { names, values }
                if names.len() == 1
                    && values.len() == 1
                    && values[0] == Expr::Table(vec![]) =>
            {
                tables.insert(names[0].clone(), TableBuild {
                    decl_idx: i,
                    entries: Vec::new(),
                    entry_idxs: Vec::new(),
                    bad: false,
                });
            }
            // Plain integer assignment (not to a table slot)
            Stat::Assign { lhs, rhs }
                if lhs.len() == 1 && rhs.len() == 1 =>
            {
                if let (Expr::Name(n), Expr::Integer(v)) = (&lhs[0], &rhs[0]) {
                    val_ctx.insert(n.clone(), *v);
                }
                // Table-slot assignment: _tN[k] = expr
                if let Expr::Index { table, key } = &lhs[0] {
                    if let (Expr::Name(tname), Expr::Integer(k)) = (table.as_ref(), key.as_ref()) {
                        let k = *k as usize;
                        if let Some(build) = tables.get_mut(tname) {
                            if !build.bad {
                                let expected = build.entries.len() + 1;
                                if k == expected {
                                    // Resolve RHS to integer.
                                    let val = match &rhs[0] {
                                        Expr::Integer(v) => Some(*v),
                                        Expr::Name(n) => val_ctx.get(n).copied(),
                                        _ => None,
                                    };
                                    match val {
                                        Some(v) => {
                                            build.entries.push(v);
                                            build.entry_idxs.push(i);
                                        }
                                        None => build.bad = true,
                                    }
                                } else {
                                    build.bad = true;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // Apply: replace decl with constructor, remove entry statements.
    let mut remove: Vec<usize> = Vec::new();
    let mut replacements: Vec<(usize, Stat)> = Vec::new();

    for (tname, build) in &tables {
        if build.bad || build.entries.is_empty() { continue; }
        let fields: Vec<TableField> = build.entries.iter()
            .map(|&v| TableField::ValueField(Expr::Integer(v)))
            .collect();
        let ctor = Stat::Local {
            names: vec![tname.clone()],
            values: vec![Expr::Table(fields)],
        };
        replacements.push((build.decl_idx, ctor));
        remove.extend_from_slice(&build.entry_idxs);
    }

    if replacements.is_empty() { return; }

    // Sort descending by index so we can mutate without shifting.
    remove.sort_unstable_by(|a, b| b.cmp(a));
    remove.dedup();
    for i in remove { block.remove(i); }

    for (orig_idx, new_stat) in replacements {
        // After removal of entry lines, the decl index may have shifted.
        // Find the decl by matching its old content (the empty table) or just scan.
        // Simpler: find the Local with that tname and an empty table.
        if let Some(pos) = block.iter().position(|s| {
            matches!(s, Stat::Local { names, values }
                if names.len() == 1 && matches!(&values[..], [Expr::Table(f)] if f.is_empty())
                    && names[0] == *match &new_stat { Stat::Local { names, .. } => &names[0], _ => return false })
        }) {
            let _ = orig_idx;
            block[pos] = new_stat;
        }
    }
}
