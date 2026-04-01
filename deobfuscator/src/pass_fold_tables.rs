/// Pass – Fold `local _tN = {}` + string-keyed assignments into table constructors.
///
/// Finds `local _tN = {}` followed by `_tN["key"] = value` assignments
/// where `_tN` appears as an RHS exactly once (in a single other statement).
/// Replaces that single use with an inline `{key = value, ...}` constructor
/// and removes the decl + entry statements.
///
/// Iterates to a fixed point so nested tables are handled.

use std::collections::BTreeMap;
use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut |b| {
        for _ in 0..30 {
            let before = b.len();
            fold_once(b);
            if b.len() == before { break; }
        }
    });
}

fn fold_once(block: &mut Block) {
    // Phase 1: collect table decls and their string-keyed entries.
    struct State {
        decl_idx:    usize,
        entries:     Vec<(Vec<u8>, Expr)>, // (key_bytes, value)
        entry_idxs:  Vec<usize>,
        bad:         bool,
    }

    let mut tables: BTreeMap<String, State> = BTreeMap::new();

    for (i, stat) in block.iter().enumerate() {
        match stat {
            Stat::Local { names, values }
                if names.len() == 1 && values.len() == 1 && values[0] == Expr::Table(vec![]) =>
            {
                tables.insert(names[0].clone(), State {
                    decl_idx: i,
                    entries: Vec::new(),
                    entry_idxs: Vec::new(),
                    bad: false,
                });
            }
            Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => {
                if let Expr::Index { table, key } = &lhs[0] {
                    if let (Expr::Name(tname), Expr::Str(kb)) = (table.as_ref(), key.as_ref()) {
                        if let Some(st) = tables.get_mut(tname) {
                            if !st.bad {
                                st.entries.push((kb.clone(), rhs[0].clone()));
                                st.entry_idxs.push(i);
                            }
                            continue;
                        }
                    }
                    // Non-string-keyed or integer-keyed write to a known table → taint it.
                    if let Expr::Name(tname) = table.as_ref() {
                        if let Some(st) = tables.get_mut(tname) {
                            st.bad = true;
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // Phase 2: find use sites.
    struct Action {
        tname:       String,
        decl_idx:    usize,
        entry_idxs:  Vec<usize>,
        use_idx:     usize,
        constructor: Expr,
    }

    let mut actions: Vec<Action> = Vec::new();

    for (tname, st) in &tables {
        if st.bad || st.entries.is_empty() { continue; }

        let my_indices: std::collections::BTreeSet<usize> =
            std::iter::once(st.decl_idx).chain(st.entry_idxs.iter().copied()).collect();

        // Find all uses of tname as a whole-word Name expression in other statements.
        let mut uses: Vec<usize> = Vec::new();
        for (i, stat) in block.iter().enumerate() {
            if my_indices.contains(&i) { continue; }
            if stat_contains_name(stat, tname) { uses.push(i); }
        }

        if uses.len() != 1 { continue; }

        let use_idx = uses[0];
        let use_stat = &block[use_idx];

        // Determine if it's an inner use (value in another table entry).
        let is_inner = is_table_entry_rhs_use(use_stat, tname);

        let constructor = build_constructor(&st.entries, is_inner);
        actions.push(Action {
            tname: tname.clone(),
            decl_idx: st.decl_idx,
            entry_idxs: st.entry_idxs.clone(),
            use_idx,
            constructor,
        });
    }

    if actions.is_empty() { return; }

    // Safety: skip actions where an entry line is another action's use site.
    let use_idx_set: std::collections::BTreeSet<usize> =
        actions.iter().map(|a| a.use_idx).collect();
    actions.retain(|a| !a.entry_idxs.iter().any(|ei| use_idx_set.contains(ei)));

    if actions.is_empty() { return; }

    // Apply actions: substitute use sites, then remove decls and entries.
    for action in &actions {
        // Substitute tname → constructor at use site.
        subst_name_in_stat(&mut block[action.use_idx], &action.tname, action.constructor.clone());
    }

    let mut remove: Vec<usize> = Vec::new();
    for action in &actions {
        remove.push(action.decl_idx);
        remove.extend_from_slice(&action.entry_idxs);
    }
    remove.sort_unstable_by(|a, b| b.cmp(a));
    remove.dedup();
    for i in remove { block.remove(i); }
}

fn build_constructor(entries: &[(Vec<u8>, Expr)], is_inner: bool) -> Expr {
    let fields: Vec<TableField> = entries.iter().map(|(kb, val)| {
        match std::str::from_utf8(kb).ok().filter(|s| lua_ast::is_lua_ident(s)) {
            Some(ident) => TableField::NameField(ident.to_string(), val.clone()),
            None => TableField::IndexField(Expr::Str(kb.clone()), val.clone()),
        }
    }).collect();
    Expr::Table(fields)
}

fn is_table_entry_rhs_use(stat: &Stat, tname: &str) -> bool {
    if let Stat::Assign { lhs, rhs } = stat {
        if lhs.len() == 1 && rhs.len() == 1 {
            if let Expr::Index { table: _, .. } = &lhs[0] {
                if let Expr::Name(n) = &rhs[0] { return n == tname; }
            }
        }
    }
    false
}

fn stat_contains_name(stat: &Stat, name: &str) -> bool {
    let mut found = false;
    match stat {
        Stat::Assign { lhs, rhs } => {
            for e in lhs.iter().chain(rhs.iter()) {
                if expr_contains_name(e, name) { found = true; }
            }
        }
        Stat::Local { values, .. } => {
            for v in values { if expr_contains_name(v, name) { found = true; } }
        }
        Stat::Return(vals) => {
            for v in vals { if expr_contains_name(v, name) { found = true; } }
        }
        Stat::Call(e) => { if expr_contains_name(e, name) { found = true; } }
        _ => {}
    }
    found
}

fn expr_contains_name(e: &Expr, name: &str) -> bool {
    match e {
        Expr::Name(n) => n == name,
        Expr::Index { table, key } =>
            expr_contains_name(table, name) || expr_contains_name(key, name),
        Expr::BinOp { lhs, rhs, .. } =>
            expr_contains_name(lhs, name) || expr_contains_name(rhs, name),
        Expr::UnOp { operand, .. } => expr_contains_name(operand, name),
        Expr::Call { func, args } =>
            expr_contains_name(func, name) || args.iter().any(|a| expr_contains_name(a, name)),
        Expr::Table(fields) => fields.iter().any(|f| match f {
            TableField::IndexField(k, v) =>
                expr_contains_name(k, name) || expr_contains_name(v, name),
            TableField::NameField(_, v) => expr_contains_name(v, name),
            TableField::ValueField(v) => expr_contains_name(v, name),
        }),
        _ => false,
    }
}

fn subst_name_in_stat(stat: &mut Stat, name: &str, replacement: Expr) {
    lua_ast::transform_expr(match stat {
        Stat::Assign { rhs, .. } => rhs.get_mut(0).unwrap(),
        Stat::Local { values, .. } => values.get_mut(0).unwrap(),
        Stat::Return(vals) => vals.get_mut(0).unwrap(),
        Stat::Call(e) => e,
        _ => return,
    }, &mut |e| {
        if let Expr::Name(n) = e {
            if n == name { *e = replacement.clone(); }
        }
    });
}
