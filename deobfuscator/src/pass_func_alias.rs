/// Pass – name local functions after the API slot they are installed into.
///
/// For `gg.searchNumber = _f3` (an obfuscator re-binding an API), the local
/// `_f3` is renamed to `gg_searchNumber` everywhere.  Renaming never changes
/// behaviour, unlike substituting `gg.searchNumber` for `_f3`, which would
/// only be right while that field still holds the function.

use std::collections::BTreeMap;
use lua_ast::{Block, Expr, Stat};

use crate::util::{assigned_names, count_refs, visit_stats};

pub fn run(block: &mut Block) {
    let assigned = assigned_names(block);
    let mut renames: BTreeMap<String, String> = BTreeMap::new();
    let mut taken: Vec<String> = Vec::new();
    visit_stats(block, &mut |s| {
        if let Stat::Assign { lhs, rhs } = s {
            if lhs.len() == 1 && rhs.len() == 1 && !matches!(lhs[0], Expr::Name(_)) {
                if let (Some(path), Expr::Name(f)) = (chain_name(&lhs[0]), &rhs[0]) {
                    // Only generated names, declared once and never reassigned.
                    if f.starts_with('_') && !assigned.contains(f) && !renames.contains_key(f) && !taken.contains(&path) {
                        taken.push(path.clone());
                        renames.insert(f.clone(), path);
                    }
                }
            }
        }
    });
    // The function must be a local function, and the new name unused.
    renames.retain(|f, new| {
        let mut is_local_fn = false;
        visit_stats(block, &mut |s| if let Stat::Local { names, values } = s {
            if names.len() == 1 && names[0] == *f && matches!(values.first(), Some(Expr::Function(_))) { is_local_fn = true; }
        });
        is_local_fn && count_refs(block, new) == 0
    });
    if renames.is_empty() { return; }
    rename(block, &renames);
}

/// `a.b.c` → `a_b_c` (only plain identifier chains).
fn chain_name(e: &Expr) -> Option<String> {
    match e {
        Expr::Name(n) if lua_ast::is_lua_ident(n) => Some(n.clone()),
        Expr::Index { table, key } => {
            let k = key.as_str_utf8().filter(|k| lua_ast::is_lua_ident(k))?;
            Some(format!("{}_{}", chain_name(table)?, k))
        }
        _ => None,
    }
}

fn rename(block: &mut Block, map: &BTreeMap<String, String>) {
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Name(n) = e {
            if let Some(x) = map.get(n) { *n = x.clone(); }
        }
    });
    rename_decls(block, map);
}

fn rename_decls(block: &mut Block, map: &BTreeMap<String, String>) {
    for s in block.iter_mut() {
        if let Stat::Local { names, values } = s {
            for n in names.iter_mut() { if let Some(x) = map.get(n) { *n = x.clone(); } }
            for v in values.iter_mut() { rename_in_functions(v, map); }
        }
        match s {
            Stat::Do(b) | Stat::While { body: b, .. } | Stat::Repeat { body: b, .. }
            | Stat::NumFor { body: b, .. } | Stat::GenFor { body: b, .. } => rename_decls(b, map),
            Stat::If { branches, else_body } => {
                for (_, b) in branches.iter_mut() { rename_decls(b, map); }
                if let Some(b) = else_body { rename_decls(b, map); }
            }
            Stat::Assign { rhs, .. } => { for v in rhs.iter_mut() { rename_in_functions(v, map); } }
            Stat::Call(e) => rename_in_functions(e, map),
            Stat::Return(v) => { for e in v.iter_mut() { rename_in_functions(e, map); } }
            _ => {}
        }
    }
}

/// Declarations inside function literals (transform_block only renames
/// expressions).
fn rename_in_functions(e: &mut Expr, map: &BTreeMap<String, String>) {
    lua_ast::transform_expr(e, &mut |x| if let Expr::Function(fb) = x { rename_decls(&mut fb.body, map); });
}
