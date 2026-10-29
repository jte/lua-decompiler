/// Pass 8 – Standard-library alias removal.
///
/// `local _x = string` (a generated name bound to a library table), where
/// neither `_x` nor `string` is ever reassigned or redeclared anywhere, is
/// removed and `_x` replaced by `string` throughout.

use std::collections::BTreeMap;
use lua_ast::{Block, Expr, Stat};

use crate::util::{assigned_names, count_refs};

const LUA_GLOBALS: &[&str] = &[
    "string", "table", "io", "os", "math", "debug", "package", "coroutine",
    "utf8", "bit32",
];

pub fn run(block: &mut Block) {
    let assigned = assigned_names(block);
    let mut renames: BTreeMap<String, String> = BTreeMap::new();
    collect(block, &assigned, &mut renames);
    // The library name must not be declared as a local anywhere.
    renames.retain(|_, module| !is_declared(block, module));
    if renames.is_empty() { return; }
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Name(n) = e {
            if let Some(m) = renames.get(n) { *n = m.clone(); }
        }
    });
    remove_self_aliases(block);
}

fn collect(block: &Block, assigned: &std::collections::BTreeSet<String>, out: &mut BTreeMap<String, String>) {
    crate::util::visit_stats(block, &mut |s| {
        if let Stat::Local { names, values } = s {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Name(module) = &values[0] {
                    let name = &names[0];
                    if LUA_GLOBALS.contains(&module.as_str()) && name.starts_with('_')
                        && !assigned.contains(name) && !assigned.contains(module)
                    {
                        out.insert(name.clone(), module.clone());
                    }
                }
            }
        }
    });
}

fn is_declared(block: &Block, name: &str) -> bool {
    // count_refs counts declarations and uses; uses of the global are fine,
    // so look for declarations specifically.
    let mut found = false;
    crate::util::visit_stats(block, &mut |s| match s {
        Stat::Local { names, .. } => { if names.iter().any(|n| n == name) { found = true; } }
        Stat::NumFor { var, .. } => { if var == name { found = true; } }
        Stat::GenFor { vars, .. } => { if vars.iter().any(|n| n == name) { found = true; } }
        _ => {}
    });
    let _ = count_refs;
    found
}

/// Drop the `local string = string` declarations left by the renaming.
fn remove_self_aliases(block: &mut Block) {
    lua_ast::transform_stats(block, &mut |s| match &s {
        Stat::Local { names, values } if names.len() == 1 && values.len() == 1
            && matches!(&values[0], Expr::Name(m) if *m == names[0] && LUA_GLOBALS.contains(&m.as_str())) => vec![],
        _ => vec![s],
    });
}
