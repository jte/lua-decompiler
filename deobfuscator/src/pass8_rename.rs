/// Pass 8 – Variable renaming.
///
/// Finds `local _NAME = MODULE` where MODULE is a known Lua standard-library
/// name and _NAME is never reassigned.  Renames _NAME → MODULE throughout,
/// then removes the now-trivial `local MODULE = MODULE` declarations.

use std::collections::{BTreeMap, BTreeSet};
use lua_ast::{Block, Expr, Stat};
use crate::for_each_block;

const LUA_GLOBALS: &[&str] = &[
    "string", "table", "io", "os", "math", "debug", "package", "coroutine",
    "utf8", "bit32",
];

pub fn run(block: &mut Block) {
    for_each_block(block, &mut rename_in_block);
}

fn rename_in_block(block: &mut Block) {
    let renames = collect_renames(block);
    if renames.is_empty() { return; }
    apply_renames(block, &renames);
    // Remove `local MODULE = MODULE` that result from renaming.
    block.retain(|s| {
        if let Stat::Local { names, values } = s {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Name(rhs) = &values[0] {
                    if names[0] == *rhs && LUA_GLOBALS.contains(&rhs.as_str()) {
                        return false;
                    }
                }
            }
        }
        true
    });
}

fn collect_renames(block: &Block) -> BTreeMap<String, String> {
    let mut map: BTreeMap<String, String> = BTreeMap::new();
    let mut reassigned: BTreeSet<String> = BTreeSet::new();

    for stat in block {
        match stat {
            Stat::Local { names, values } if names.len() == 1 && values.len() == 1 => {
                let name = &names[0];
                if let Expr::Name(module) = &values[0] {
                    if LUA_GLOBALS.contains(&module.as_str()) && name.starts_with('_') {
                        map.insert(name.clone(), module.clone());
                    }
                }
            }
            Stat::Assign { lhs, .. } => {
                for e in lhs {
                    if let Expr::Name(n) = e { reassigned.insert(n.clone()); }
                }
            }
            _ => {}
        }
    }

    map.retain(|name, _| !reassigned.contains(name));
    map
}

fn apply_renames(block: &mut Block, renames: &BTreeMap<String, String>) {
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Name(n) = e {
            if let Some(new_name) = renames.get(n) {
                *e = Expr::Name(new_name.clone());
            }
        }
    });
}
