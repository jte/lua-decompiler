/// Pass 9 – `_G.name` → `name` for standard-library functions.
///
/// `_G.tostring(x)` reads the same global as `tostring(x)` as long as no
/// local called `tostring` exists, which is checked over the whole chunk.
/// Module tables (`os`, `io`, ...) and `load*` are left alone.

use std::collections::BTreeSet;
use lua_ast::{Block, Expr, Stat};

use crate::util::{visit_exprs, visit_stats};

pub fn run(block: &mut Block) {
    let mut locals: BTreeSet<String> = BTreeSet::new();
    visit_stats(block, &mut |s| match s {
        Stat::Local { names, .. } => locals.extend(names.iter().cloned()),
        Stat::NumFor { var, .. } => { locals.insert(var.clone()); }
        Stat::GenFor { vars, .. } => locals.extend(vars.iter().cloned()),
        _ => {}
    });
    visit_exprs(block, &mut |e| if let Expr::Function(fb) = e { locals.extend(fb.params.iter().cloned()); });
    if locals.contains("_G") { return; }
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Index { table, key } = e {
            if matches!(table.as_ref(), Expr::Name(n) if n == "_G") {
                if let Some(k) = key.as_str_utf8() {
                    if is_stdlib_func(k) && !locals.contains(k) {
                        *e = Expr::Name(k.to_string());
                    }
                }
            }
        }
    });
}

fn is_stdlib_func(name: &str) -> bool {
    matches!(name,
        "tostring" | "tonumber" | "type" | "ipairs" | "pairs" | "next" |
        "xpcall" | "assert" | "error" | "rawget" | "rawset" |
        "rawequal" | "rawlen" | "getmetatable" | "setmetatable" |
        "select" | "unpack" | "collectgarbage" | "warn"
    )
}
