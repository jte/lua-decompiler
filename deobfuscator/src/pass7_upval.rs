/// Pass 7 – Upvalue / field-access resolution.
///
/// `_upvN["global"]`  →  `global`   (for known Lua standard-library names)
///
/// The printer already converts `expr["ident"]` → `expr.ident` for valid
/// identifiers, so no extra work is needed for method-access desugaring here.

use lua_ast::{Block, Expr, transform_block};
use crate::for_each_block;

const LUA_GLOBALS: &[&str] = &[
    "string", "table", "io", "os", "math", "debug", "package", "coroutine",
    "utf8", "bit32", "type", "tostring", "tonumber", "print", "next",
    "ipairs", "pairs", "select", "error", "assert", "pcall", "xpcall",
    "rawget", "rawset", "rawequal", "rawlen", "require", "load", "loadfile",
    "dofile", "collectgarbage", "setmetatable", "getmetatable", "unpack",
];

pub fn run(block: &mut Block) {
    for_each_block(block, &mut |b| {
        transform_block(b, &mut resolve_upval);
    });
}

fn resolve_upval(e: &mut Expr) {
    // Pattern: _upvN["known_global"] → known_global
    if let Expr::Index { table, key } = e {
        if let (Expr::Name(tname), Expr::Str(kbytes)) = (table.as_ref(), key.as_ref()) {
            if tname.starts_with("_upv") {
                if let Ok(kstr) = std::str::from_utf8(kbytes) {
                    if LUA_GLOBALS.contains(&kstr) {
                        *e = Expr::Name(kstr.to_string());
                        return;
                    }
                }
            }
        }
    }
}
