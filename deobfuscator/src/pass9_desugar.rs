/// Pass 9 – Global-environment desugaring.
///
/// 1. `_upv0["X"]`      → `X`     (single-level global env access)
/// 2. `_upv0["X"]["Y"]` → `X.Y`   (handled transitively via step 1 +
///                                  the printer's dot-notation for ident keys)
/// 3. `_upv0`           → `_G`    (bare reference to the global env upvalue)
///
/// The printer already renders `expr[Str("ident")]` as `expr.ident` when the
/// key is a valid Lua identifier, so after step 1, two-level accesses become
/// `X["Y"]` → `X.Y` automatically.
///
/// Uses TOP-DOWN traversal so that `_upv0["X"]` is matched and replaced before
/// any bottom-up pass could first convert `_upv0` → `_G`, which would break
/// the parent pattern match.

use lua_ast::{Block, Expr, Stat};
use lua_ast::is_lua_ident;
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut |b| {
        for _ in 0..10 {
            let s0 = lua_ast::print_block(b, 0);
            desugar_block(b, 0);
            if lua_ast::print_block(b, 0) == s0 { break; }
        }
    });
}

/// Top-down traversal: apply substitution before recursing into children.
/// `func_depth` tracks how many function literals deep we are; bare `_upv0`
/// is only replaced at depth 0 (top-level block), because in inner closures
/// upvalue 0 captures a different value (e.g. `ipairs`).
fn desugar_block(block: &mut Block, func_depth: u32) {
    for stat in block.iter_mut() {
        desugar_stat(stat, func_depth);
    }
}

fn desugar_stat(stat: &mut Stat, func_depth: u32) {
    match stat {
        Stat::Assign { lhs, rhs } => {
            for e in lhs.iter_mut() { desugar_expr(e, func_depth); }
            for e in rhs.iter_mut() { desugar_expr(e, func_depth); }
        }
        Stat::Local { values, .. } => {
            for v in values.iter_mut() { desugar_expr(v, func_depth); }
        }
        Stat::Do(body) => desugar_block(body, func_depth),
        Stat::While { cond, body } => { desugar_expr(cond, func_depth); desugar_block(body, func_depth); }
        Stat::Repeat { body, cond } => { desugar_block(body, func_depth); desugar_expr(cond, func_depth); }
        Stat::If { branches, else_body } => {
            for (cond, body) in branches.iter_mut() {
                desugar_expr(cond, func_depth);
                desugar_block(body, func_depth);
            }
            if let Some(b) = else_body { desugar_block(b, func_depth); }
        }
        Stat::NumFor { from, to, step, body, .. } => {
            desugar_expr(from, func_depth); desugar_expr(to, func_depth);
            if let Some(s) = step { desugar_expr(s, func_depth); }
            desugar_block(body, func_depth);
        }
        Stat::GenFor { iters, body, .. } => {
            for e in iters.iter_mut() { desugar_expr(e, func_depth); }
            desugar_block(body, func_depth);
        }
        Stat::Return(vals) => { for v in vals.iter_mut() { desugar_expr(v, func_depth); } }
        Stat::Call(e) => desugar_expr(e, func_depth),
        _ => {}
    }
}

/// Top-down expression desugaring.
fn desugar_expr(e: &mut Expr, func_depth: u32) {
    // Apply substitution at THIS node FIRST (top-down), then recurse.
    match e {
        // _upv0["X"] → X  (only when X is a valid Lua identifier)
        // _G["X"]    → X  (for well-known Lua standard functions accessed via _G)
        Expr::Index { table, key } => {
            if let (Expr::Name(tname), Expr::Str(kb)) = (table.as_ref(), key.as_ref()) {
                if tname == "_upv0" {
                    if let Ok(ks) = std::str::from_utf8(kb) {
                        if is_lua_ident(ks) {
                            *e = Expr::Name(ks.to_string());
                            return;
                        }
                    }
                } else if tname == "_G" {
                    if let Ok(ks) = std::str::from_utf8(kb) {
                        if is_stdlib_func(ks) {
                            *e = Expr::Name(ks.to_string());
                            return;
                        }
                    }
                }
            }
            // Not replaced: recurse into children.
            if let Expr::Index { table, key } = e {
                desugar_expr(table, func_depth);
                desugar_expr(key, func_depth);
            }
        }
        // _upv0 (bare) → _G
        Expr::Name(n) if n == "_upv0" => {
            *e = Expr::Name("_G".to_string());
        }
        // Recurse into all other compound expressions.
        Expr::BinOp { lhs, rhs, .. } => { desugar_expr(lhs, func_depth); desugar_expr(rhs, func_depth); }
        Expr::UnOp { operand, .. } => desugar_expr(operand, func_depth),
        Expr::Call { func, args } => {
            desugar_expr(func, func_depth);
            for a in args.iter_mut() { desugar_expr(a, func_depth); }
        }
        // When entering a function literal, increment depth so bare _upv0 is not replaced.
        Expr::Function(fb) => desugar_block(&mut fb.body, func_depth + 1),
        Expr::Table(fields) => {
            use lua_ast::TableField;
            for f in fields.iter_mut() {
                match f {
                    TableField::IndexField(k, v) => { desugar_expr(k, func_depth); desugar_expr(v, func_depth); }
                    TableField::NameField(_, v) => desugar_expr(v, func_depth),
                    TableField::ValueField(v) => desugar_expr(v, func_depth),
                }
            }
        }
        _ => {} // Leaf nodes (Name, Integer, Float, Str, Bool, Nil, Vararg)
    }
}

/// True for well-known Lua standard library functions that are safe to
/// desugar from `_G.X` to bare `X`.  Module tables (os, io, math, etc.)
/// and special globals (load, loadfile, _G itself) are excluded so that
/// `_G.os.remove` stays as-is rather than becoming `os.remove`.
fn is_stdlib_func(name: &str) -> bool {
    matches!(name,
        "tostring" | "tonumber" | "type" | "ipairs" | "pairs" | "next" |
        "xpcall" | "assert" | "error" | "rawget" | "rawset" |
        "rawequal" | "rawlen" | "getmetatable" | "setmetatable" |
        "select" | "unpack" | "collectgarbage" | "warn"
    )
}
