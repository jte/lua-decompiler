//! Lua AST deobfuscator.
//!
//! All passes operate on [`lua_ast::Block`] in-place.

pub mod pass1_fold;
pub mod pass2_prop;
pub mod pass3_table;
pub mod pass4_concat;
pub mod pass5_perm;
pub mod pass6_dead;
pub mod pass7_upval;
pub mod pass8_rename;
pub mod pass_table_ctor;
pub mod pass_strdec;
pub mod pass_stream_dec;
pub mod pass_const_func;
pub mod pass_fold_tables;
pub mod pass_inline_locals;
pub mod pass_subtable_decode;
pub mod pass9_desugar;
pub mod pass_cipher_dec;
pub mod pass_func_alias;

use lua_ast::{Block, Expr, FuncBody, Stat};

// ---------------------------------------------------------------------------
// Shared recursive utility
// ---------------------------------------------------------------------------

/// Call `f` on every [`Block`] reachable from `root`, including blocks nested
/// inside statements and inside function-literal bodies.  Each block is visited
/// after all its ancestors (pre-order), so passes that need to see the whole
/// tree before acting on a sub-block should iterate to fixed-point themselves.
pub fn for_each_block(block: &mut Block, f: &mut impl FnMut(&mut Block)) {
    f(block);
    for stat in block.iter_mut() {
        visit_stat_blocks(stat, f);
    }
}

fn visit_stat_blocks(stat: &mut Stat, f: &mut impl FnMut(&mut Block)) {
    match stat {
        Stat::Do(b) => for_each_block(b, f),
        Stat::While { body, .. } => for_each_block(body, f),
        Stat::Repeat { body, .. } => for_each_block(body, f),
        Stat::NumFor { body, .. } => for_each_block(body, f),
        Stat::GenFor { body, .. } => for_each_block(body, f),
        Stat::If { branches, else_body } => {
            for (_, b) in branches { for_each_block(b, f); }
            if let Some(b) = else_body { for_each_block(b, f); }
        }
        Stat::Local { values, .. } => {
            for v in values { visit_expr_func_bodies(v, f); }
        }
        Stat::Assign { lhs, rhs } => {
            for v in lhs.iter_mut().chain(rhs.iter_mut()) {
                visit_expr_func_bodies(v, f);
            }
        }
        Stat::Return(vals) => {
            for v in vals { visit_expr_func_bodies(v, f); }
        }
        Stat::Call(e) => visit_expr_func_bodies(e, f),
        _ => {}
    }
}

fn visit_expr_func_bodies(expr: &mut Expr, f: &mut impl FnMut(&mut Block)) {
    match expr {
        Expr::Function(fb) => for_each_block(&mut fb.body, f),
        Expr::Call { func, args } => {
            visit_expr_func_bodies(func, f);
            for a in args { visit_expr_func_bodies(a, f); }
        }
        Expr::Index { table, key } => {
            visit_expr_func_bodies(table, f);
            visit_expr_func_bodies(key, f);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            visit_expr_func_bodies(lhs, f);
            visit_expr_func_bodies(rhs, f);
        }
        Expr::UnOp { operand, .. } => visit_expr_func_bodies(operand, f),
        Expr::Table(fields) => {
            for field in fields {
                match field {
                    lua_ast::TableField::IndexField(k, v) => {
                        visit_expr_func_bodies(k, f);
                        visit_expr_func_bodies(v, f);
                    }
                    lua_ast::TableField::NameField(_, v) => visit_expr_func_bodies(v, f),
                    lua_ast::TableField::ValueField(v) => visit_expr_func_bodies(v, f),
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Run all deobfuscation passes on `block` in place.
pub fn deobfuscate(block: &mut Block) {
    // Phase A: name/structure cleanup
    pass7_upval::run(block);
    pass6_dead::run(block);

    // Phase B: constant simplification (iterate to fixed point)
    for _ in 0..8 {
        let s0 = lua_ast::print_block(block, 0);
        pass2_prop::run(block);
        pass1_fold::run(block);
        if lua_ast::print_block(block, 0) == s0 { break; }
    }

    // Phase C: table-based obfuscation
    pass3_table::run(block);
    pass_table_ctor::run(block);
    pass5_perm::run(block);

    // Fold again after table substitution
    for _ in 0..8 {
        let s0 = lua_ast::print_block(block, 0);
        pass1_fold::run(block);
        if lua_ast::print_block(block, 0) == s0 { break; }
    }

    // Phase D: string reconstruction
    pass_strdec::run(block);
    pass_stream_dec::run(block);
    pass4_concat::run(block);

    // Phase E: final cleanup
    pass_inline_locals::run(block);
    pass_subtable_decode::run(block);
    pass9_desugar::run(block);  // desugar _upv0.X → X so _acc15 entries become leaf exprs
    pass5_perm::run(block);     // resolve mixed-type lookup tables (e.g. _acc15) after decode
    pass1_fold::run(block);     // fold any new constants exposed by table substitution
    pass_cipher_dec::run(block); // decrypt XOR cipher wrapper functions
    pass_const_func::run(block);
    pass_fold_tables::run(block);
    pass_const_func::run(block);  // second pass after fold — resolves _acc16[key] from constructors
    pass_func_alias::run(block);  // resolve gg.X = _fN → substitute _fN → gg.X everywhere
    pass6_dead::run(block);
    pass8_rename::run(block);
    pass9_desugar::run(block);
}
