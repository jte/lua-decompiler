//! Lua AST deobfuscator.
//!
//! All passes operate on [`lua_ast::Block`] in-place.

pub mod pass1_fold;
pub mod pass2_prop;
pub mod pass3_table;
pub mod pass4_concat;
pub mod pass5_perm;
pub mod pass6_dead;
pub mod pass8_rename;
pub mod pass9_desugar;
pub mod pass_cipher_dec;
pub mod pass_cond;
pub mod pass_const_func;
pub mod pass_dce;
pub mod pass_eval;
pub mod pass_fold_tables;
pub mod pass_func_alias;
pub mod pass_junk;
pub mod pass_limit;
pub mod pass_stdlib;
pub mod pass_unique;
pub mod util;

use lua_ast::{Block, Expr, Stat};

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
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
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

/// Pre-order walk over an expression.  Function literals are visited but not
/// entered (callers decide whether to look at their bodies).
pub fn walk_expr(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Index { table, key } => { walk_expr(table, f); walk_expr(key, f); }
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => { walk_expr(func, f); for a in args { walk_expr(a, f); } }
        Expr::BinOp { lhs, rhs, .. } => { walk_expr(lhs, f); walk_expr(rhs, f); }
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => walk_expr(operand, f),
        Expr::Table(fields) => {
            for fl in fields {
                match fl {
                    lua_ast::TableField::IndexField(k, v) => { walk_expr(k, f); walk_expr(v, f); }
                    lua_ast::TableField::NameField(_, v) | lua_ast::TableField::ValueField(v) => walk_expr(v, f),
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
///
/// Every pass only rewrites what it can prove equivalent (see
/// [`util`] for the shared checks), so the result behaves like the input.
pub fn deobfuscate(block: &mut Block) {
    let fixpoint = |block: &mut Block, f: &mut dyn FnMut(&mut Block)| {
        for _ in 0..8 {
            let s0 = lua_ast::print_block(block, 0);
            f(block);
            if lua_ast::print_block(block, 0) == s0 { break; }
        }
    };

    // One name per variable, so the name-based checks below are exact.
    pass_unique::run(block);

    // Obfuscator noise and trivially dead code.
    pass_junk::run(block);
    pass6_dead::run(block);

    // Constants.
    fixpoint(block, &mut |b| {
        pass2_prop::run(b);
        pass1_fold::run(b);
        pass_stdlib::run(b);
        pass_cond::run(b);
    });

    // Lookup tables.
    pass3_table::run(block);
    pass5_perm::run(block);
    pass1_fold::run(block);
    pass4_concat::run(block);

    // Encrypted strings.
    pass_cipher_dec::run(block);

    // Helper functions and constant tables.
    fixpoint(block, &mut |b| {
        pass_const_func::run(b);
        pass_eval::run(b);
        pass_fold_tables::run(b);
        pass2_prop::run(b);
        pass1_fold::run(b);
        pass_stdlib::run(b);
        pass_cond::run(b);
    });

    // Names and clean-up.
    pass_func_alias::run(block);
    pass_dce::run(block);
    pass6_dead::run(block);
    pass8_rename::run(block);
    pass9_desugar::run(block);

    // Lua's 200-locals limit, now that unused locals are gone.
    pass_limit::run(block);
}
