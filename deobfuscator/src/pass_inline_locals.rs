/// Pass – Inline single-use local table declarations.
///
/// Finds `local _tN = { ... }` where `_tN` appears exactly twice in the block
/// (the declaration and exactly one use as an assignment RHS).
/// Replaces the use with the constructor and removes the declaration.

use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut |b| {
        loop {
            let before = b.len();
            inline_once(b);
            if b.len() == before { break; }
        }
    });
}

fn inline_once(block: &mut Block) {
    // Find all `local _tN = { ... }` declarations (table vars starting with `_t`).
    let decls: Vec<(usize, String, Expr)> = block.iter().enumerate().filter_map(|(i, s)| {
        if let Stat::Local { names, values } = s {
            if names.len() == 1 && names[0].starts_with("_t") && values.len() == 1 {
                if matches!(&values[0], Expr::Table(_)) {
                    return Some((i, names[0].clone(), values[0].clone()));
                }
            }
        }
        None
    }).collect();

    for (decl_idx, tname, body) in decls {
        // Count whole-word occurrences of tname in the block.
        let count = count_name_in_block(block, &tname);
        if count != 2 { continue; } // exactly decl + one use

        // Find the use site (must be an RHS of an assignment).
        let use_idx = match find_rhs_use(block, &tname, decl_idx) {
            Some(i) => i,
            None => continue,
        };

        // Substitute tname at the use site.
        subst_rhs(block, use_idx, &tname, body);

        // Remove the declaration (index may have shifted if use_idx < decl_idx).
        let actual_decl = if use_idx < decl_idx { decl_idx - 0 } else { decl_idx };
        if actual_decl < block.len() {
            block.remove(actual_decl);
        }
        return; // One at a time; loop will repeat.
    }
}

fn count_name_in_block(block: &Block, name: &str) -> usize {
    block.iter().map(|s| count_name_in_stat(s, name)).sum()
}

fn count_name_in_stat(stat: &Stat, name: &str) -> usize {
    match stat {
        Stat::Local { names, values } => {
            let in_decl = if names.contains(&name.to_string()) { 1 } else { 0 };
            let in_vals: usize = values.iter().map(|v| count_name_in_expr(v, name)).sum();
            in_decl + in_vals
        }
        Stat::Assign { lhs, rhs } => {
            lhs.iter().map(|e| count_name_in_expr(e, name)).sum::<usize>()
                + rhs.iter().map(|e| count_name_in_expr(e, name)).sum::<usize>()
        }
        Stat::Return(vals) => vals.iter().map(|v| count_name_in_expr(v, name)).sum(),
        Stat::Call(e) => count_name_in_expr(e, name),
        // Recurse into nested blocks, including loop/condition headers.
        Stat::Do(b) => b.iter().map(|s| count_name_in_stat(s, name)).sum(),
        Stat::While { cond, body } => {
            count_name_in_expr(cond, name)
                + body.iter().map(|s| count_name_in_stat(s, name)).sum::<usize>()
        }
        Stat::Repeat { body, cond } => {
            body.iter().map(|s| count_name_in_stat(s, name)).sum::<usize>()
                + count_name_in_expr(cond, name)
        }
        Stat::NumFor { from, to, step, body, .. } => {
            count_name_in_expr(from, name)
                + count_name_in_expr(to, name)
                + step.as_ref().map_or(0, |s| count_name_in_expr(s, name))
                + body.iter().map(|s| count_name_in_stat(s, name)).sum::<usize>()
        }
        Stat::GenFor { iters, body, .. } => {
            iters.iter().map(|e| count_name_in_expr(e, name)).sum::<usize>()
                + body.iter().map(|s| count_name_in_stat(s, name)).sum::<usize>()
        }
        Stat::If { branches, else_body } => {
            let in_branches: usize = branches.iter()
                .map(|(cond, b)| {
                    count_name_in_expr(cond, name)
                        + b.iter().map(|s| count_name_in_stat(s, name)).sum::<usize>()
                })
                .sum();
            let in_else: usize = else_body.iter()
                .flat_map(|b| b.iter())
                .map(|s| count_name_in_stat(s, name))
                .sum();
            in_branches + in_else
        }
        _ => 0,
    }
}

fn count_name_in_expr(e: &Expr, name: &str) -> usize {
    match e {
        Expr::Name(n) => if n == name { 1 } else { 0 },
        Expr::Index { table, key } =>
            count_name_in_expr(table, name) + count_name_in_expr(key, name),
        Expr::BinOp { lhs, rhs, .. } =>
            count_name_in_expr(lhs, name) + count_name_in_expr(rhs, name),
        Expr::UnOp { operand, .. } => count_name_in_expr(operand, name),
        Expr::Call { func, args } =>
            count_name_in_expr(func, name) + args.iter().map(|a| count_name_in_expr(a, name)).sum::<usize>(),
        Expr::Table(fields) => fields.iter().map(|f| match f {
            TableField::IndexField(k, v) =>
                count_name_in_expr(k, name) + count_name_in_expr(v, name),
            TableField::NameField(_, v) => count_name_in_expr(v, name),
            TableField::ValueField(v) => count_name_in_expr(v, name),
        }).sum(),
        _ => 0,
    }
}

/// Find the index of a statement where `name` appears as an RHS (not decl).
fn find_rhs_use(block: &Block, name: &str, skip_idx: usize) -> Option<usize> {
    for (i, stat) in block.iter().enumerate() {
        if i == skip_idx { continue; }
        let is_rhs = match stat {
            Stat::Assign { rhs, .. } => rhs.iter().any(|e| expr_contains_name_top(e, name)),
            Stat::Return(vals) => vals.iter().any(|e| expr_contains_name_top(e, name)),
            Stat::Local { values, .. } => values.iter().any(|e| expr_contains_name_top(e, name)),
            Stat::Call(e) => expr_contains_name_top(e, name),
            _ => false,
        };
        if is_rhs { return Some(i); }
    }
    None
}

fn expr_contains_name_top(e: &Expr, name: &str) -> bool {
    count_name_in_expr(e, name) > 0
}

fn subst_rhs(block: &mut Block, idx: usize, name: &str, replacement: Expr) {
    let subst = &mut |e: &mut Expr| {
        lua_ast::transform_expr(e, &mut |node| {
            if let Expr::Name(n) = node {
                if n == name { *node = replacement.clone(); }
            }
        });
    };
    match &mut block[idx] {
        Stat::Assign { rhs, .. } => { for e in rhs { subst(e); } }
        Stat::Local { values, .. } => { for v in values { subst(v); } }
        Stat::Return(vals) => { for v in vals { subst(v); } }
        Stat::Call(e) => subst(e),
        _ => {}
    }
}
