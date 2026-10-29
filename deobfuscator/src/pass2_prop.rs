/// Pass 2 – Constant propagation.
///
/// Finds `local NAME = LITERAL` where the name is never reassigned within
/// its scope, and substitutes every use of NAME with the literal.
/// Operates per-block (does not propagate across block boundaries).

use std::collections::{BTreeMap, BTreeSet};
use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut propagate_in_block);
}

fn propagate_in_block(block: &mut Block) {
    let consts = collect_consts(block);
    if consts.is_empty() { return; }
    // Substitute in every expression in the block (except the decl lines).
    substitute_block(block, &consts);
}

/// Collect { name → literal } for names declared exactly once with a literal
/// and never plain-assigned within this block OR any nested block.
fn collect_consts(block: &Block) -> BTreeMap<String, Expr> {
    let mut decls: BTreeMap<String, Expr> = BTreeMap::new();
    let mut reassigned: BTreeSet<String> = BTreeSet::new();

    for stat in block {
        // Collect direct declarations at this level.
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                let name = &names[0];
                let val  = &values[0];
                if val.is_literal() && !decls.contains_key(name) {
                    decls.insert(name.clone(), val.clone());
                }
            }
        }
        // Collect ALL assignments (current + nested blocks).
        collect_assigned_names_deep(stat, &mut reassigned);
    }

    decls.retain(|name, _| !reassigned.contains(name));
    decls
}

/// Recursively collect every `Name` that appears on the LHS of any assignment
/// at any nesting depth within `stat`.
fn collect_assigned_names_deep(stat: &Stat, out: &mut BTreeSet<String>) {
    if let Stat::Assign { lhs, .. } = stat {
        for e in lhs {
            if let Expr::Name(n) = e { out.insert(n.clone()); }
        }
    }
    // Closures can assign the local through an upvalue.
    let mut in_fn = |e: &Expr| collect_in_closures(e, out);
    match stat {
        Stat::Assign { lhs, rhs } => { for e in lhs.iter().chain(rhs) { in_fn(e); } }
        Stat::Local { values, .. } => { for e in values { in_fn(e); } }
        Stat::Return(v) => { for e in v { in_fn(e); } }
        Stat::Call(e) => in_fn(e),
        Stat::While { cond, .. } | Stat::Repeat { cond, .. } => in_fn(cond),
        Stat::If { branches, .. } => { for (c, _) in branches { in_fn(c); } }
        Stat::NumFor { from, to, step, .. } => {
            in_fn(from);
            in_fn(to);
            if let Some(s) = step { in_fn(s); }
        }
        Stat::GenFor { iters, .. } => { for e in iters { in_fn(e); } }
        _ => {}
    }
    match stat {
        Stat::Do(b) | Stat::While { body: b, .. } | Stat::Repeat { body: b, .. }
        | Stat::NumFor { body: b, .. } | Stat::GenFor { body: b, .. } => {
            for s in b { collect_assigned_names_deep(s, out); }
        }
        Stat::If { branches, else_body } => {
            for (_, b) in branches { for s in b { collect_assigned_names_deep(s, out); } }
            if let Some(b) = else_body { for s in b { collect_assigned_names_deep(s, out); } }
        }
        _ => {}
    }
}

/// Names assigned anywhere inside function literals within `e`.
fn collect_in_closures(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Function(fb) => { for s in &fb.body { collect_assigned_names_deep(s, out); } }
        Expr::Index { table, key } => { collect_in_closures(table, out); collect_in_closures(key, out); }
        Expr::BinOp { lhs, rhs, .. } => { collect_in_closures(lhs, out); collect_in_closures(rhs, out); }
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => collect_in_closures(operand, out),
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
            collect_in_closures(func, out);
            for a in args { collect_in_closures(a, out); }
        }
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::IndexField(k, v) => { collect_in_closures(k, out); collect_in_closures(v, out); }
                    TableField::NameField(_, v) | TableField::ValueField(v) => collect_in_closures(v, out),
                }
            }
        }
        _ => {}
    }
}

/// Replace all occurrences of `Name(n)` (that are not the LHS of a
/// `local NAME =` declaration) with the mapped literal.
fn substitute_block(block: &mut Block, consts: &BTreeMap<String, Expr>) {
    for stat in block.iter_mut() {
        match stat {
            // Skip the declaration line itself (don't replace the name there).
            Stat::Local { names, values } if names.len() == 1 => {
                let name = &names[0];
                if consts.contains_key(name) {
                    // Still substitute inside the RHS (may reference other consts).
                    for v in values.iter_mut() { substitute_expr(v, consts); }
                    continue;
                }
                for v in values.iter_mut() { substitute_expr(v, consts); }
            }
            Stat::Local { values, .. } => {
                for v in values.iter_mut() { substitute_expr(v, consts); }
            }
            Stat::Assign { lhs, rhs } => {
                // Don't substitute on LHS names (they are targets).
                for e in lhs.iter_mut() {
                    // But DO substitute inside index keys.
                    if let Expr::Index { key, .. } = e { substitute_expr(key, consts); }
                }
                for e in rhs.iter_mut() { substitute_expr(e, consts); }
            }
            Stat::Return(vals) => {
                for v in vals.iter_mut() { substitute_expr(v, consts); }
            }
            Stat::Call(e) => substitute_expr(e, consts),
            // Nested blocks are handled by for_each_block → separate propagate_in_block calls.
            _ => {}
        }
    }
}

fn substitute_expr(e: &mut Expr, consts: &BTreeMap<String, Expr>) {
    // Do NOT use transform_expr here — it recurses into Expr::Function bodies,
    // which would propagate outer-scope constants into closures (wrong: closures
    // capture upvalues, and their own for_each_block call handles them separately).
    subst_expr_no_closure(e, consts);
}

fn subst_expr_no_closure(e: &mut Expr, consts: &BTreeMap<String, Expr>) {
    match e {
        Expr::Name(n) => {
            if let Some(lit) = consts.get(n) {
                *e = lit.clone();
            }
        }
        // Stop at closure boundaries — closure bodies are handled by their own block visit.
        Expr::Function(_) => {}
        Expr::Index { table, key } => {
            subst_expr_no_closure(table, consts);
            subst_expr_no_closure(key, consts);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            subst_expr_no_closure(lhs, consts);
            subst_expr_no_closure(rhs, consts);
        }
        Expr::UnOp { operand, .. } => subst_expr_no_closure(operand, consts),
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
            subst_expr_no_closure(func, consts);
            for a in args.iter_mut() { subst_expr_no_closure(a, consts); }
        }
        Expr::Table(fields) => {
            use lua_ast::TableField;
            for f in fields.iter_mut() {
                match f {
                    TableField::IndexField(k, v) => {
                        subst_expr_no_closure(k, consts);
                        subst_expr_no_closure(v, consts);
                    }
                    TableField::NameField(_, v) => subst_expr_no_closure(v, consts),
                    TableField::ValueField(v) => subst_expr_no_closure(v, consts),
                }
            }
        }
        _ => {} // Leaf nodes (Integer, Float, Str, True, False, Nil, Vararg)
    }
}
