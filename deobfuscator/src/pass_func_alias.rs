/// Pass – Global function alias resolution.
///
/// Finds assignments of the form:
///   `CHAIN = _fN`
/// where CHAIN is a pure index chain (e.g. `gg.searchNumber`),
/// and _fN is a local function name.
///
/// Then substitutes every `_fN` name occurrence with `CHAIN` throughout the
/// whole AST, EXCEPT in the assignment itself (`CHAIN = _fN` is preserved).

use std::collections::BTreeMap;
use lua_ast::{Block, Expr, Stat, TableField};

pub fn run(block: &mut Block) {
    let mut mapping: BTreeMap<String, Expr> = BTreeMap::new();
    collect_block(block, &mut mapping);
    if mapping.is_empty() { return; }
    apply_block(block, &mapping);
}

// ---------------------------------------------------------------------------
// Collection: find CHAIN = _fN assignments recursively
// ---------------------------------------------------------------------------

fn collect_block(block: &Block, mapping: &mut BTreeMap<String, Expr>) {
    for stat in block.iter() {
        match stat {
            Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => {
                if !matches!(&lhs[0], Expr::Name(_)) && is_pure_index_chain(&lhs[0]) {
                    if let Expr::Name(fn_name) = &rhs[0] {
                        mapping.entry(fn_name.clone()).or_insert_with(|| lhs[0].clone());
                    }
                }
                collect_expr(&rhs[0], mapping);
            }
            Stat::Local { values, .. } => {
                for v in values { collect_expr(v, mapping); }
            }
            Stat::Return(vals) => {
                for v in vals { collect_expr(v, mapping); }
            }
            Stat::Call(e) => collect_expr(e, mapping),
            Stat::Do(b) => collect_block(b, mapping),
            Stat::While { body, .. } => collect_block(body, mapping),
            Stat::Repeat { body, .. } => collect_block(body, mapping),
            Stat::NumFor { body, .. } => collect_block(body, mapping),
            Stat::GenFor { body, .. } => collect_block(body, mapping),
            Stat::If { branches, else_body } => {
                for (_, b) in branches { collect_block(b, mapping); }
                if let Some(b) = else_body { collect_block(b, mapping); }
            }
            _ => {}
        }
    }
}

fn collect_expr(expr: &Expr, mapping: &mut BTreeMap<String, Expr>) {
    match expr {
        Expr::Function(fb) => collect_block(&fb.body, mapping),
        Expr::Call { func, args } => {
            collect_expr(func, mapping);
            for a in args { collect_expr(a, mapping); }
        }
        Expr::Index { table, key } => {
            collect_expr(table, mapping);
            collect_expr(key, mapping);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            collect_expr(lhs, mapping);
            collect_expr(rhs, mapping);
        }
        Expr::UnOp { operand, .. } => collect_expr(operand, mapping),
        Expr::Table(fields) => {
            for field in fields {
                match field {
                    TableField::IndexField(k, v) => { collect_expr(k, mapping); collect_expr(v, mapping); }
                    TableField::NameField(_, v) => collect_expr(v, mapping),
                    TableField::ValueField(v) => collect_expr(v, mapping),
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Application: replace _fN with CHAIN everywhere (except defining assignment)
// ---------------------------------------------------------------------------

fn apply_block(block: &mut Block, mapping: &BTreeMap<String, Expr>) {
    for stat in block.iter_mut() {
        match stat {
            // Preserve defining assignments: `CHAIN = _fN` — don't touch RHS.
            Stat::Assign { lhs, rhs }
                if lhs.len() == 1 && rhs.len() == 1
                && !matches!(&lhs[0], Expr::Name(_))
                && is_pure_index_chain(&lhs[0])
                && matches!(&rhs[0], Expr::Name(n) if mapping.contains_key(n)) =>
            {
                // LHS sub-expressions (keys inside the chain) can be substituted
                // but there are none in a simple chain, so skip entirely.
            }
            Stat::Assign { lhs, rhs } => {
                for e in lhs.iter_mut() { apply_expr(e, mapping); }
                for e in rhs.iter_mut() { apply_expr(e, mapping); }
            }
            Stat::Local { values, .. } => {
                for v in values.iter_mut() { apply_expr(v, mapping); }
            }
            Stat::Return(vals) => {
                for v in vals.iter_mut() { apply_expr(v, mapping); }
            }
            Stat::Call(e) => apply_expr(e, mapping),
            Stat::Do(b) => apply_block(b, mapping),
            Stat::While { cond, body } => {
                apply_expr(cond, mapping);
                apply_block(body, mapping);
            }
            Stat::Repeat { body, cond } => {
                apply_block(body, mapping);
                apply_expr(cond, mapping);
            }
            Stat::NumFor { from, to, step, body, .. } => {
                apply_expr(from, mapping);
                apply_expr(to, mapping);
                if let Some(s) = step { apply_expr(s, mapping); }
                apply_block(body, mapping);
            }
            Stat::GenFor { iters, body, .. } => {
                for e in iters.iter_mut() { apply_expr(e, mapping); }
                apply_block(body, mapping);
            }
            Stat::If { branches, else_body } => {
                for (cond, b) in branches.iter_mut() {
                    apply_expr(cond, mapping);
                    apply_block(b, mapping);
                }
                if let Some(b) = else_body { apply_block(b, mapping); }
            }
            _ => {}
        }
    }
}

fn apply_expr(e: &mut Expr, mapping: &BTreeMap<String, Expr>) {
    match e {
        Expr::Name(n) => {
            if let Some(replacement) = mapping.get(n) {
                *e = replacement.clone();
            }
        }
        Expr::Function(fb) => apply_block(&mut fb.body, mapping),
        Expr::Call { func, args } => {
            apply_expr(func, mapping);
            for a in args.iter_mut() { apply_expr(a, mapping); }
        }
        Expr::Index { table, key } => {
            apply_expr(table, mapping);
            apply_expr(key, mapping);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            apply_expr(lhs, mapping);
            apply_expr(rhs, mapping);
        }
        Expr::UnOp { operand, .. } => apply_expr(operand, mapping),
        Expr::Table(fields) => {
            for field in fields.iter_mut() {
                match field {
                    TableField::IndexField(k, v) => { apply_expr(k, mapping); apply_expr(v, mapping); }
                    TableField::NameField(_, v) => apply_expr(v, mapping),
                    TableField::ValueField(v) => apply_expr(v, mapping),
                }
            }
        }
        _ => {}
    }
}

fn is_pure_index_chain(e: &Expr) -> bool {
    match e {
        Expr::Name(_) => true,
        Expr::Index { table, key } => {
            if let Expr::Str(kb) = key.as_ref() {
                if let Ok(ks) = std::str::from_utf8(kb) {
                    if lua_ast::is_lua_ident(ks) {
                        return is_pure_index_chain(table);
                    }
                }
            }
            false
        }
        _ => false,
    }
}
