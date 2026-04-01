/// Pass 3 – 256-char identity lookup-table resolution.
///
/// Detects `local _tN = {"\x00", "\x01", ..., "\xFF"}` (256 entries) and
/// replaces every `_tN[K]` with the byte literal `string.char(K-1)` (as
/// `Expr::Str(vec![(K-1) as u8])`).

use lua_ast::{Block, Expr, Stat, TableField, transform_block};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    // Find all 256-char table variable names in this block.
    let tables: Vec<String> = find_lookup_tables(block);
    if tables.is_empty() { return; }

    for tname in &tables {
        // Replace _tN[K] expressions in all statements (including the decl line).
        for stat in block.iter_mut() {
            substitute_stat(stat, tname);
        }
        // Remove the declaration statement.
        block.retain(|s| !is_lookup_decl(s, tname));
    }
}

/// Returns the names of all 256-char identity table variables declared in `block`.
fn find_lookup_tables(block: &Block) -> Vec<String> {
    let mut result = Vec::new();
    for stat in block {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if is_256_char_table(&values[0]) {
                    result.push(names[0].clone());
                }
            }
        }
    }
    result
}

/// True if `e` is a Table with 256 ValueField entries where entry 0 is `Str([0])`.
fn is_256_char_table(e: &Expr) -> bool {
    if let Expr::Table(fields) = e {
        if fields.len() == 256 {
            if let TableField::ValueField(Expr::Str(b)) = &fields[0] {
                return b.as_slice() == &[0u8];
            }
        }
    }
    false
}

fn is_lookup_decl(stat: &Stat, tname: &str) -> bool {
    if let Stat::Local { names, values } = stat {
        names.len() == 1 && names[0] == tname
            && values.len() == 1 && is_256_char_table(&values[0])
    } else {
        false
    }
}

fn substitute_stat(stat: &mut Stat, tname: &str) {
    // We use transform_block on a single-statement wrapper isn't possible, but
    // we can use transform_expr on each expression in the statement.
    match stat {
        Stat::Local { values, .. } => {
            for v in values.iter_mut() { subst_expr(v, tname); }
        }
        Stat::Assign { lhs, rhs } => {
            for e in lhs.iter_mut().chain(rhs.iter_mut()) { subst_expr(e, tname); }
        }
        Stat::Return(vals) => {
            for v in vals.iter_mut() { subst_expr(v, tname); }
        }
        Stat::Call(e) => subst_expr(e, tname),
        _ => {}
    }
}

fn subst_expr(e: &mut Expr, tname: &str) {
    lua_ast::transform_expr(e, &mut |node| {
        if let Expr::Index { table, key } = node {
            if let (Expr::Name(n), Expr::Integer(k)) = (table.as_ref(), key.as_ref()) {
                if n == tname {
                    let k = *k;
                    if k >= 1 && k <= 256 {
                        *node = Expr::Str(vec![(k - 1) as u8]);
                    }
                }
            }
        }
    });
}
