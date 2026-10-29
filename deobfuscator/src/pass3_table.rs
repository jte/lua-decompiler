/// Pass 3 – 256-char identity lookup-table resolution.
///
/// Detects `local t = {"\0", "\1", ..., "\255"}` (256 single-byte strings,
/// entry K = byte K-1) and replaces every `t[K]` with that one-byte string.
/// Only done when the table is never modified or passed around; the
/// declaration is removed once nothing refers to it any more.

use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;
use crate::util::{count_refs, read_only_table};

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    let tables: Vec<String> = block.iter().filter_map(|s| match s {
        Stat::Local { names, values } if names.len() == 1 && values.len() == 1 && is_256_char_table(&values[0]) => {
            Some(names[0].clone())
        }
        _ => None,
    }).collect();

    for tname in tables {
        if !read_only_table(block, &tname) { continue; }
        lua_ast::transform_block(block, &mut |node| {
            if let Expr::Index { table, key } = node {
                if let (Expr::Name(n), Expr::Integer(k)) = (table.as_ref(), key.as_ref()) {
                    if *n == tname && (1..=256).contains(k) {
                        *node = Expr::Str(vec![(*k - 1) as u8]);
                    }
                }
            }
        });
        if count_refs(block, &tname) == 1 {
            block.retain(|s| !matches!(s, Stat::Local { names, .. } if names.len() == 1 && names[0] == tname));
        }
    }
}

/// 256 one-byte strings where entry K is byte K-1.
fn is_256_char_table(e: &Expr) -> bool {
    if let Expr::Table(fields) = e {
        return fields.len() == 256 && fields.iter().enumerate().all(|(i, f)| {
            matches!(f, TableField::ValueField(Expr::Str(b)) if b.len() == 1 && b[0] as usize == i)
        });
    }
    false
}
