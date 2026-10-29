/// Pass – merge `local t = {...}` with the field assignments right after it.
///
///   local t = {}            local t = {
///   t.a = 1          →        a = 1,
///   t["b c"] = x              ["b c"] = x,
///                           }
///
/// Only consecutive `t["key"] = <call-free value>` statements are merged, so
/// nothing is reordered and no value can observe the table early.

use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;
use crate::util::{count_refs, is_pure};

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    let mut i = 0;
    while i < block.len() {
        let name = match &block[i] {
            Stat::Local { names, values } if names.len() == 1 && values.len() == 1
                && matches!(values[0], Expr::Table(_)) => names[0].clone(),
            _ => { i += 1; continue; }
        };
        let mut added: Vec<TableField> = Vec::new();
        let mut j = i + 1;
        while j < block.len() {
            let Stat::Assign { lhs, rhs } = &block[j] else { break };
            if lhs.len() != 1 || rhs.len() != 1 { break; }
            let Expr::Index { table, key } = &lhs[0] else { break };
            if !matches!(table.as_ref(), Expr::Name(n) if *n == name) { break; }
            let k = key.as_ref();
            let v = &rhs[0];
            // Integer keys would interact with positional entries; skip them.
            if !matches!(k, Expr::Str(_)) || !is_pure(v) { break; }
            if count_refs(&[Stat::Return(vec![v.clone()])], &name) > 0 { break; }
            added.push(match k.as_str_utf8().filter(|s| lua_ast::is_lua_ident(s)) {
                Some(id) => TableField::NameField(id.to_string(), v.clone()),
                None => TableField::IndexField(k.clone(), v.clone()),
            });
            j += 1;
        }
        if !added.is_empty() {
            if let Stat::Local { values, .. } = &mut block[i] {
                if let Expr::Table(fields) = &mut values[0] { fields.extend(added); }
            }
            block.drain(i + 1..j);
        }
        i += 1;
    }
}
