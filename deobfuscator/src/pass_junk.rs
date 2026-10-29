/// Pass – dead "fresh table" checks.
///
/// Obfuscators sprinkle
///
/// ```lua
/// local t = {}
/// if t.i ~= nil then t.i = t:i() end
/// ```
///
/// A freshly created empty table (no metatable) that nothing has touched
/// yet has no fields, so `t.k ~= nil` is false and the branch is dead.
/// Such `if`s are replaced by their `else` part; the table itself is left to
/// the dead-local pass.
use lua_ast::{BinOp, Block, Expr, Stat};

use crate::for_each_block;
use crate::util::count_refs;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

/// `t.k ~= nil` / `t[k] ~= nil` for this table name.
fn is_field_check(cond: &Expr, t: &str) -> bool {
    match cond {
        Expr::BinOp { op: BinOp::Ne, lhs, rhs } => {
            let field = |e: &Expr| matches!(e, Expr::Index { table, key }
                if matches!(table.as_ref(), Expr::Name(n) if n == t) && key.is_literal());
            (field(lhs) && matches!(rhs.as_ref(), Expr::Nil)) || (field(rhs) && matches!(lhs.as_ref(), Expr::Nil))
        }
        _ => false,
    }
}

fn process_block(block: &mut Block) {
    let mut i = 0;
    while i < block.len() {
        let t = match &block[i] {
            Stat::Local { names, values } if names.len() == 1 && values.len() == 1
                && matches!(&values[0], Expr::Table(f) if f.is_empty()) => names[0].clone(),
            _ => { i += 1; continue; }
        };
        // Following statements that don't mention `t` leave it untouched.
        let mut j = i + 1;
        while j < block.len() {
            let mentions = count_refs(std::slice::from_ref(&block[j]), &t) > 0;
            if !mentions { j += 1; continue; }
            let dead = matches!(&block[j], Stat::If { branches, .. }
                if branches.len() == 1 && is_field_check(&branches[0].0, &t));
            if !dead { break; }
            let Stat::If { else_body, .. } = block.remove(j) else { unreachable!() };
            let rest = else_body.unwrap_or_default();
            let n = rest.len();
            for (k, s) in rest.into_iter().enumerate() { block.insert(j + k, s); }
            // Statements spliced in may mention `t`; re-examine from j.
            if n == 0 { continue; }
        }
        i += 1;
    }
}
