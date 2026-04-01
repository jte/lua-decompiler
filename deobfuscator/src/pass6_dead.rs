/// Pass 6 – Dead-code elimination.
///
/// Removes:
///   • `local _NAME = nil`               (useless nil initialisation)
///   • empty `if cond then end` blocks
///   • empty `for … do end` loops
///   • empty `while cond do end` loops

use lua_ast::{Block, Stat};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut clean_block);
}

fn clean_block(block: &mut Block) {
    lua_ast::transform_stats(block, &mut |stat| {
        match &stat {
            // `local _NAME = nil`
            Stat::Local { names, values }
                if values.len() == 1
                    && values[0] == lua_ast::Expr::Nil
                    && names.iter().all(|n| n.starts_with('_')) =>
            {
                vec![]
            }
            // Empty if block
            Stat::If { branches, else_body }
                if branches.iter().all(|(_, b)| b.is_empty())
                    && else_body.as_ref().map_or(true, |b| b.is_empty()) =>
            {
                vec![]
            }
            // Empty numeric for
            Stat::NumFor { body, .. } if body.is_empty() => vec![],
            // Empty generic for
            Stat::GenFor { body, .. } if body.is_empty() => vec![],
            // Empty while
            Stat::While { body, .. } if body.is_empty() => vec![],
            _ => vec![stat],
        }
    });
}
