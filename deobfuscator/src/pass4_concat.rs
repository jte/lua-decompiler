/// Pass 4 – String-concatenation collapse.
///
/// Collapses:
///   local _NAME = ""          (empty seed)
///   _NAME = _NAME .. "a"
///   _NAME = _NAME .. "b"  →  local _NAME = "ab"
///
/// Works entirely at the AST level.  Only processes declarations whose
/// value is `Str(b"")` followed by `Assign { [Name], [BinOp(Concat, Name, Str)] }`.

use lua_ast::{Block, BinOp, Expr, Stat};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut collapse_block);
}

fn collapse_block(block: &mut Block) {
    let mut i = 0;
    while i < block.len() {
        // Look for `local _NAME = ""`
        let seed_name = match &block[i] {
            Stat::Local { names, values }
                if names.len() == 1
                    && values.len() == 1
                    && values[0] == Expr::Str(vec![])
                    && names[0].starts_with('_') =>
            {
                names[0].clone()
            }
            _ => { i += 1; continue; }
        };

        // Greedily consume `_NAME = _NAME .. "piece"` assignments.
        let mut accumulated: Vec<u8> = Vec::new();
        let mut j = i + 1;
        while j < block.len() {
            if let Stat::Assign { lhs, rhs } = &block[j] {
                if lhs.len() == 1 && rhs.len() == 1 {
                    if let Expr::Name(ln) = &lhs[0] {
                        if *ln == seed_name {
                            if let Expr::BinOp { op: BinOp::Concat, lhs: blhs, rhs: brhs } = &rhs[0] {
                                if let (Expr::Name(bn), Expr::Str(piece)) =
                                    (blhs.as_ref(), brhs.as_ref())
                                {
                                    if *bn == seed_name {
                                        accumulated.extend_from_slice(piece);
                                        j += 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            break;
        }

        if j > i + 1 {
            // Replace declaration with the accumulated string.
            let new_stat = Stat::Local {
                names: vec![seed_name],
                values: vec![Expr::Str(accumulated)],
            };
            // Remove consumed assignment statements.
            block.drain(i + 1..j);
            block[i] = new_stat;
        }

        i += 1;
    }
}
