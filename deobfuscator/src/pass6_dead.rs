/// Pass 6 – Dead-code elimination (only where provably without effect).
///
///   • `local x = nil`               →  `local x`  (same meaning, shorter)
///   • `if c then end` with a call-free condition   →  removed
///   • `for i = <num>, <num>[, <num>] do end`        →  removed
///   • `while false do ... end`                       →  removed
///
/// Empty generic `for` loops and other empty `while` loops are kept: their
/// iterator calls and conditions can have effects, or never terminate.

use lua_ast::{Block, Expr, Stat};
use crate::for_each_block;
use crate::util::is_pure;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut clean_block);
}

fn is_number(e: &Expr) -> bool {
    match e {
        Expr::Integer(_) | Expr::Float(_) => true,
        Expr::UnOp { op: lua_ast::UnOp::Neg, operand } => is_number(operand),
        _ => false,
    }
}

fn clean_block(block: &mut Block) {
    lua_ast::transform_stats(block, &mut |stat| {
        match stat {
            Stat::Local { names, values } if !values.is_empty() && values.iter().all(|v| *v == Expr::Nil) => {
                vec![Stat::Local { names, values: vec![] }]
            }
            Stat::If { ref branches, ref else_body }
                if branches.iter().all(|(c, b)| b.is_empty() && is_pure(c))
                    && else_body.as_ref().map_or(true, |b| b.is_empty()) =>
            {
                vec![]
            }
            Stat::NumFor { ref from, ref to, ref step, ref body, .. }
                if body.is_empty() && is_number(from) && is_number(to)
                    && step.as_ref().map_or(true, is_number) =>
            {
                vec![]
            }
            Stat::While { cond: Expr::False | Expr::Nil, .. } => vec![],
            other => vec![other],
        }
    });
}
