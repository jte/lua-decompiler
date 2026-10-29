/// Pass – constant conditions and loop shapes.
///
///   • `if <truthy literal> then B end`   →  `B` (in `do ... end` when needed)
///   • branches whose condition is `false`/`nil` are dropped; a branch with a
///     truthy literal condition becomes the `else` and ends the chain
///   • `while <truthy> do if c then break end B end`  →  `while not c do B end`
///   • `while <truthy> do B if c then break end end`  →  `repeat B until c`
///   • unreachable statements, redundant `goto`s and unused labels go
///
/// Literal conditions have no effects, so dropping or skipping them is exact.
/// The loop rewrites evaluate `c` at the same points as before.

use std::collections::BTreeSet;
use lua_ast::{Block, Expr, Stat, UnOp};
use crate::for_each_block;
use crate::util::visit_stats;

pub fn run(block: &mut Block) {
    let mut targets = BTreeSet::new();
    visit_stats(block, &mut |s| if let Stat::Goto(l) = s { targets.insert(l.clone()); });
    for_each_block(block, &mut |b| {
        b.retain(|s| !matches!(s, Stat::Label(l) if !targets.contains(l)));
        lua_ast::transform_stats(b, &mut rewrite);
        drop_unreachable(b);
    });
}

/// Does control never fall through `s`?
fn ends(s: &Stat) -> bool {
    match s {
        Stat::Return(_) | Stat::Break | Stat::Goto(_) => true,
        Stat::Do(b) => b.last().map_or(false, ends),
        _ => false,
    }
}

/// Statements between one that never falls through and the next label (the
/// only way back in), a `goto` to the very next label, and a final
/// `do ... end` that scopes nothing.  A skipped region that declares locals
/// is kept when a label follows: code after the label may be in their scope.
fn drop_unreachable(b: &mut Block) {
    let mut i = 0;
    while i < b.len() {
        if ends(&b[i]) {
            let next = b[i + 1..].iter().position(|s| matches!(s, Stat::Label(_))).map_or(b.len(), |p| i + 1 + p);
            if next == b.len() || !b[i + 1..next].iter().any(|s| matches!(s, Stat::Local { .. })) {
                b.drain(i + 1..next);
            }
            if matches!((&b[i], b.get(i + 1)), (Stat::Goto(g), Some(Stat::Label(l))) if g == l) {
                b.remove(i);
                continue;
            }
        }
        i += 1;
    }
    if let Some(Stat::Do(inner)) = b.last() {
        if !inner.iter().any(|s| matches!(s, Stat::Local { .. } | Stat::Label(_))) {
            let Some(Stat::Do(inner)) = b.pop() else { unreachable!() };
            b.extend(inner);
        }
    }
}

fn truthy(e: &Expr) -> bool {
    matches!(e, Expr::True | Expr::Integer(_) | Expr::Float(_) | Expr::Str(_))
}

fn falsy(e: &Expr) -> bool {
    matches!(e, Expr::False | Expr::Nil)
}

/// `B` as statements of the enclosing block.  A `do` keeps locals and labels
/// scoped, and keeps a trailing `return`/`break` last in its block.
fn splice(b: Block) -> Vec<Stat> {
    let needs_do = b.iter().any(|s| matches!(s, Stat::Local { .. } | Stat::Label(_)))
        || matches!(b.last(), Some(Stat::Return(_) | Stat::Break));
    if b.is_empty() { vec![] } else if needs_do { vec![Stat::Do(b)] } else { b }
}

/// `if c then break end` → `c`.
fn break_cond(s: &Stat) -> Option<&Expr> {
    match s {
        Stat::If { branches, else_body: None } if branches.len() == 1
            && matches!(branches[0].1.as_slice(), [Stat::Break]) => Some(&branches[0].0),
        _ => None,
    }
}

fn negate(e: Expr) -> Expr {
    match e {
        // Only used as a condition, where `not not x` and `x` agree.
        Expr::UnOp { op: UnOp::Not, operand } => *operand,
        other => Expr::UnOp { op: UnOp::Not, operand: Box::new(other) },
    }
}

fn rewrite(stat: Stat) -> Vec<Stat> {
    match stat {
        Stat::If { branches, else_body } => {
            let mut kept = Vec::new();
            let mut else_body = else_body;
            for (c, b) in branches {
                if falsy(&c) { continue; }
                if truthy(&c) { else_body = Some(b); break; }
                kept.push((c, b));
            }
            if kept.is_empty() {
                return else_body.map_or(vec![], splice);
            }
            vec![Stat::If { branches: kept, else_body }]
        }
        Stat::While { cond, mut body } if truthy(&cond) => {
            if let Some(c) = body.first().and_then(break_cond).cloned() {
                body.remove(0);
                return vec![Stat::While { cond: negate(c), body }];
            }
            let has_label = body.iter().any(|s| matches!(s, Stat::Label(_)));
            if body.len() > 1 && !has_label {
                if let Some(c) = body.last().and_then(break_cond).cloned() {
                    body.pop();
                    return vec![Stat::Repeat { body, cond: c }];
                }
            }
            vec![Stat::While { cond, body }]
        }
        other => vec![other],
    }
}
