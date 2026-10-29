/// Pass 1 – Constant folding.
///
/// Walks all expressions bottom-up and folds literal arithmetic:
///   BinOp(+, Integer(a), Integer(b))  →  Integer(a+b)
///   UnOp(-, Integer(n))               →  Integer(-n)
///   etc.

use lua_ast::{Block, BinOp, Expr, UnOp};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut |b| {
        lua_ast::transform_block(b, &mut fold_expr);
    });
}

fn fold_expr(e: &mut Expr) {
    let folded = match e {
        Expr::BinOp { op, lhs, rhs } => fold_binop(op, lhs, rhs),
        Expr::UnOp { op, operand }   => fold_unop(op, operand),
        _ => None,
    };
    if let Some(f) = folded {
        *e = f;
    }
}

fn fold_binop(op: &BinOp, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    if let Some(b) = fold_compare(op, lhs, rhs) {
        return Some(if b { Expr::True } else { Expr::False });
    }
    // `L and R` / `L or R` with a literal `L` (R yields exactly one value).
    if matches!(op, BinOp::And | BinOp::Or) && lhs.is_literal() {
        let truthy = !matches!(lhs, Expr::Nil | Expr::False);
        let take_rhs = truthy == matches!(op, BinOp::And);
        return Some(if !take_rhs { lhs.clone() } else {
            match rhs {
                Expr::Call { .. } | Expr::Method { .. } | Expr::Vararg => Expr::Paren(Box::new(rhs.clone())),
                other => other.clone(),
            }
        });
    }
    // Integer × Integer
    match (lhs, rhs) {
        (Expr::Integer(a), Expr::Integer(b)) => {
            let a = *a;
            let b = *b;
            return match op {
                BinOp::Add  => Some(Expr::Integer(a.wrapping_add(b))),
                BinOp::Sub  => Some(Expr::Integer(a.wrapping_sub(b))),
                BinOp::Mul  => Some(Expr::Integer(a.wrapping_mul(b))),
                // Lua floors (rounds toward -inf), unlike Rust's euclidean ops.
                BinOp::IDiv if b != 0 => Some(Expr::Integer(floor_div(a, b))),
                BinOp::Mod  if b != 0 => Some(Expr::Integer(a.wrapping_sub(floor_div(a, b).wrapping_mul(b)))),
                // `^` and `/` always produce floats.
                BinOp::Pow  => Some(Expr::Float((a as f64).powf(b as f64))),
                BinOp::Div  if b != 0 => Some(Expr::Float(a as f64 / b as f64)),
                BinOp::BAnd => Some(Expr::Integer(a & b)),
                BinOp::BOr  => Some(Expr::Integer(a | b)),
                BinOp::BXor => Some(Expr::Integer(a ^ b)),
                BinOp::Shl  if b >= 0 && b < 64 => Some(Expr::Integer(a << b)),
                BinOp::Shr  if b >= 0 && b < 64 => Some(Expr::Integer(((a as u64) >> b) as i64)),
                BinOp::Eq   => Some(if a == b { Expr::True } else { Expr::False }),
                BinOp::Ne   => Some(if a != b { Expr::True } else { Expr::False }),
                BinOp::Lt   => Some(if a <  b { Expr::True } else { Expr::False }),
                BinOp::Le   => Some(if a <= b { Expr::True } else { Expr::False }),
                BinOp::Gt   => Some(if a >  b { Expr::True } else { Expr::False }),
                BinOp::Ge   => Some(if a >= b { Expr::True } else { Expr::False }),
                _ => None,
            };
        }
        // Float × Float
        (Expr::Float(a), Expr::Float(b)) => {
            let (a, b) = (*a, *b);
            return match op {
                BinOp::Add => Some(Expr::Float(a + b)),
                BinOp::Sub => Some(Expr::Float(a - b)),
                BinOp::Mul => Some(Expr::Float(a * b)),
                BinOp::Div if b != 0.0 => Some(Expr::Float(a / b)),
                _ => None,
            };
        }
        // Integer promoted to float for div
        (Expr::Integer(a), Expr::Integer(b)) if matches!(op, BinOp::Div) && *b != 0 => {
            return Some(Expr::Float(*a as f64 / *b as f64));
        }
        // String concat
        (Expr::Str(a), Expr::Str(b)) if matches!(op, BinOp::Concat) => {
            let mut out = a.clone();
            out.extend_from_slice(b);
            return Some(Expr::Str(out));
        }
        // Algebraic simplification: (x ± a) ± b → x ± (a ± b)  when a, b are integers.
        // This lets pass_subtable_decode match `v - 250 - 20` as `v - 270`.
        (Expr::BinOp { op: inner_op, lhs: x, rhs }, Expr::Integer(b)) if matches!(rhs.as_ref(), Expr::Integer(_)) => {
            let a = if let Expr::Integer(a) = rhs.as_ref() { *a } else { unreachable!() };
            let b = *b;
            let new_rhs: Option<i64> = match (inner_op, op) {
                (BinOp::Sub, BinOp::Sub) => Some(a.wrapping_add(b)),   // (x-a)-b = x-(a+b)
                (BinOp::Sub, BinOp::Add) => Some(a.wrapping_sub(b)),   // (x-a)+b = x-(a-b)
                (BinOp::Add, BinOp::Sub) => Some(b.wrapping_sub(a)),   // (x+a)-b = x-(b-a) if b>a else x+(a-b)
                (BinOp::Add, BinOp::Add) => {
                    // (x+a)+b = x+(a+b), but only if inner is Add → keep as Add
                    let sum = a.wrapping_add(b);
                    return Some(Expr::BinOp {
                        op: BinOp::Add,
                        lhs: x.clone(),
                        rhs: Box::new(Expr::Integer(sum)),
                    });
                }
                _ => None,
            };
            if let Some(c) = new_rhs {
                if c == 0 {
                    return Some(*x.clone());
                }
                let (new_op, new_c) = if c < 0 {
                    (BinOp::Add, c.wrapping_neg())
                } else {
                    (BinOp::Sub, c)
                };
                return Some(Expr::BinOp {
                    op: new_op,
                    lhs: x.clone(),
                    rhs: Box::new(Expr::Integer(new_c)),
                });
            }
        }
        _ => {}
    }
    None
}

/// Comparisons between literals.  Ordering is folded for numbers only
/// (string order depends on the C locale).
fn fold_compare(op: &BinOp, lhs: &Expr, rhs: &Expr) -> Option<bool> {
    // Exact as f64 (ints beyond 2^53 are left alone).
    let num = |e: &Expr| match e {
        Expr::Integer(n) if n.unsigned_abs() <= 1 << 53 => Some(*n as f64),
        Expr::Float(f) => Some(*f),
        _ => None,
    };
    if !lhs.is_literal() || !rhs.is_literal() { return None; }
    let eq = || -> Option<bool> {
        Some(match (lhs, rhs) {
            (Expr::Integer(a), Expr::Integer(b)) => a == b,
            (Expr::Str(a), Expr::Str(b)) => a == b,
            (Expr::Nil, Expr::Nil) | (Expr::True, Expr::True) | (Expr::False, Expr::False) => true,
            _ => match (num(lhs), num(rhs)) {
                (Some(a), Some(b)) => a == b,
                // Different types (a huge integer against a number is unknown).
                _ if matches!(lhs, Expr::Integer(_) | Expr::Float(_))
                    && matches!(rhs, Expr::Integer(_) | Expr::Float(_)) => return None,
                _ => false,
            },
        })
    };
    let (a, b) = (num(lhs), num(rhs));
    match op {
        BinOp::Eq => eq(),
        BinOp::Ne => eq().map(|x| !x),
        BinOp::Lt => Some(a? < b?),
        BinOp::Le => Some(a? <= b?),
        BinOp::Gt => Some(a? > b?),
        BinOp::Ge => Some(a? >= b?),
        _ => None,
    }
}

fn floor_div(a: i64, b: i64) -> i64 {
    let q = a.wrapping_div(b);
    if (a % b != 0) && ((a < 0) != (b < 0)) { q - 1 } else { q }
}

fn fold_unop(op: &UnOp, operand: &Expr) -> Option<Expr> {
    match (op, operand) {
        (UnOp::Neg,  Expr::Integer(n)) => Some(Expr::Integer(n.wrapping_neg())),
        (UnOp::Neg,  Expr::Float(f))   => Some(Expr::Float(-f)),
        (UnOp::BNot, Expr::Integer(n)) => Some(Expr::Integer(!n)),
        (UnOp::Not,  Expr::True)       => Some(Expr::False),
        (UnOp::Not,  Expr::False)      => Some(Expr::True),
        (UnOp::Not,  Expr::Nil)        => Some(Expr::True),
        _ => None,
    }
}
