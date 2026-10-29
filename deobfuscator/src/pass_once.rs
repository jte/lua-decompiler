/// Pass – loops that provably run once (or never).
///
/// ```lua
/// local a, b, n = 7, 7, 0              local a, b, n = 7, 7, 0
/// while a == b and n < 1 do            do
///   a = a + 1                    →       a = 8
///   n = n + 1                            n = 1
///   if a == b then <junk>                <body>
///   else <body> break end              end
/// end
/// ```
///
/// The loop's condition must mention only *control variables*: locals
/// declared once with a number literal in the same block before the loop and
/// written nowhere except by plain assignments at the top level of the loop
/// body.  Their values are then known at every point of the first iteration,
/// so conditions over them (the loop's, `if ... then break end`, and `if`s
/// choosing a branch) can be decided.  The rewrite happens when the
/// iteration provably ends — by a top-level `break`, or by falling through
/// to a condition that is false — and the body has no `goto` or labels.
/// Other `break`s then end the only iteration: they are dropped where nothing
/// of it follows them, otherwise the iteration becomes `repeat ... until true`.
/// Assignments to control variables stay, with their constant values, so
/// later reads see the same values.

use std::collections::BTreeMap;
use lua_ast::{Block, Expr, Stat};

use crate::for_each_block;
use crate::pass1_fold::fold_tree;
use crate::util::visit_stats;
use crate::walk_expr;

pub fn run(block: &mut Block) {
    // Every declaration and plain assignment, by name, over the whole tree.
    let mut decls: BTreeMap<String, usize> = BTreeMap::new();
    let mut writes: BTreeMap<String, usize> = BTreeMap::new();
    visit_stats(block, &mut |s| match s {
        Stat::Local { names, .. } => { for n in names { *decls.entry(n.clone()).or_default() += 1; } }
        Stat::NumFor { var, .. } => *decls.entry(var.clone()).or_default() += 2,
        Stat::GenFor { vars, .. } => { for v in vars { *decls.entry(v.clone()).or_default() += 2; } }
        Stat::Assign { lhs, .. } => {
            for l in lhs { if let Expr::Name(n) = l { *writes.entry(n.clone()).or_default() += 1; } }
        }
        _ => {}
    });
    crate::util::visit_exprs(block, &mut |e| if let Expr::Function(fb) = e {
        for p in &fb.params { *decls.entry(p.clone()).or_default() += 2; }
    });
    for_each_block(block, &mut |b| {
        for i in (0..b.len()).rev() {
            if let Some(new) = rewrite_loop(b, i, &decls, &writes) {
                // Keep a block when the iteration declares something, or
                // returns (`return` must end a block).
                let scoped = new.iter().any(|s| matches!(s, Stat::Local { .. } | Stat::Label(_) | Stat::Return(_)));
                let new = if scoped { vec![Stat::Do(new)] } else { new };
                b.splice(i..=i, new);
            }
        }
    });
}

type Env = BTreeMap<String, Expr>;

fn names_in(e: &Expr) -> Vec<String> {
    let mut out = Vec::new();
    walk_expr(e, &mut |x| if let Expr::Name(n) = x { out.push(n.clone()); });
    out
}

/// Value of `e` given the control variables, if it is decided by them.
fn eval(e: &Expr, env: &Env) -> Option<Expr> {
    if names_in(e).iter().any(|n| !env.contains_key(n)) { return None; }
    let mut e = e.clone();
    lua_ast::transform_expr(&mut e, &mut |x| {
        if let Expr::Name(n) = x { if let Some(v) = env.get(n) { *x = v.clone(); } }
    });
    fold_tree(&mut e);
    e.is_literal().then_some(e)
}

fn truthy(e: &Expr) -> bool { !matches!(e, Expr::Nil | Expr::False) }

/// Does `b` contain a `break` that leaves the enclosing loop (or a goto/label)?
fn leaves(b: &[Stat]) -> bool {
    b.iter().any(|s| match s {
        Stat::Break | Stat::Goto(_) | Stat::Label(_) => true,
        Stat::Do(x) => leaves(x),
        Stat::If { branches, else_body } => {
            branches.iter().any(|(_, x)| leaves(x)) || else_body.as_ref().is_some_and(|x| leaves(x))
        }
        // Breaks inside nested loops are theirs; gotos are not.
        Stat::While { body, .. } | Stat::Repeat { body, .. } | Stat::NumFor { body, .. } | Stat::GenFor { body, .. } => {
            has_goto(body)
        }
        _ => false,
    })
}

fn has_goto(b: &[Stat]) -> bool {
    let mut found = false;
    for s in b {
        if matches!(s, Stat::Goto(_) | Stat::Label(_)) { found = true; }
    }
    found || b.iter().any(|s| match s {
        Stat::Do(x) | Stat::While { body: x, .. } | Stat::Repeat { body: x, .. }
        | Stat::NumFor { body: x, .. } | Stat::GenFor { body: x, .. } => has_goto(x),
        Stat::If { branches, else_body } => {
            branches.iter().any(|(_, x)| has_goto(x)) || else_body.as_ref().is_some_and(|x| has_goto(x))
        }
        _ => false,
    })
}

enum Exit { Fallthrough, Break }

/// Run one pass over `stats` with known control variables, emitting the
/// statements that execute.  `None` when something is undecided.
fn simulate(stats: &[Stat], env: &mut Env, out: &mut Vec<Stat>) -> Option<Exit> {
    for s in stats {
        match s {
            Stat::Break => return Some(Exit::Break),
            Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1
                && matches!(&lhs[0], Expr::Name(n) if env.contains_key(n)) =>
            {
                let Expr::Name(n) = &lhs[0] else { unreachable!() };
                let v = eval(&rhs[0], env)?;
                env.insert(n.clone(), v.clone());
                out.push(Stat::Assign { lhs: lhs.clone(), rhs: vec![v] });
            }
            Stat::If { branches, else_body }
                if branches.iter().any(|(c, _)| names_in(c).iter().any(|n| env.contains_key(n))) =>
            {
                let mut chosen = else_body.as_ref();
                for (c, b) in branches {
                    if truthy(&eval(c, env)?) { chosen = Some(b); break; }
                }
                let mut inner = Vec::new();
                let exit = match chosen { Some(b) => simulate(b, env, &mut inner)?, None => Exit::Fallthrough };
                if inner.iter().any(|s| matches!(s, Stat::Local { .. })) {
                    out.push(Stat::Do(inner));
                } else {
                    out.extend(inner);
                }
                if let Exit::Break = exit { return Some(Exit::Break); }
            }
            // May hold breaks; `rewrite_loop` checks where they sit.
            other => out.push(other.clone()),
        }
    }
    Some(Exit::Fallthrough)
}

/// The statements that replace the loop at `b[i]`.
fn rewrite_loop(b: &Block, i: usize, decls: &BTreeMap<String, usize>, writes: &BTreeMap<String, usize>) -> Option<Vec<Stat>> {
    let Stat::While { cond, body } = &b[i] else { return None };
    if names_in(cond).is_empty() { return None; }
    // Control variables: declared once with a number before the loop, and
    // every write is a top-level assignment in the body.  Candidates are the
    // names in the loop condition and in the body's top-level `if`s.
    let top_writes = |v: &str| body.iter().filter(|s| matches!(s, Stat::Assign { lhs, .. }
        if lhs.len() == 1 && matches!(&lhs[0], Expr::Name(n) if n == v))).count();
    let mut candidates = names_in(cond);
    for s in body {
        if let Stat::If { branches, .. } = s {
            for (c, _) in branches { candidates.extend(names_in(c)); }
        }
    }
    let mut env = Env::new();
    for v in &candidates {
        if env.contains_key(v) { continue; }
        if decls.get(v) != Some(&1) || writes.get(v).copied().unwrap_or(0) != top_writes(v) { continue; }
        let init = b[..i].iter().find_map(|s| match s {
            Stat::Local { names, values } => names.iter().position(|n| n == v)
                .map(|k| values.get(k).cloned().unwrap_or(Expr::Nil)),
            _ => None,
        });
        if let Some(init @ (Expr::Integer(_) | Expr::Float(_))) = init { env.insert(v.clone(), init); }
    }
    if names_in(cond).iter().any(|n| !env.contains_key(n)) { return None; }
    // Writes nested deeper (e.g. inside an `if`) are not top-level ones.
    for v in env.keys() {
        let mut nested = 0;
        visit_stats(body, &mut |s| if let Stat::Assign { lhs, .. } = s {
            nested += lhs.iter().filter(|l| matches!(l, Expr::Name(n) if n == v)).count();
        });
        if nested != top_writes(v) { return None; }
    }
    if has_goto(body) { return None; }

    if !truthy(&eval(cond, &env)?) { return Some(vec![]); }
    let mut out = Vec::new();
    if let Exit::Fallthrough = simulate(body, &mut env, &mut out)? {
        if truthy(&eval(cond, &env)?) { return None; }
    }
    // The iteration is the last either way, so a `break` that ends it is the
    // same as reaching its end.  Breaks with more of the iteration after them
    // need a loop to leave: one that runs once.
    let mut stripped = out.clone();
    if strip_tail_breaks(&mut stripped) { return Some(stripped); }
    Some(vec![Stat::Repeat { body: out, cond: Expr::True }])
}

/// Remove `break`s in tail position (nothing of the iteration follows them);
/// false if any other `break` (or goto) remains.
fn strip_tail_breaks(b: &mut Vec<Stat>) -> bool {
    let Some(last) = b.len().checked_sub(1) else { return true };
    if leaves(&b[..last]) { return false; }
    match &mut b[last] {
        Stat::Break => { b.pop(); true }
        Stat::If { branches, else_body } => {
            branches.iter_mut().all(|(_, x)| strip_tail_breaks(x))
                && else_body.as_mut().map_or(true, strip_tail_breaks)
        }
        Stat::Do(x) => strip_tail_breaks(x),
        other => !leaves(std::slice::from_ref(other)),
    }
}
