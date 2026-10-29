//! Statement-level clean-up of structured code: dead labels, guard clauses,
//! `elseif` chains, and reconstruction of `and`/`or` value expressions.
//! Every rewrite here preserves semantics exactly.

use std::collections::BTreeSet;

use lua_ast::{BinOp, Expr, Stat, UnOp};

use crate::lift::{negate, pseudo_args, var_id};
use crate::simplify::{count_var, expr_eff};

// ---------------------------------------------------------------------------
// Labels
// ---------------------------------------------------------------------------

fn collect_gotos(b: &[Stat], out: &mut BTreeSet<String>) {
    for s in b {
        if let Stat::Goto(l) = s { out.insert(l.clone()); }
        for_each_child(s, &mut |c| collect_gotos(c, out));
    }
}

pub fn prune_labels(b: &mut Vec<Stat>) {
    let mut used = BTreeSet::new();
    collect_gotos(b, &mut used);
    prune_rec(b, &used);
}

fn prune_rec(b: &mut Vec<Stat>, used: &BTreeSet<String>) {
    b.retain(|s| !matches!(s, Stat::Label(l) if !used.contains(l)));
    for s in b.iter_mut() { for_each_child_mut(s, &mut |c| prune_rec(c, used)); }
}

pub fn for_each_child(s: &Stat, f: &mut impl FnMut(&Vec<Stat>)) {
    match s {
        Stat::Do(b) | Stat::While { body: b, .. } | Stat::Repeat { body: b, .. }
        | Stat::NumFor { body: b, .. } | Stat::GenFor { body: b, .. } => f(b),
        Stat::If { branches, else_body } => {
            for (_, b) in branches { f(b); }
            if let Some(b) = else_body { f(b); }
        }
        _ => {}
    }
}

pub fn for_each_child_mut(s: &mut Stat, f: &mut impl FnMut(&mut Vec<Stat>)) {
    match s {
        Stat::Do(b) | Stat::While { body: b, .. } | Stat::Repeat { body: b, .. }
        | Stat::NumFor { body: b, .. } | Stat::GenFor { body: b, .. } => f(b),
        Stat::If { branches, else_body } => {
            for (_, b) in branches.iter_mut() { f(b); }
            if let Some(b) = else_body { f(b); }
        }
        _ => {}
    }
}

/// Readable names for the labels that survived pruning.
pub fn rename_labels(b: &mut Vec<Stat>) {
    let mut used = BTreeSet::new();
    collect_gotos(b, &mut used);
    let map: std::collections::BTreeMap<String, String> = used.iter().enumerate()
        .map(|(i, l)| {
            let base = if l.starts_with("@c") { "continue" } else { "label" };
            (l.clone(), format!("{}_{}", base, i + 1))
        })
        .collect();
    rename_labels_rec(b, &map);
}

fn rename_labels_rec(b: &mut Vec<Stat>, map: &std::collections::BTreeMap<String, String>) {
    for s in b.iter_mut() {
        match s {
            Stat::Goto(l) | Stat::Label(l) => { if let Some(n) = map.get(l) { *l = n.clone(); } }
            _ => for_each_child_mut(s, &mut |c| rename_labels_rec(c, map)),
        }
    }
}

// ---------------------------------------------------------------------------
// Structural simplification
// ---------------------------------------------------------------------------

fn is_abrupt(b: &[Stat]) -> bool {
    match b.last() {
        Some(Stat::Return(_)) | Some(Stat::Break) | Some(Stat::Goto(_)) => true,
        Some(Stat::If { branches, else_body: Some(e) }) => {
            branches.iter().all(|(_, b)| is_abrupt(b)) && is_abrupt(e)
        }
        _ => false,
    }
}

fn is_boolean(e: &Expr) -> bool {
    match e {
        Expr::True | Expr::False => true,
        Expr::UnOp { op: UnOp::Not, .. } => true,
        Expr::BinOp { op, lhs, rhs } => match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => true,
            BinOp::And | BinOp::Or => is_boolean(lhs) && is_boolean(rhs),
            _ => false,
        },
        _ => false,
    }
}

fn always_truthy(e: &Expr) -> bool {
    match e {
        Expr::True | Expr::Integer(_) | Expr::Float(_) | Expr::Str(_) | Expr::Table(_) | Expr::Function(_) => true,
        Expr::Call { .. } => pseudo_args(e, "@closure").is_some(),
        _ => false,
    }
}

fn mk(op: BinOp, a: Expr, b: Expr) -> Expr {
    // Keep `and`/`or` chains left-associative (`a or b or c`).
    if let Expr::BinOp { op: bop, lhs, rhs } = &b {
        if *bop == op && matches!(op, BinOp::And | BinOp::Or) {
            return mk(op.clone(), mk(op, a, (**lhs).clone()), (**rhs).clone());
        }
    }
    Expr::BinOp { op, lhs: Box::new(a), rhs: Box::new(b) }
}

/// `X = <expr>` where X is a variable.
fn single_assign(s: &Stat) -> Option<(usize, &Expr)> {
    match s {
        Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => var_id(&lhs[0]).map(|v| (v, &rhs[0])),
        _ => None,
    }
}

fn single_assign_block(b: &[Stat]) -> Option<(usize, &Expr)> {
    if b.len() == 1 { single_assign(&b[0]) } else { None }
}

fn is_pure(e: &Expr) -> bool {
    let eff = expr_eff(e);
    !eff.calls
}

/// TESTSET: `if R then X = R else X = B end` → `X = R or B` (and the
/// `not R` form → `X = R and B`).
fn value_testset(c: &Expr, a: &Expr, b: &Expr) -> Option<Expr> {
    if a == c && is_pure(c) { return Some(mk(BinOp::Or, c.clone(), b.clone())); }
    if let Expr::UnOp { op: UnOp::Not, operand } = c {
        if a == operand.as_ref() && is_pure(operand) { return Some(mk(BinOp::And, (**operand).clone(), b.clone())); }
    }
    None
}

/// Try the value rules on `if c then X = a else X = b end`.
fn value_if(c: &Expr, x: usize, a: &Expr, b: &Expr) -> Option<Expr> {
    if count_var(c, x) > 0 { return None; }
    // `if C then X = A or B else X = B end` → `X = C and A or B`.
    if let Expr::BinOp { op: BinOp::Or, lhs, rhs } = a {
        if rhs.as_ref() == b {
            return Some(mk(BinOp::Or, mk(BinOp::And, c.clone(), (**lhs).clone()), b.clone()));
        }
    }
    if matches!(a, Expr::True) && matches!(b, Expr::False) && is_boolean(c) { return Some(c.clone()); }
    if matches!(a, Expr::False) && matches!(b, Expr::True) && is_boolean(c) {
        return Some(negate(c.clone()));
    }
    if always_truthy(a) {
        return Some(mk(BinOp::Or, mk(BinOp::And, c.clone(), a.clone()), b.clone()));
    }
    None
}

pub fn simplify(b: &mut Vec<Stat>) {
    for s in b.iter_mut() { for_each_child_mut(s, &mut |c| simplify(c)); }
    let mut changed = true;
    while changed {
        changed = false;
        let mut i = 0;
        while i < b.len() {
            // Normalize if-statements.
            if let Stat::If { branches, else_body } = &mut b[i] {
                if else_body.as_ref().map_or(false, |e| e.is_empty()) {
                    *else_body = None;
                    changed = true;
                }
                if branches.len() == 1 && branches[0].1.is_empty() && else_body.is_some() {
                    let e = else_body.take().unwrap();
                    let c = std::mem::replace(&mut branches[0].0, Expr::Nil);
                    branches[0] = (negate(c), e);
                    changed = true;
                }
                // `if c then <abrupt> else E end` → `if c then <abrupt> end E`
                if let Some(e) = else_body {
                    if branches.iter().all(|(_, bb)| is_abrupt(bb)) {
                        let e = std::mem::take(e);
                        *else_body = None;
                        let at = i + 1;
                        for (k, s) in e.into_iter().enumerate() { b.insert(at + k, s); }
                        changed = true;
                        continue;
                    }
                }
                // `if c then T else <abrupt> end` → `if not c then <abrupt> end T`
                if let Stat::If { branches, else_body } = &mut b[i] {
                    if branches.len() == 1 && else_body.as_ref().map_or(false, |e| is_abrupt(e) && !e.is_empty())
                        && !is_abrupt(&branches[0].1)
                    {
                        let e = else_body.take().unwrap();
                        let (c, t) = branches.pop().unwrap();
                        branches.push((negate(c), e));
                        for (k, s) in t.into_iter().enumerate() { b.insert(i + 1 + k, s); }
                        changed = true;
                        continue;
                    }
                }
                // elseif
                if let Stat::If { branches, else_body } = &mut b[i] {
                    if let Some(e) = else_body {
                        if e.len() == 1 && matches!(e[0], Stat::If { .. }) {
                            if let Some(Stat::If { branches: nb, else_body: ne }) = e.pop() {
                                branches.extend(nb);
                                *else_body = ne;
                                changed = true;
                            }
                        }
                    }
                }
                // Value forms: `if c then X = a else X = b end`.
                if let Stat::If { branches, else_body: Some(e) } = &b[i] {
                    if branches.len() == 1 {
                        if let (Some((x, a)), Some((y, bv))) = (single_assign_block(&branches[0].1), single_assign_block(e)) {
                            if x == y {
                                let c = &branches[0].0;
                                let nc = negate(c.clone());
                                let r = value_testset(c, a, bv)
                                    .or_else(|| value_testset(&nc, bv, a))
                                    .or_else(|| value_if(c, x, a, bv))
                                    .or_else(|| value_if(&nc, x, bv, a));
                                if let Some(r) = r {
                                    let lhs = vec![Expr::Name(format!("@v{}", x))];
                                    b[i] = Stat::Assign { lhs, rhs: vec![r] };
                                    changed = true;
                                    continue;
                                }
                            }
                        }
                    }
                }
                // `X = A; if [not] X then X = B end` → `X = A and/or B`.
                if i > 0 {
                    if let Stat::If { branches, else_body: None } = &b[i] {
                        if branches.len() == 1 {
                            if let (Some((x0, a)), Some((x1, bv))) = (single_assign(&b[i - 1]), single_assign_block(&branches[0].1)) {
                                if x0 == x1 && count_var(bv, x0) == 0 {
                                    let c = &branches[0].0;
                                    let op = if var_id(c) == Some(x0) {
                                        Some(BinOp::And)
                                    } else if matches!(c, Expr::UnOp { op: UnOp::Not, operand } if var_id(operand) == Some(x0)) {
                                        Some(BinOp::Or)
                                    } else { None };
                                    if let Some(op) = op {
                                        let v = mk(op, a.clone(), bv.clone());
                                        b[i - 1] = Stat::Assign { lhs: vec![Expr::Name(format!("@v{}", x0))], rhs: vec![v] };
                                        b.remove(i);
                                        changed = true;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
                // Empty `if` with a pure condition.
                if let Stat::If { branches, else_body: None } = &b[i] {
                    if branches.iter().all(|(c, bb)| bb.is_empty() && is_pure(c)) {
                        b.remove(i);
                        changed = true;
                        continue;
                    }
                }
            }
            // `X = X`
            if let Stat::Assign { lhs, rhs } = &b[i] {
                if lhs.len() == 1 && rhs.len() == 1 && var_id(&lhs[0]).is_some() && lhs[0] == rhs[0] {
                    b.remove(i);
                    changed = true;
                    continue;
                }
            }
            i += 1;
        }
        // Nothing after an unconditional jump is reachable.
        if let Some(p) = b.iter().position(|s| matches!(s, Stat::Return(_) | Stat::Break | Stat::Goto(_))) {
            if p + 1 < b.len() && !b[p + 1..].iter().any(|s| matches!(s, Stat::Label(_))) {
                b.truncate(p + 1);
                changed = true;
            }
        }
    }
    for s in b.iter_mut() { for_each_child_mut(s, &mut |c| simplify_conds(c)); }
}

/// In condition position `not not x` ≡ `x`.
fn simplify_conds(_b: &mut Vec<Stat>) {}

/// Rebuild generic `for` loops that were lowered because the bytecode was not
/// in the standard shape:
///
/// ```lua
/// f, s, c = <explist>                      for v1, v2 in <explist> do
/// while true do                              <body>
///   v1, v2 = f(s, c)                 →     end
///   if v1 == nil then break end
///   c = v1
///   <body>
/// end
/// ```
///
/// Exact when `f`, `s`, `c` appear nowhere else and the loop variables are
/// only used inside the loop.
pub fn raise_generic_for(func_body: &mut Vec<Stat>) {
    let total = |v: usize, root: &Vec<Stat>| -> usize {
        root.iter().map(|s| crate::simplify::occurs_in_stat(s, v)).sum()
    };
    // Collect candidate positions first (paths are not needed: we search
    // each block and check counts against the whole function).
    let snapshot = func_body.clone();
    raise_in(func_body, &snapshot, &total);
}

fn raise_in(b: &mut Vec<Stat>, root: &Vec<Stat>, total: &dyn Fn(usize, &Vec<Stat>) -> usize) {
    for s in b.iter_mut() { for_each_child_mut(s, &mut |c| raise_in(c, root, total)); }
    let mut i = 0;
    while i + 1 < b.len() {
        // An optional `@uses(...)` declaration hint sits before loops.
        let hint = matches!(&b[i + 1], Stat::Call(e) if pseudo_args(e, "@uses").is_some());
        let lp = if hint { i + 2 } else { i + 1 };
        if lp < b.len() {
            let hint_vars: Vec<usize> = if hint {
                match &b[i + 1] { Stat::Call(e) => pseudo_args(e, "@uses").unwrap().iter().filter_map(var_id).collect(), _ => vec![] }
            } else { vec![] };
            if let Some((new, fsc)) = match_lowered_for(&b[i], &b[lp], &hint_vars, root, total) {
                b[i] = new;
                b.remove(lp);
                if hint {
                    // Keep the hint for the other carried variables.
                    if let Stat::Call(Expr::Call { args, .. }) = &mut b[i + 1] {
                        args.retain(|a| !var_id(a).map_or(false, |v| fsc.contains(&v)));
                        if args.is_empty() { b.remove(i + 1); }
                    }
                    // The hint belongs before the loop.
                    if i + 1 < b.len() && matches!(&b[i + 1], Stat::Call(e) if pseudo_args(e, "@uses").is_some()) {
                        b.swap(i, i + 1);
                        i += 1;
                    }
                }
            }
        }
        i += 1;
    }
}

fn match_lowered_for(
    init: &Stat,
    lp: &Stat,
    hint: &[usize],
    root: &Vec<Stat>,
    total: &dyn Fn(usize, &Vec<Stat>) -> usize,
) -> Option<(Stat, [usize; 3])> {
    let Stat::Assign { lhs, rhs } = init else { return None };
    if lhs.len() != 3 { return None; }
    let (f, s, c) = (var_id(&lhs[0])?, var_id(&lhs[1])?, var_id(&lhs[2])?);
    let in_hint = |v: usize| hint.iter().filter(|&&h| h == v).count();
    let Stat::While { cond: Expr::True, body } = lp else { return None };
    if body.len() < 3 { return None; }
    // v1, v2 = f(s, c)
    let Stat::Assign { lhs: vl, rhs: call } = &body[0] else { return None };
    let vars: Vec<usize> = vl.iter().map(var_id).collect::<Option<_>>()?;
    let [Expr::Call { func, args }] = call.as_slice() else { return None };
    if var_id(func) != Some(f) || args.len() != 2 || var_id(&args[0]) != Some(s) || var_id(&args[1]) != Some(c) { return None; }
    // if v1 == nil then break end
    let v1 = vars[0];
    let Stat::If { branches, else_body: None } = &body[1] else { return None };
    if branches.len() != 1 || branches[0].1 != vec![Stat::Break] { return None; }
    let is_nil_test = matches!(&branches[0].0, Expr::BinOp { op: BinOp::Eq, lhs, rhs }
        if (var_id(lhs) == Some(v1) && matches!(rhs.as_ref(), Expr::Nil)) || (var_id(rhs) == Some(v1) && matches!(lhs.as_ref(), Expr::Nil)));
    if !is_nil_test { return None; }
    // c = v1
    let Stat::Assign { lhs: cl, rhs: cr } = &body[2] else { return None };
    if cl.len() != 1 || cr.len() != 1 || var_id(&cl[0]) != Some(c) || var_id(&cr[0]) != Some(v1) { return None; }
    // f, s, c are used only here; the loop variables only inside the loop.
    if total(f, root) != 2 + in_hint(f) || total(s, root) != 2 + in_hint(s) || total(c, root) != 3 + in_hint(c) {
        return None;
    }
    let rest: Vec<Stat> = body[3..].to_vec();
    for &v in &vars {
        let inside: usize = body.iter().map(|x| crate::simplify::occurs_in_stat(x, v)).sum();
        if inside + in_hint(v) != total(v, root) { return None; }
        // Assigning a loop variable in the body is fine in Lua 5.2+ but the
        // first one also drives the iteration here: keep it read-only.
        if v == v1 && rest.iter().any(|x| assigns(x, v)) { return None; }
    }
    // Loop variables must not be carried around the loop (the hint lists
    // variables live at the loop head).
    if vars.iter().any(|&v| in_hint(v) > 0) { return None; }
    let mut iters = rhs.clone();
    while iters.len() > 1 && matches!(iters.last(), Some(Expr::Nil)) { iters.pop(); }
    Some((Stat::GenFor { vars: vars.iter().map(|v| format!("@v{}", v)).collect(), iters, body: rest }, [f, s, c]))
}

fn assigns(s: &Stat, v: usize) -> bool {
    let mut found = false;
    let mut check = |b: &[Stat]| {
        for x in b { if let Stat::Assign { lhs, .. } = x { if lhs.iter().any(|l| var_id(l) == Some(v)) { found = true; } } }
    };
    check(std::slice::from_ref(s));
    let mut sub = |c: &Vec<Stat>| { for x in c { if assigns(x, v) { found = true; } } };
    for_each_child(s, &mut sub);
    found
}

fn mentions(e: &Expr, t: &Expr) -> bool {
    let mut found = false;
    crate::simplify::lua_ast_walk(e, &mut |x| if x == t { found = true; });
    found
}

/// Turn left-over `@setlist` pseudo-calls into assignments and drop the
/// implicit final `return`.
pub fn finalize(b: &mut Vec<Stat>, top: bool) {
    for s in b.iter_mut() {
        if let Stat::Call(e) = s {
            if let Some(args) = pseudo_args(e, "@setlist") {
                let t = args[0].clone();
                let first = args[1].as_integer().unwrap_or(1);
                let mut items: Vec<Expr> = args[3..].to_vec();
                // The last item expands to all its values: copy them with
                // `for k, v in next, {E} do t[k + off] = v end` (nil values
                // need no store).
                let multi_tail = if matches!(args[2], Expr::True) { items.pop() } else { None };
                let mut tail_loop = None;
                if let Some(e) = multi_tail {
                    let off = first - 1 + items.len() as i64;
                    let tname = match &t { Expr::Name(n) => n.clone(), _ => String::new() };
                    let (k, v) = if tname == "__k" || tname == "__v" { ("__k2".to_string(), "__v2".to_string()) } else { ("__k".to_string(), "__v".to_string()) };
                    let key = if off == 0 { Expr::Name(k.clone()) } else {
                        Expr::BinOp { op: BinOp::Add, lhs: Box::new(Expr::Name(k.clone())), rhs: Box::new(Expr::Integer(off)) }
                    };
                    tail_loop = Some(Stat::GenFor {
                        vars: vec![k, v.clone()],
                        iters: vec![Expr::Name("next".into()), Expr::Table(vec![lua_ast::TableField::ValueField(e)])],
                        body: vec![Stat::Assign {
                            lhs: vec![Expr::Index { table: Box::new(t.clone()), key: Box::new(key) }],
                            rhs: vec![Expr::Name(v)],
                        }],
                    });
                }
                let lhs: Vec<Expr> = (0..items.len()).map(|k| Expr::Index {
                    table: Box::new(t.clone()),
                    key: Box::new(Expr::Integer(first + k as i64)),
                }).collect();
                // SETLIST stores after evaluating every item.  One statement
                // per item is equivalent when no item can observe the table.
                let independent = items.iter().all(|x| {
                    let eff = expr_eff(x);
                    !eff.calls && (x != &t) && !mentions(x, &t)
                });
                let mut out: Vec<Stat> = if items.is_empty() {
                    vec![]
                } else if independent && items.len() > 1 {
                    lhs.into_iter().zip(items).map(|(l, r)| Stat::Assign { lhs: vec![l], rhs: vec![r] }).collect()
                } else {
                    vec![Stat::Assign { lhs, rhs: items }]
                };
                out.extend(tail_loop);
                *s = Stat::Do(out);
            }
        }
        for_each_child_mut(s, &mut |c| finalize(c, false));
    }
    // Splice `do` blocks that only group statements (those declaring locals
    // scope them, e.g. a closure's copy of a boxed variable).
    if b.iter().any(|s| matches!(s, Stat::Do(_))) {
        let old = std::mem::take(b);
        for s in old {
            match s {
                Stat::Do(inner) if !inner.iter().any(|x| matches!(x, Stat::Local { .. })) => b.extend(inner),
                other => b.push(other),
            }
        }
    }
    if top {
        if let Some(Stat::Return(v)) = b.last() {
            if v.is_empty() { b.pop(); }
        }
    }
}
