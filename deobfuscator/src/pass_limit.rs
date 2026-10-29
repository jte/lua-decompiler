/// Pass – keep every function under Lua's 200-active-locals limit.
///
/// Runs last, on uniquely named variables (see `pass_unique`).  Where a
/// block declares too many locals, a new local reuses the name of an earlier
/// one that is no longer used and not captured by a closure (what the VM's
/// register allocator did).  If that is not enough, uncaptured locals move
/// into slots of one table.

use std::collections::{BTreeMap, BTreeSet};
use lua_ast::{Block, Expr, FuncBody, Stat};

use crate::util::{visit_exprs, visit_stats};

const REUSE_ABOVE: usize = 100;
const SPILL_ABOVE: usize = 110;

pub fn run(block: &mut Block) {
    let mut taken: BTreeSet<String> = BTreeSet::new();
    visit_exprs(block, &mut |e| if let Expr::Name(n) = e { taken.insert(n.clone()); });
    visit_stats(block, &mut |s| if let Stat::Local { names, .. } = s { taken.extend(names.iter().cloned()); });
    // Captured: referenced from a function other than the declaring one.
    let mut decl_fn: BTreeMap<String, usize> = BTreeMap::new();
    let mut refs: Vec<(String, usize)> = Vec::new();
    let mut next_fn = 1;
    scan_fn(block, 0, &mut next_fn, &mut decl_fn, &mut refs);
    let captured: BTreeSet<String> = refs.into_iter()
        .filter(|(n, f)| decl_fn.get(n).map_or(false, |d| d != f))
        .map(|(n, _)| n)
        .collect();
    let mut cx = Cx { taken, captured, spill_n: 0 };
    cx.function(block, 0);
}

struct Cx {
    taken: BTreeSet<String>,
    captured: BTreeSet<String>,
    spill_n: usize,
}

fn declared(b: &Block) -> usize {
    b.iter().map(|s| match s { Stat::Local { names, .. } => names.len(), _ => 0 }).sum()
}

fn for_each_child(s: &mut Stat, f: &mut impl FnMut(&mut Block)) {
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

impl Cx {
    /// One function body (`params` locals already active).
    fn function(&mut self, body: &mut Block, params: usize) {
        self.coalesce(body, params);
        if self.max_active(body, params) > SPILL_ABOVE { self.spill(body, params); }
        // Nested functions are separate.
        for_each_top_fn(body, &mut |f| {
            let n = f.params.len();
            self.function(&mut f.body, n);
        });
    }

    fn max_active(&self, b: &Block, outer: usize) -> usize {
        let here = outer + declared(b);
        let mut m = here;
        for s in b {
            let mut sub = |c: &Block| { m = m.max(self.max_active(c, here)); };
            match s {
                Stat::Do(c) | Stat::While { body: c, .. } | Stat::Repeat { body: c, .. }
                | Stat::NumFor { body: c, .. } | Stat::GenFor { body: c, .. } => sub(c),
                Stat::If { branches, else_body } => {
                    for (_, c) in branches { sub(c); }
                    if let Some(c) = else_body { sub(c); }
                }
                _ => {}
            }
        }
        m
    }

    fn coalesce(&mut self, b: &mut Block, outer: usize) {
        if outer + declared(b) > REUSE_ABOVE { self.coalesce_block(b); }
        let here = outer + declared(b);
        for s in b.iter_mut() { for_each_child(s, &mut |c| self.coalesce(c, here)); }
    }

    fn coalesce_block(&mut self, b: &mut Block) {
        // Last statement (at this level) mentioning each name.
        let mut last: BTreeMap<String, usize> = BTreeMap::new();
        for (i, s) in b.iter().enumerate() {
            let one = std::slice::from_ref(s);
            visit_exprs(one, &mut |e| if let Expr::Name(n) = e { last.insert(n.clone(), i); });
            visit_stats(one, &mut |x| if let Stat::Local { names, .. } = x {
                for n in names { last.insert(n.clone(), i); }
            });
        }
        let mut free_names: Vec<String> = Vec::new(); // declared here, maybe dead
        let mut alias: BTreeMap<String, String> = BTreeMap::new();
        for i in 0..b.len() {
            if !alias.is_empty() {
                let mut one = vec![std::mem::replace(&mut b[i], Stat::Break)];
                rename(&mut one, &alias);
                b[i] = one.pop().unwrap();
            }
            let Stat::Local { names, values } = &b[i] else { continue };
            if names.len() != 1 {
                free_names.extend(names.iter().cloned());
                continue;
            }
            let new = names[0].clone();
            let pick = free_names.iter().position(|old| {
                last.get(old).map_or(true, |&l| l < i) && !self.captured.contains(old) && !self.captured.contains(&new)
            });
            match pick {
                Some(p) => {
                    let old = free_names.remove(p);
                    let rhs = if values.is_empty() { vec![Expr::Nil] } else { values.clone() };
                    b[i] = Stat::Assign { lhs: vec![Expr::Name(old.clone())], rhs };
                    let l = last.get(&new).copied().unwrap_or(i);
                    last.insert(old.clone(), l);
                    alias.insert(new, old.clone());
                    free_names.push(old);
                }
                None => free_names.push(new),
            }
        }
    }

    fn spill(&mut self, body: &mut Block, params: usize) {
        let mut chosen: Vec<String> = Vec::new();
        self.pick(body, params + 1, &mut chosen);
        if chosen.is_empty() { return; }
        let table = loop {
            let n = if self.spill_n == 0 { "_spill".to_string() } else { format!("_spill{}", self.spill_n) };
            self.spill_n += 1;
            if !self.taken.contains(&n) { self.taken.insert(n.clone()); break n; }
        };
        let slots: BTreeMap<String, i64> = chosen.iter().enumerate().map(|(i, n)| (n.clone(), i as i64 + 1)).collect();
        let slot = |n: &str| Expr::Index { table: Box::new(Expr::Name(table.clone())), key: Box::new(Expr::Integer(slots[n])) };
        lua_ast::transform_block(body, &mut |e| {
            if let Expr::Name(n) = e { if slots.contains_key(n) { *e = slot(n); } }
        });
        rewrite_decls(body, &slots, &slot, true);
        body.insert(0, Stat::Local { names: vec![table], values: vec![Expr::Table(vec![])] });
    }

    fn pick(&self, b: &Block, outer: usize, chosen: &mut Vec<String>) {
        let mine: Vec<String> = b.iter().flat_map(|s| match s {
            Stat::Local { names, .. } => names.clone(),
            _ => vec![],
        }).collect();
        let mut kept = mine.len();
        if outer + kept > SPILL_ABOVE {
            for n in mine.iter().rev() {
                if outer + kept <= SPILL_ABOVE { break; }
                if self.captured.contains(n) { continue; }
                chosen.push(n.clone());
                kept -= 1;
            }
        }
        let here = outer + kept;
        for s in b {
            match s {
                Stat::Do(c) | Stat::While { body: c, .. } | Stat::Repeat { body: c, .. }
                | Stat::NumFor { body: c, .. } | Stat::GenFor { body: c, .. } => self.pick(c, here, chosen),
                Stat::If { branches, else_body } => {
                    for (_, c) in branches { self.pick(c, here, chosen); }
                    if let Some(c) = else_body { self.pick(c, here, chosen); }
                }
                _ => {}
            }
        }
    }
}

/// Declarations of spilled locals become slot assignments; one without a
/// value resets its slot (except at the top of the function body).
fn rewrite_decls(b: &mut Block, slots: &BTreeMap<String, i64>, slot: &dyn Fn(&str) -> Expr, root: bool) {
    let old = std::mem::take(b);
    let mut at_top = root;
    for st in old {
        match st {
            Stat::Local { names, values } if names.iter().any(|n| slots.contains_key(n)) => {
                let keep: Vec<String> = names.iter().filter(|n| !slots.contains_key(*n)).cloned().collect();
                if !keep.is_empty() { b.push(Stat::Local { names: keep, values: vec![] }); }
                if values.is_empty() {
                    if !at_top {
                        let targets: Vec<Expr> = names.iter().filter(|n| slots.contains_key(*n)).map(|n| slot(n)).collect();
                        for chunk in targets.chunks(50) {
                            b.push(Stat::Assign { lhs: chunk.to_vec(), rhs: vec![Expr::Nil] });
                        }
                    }
                } else {
                    let lhs = names.iter().map(|n| if slots.contains_key(n) { slot(n) } else { Expr::Name(n.clone()) }).collect();
                    b.push(Stat::Assign { lhs, rhs: values });
                }
            }
            mut other => {
                at_top = at_top && matches!(other, Stat::Local { .. });
                for_each_child(&mut other, &mut |c| rewrite_decls(c, slots, slot, false));
                b.push(other);
            }
        }
    }
}

fn rename(b: &mut Block, map: &BTreeMap<String, String>) {
    lua_ast::transform_block(b, &mut |e| {
        if let Expr::Name(n) = e { if let Some(x) = map.get(n) { *n = x.clone(); } }
    });
    fn decls(b: &mut Block, map: &BTreeMap<String, String>) {
        for s in b.iter_mut() {
            if let Stat::Local { names, .. } = s {
                for n in names.iter_mut() { if let Some(x) = map.get(n) { *n = x.clone(); } }
            }
            for_each_child(s, &mut |c| decls(c, map));
        }
    }
    decls(b, map);
}

/// Record, per name, the function that declares it, and every reference with
/// the function it appears in (function ids: 0 = main chunk).
fn scan_fn(b: &Block, me: usize, next: &mut usize, decl: &mut BTreeMap<String, usize>, refs: &mut Vec<(String, usize)>) {
    fn expr(e: &Expr, me: usize, next: &mut usize, decl: &mut BTreeMap<String, usize>, refs: &mut Vec<(String, usize)>) {
        match e {
            Expr::Name(n) => refs.push((n.clone(), me)),
            Expr::Function(fb) => {
                let id = *next;
                *next += 1;
                for p in &fb.params { decl.insert(p.clone(), id); }
                scan_fn(&fb.body, id, next, decl, refs);
            }
            Expr::Index { table, key } => { expr(table, me, next, decl, refs); expr(key, me, next, decl, refs); }
            Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
                expr(func, me, next, decl, refs);
                for a in args { expr(a, me, next, decl, refs); }
            }
            Expr::BinOp { lhs, rhs, .. } => { expr(lhs, me, next, decl, refs); expr(rhs, me, next, decl, refs); }
            Expr::UnOp { operand, .. } | Expr::Paren(operand) => expr(operand, me, next, decl, refs),
            Expr::Table(fields) => {
                for f in fields {
                    match f {
                        lua_ast::TableField::IndexField(k, v) => { expr(k, me, next, decl, refs); expr(v, me, next, decl, refs); }
                        lua_ast::TableField::NameField(_, v) | lua_ast::TableField::ValueField(v) => expr(v, me, next, decl, refs),
                    }
                }
            }
            _ => {}
        }
    }
    for s in b {
        match s {
            Stat::Local { names, values } => {
                for v in values { expr(v, me, next, decl, refs); }
                for n in names { decl.insert(n.clone(), me); }
            }
            Stat::Assign { lhs, rhs } => { for e in lhs.iter().chain(rhs) { expr(e, me, next, decl, refs); } }
            Stat::Call(e) => expr(e, me, next, decl, refs),
            Stat::Return(v) => { for e in v { expr(e, me, next, decl, refs); } }
            Stat::Do(c) => scan_fn(c, me, next, decl, refs),
            Stat::While { cond, body } | Stat::Repeat { body, cond } => {
                expr(cond, me, next, decl, refs);
                scan_fn(body, me, next, decl, refs);
            }
            Stat::If { branches, else_body } => {
                for (c, bb) in branches { expr(c, me, next, decl, refs); scan_fn(bb, me, next, decl, refs); }
                if let Some(e) = else_body { scan_fn(e, me, next, decl, refs); }
            }
            Stat::NumFor { var, from, to, step, body } => {
                expr(from, me, next, decl, refs);
                expr(to, me, next, decl, refs);
                if let Some(x) = step { expr(x, me, next, decl, refs); }
                decl.insert(var.clone(), me);
                scan_fn(body, me, next, decl, refs);
            }
            Stat::GenFor { vars, iters, body } => {
                for e in iters { expr(e, me, next, decl, refs); }
                for v in vars { decl.insert(v.clone(), me); }
                scan_fn(body, me, next, decl, refs);
            }
            _ => {}
        }
    }
}

/// Call `f` on each function literal in `b` that is not inside another one.
fn for_each_top_fn(b: &mut Block, f: &mut dyn FnMut(&mut FuncBody)) {
    fn expr(e: &mut Expr, f: &mut dyn FnMut(&mut FuncBody)) {
        match e {
            Expr::Function(fb) => f(fb),
            Expr::Index { table, key } => { expr(table, f); expr(key, f); }
            Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
                expr(func, f);
                for a in args.iter_mut() { expr(a, f); }
            }
            Expr::BinOp { lhs, rhs, .. } => { expr(lhs, f); expr(rhs, f); }
            Expr::UnOp { operand, .. } | Expr::Paren(operand) => expr(operand, f),
            Expr::Table(fields) => {
                for fl in fields.iter_mut() {
                    match fl {
                        lua_ast::TableField::IndexField(k, v) => { expr(k, f); expr(v, f); }
                        lua_ast::TableField::NameField(_, v) | lua_ast::TableField::ValueField(v) => expr(v, f),
                    }
                }
            }
            _ => {}
        }
    }
    for s in b.iter_mut() {
        let mut look = |e: &mut Expr| expr(e, f);
        match s {
            Stat::Assign { lhs, rhs } => { for e in lhs.iter_mut().chain(rhs.iter_mut()) { look(e); } }
            Stat::Local { values, .. } => { for e in values.iter_mut() { look(e); } }
            Stat::Return(v) => { for e in v.iter_mut() { look(e); } }
            Stat::Call(e) => look(e),
            Stat::While { cond, .. } | Stat::Repeat { cond, .. } => look(cond),
            Stat::If { branches, .. } => { for (c, _) in branches.iter_mut() { look(c); } }
            Stat::NumFor { from, to, step, .. } => { look(from); look(to); if let Some(x) = step { look(x); } }
            Stat::GenFor { iters, .. } => { for e in iters.iter_mut() { look(e); } }
            _ => {}
        }
        for_each_child(s, &mut |c| for_each_top_fn(c, f));
    }
}
