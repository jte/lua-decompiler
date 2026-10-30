/// Pass – give every local a chunk-wide unique name (alpha renaming).
///
/// The decompiler names variables per function, so `_v0` is a different
/// variable in each function.  After this pass a name means exactly one
/// variable, which is what the name-based checks in the other passes assume.
/// Follows Lua scoping: a `local`'s values are evaluated before its names
/// come into scope; loop variables and parameters scope over the body;
/// `until` sees the `repeat` body's locals.

use std::collections::{BTreeSet, HashMap};
use lua_ast::{Block, Expr, Stat, TableField};

use crate::util::{visit_exprs, visit_stats};

pub fn run(block: &mut Block) {
    let mut taken: BTreeSet<String> = BTreeSet::new();
    visit_exprs(block, &mut |e| if let Expr::Name(n) = e { taken.insert(n.clone()); });
    visit_stats(block, &mut |s| match s {
        Stat::Local { names, .. } => taken.extend(names.iter().cloned()),
        Stat::NumFor { var, .. } => { taken.insert(var.clone()); }
        Stat::GenFor { vars, .. } => taken.extend(vars.iter().cloned()),
        _ => {}
    });
    let mut r = Renamer { taken, seen: HashMap::new(), env: Vec::new() };
    r.block(block);
}

struct Renamer {
    /// Every name in the chunk (to avoid when making new ones).
    taken: BTreeSet<String>,
    /// Names already declared once.
    seen: HashMap<String, usize>,
    /// Scope stack: (source name, unique name).
    env: Vec<(String, String)>,
}

impl Renamer {
    fn declare(&mut self, name: &str) -> String {
        let count = self.seen.entry(name.to_string()).or_insert(0);
        *count += 1;
        let new = if *count == 1 {
            name.to_string()
        } else {
            let mut k = *count;
            loop {
                let cand = format!("{}_{}", name, k);
                if !self.taken.contains(&cand) { break cand; }
                k += 1;
            }
        };
        self.taken.insert(new.clone());
        self.env.push((name.to_string(), new.clone()));
        new
    }

    fn lookup(&self, name: &str) -> Option<&String> {
        self.env.iter().rev().find(|(n, _)| n == name).map(|(_, u)| u)
    }

    fn block(&mut self, b: &mut Block) {
        let mark = self.env.len();
        for s in b.iter_mut() { self.stat(s); }
        self.env.truncate(mark);
    }

    fn stat(&mut self, s: &mut Stat) {
        match s {
            Stat::Local { names, values } => {
                for e in values.iter_mut() { self.expr(e); }
                for n in names.iter_mut() { *n = self.declare(n); }
            }
            Stat::Assign { lhs, rhs } => { for e in lhs.iter_mut().chain(rhs.iter_mut()) { self.expr(e); } }
            Stat::Call(e) => self.expr(e),
            Stat::Return(v) => { for e in v.iter_mut() { self.expr(e); } }
            Stat::Do(b) => self.block(b),
            Stat::While { cond, body } => { self.expr(cond); self.block(body); }
            Stat::Repeat { body, cond } => {
                let mark = self.env.len();
                for s in body.iter_mut() { self.stat(s); }
                self.expr(cond);
                self.env.truncate(mark);
            }
            Stat::If { branches, else_body } => {
                for (c, b) in branches.iter_mut() { self.expr(c); self.block(b); }
                if let Some(b) = else_body { self.block(b); }
            }
            Stat::NumFor { var, from, to, step, body } => {
                self.expr(from);
                self.expr(to);
                if let Some(x) = step { self.expr(x); }
                let mark = self.env.len();
                *var = self.declare(var);
                self.block(body);
                self.env.truncate(mark);
            }
            Stat::GenFor { vars, iters, body } => {
                for e in iters.iter_mut() { self.expr(e); }
                let mark = self.env.len();
                for v in vars.iter_mut() { *v = self.declare(v); }
                self.block(body);
                self.env.truncate(mark);
            }
            Stat::Break | Stat::Goto(_) | Stat::Label(_) => {}
        }
    }

    fn expr(&mut self, e: &mut Expr) {
        match e {
            Expr::Name(n) => { if let Some(u) = self.lookup(n) { *n = u.clone(); } }
            Expr::Index { table, key } => { self.expr(table); self.expr(key); }
            Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
                self.expr(func);
                for a in args.iter_mut() { self.expr(a); }
            }
            Expr::BinOp { lhs, rhs, .. } => { self.expr(lhs); self.expr(rhs); }
            Expr::UnOp { operand, .. } | Expr::Paren(operand) => self.expr(operand),
            Expr::Table(fields) => {
                for f in fields.iter_mut() {
                    match f {
                        TableField::IndexField(k, v) => { self.expr(k); self.expr(v); }
                        TableField::NameField(_, v) | TableField::ValueField(v) => self.expr(v),
                    }
                }
            }
            Expr::Function(fb) => {
                let mark = self.env.len();
                for p in fb.params.iter_mut() { *p = self.declare(p); }
                if let Some(v) = fb.vararg_name.as_mut() { *v = self.declare(v); }
                self.block(&mut fb.body);
                self.env.truncate(mark);
            }
            _ => {}
        }
    }
}
