/// Pass – standard library and globals.
///
///   • `local p = print` (never reassigned)   →  uses of `p` become `print`
///   • `local c = string.char`                →  uses of `c` become `string.char`
///   • `string.char(104, 105)`                →  `"hi"`
///
/// Assumes the host runs the script with the standard library, and only
/// rewrites when the script itself cannot change what these names mean: the
/// global is never declared as a local or assigned (for a library field, the
/// library is never declared, assigned or used other than as `lib.<name>`,
/// and that field is never written), nothing that can reach globals or
/// library tables (`_G`, `_ENV`, `setfenv`, `getmetatable`, `rawset`,
/// `require`, ...) appears, and no loaded code can run (see
/// [`loaders_reachable`]).

use std::collections::BTreeSet;
use lua_ast::{BinOp, Block, Expr, Stat, UnOp};
use crate::for_each_block;
use crate::util::{assigned_names, count_refs, visit_exprs, visit_stats};

/// Any mention of these can reach globals or library tables.
const REACH: &[&str] = &["_G", "_ENV", "getfenv", "setfenv", "getmetatable", "rawset", "require", "package"];
/// These run code that can do anything, but only when called.
const LOADERS: &[&str] = &["load", "loadstring", "loadfile", "dofile"];

pub fn run(block: &mut Block) {
    if escapes(block) { return; }
    let assigned = assigned_names(block);
    let string_w = lib_written_fields(block, "string", &assigned);
    let stable = |e: &Expr| match e {
        Expr::Name(g) => global_untouched(block, g, &assigned),
        Expr::Index { key, .. } if is_lib_field(e, "string", &[]) => {
            matches!((&string_w, key.as_ref()), (Some(w), Expr::Str(k)) if !w.contains(k))
        }
        _ => false,
    };
    let mut aliases = Vec::new();
    visit_stats(block, &mut |s| if let Stat::Local { names, values } = s {
        if names.len() == 1 && values.len() == 1 && !assigned.contains(&names[0]) && stable(&values[0]) {
            aliases.push(names[0].clone());
        }
    });
    if !aliases.is_empty() { substitute_aliases(block, &aliases.into_iter().collect()); }
    if string_w.as_ref().is_some_and(|w| !w.contains(b"char".as_slice())) {
        lua_ast::transform_block(block, &mut |e| {
            if let Some(s) = fold_char(e) { *e = Expr::Str(s); }
        });
    }
}

/// Replace uses of each alias after its declaration, then drop the declaration
/// (reading a global or library field has no effect).
fn substitute_aliases(block: &mut Block, aliases: &BTreeSet<String>) {
    for_each_block(block, &mut |b| {
        let mut i = 0;
        while i < b.len() {
            let found = match &b[i] {
                Stat::Local { names, values } if names.len() == 1 && aliases.contains(&names[0]) => {
                    Some((names[0].clone(), values[0].clone()))
                }
                _ => None,
            };
            let Some((n, v)) = found else { i += 1; continue };
            let mut rest = b.split_off(i + 1);
            lua_ast::transform_block(&mut rest, &mut |e| {
                if matches!(e, Expr::Name(m) if *m == n) { *e = v.clone(); }
            });
            b.pop();
            b.extend(rest);
        }
    });
}

/// Is anything present that can reach globals or library tables, or run
/// loaded code?
pub(crate) fn escapes(b: &Block) -> bool {
    let (mut esc, mut debug, mut debug_ok) = (false, 0, 0);
    visit_exprs(b, &mut |e| match e {
        Expr::Name(n) if n == "debug" => debug += 1,
        Expr::Name(n) if REACH.contains(&n.as_str()) => esc = true,
        // These cannot reach other tables or environments.
        _ if is_lib_field(e, "debug", &["getinfo", "traceback", "gethook", "sethook"]) => debug_ok += 1,
        _ => {}
    });
    esc || debug != debug_ok || count_refs(b, "debug") != debug || loaders_reachable(b)
}

/// Can a loader (`load`, ...) be called, or escape as a value?
///
/// Names holding a loader are tracked: the loaders themselves, names a loader
/// is copied to, and names bound to a function that calls one.  Calling such
/// a name from anywhere else — top-level code or a function that is not bound
/// to a name — or using it as any value other than a condition (`if not
/// loadstring then ...`) counts.  Defining a fallback that is never called,
/// as compatibility headers do, does not.
fn loaders_reachable(b: &Block) -> bool {
    let mut held: BTreeSet<String> = LOADERS.iter().map(|s| s.to_string()).collect();
    loop {
        let mut w = LoaderWalk { held: &held, new: BTreeSet::new(), hit: false };
        w.block(b, None);
        if w.hit { return true; }
        let new: Vec<String> = w.new.into_iter().filter(|n| !held.contains(n)).collect();
        if new.is_empty() { return false; }
        held.extend(new);
    }
}

struct LoaderWalk<'a> {
    held: &'a BTreeSet<String>,
    new: BTreeSet<String>,
    hit: bool,
}

impl LoaderWalk<'_> {
    fn holds(&self, e: &Expr) -> bool {
        matches!(e, Expr::Name(n) if self.held.contains(n))
    }

    /// A loader is called inside the function bound to `owner` (if any).
    fn called(&mut self, owner: Option<&str>) {
        match owner {
            Some(o) => { self.new.insert(o.to_string()); }
            None => self.hit = true,
        }
    }

    fn block(&mut self, b: &Block, owner: Option<&str>) {
        for s in b { self.stat(s, owner); }
    }

    fn stat(&mut self, s: &Stat, owner: Option<&str>) {
        let pairs = |lhs: Vec<Option<&str>>, rhs: &[Expr], w: &mut Self| {
            for (i, v) in rhs.iter().enumerate() {
                let target = if lhs.len() == rhs.len() { lhs[i] } else { None };
                match (target, v) {
                    (Some(t), _) if w.holds(v) => { w.new.insert(t.to_string()); }
                    (Some(t), Expr::Function(fb)) => w.block(&fb.body, Some(t)),
                    _ => w.expr(v, owner, false),
                }
            }
        };
        match s {
            Stat::Local { names, values } => pairs(names.iter().map(|n| Some(n.as_str())).collect(), values, self),
            Stat::Assign { lhs, rhs } => {
                for l in lhs {
                    if let Expr::Index { table, key } = l { self.expr(table, owner, false); self.expr(key, owner, false); }
                }
                let targets = lhs.iter().map(|l| if let Expr::Name(n) = l { Some(n.as_str()) } else { None }).collect();
                pairs(targets, rhs, self);
            }
            Stat::While { cond, body } | Stat::Repeat { body, cond } => { self.expr(cond, owner, true); self.block(body, owner); }
            Stat::If { branches, else_body } => {
                for (c, bl) in branches { self.expr(c, owner, true); self.block(bl, owner); }
                if let Some(bl) = else_body { self.block(bl, owner); }
            }
            Stat::NumFor { from, to, step, body, .. } => {
                for e in [Some(from), Some(to), step.as_ref()].into_iter().flatten() { self.expr(e, owner, false); }
                self.block(body, owner);
            }
            Stat::GenFor { iters, body, .. } => {
                for e in iters { self.expr(e, owner, false); }
                self.block(body, owner);
            }
            Stat::Do(bl) => self.block(bl, owner),
            Stat::Return(v) => { for e in v { self.expr(e, owner, false); } }
            Stat::Call(e) => self.expr(e, owner, false),
            Stat::Break | Stat::Goto(_) | Stat::Label(_) => {}
        }
    }

    /// `cond`: inside a condition, where testing a loader's presence is harmless.
    fn expr(&mut self, e: &Expr, owner: Option<&str>, cond: bool) {
        match e {
            Expr::Name(_) if self.holds(e) => if !cond { self.hit = true },
            Expr::Call { func, args } => {
                if self.holds(func) { self.called(owner); } else { self.expr(func, owner, false); }
                for a in args { self.expr(a, owner, false); }
            }
            Expr::Method { obj, args, .. } => {
                self.expr(obj, owner, false);
                for a in args { self.expr(a, owner, false); }
            }
            Expr::Function(fb) => self.block(&fb.body, None),
            Expr::BinOp { op, lhs, rhs } => {
                let keep = cond && matches!(op, BinOp::And | BinOp::Or | BinOp::Eq | BinOp::Ne);
                self.expr(lhs, owner, keep);
                self.expr(rhs, owner, keep);
            }
            Expr::UnOp { op, operand } => self.expr(operand, owner, cond && *op == UnOp::Not),
            Expr::Paren(x) => self.expr(x, owner, cond),
            Expr::Index { table, key } => { self.expr(table, owner, false); self.expr(key, owner, false); }
            Expr::Table(fields) => {
                for f in fields {
                    match f {
                        lua_ast::TableField::IndexField(k, v) => { self.expr(k, owner, false); self.expr(v, owner, false); }
                        lua_ast::TableField::NameField(_, v) | lua_ast::TableField::ValueField(v) => self.expr(v, owner, false),
                    }
                }
            }
            _ => {}
        }
    }
}

/// The global `g` is never declared (so never shadowed) nor assigned.
fn global_untouched(b: &Block, g: &str, assigned: &BTreeSet<String>) -> bool {
    let mut names = 0;
    visit_exprs(b, &mut |e| if matches!(e, Expr::Name(n) if n == g) { names += 1; });
    !assigned.contains(g) && count_refs(b, g) == names
}

/// `lib.<name>`, for any name when `names` is empty.
fn is_lib_field(e: &Expr, lib: &str, names: &[&str]) -> bool {
    matches!(e, Expr::Index { table, key } if matches!(table.as_ref(), Expr::Name(n) if n == lib)
        && matches!(key.as_ref(), Expr::Str(k) if names.is_empty() || names.iter().any(|n| n.as_bytes() == k.as_slice())))
}

/// The fields of library table `lib` that the script writes, or `None` when
/// the table itself may change: it is declared, assigned, or used other than
/// as `lib.<name>` (e.g. passed somewhere or indexed with a computed key).
pub(crate) fn lib_written_fields(b: &Block, lib: &str, assigned: &BTreeSet<String>) -> Option<BTreeSet<Vec<u8>>> {
    let (mut names, mut fields) = (0, 0);
    visit_exprs(b, &mut |e| match e {
        Expr::Name(n) if n == lib => names += 1,
        _ if is_lib_field(e, lib, &[]) => fields += 1,
        _ => {}
    });
    let mut written = BTreeSet::new();
    visit_stats(b, &mut |s| if let Stat::Assign { lhs, .. } = s {
        for l in lhs {
            if let Expr::Index { key, .. } = l {
                if is_lib_field(l, lib, &[]) { if let Expr::Str(k) = key.as_ref() { written.insert(k.clone()); } }
            }
        }
    });
    (names == fields && global_untouched(b, lib, assigned)).then_some(written)
}

/// `string.char(<integers 0..=255>)`.
fn fold_char(e: &Expr) -> Option<Vec<u8>> {
    let Expr::Call { func, args } = e else { return None };
    if !is_lib_field(func, "string", &["char"]) { return None; }
    args.iter().map(|a| {
        let n = match a {
            Expr::Integer(n) => *n,
            Expr::Float(f) if f.fract() == 0.0 => *f as i64,
            _ => return None,
        };
        u8::try_from(n).ok()
    }).collect()
}
