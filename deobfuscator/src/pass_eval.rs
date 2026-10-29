/// Pass – evaluate calls of small pure functions on constant arguments.
///
///   local function dec(a, k) ... end   ...   dec({7, 1}, {104, 105})   →   "hi"
///
/// The callee is a local function declared once and never reassigned (or a
/// function literal called on the spot), called where that declaration is in
/// scope.  Arguments must be constants: literals, and table constructors and
/// library calls built from them, so every table the call sees is its own.
/// A small interpreter with a step limit runs the body; anything it does not
/// model exactly — upvalues, globals other than the library functions below,
/// closures, varargs, `pairs` order, number-to-string of floats, string
/// ordering — aborts it and the call is left alone.  The call is replaced only
/// when it returns exactly one string, boolean, nil or number.
///
/// Library functions are used only when the script cannot change them (see
/// [`crate::pass_stdlib`]).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use lua_ast::{BinOp, Block, Expr, FuncBody, Stat, TableField, UnOp};

use crate::for_each_block;
use crate::pass_stdlib::{escapes, lib_untouched};
use crate::util::{assigned_names, visit_stats};

const LIBS: &[(&str, &[&str])] = &[
    ("string", &["char", "byte", "sub", "len", "rep", "reverse", "upper", "lower"]),
    ("table", &["concat", "insert"]),
    ("math", &["floor", "abs", "max", "min"]),
];
const STEP_LIMIT: u32 = 1_000_000;
const MAX_STR: usize = 1 << 20;
/// Integers beyond this are not exact in Lua 5.1/5.2 numbers.
const MAX_INT: i64 = 1 << 53;

pub fn run(block: &mut Block) {
    if escapes(block) { return; }
    let assigned = assigned_names(block);
    let libs: Vec<&'static str> = LIBS.iter().map(|(l, _)| *l).filter(|l| lib_untouched(block, l, &assigned)).collect();

    let mut funcs = BTreeMap::new();
    visit_stats(block, &mut |s| if let Stat::Local { names, values } = s {
        if names.len() == 1 && values.len() == 1 && !assigned.contains(&names[0]) {
            if let Expr::Function(fb) = &values[0] {
                if !fb.has_vararg { funcs.insert(names[0].clone(), Rc::new((**fb).clone())); }
            }
        }
    });

    // Calls in the scope of each declaration.
    for_each_block(block, &mut |b| {
        for i in 0..b.len() {
            let f = match &b[i] {
                Stat::Local { names, .. } if names.len() == 1 => funcs.get(&names[0]).map(|f| (names[0].clone(), f.clone())),
                _ => None,
            };
            let Some((name, fb)) = f else { continue };
            let mut rest = b.split_off(i + 1);
            lua_ast::transform_block(&mut rest, &mut |e| {
                if let Expr::Call { func, args } = e {
                    if matches!(func.as_ref(), Expr::Name(n) if *n == name) {
                        if let Some(v) = call(&fb, args, &libs) { *e = v; }
                    }
                }
            });
            b.extend(rest);
        }
    });
    // Function literals called on the spot.
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Call { func, args } = e {
            if let Expr::Function(fb) = func.as_ref() {
                if !fb.has_vararg {
                    if let Some(v) = call(&Rc::new((**fb).clone()), args, &libs) { *e = v; }
                }
            }
        }
    });
}

fn call(fb: &Rc<FuncBody>, args: &[Expr], libs: &[&'static str]) -> Option<Expr> {
    let mut ev = Ev { steps: 0, scopes: vec![], libs };
    ev.scopes.push(HashMap::new());
    let vals = ev.eval_list(args).ok()?;
    let mut frame = HashMap::new();
    for (i, p) in fb.params.iter().enumerate() {
        frame.insert(p.clone(), vals.get(i).cloned().unwrap_or(V::Nil));
    }
    ev.scopes = vec![frame];
    match ev.exec_block(&fb.body).ok()? {
        Flow::Return(r) if r.len() == 1 => match &r[0] {
            V::Nil => Some(Expr::Nil),
            V::Bool(b) => Some(if *b { Expr::True } else { Expr::False }),
            V::Int(n) => Some(Expr::Integer(*n)),
            V::Num(f) if f.is_finite() => Some(Expr::Float(*f)),
            V::Str(s) => Some(Expr::Str(s.to_vec())),
            _ => None,
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Interpreter
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum V {
    Nil,
    Bool(bool),
    Int(i64),
    Num(f64),
    Str(Rc<[u8]>),
    Tab(Rc<RefCell<HashMap<Key, V>>>),
    Lib(&'static str, &'static str),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Key { Int(i64), Str(Rc<[u8]>), Bool(bool) }

enum Flow { Normal, Break, Return(Vec<V>) }

/// Anything not modelled exactly.
type R<T> = Result<T, ()>;

struct Ev<'a> {
    steps: u32,
    scopes: Vec<HashMap<String, V>>,
    libs: &'a [&'static str],
}

fn truthy(v: &V) -> bool { !matches!(v, V::Nil | V::Bool(false)) }

fn int_ok(n: i64) -> R<V> { if n.abs() <= MAX_INT { Ok(V::Int(n)) } else { Err(()) } }

fn to_int(v: &V) -> R<i64> {
    match v {
        V::Int(n) => Ok(*n),
        V::Num(f) if f.fract() == 0.0 && f.abs() <= MAX_INT as f64 => Ok(*f as i64),
        _ => Err(()),
    }
}

fn to_num(v: &V) -> R<f64> {
    match v { V::Int(n) => Ok(*n as f64), V::Num(f) => Ok(*f), _ => Err(()) }
}

fn to_str(v: &V) -> R<Rc<[u8]>> {
    match v { V::Str(s) => Ok(s.clone()), V::Int(n) => Ok(n.to_string().as_bytes().into()), _ => Err(()) }
}

fn key(v: &V) -> R<Key> {
    match v {
        V::Int(n) => Ok(Key::Int(*n)),
        V::Num(_) => to_int(v).map(Key::Int),
        V::Str(s) => Ok(Key::Str(s.clone())),
        V::Bool(b) => Ok(Key::Bool(*b)),
        _ => Err(()),
    }
}

fn str_v(s: Vec<u8>) -> R<V> { if s.len() <= MAX_STR { Ok(V::Str(s.into())) } else { Err(()) } }

/// `#t` when the table is a proper sequence.
fn border(t: &HashMap<Key, V>) -> R<i64> {
    let mut n = 0;
    while t.contains_key(&Key::Int(n + 1)) { n += 1; }
    if t.keys().any(|k| matches!(k, Key::Int(i) if *i > n)) { return Err(()); }
    Ok(n)
}

/// Lua's string index adjustment (negative counts from the end).
fn pos(i: i64, len: usize) -> i64 { if i < 0 { len as i64 + i + 1 } else { i } }

impl<'a> Ev<'a> {
    fn tick(&mut self) -> R<()> {
        self.steps += 1;
        if self.steps > STEP_LIMIT { Err(()) } else { Ok(()) }
    }

    fn lookup(&self, n: &str) -> R<V> {
        self.scopes.iter().rev().find_map(|s| s.get(n)).cloned().ok_or(())
    }

    fn exec_block(&mut self, b: &Block) -> R<Flow> {
        self.scopes.push(HashMap::new());
        let r = self.exec_stats(b);
        self.scopes.pop();
        r
    }

    fn exec_stats(&mut self, b: &Block) -> R<Flow> {
        for s in b {
            match self.exec(s)? {
                Flow::Normal => {}
                f => return Ok(f),
            }
        }
        Ok(Flow::Normal)
    }

    fn exec(&mut self, s: &Stat) -> R<Flow> {
        self.tick()?;
        match s {
            Stat::Local { names, values } => {
                let vals = self.eval_list(values)?;
                let top = self.scopes.last_mut().unwrap();
                for (i, n) in names.iter().enumerate() {
                    top.insert(n.clone(), vals.get(i).cloned().unwrap_or(V::Nil));
                }
            }
            Stat::Assign { lhs, rhs } => {
                let vals = self.eval_list(rhs)?;
                for (i, l) in lhs.iter().enumerate() {
                    let v = vals.get(i).cloned().unwrap_or(V::Nil);
                    match l {
                        Expr::Name(n) => {
                            let scope = self.scopes.iter_mut().rev().find(|s| s.contains_key(n)).ok_or(())?;
                            scope.insert(n.clone(), v);
                        }
                        Expr::Index { table, key: k } => {
                            let V::Tab(t) = self.eval(table)? else { return Err(()) };
                            let k = key(&self.eval(k)?)?;
                            if matches!(v, V::Nil) { t.borrow_mut().remove(&k); } else { t.borrow_mut().insert(k, v); }
                        }
                        _ => return Err(()),
                    }
                }
            }
            Stat::Call(e) => { self.eval_multi(e)?; }
            Stat::Do(b) => return self.exec_block(b),
            Stat::While { cond, body } => {
                while truthy(&self.eval(cond)?) {
                    match self.exec_block(body)? {
                        Flow::Break => break,
                        Flow::Return(r) => return Ok(Flow::Return(r)),
                        Flow::Normal => self.tick()?,
                    }
                }
            }
            Stat::Repeat { body, cond } => loop {
                // The condition sees the body's locals.
                self.scopes.push(HashMap::new());
                let f = self.exec_stats(body);
                let c = match f {
                    Ok(Flow::Normal) => self.eval(cond),
                    _ => Ok(V::Nil),
                };
                self.scopes.pop();
                match f? {
                    Flow::Break => break,
                    Flow::Return(r) => return Ok(Flow::Return(r)),
                    Flow::Normal => if truthy(&c?) { break },
                }
            },
            Stat::If { branches, else_body } => {
                for (c, b) in branches {
                    if truthy(&self.eval(c)?) { return self.exec_block(b); }
                }
                if let Some(b) = else_body { return self.exec_block(b); }
            }
            Stat::NumFor { var, from, to, step, body } => {
                let (a, b) = (self.eval(from)?, self.eval(to)?);
                let st = match step { Some(s) => self.eval(s)?, None => V::Int(1) };
                // Integer loops only (float loops count differently across versions).
                let (mut i, b, st) = (to_int(&a)?, to_int(&b)?, to_int(&st)?);
                if st == 0 || !matches!(a, V::Int(_)) { return Err(()); }
                while if st > 0 { i <= b } else { i >= b } {
                    self.scopes.push(HashMap::from([(var.clone(), V::Int(i))]));
                    let f = self.exec_block(body);
                    self.scopes.pop();
                    match f? {
                        Flow::Break => break,
                        Flow::Return(r) => return Ok(Flow::Return(r)),
                        Flow::Normal => self.tick()?,
                    }
                    i = i.checked_add(st).ok_or(())?;
                }
            }
            Stat::Return(vals) => return Ok(Flow::Return(self.eval_list(vals)?)),
            Stat::Break => return Ok(Flow::Break),
            Stat::GenFor { .. } | Stat::Goto(_) | Stat::Label(_) => return Err(()),
        }
        Ok(Flow::Normal)
    }

    /// Values of an expression list (the last one may yield several).
    fn eval_list(&mut self, es: &[Expr]) -> R<Vec<V>> {
        let mut out = Vec::new();
        for (i, e) in es.iter().enumerate() {
            if i + 1 == es.len() { out.extend(self.eval_multi(e)?); } else { out.push(self.eval(e)?); }
        }
        Ok(out)
    }

    fn eval_multi(&mut self, e: &Expr) -> R<Vec<V>> {
        match e {
            Expr::Call { func, args } => {
                let V::Lib(lib, f) = self.eval(func)? else { return Err(()) };
                let args = self.eval_list(args)?;
                self.builtin(lib, f, &args)
            }
            Expr::Method { obj, method, args } => {
                let o = self.eval(obj)?;
                if !matches!(o, V::Str(_)) || !self.libs.contains(&"string") { return Err(()); }
                let f = LIBS[0].1.iter().find(|m| **m == method.as_str()).ok_or(())?;
                let mut all = vec![o];
                all.extend(self.eval_list(args)?);
                self.builtin("string", f, &all)
            }
            Expr::Vararg => Err(()),
            other => Ok(vec![self.eval(other)?]),
        }
    }

    fn eval(&mut self, e: &Expr) -> R<V> {
        self.tick()?;
        Ok(match e {
            Expr::Nil => V::Nil,
            Expr::True => V::Bool(true),
            Expr::False => V::Bool(false),
            Expr::Integer(n) => int_ok(*n)?,
            Expr::Float(f) => V::Num(*f),
            Expr::Str(s) => V::Str(s.as_slice().into()),
            Expr::Name(n) => self.lookup(n)?,
            Expr::Index { table, key: k } => {
                if let (Expr::Name(lib), Expr::Str(f)) = (table.as_ref(), k.as_ref()) {
                    if self.lookup(lib).is_err() {
                        let (l, fs) = LIBS.iter().find(|(l, _)| *l == lib.as_str() && self.libs.contains(l)).ok_or(())?;
                        let f = fs.iter().find(|x| x.as_bytes() == f.as_slice()).ok_or(())?;
                        return Ok(V::Lib(l, f));
                    }
                }
                let V::Tab(t) = self.eval(table)? else { return Err(()) };
                let k = key(&self.eval(k)?)?;
                let v = t.borrow().get(&k).cloned().unwrap_or(V::Nil);
                v
            }
            Expr::Call { .. } | Expr::Method { .. } => self.eval_multi(e)?.into_iter().next().unwrap_or(V::Nil),
            Expr::Paren(x) => self.eval(x)?,
            Expr::Table(fields) => {
                let mut t = HashMap::new();
                let mut n = 0;
                for (i, f) in fields.iter().enumerate() {
                    match f {
                        TableField::ValueField(v) => {
                            let vals = if i + 1 == fields.len() { self.eval_multi(v)? } else { vec![self.eval(v)?] };
                            for v in vals {
                                n += 1;
                                if !matches!(v, V::Nil) { t.insert(Key::Int(n), v); }
                            }
                        }
                        TableField::NameField(k, v) => {
                            let v = self.eval(v)?;
                            if !matches!(v, V::Nil) { t.insert(Key::Str(k.as_bytes().into()), v); }
                        }
                        TableField::IndexField(k, v) => {
                            let k = key(&self.eval(k)?)?;
                            let v = self.eval(v)?;
                            if !matches!(v, V::Nil) { t.insert(k, v); }
                        }
                    }
                }
                V::Tab(Rc::new(RefCell::new(t)))
            }
            Expr::BinOp { op: BinOp::And, lhs, rhs } => {
                let l = self.eval(lhs)?;
                if truthy(&l) { self.eval(rhs)? } else { l }
            }
            Expr::BinOp { op: BinOp::Or, lhs, rhs } => {
                let l = self.eval(lhs)?;
                if truthy(&l) { l } else { self.eval(rhs)? }
            }
            Expr::BinOp { op, lhs, rhs } => {
                let (l, r) = (self.eval(lhs)?, self.eval(rhs)?);
                binop(op, &l, &r)?
            }
            Expr::UnOp { op, operand } => {
                let v = self.eval(operand)?;
                match (op, &v) {
                    (UnOp::Not, _) => V::Bool(!truthy(&v)),
                    (UnOp::Neg, V::Int(n)) => int_ok(-n)?,
                    (UnOp::Neg, V::Num(f)) => V::Num(-f),
                    (UnOp::Len, V::Str(s)) => V::Int(s.len() as i64),
                    (UnOp::Len, V::Tab(t)) => V::Int(border(&t.borrow())?),
                    (UnOp::BNot, _) => int_ok(!to_int(&v)?)?,
                    _ => return Err(()),
                }
            }
            Expr::Function(_) | Expr::Vararg => return Err(()),
        })
    }

    fn builtin(&mut self, lib: &str, f: &str, a: &[V]) -> R<Vec<V>> {
        let arg = |i: usize| a.get(i).cloned().unwrap_or(V::Nil);
        let opt_int = |i: usize, d: i64| match a.get(i) { None | Some(V::Nil) => Ok(d), Some(v) => to_int(v) };
        let s = |i: usize| match a.get(i) { Some(V::Str(s)) => Ok(s.clone()), _ => Err(()) };
        let one = |v: V| Ok(vec![v]);
        match (lib, f) {
            ("string", "char") => {
                let bytes = a.iter().map(|v| to_int(v).and_then(|n| u8::try_from(n).map_err(|_| ()))).collect::<R<Vec<u8>>>()?;
                one(str_v(bytes)?)
            }
            ("string", "byte") => {
                let s = s(0)?;
                let i = pos(opt_int(1, 1)?, s.len()).max(1);
                let j = pos(opt_int(2, i)?, s.len()).min(s.len() as i64);
                Ok((i..=j).map(|k| V::Int(s[k as usize - 1] as i64)).collect())
            }
            ("string", "sub") => {
                let s = s(0)?;
                let i = pos(opt_int(1, 1)?, s.len()).max(1);
                let j = pos(opt_int(2, -1)?, s.len()).min(s.len() as i64);
                one(str_v(if i > j { vec![] } else { s[i as usize - 1..j as usize].to_vec() })?)
            }
            ("string", "len") => one(V::Int(s(0)?.len() as i64)),
            ("string", "rep") if a.len() == 2 => {
                let (s, n) = (s(0)?, to_int(&arg(1))?.max(0) as usize);
                if s.len().saturating_mul(n) > MAX_STR { return Err(()); }
                one(str_v(s.repeat(n))?)
            }
            ("string", "reverse") => one(str_v(s(0)?.iter().rev().copied().collect())?),
            // The C locale only maps ASCII letters.
            ("string", "upper") if s(0)?.is_ascii() => one(str_v(s(0)?.to_ascii_uppercase())?),
            ("string", "lower") if s(0)?.is_ascii() => one(str_v(s(0)?.to_ascii_lowercase())?),
            ("table", "concat") => {
                let V::Tab(t) = arg(0) else { return Err(()) };
                let t = t.borrow();
                let sep = match a.get(1) { None | Some(V::Nil) => Rc::from(&b""[..]), Some(v) => to_str(v)? };
                let (i, j) = (opt_int(2, 1)?, opt_int(3, border(&t)?)?);
                let mut out = Vec::new();
                for k in i..=j {
                    if k > i { out.extend_from_slice(&sep); }
                    out.extend_from_slice(&to_str(t.get(&Key::Int(k)).ok_or(())?)?);
                    if out.len() > MAX_STR { return Err(()); }
                }
                one(str_v(out)?)
            }
            ("table", "insert") => {
                let V::Tab(t) = arg(0) else { return Err(()) };
                let mut t = t.borrow_mut();
                let n = border(&t)?;
                match a.len() {
                    2 => { if !matches!(a[1], V::Nil) { t.insert(Key::Int(n + 1), a[1].clone()); } }
                    3 => {
                        let p = to_int(&a[1])?;
                        if p < 1 || p > n + 1 || matches!(a[2], V::Nil) { return Err(()); }
                        for k in (p..=n).rev() {
                            let v = t.remove(&Key::Int(k)).ok_or(())?;
                            t.insert(Key::Int(k + 1), v);
                        }
                        t.insert(Key::Int(p), a[2].clone());
                    }
                    _ => return Err(()),
                }
                Ok(vec![])
            }
            ("math", "floor") => one(match arg(0) {
                V::Int(n) => V::Int(n),
                V::Num(f) if f.is_finite() => int_ok(f.floor() as i64)?,
                _ => return Err(()),
            }),
            ("math", "abs") => one(match arg(0) {
                V::Int(n) => int_ok(n.abs())?,
                V::Num(f) => V::Num(f.abs()),
                _ => return Err(()),
            }),
            ("math", "max") | ("math", "min") => {
                let mut best = a.first().cloned().ok_or(())?;
                for v in &a[1..] {
                    let better = if f == "max" { to_num(v)? > to_num(&best)? } else { to_num(v)? < to_num(&best)? };
                    if better { best = v.clone(); }
                }
                to_num(&best)?;
                one(best)
            }
            _ => Err(()),
        }
    }
}

/// Lua rounds toward minus infinity.
fn floor_div(a: i64, b: i64) -> R<i64> {
    let q = a.checked_div(b).ok_or(())?;
    Ok(if a % b != 0 && (a < 0) != (b < 0) { q - 1 } else { q })
}

fn binop(op: &BinOp, l: &V, r: &V) -> R<V> {
    use BinOp::*;
    if let (V::Int(a), V::Int(b)) = (l, r) {
        let (a, b) = (*a, *b);
        return match op {
            Add => int_ok(a.checked_add(b).ok_or(())?),
            Sub => int_ok(a.checked_sub(b).ok_or(())?),
            Mul => int_ok(a.checked_mul(b).ok_or(())?),
            IDiv | Mod if b == 0 => Err(()),
            IDiv => int_ok(floor_div(a, b)?),
            Mod => int_ok(a - floor_div(a, b)? * b),
            Div => Ok(V::Num(a as f64 / b as f64)),
            Pow => Ok(V::Num((a as f64).powf(b as f64))),
            BAnd => int_ok(a & b),
            BOr => int_ok(a | b),
            BXor => int_ok(a ^ b),
            Shl if (0..64).contains(&b) => int_ok(a << b),
            Shr if (0..64).contains(&b) => int_ok(((a as u64) >> b) as i64),
            Eq => Ok(V::Bool(a == b)),
            Ne => Ok(V::Bool(a != b)),
            Lt => Ok(V::Bool(a < b)),
            Le => Ok(V::Bool(a <= b)),
            Gt => Ok(V::Bool(a > b)),
            Ge => Ok(V::Bool(a >= b)),
            Concat => str_v([to_str(l)?, to_str(r)?].concat()),
            _ => Err(()),
        };
    }
    match op {
        Concat => str_v([to_str(l)?, to_str(r)?].concat()),
        Eq | Ne => {
            let eq = match (l, r) {
                (V::Str(a), V::Str(b)) => a == b,
                (V::Nil, V::Nil) => true,
                (V::Bool(a), V::Bool(b)) => a == b,
                (V::Tab(a), V::Tab(b)) => Rc::ptr_eq(a, b),
                (V::Int(_) | V::Num(_), V::Int(_) | V::Num(_)) => to_num(l)? == to_num(r)?,
                _ => false,
            };
            Ok(V::Bool(eq == matches!(op, Eq)))
        }
        BAnd | BOr | BXor | Shl | Shr => binop(op, &V::Int(to_int(l)?), &V::Int(to_int(r)?)),
        _ => {
            let (a, b) = (to_num(l)?, to_num(r)?);
            Ok(match op {
                Add => V::Num(a + b),
                Sub => V::Num(a - b),
                Mul => V::Num(a * b),
                Div => V::Num(a / b),
                IDiv => V::Num((a / b).floor()),
                Mod => V::Num(a - (a / b).floor() * b),
                Pow => V::Num(a.powf(b)),
                Lt => V::Bool(a < b),
                Le => V::Bool(a <= b),
                Gt => V::Bool(a > b),
                Ge => V::Bool(a >= b),
                _ => return Err(()),
            })
        }
    }
}
