/// Pass – XOR stream cipher decryption.
///
/// Recognises (names vary):
///
/// ```lua
/// local KEY = "<long byte string>"
/// local POS = #T / #T                         -- 1
/// local function F3(s)                        -- decrypt: bytes table
///   local out = {}
///   for k, v in ITER({string.byte(s, 1, #s)}) do
///     out[k] = v ~ (CHARS["\t"] ~ string.byte(KEY, POS))
///   end
///   POS = POS + #KEY / #KEY                   -- next key byte
///   return out
/// end
/// local function F4(t) ... s = s .. CHARS[v] ... return s end   -- bytes→string
/// local TBL = {}
/// W = function() return F3("<ciphertext>") end
/// TBL["<id>"] = W()
/// ...                                          -- one wrapper per string
/// ... F4(TBL["<id>"]) ...                      -- use sites
/// ```
///
/// Call n of F3 uses key byte n.  This only holds when F3 is called solely by
/// the wrappers, each wrapper runs once in order, and nothing else touches
/// POS or TBL — all of which are checked.  `F4(TBL[id])` becomes the
/// decrypted string; when nothing else uses the machinery, it is removed.

use std::collections::BTreeMap;
use lua_ast::{BinOp, Block, Expr, Stat, UnOp};

use crate::util::{assigned_names, count_refs, visit_stats};


pub fn run(block: &mut Block) {
    // Only function bodies (and the main chunk): a loop body would run the
    // wrappers more than once.
    process_body(block);
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Function(fb) = e { process_body(&mut fb.body); }
    });
}

struct Cipher {
    f3: String,
    key: Vec<u8>,
    pos: String,
    xor: u8,
}

fn local_fn(s: &Stat) -> Option<(&str, &lua_ast::FuncBody)> {
    match s {
        Stat::Local { names, values } if names.len() == 1 && values.len() == 1 => match &values[0] {
            Expr::Function(fb) => Some((&names[0], fb)),
            _ => None,
        },
        _ => None,
    }
}

fn name(e: &Expr) -> Option<&str> {
    if let Expr::Name(n) = e { Some(n) } else { None }
}

/// `#X / #X` or `1`.
fn is_one(e: &Expr) -> bool {
    match e {
        Expr::Integer(1) => true,
        Expr::Float(f) => *f == 1.0,
        Expr::BinOp { op: BinOp::Div, lhs, rhs } => {
            matches!((lhs.as_ref(), rhs.as_ref()), (Expr::UnOp { op: UnOp::Len, operand: a }, Expr::UnOp { op: UnOp::Len, operand: b }) if a == b)
        }
        _ => false,
    }
}

/// Match F3's body; returns (key var, pos var, xor constant).
fn match_f3(body: &Block) -> Option<(String, String, u8)> {
    let mut found: Option<(String, String, u8)> = None;
    let mut steps = 0;
    for s in body {
        match s {
            Stat::GenFor { body: lb, .. } | Stat::While { body: lb, .. } | Stat::NumFor { body: lb, .. } => {
                for x in lb {
                    if let Stat::Assign { rhs, .. } = x {
                        if let Some(m) = rhs.first().and_then(match_xor) { found = Some(m); }
                    }
                }
            }
            Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => {
                if let (Some(p), Expr::BinOp { op: BinOp::Add, lhs: a, rhs: b }) = (name(&lhs[0]), &rhs[0]) {
                    if name(a) == Some(p) && is_one(b) {
                        if found.as_ref().map_or(false, |f| f.1 == p) { steps += 1; }
                    }
                }
            }
            _ => {}
        }
    }
    if steps == 1 { found } else { None }
}

/// `v ~ (CHARS["c"] ~ BYTE(KEY, POS))`.
fn match_xor(e: &Expr) -> Option<(String, String, u8)> {
    let Expr::BinOp { op: BinOp::BXor, rhs, .. } = e else { return None };
    let Expr::BinOp { op: BinOp::BXor, lhs: c, rhs: b } = rhs.as_ref() else { return None };
    let xor = match c.as_ref() {
        Expr::Index { key, .. } => match key.as_ref() { Expr::Str(s) if s.len() == 1 => s[0], _ => return None },
        _ => return None,
    };
    let Expr::Call { args, .. } = b.as_ref() else { return None };
    if args.len() != 2 { return None; }
    Some((name(&args[0])?.to_string(), name(&args[1])?.to_string(), xor))
}

/// `W = function() ... return F3("ct") end` (local or assignment).
fn wrapper(s: &Stat, f3: &str) -> Option<(String, Vec<u8>)> {
    let (w, fb) = match s {
        Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => match (&lhs[0], &rhs[0]) {
            (Expr::Name(w), Expr::Function(fb)) => (w.as_str(), fb.as_ref()),
            _ => return None,
        },
        _ => { let (w, fb) = local_fn(s)?; (w, fb) }
    };
    if !fb.params.is_empty() { return None; }
    let Some(Stat::Return(v)) = fb.body.last() else { return None };
    let mut e = v.first()?;
    if let Expr::Paren(inner) = e { e = inner; }
    let Expr::Call { func, args } = e else { return None };
    if name(func) != Some(f3) || args.len() != 1 { return None; }
    let Expr::Str(ct) = &args[0] else { return None };
    // Nothing else in the wrapper may have effects (left-over `local t = {}`
    // noise is fine).
    let rest = &fb.body[..fb.body.len() - 1];
    if !rest.iter().all(|s| matches!(s, Stat::Local { values, .. } if values.iter().all(crate::util::is_pure))) {
        return None;
    }
    Some((w.to_string(), ct.clone()))
}

/// `TBL["id"] = W()`.
fn table_store(s: &Stat, w: &str) -> Option<(String, Vec<u8>)> {
    let Stat::Assign { lhs, rhs } = s else { return None };
    if lhs.len() != 1 || rhs.len() != 1 { return None; }
    let Expr::Index { table, key } = &lhs[0] else { return None };
    let Expr::Call { func, args } = &rhs[0] else { return None };
    if !args.is_empty() || name(func) != Some(w) { return None; }
    let Expr::Str(id) = key.as_ref() else { return None };
    Some((name(table)?.to_string(), id.clone()))
}

fn process_body(block: &mut Block) {
    let assigned = assigned_names(block);
    // F3 and its key/position variables.
    let mut cipher: Option<Cipher> = None;
    for s in block.iter() {
        let Some((f3, fb)) = local_fn(s) else { continue };
        if fb.params.len() != 1 || assigned.contains(f3) { continue; }
        let Some((key_var, pos, xor)) = match_f3(&fb.body) else { continue };
        let key = block.iter().find_map(|x| match x {
            Stat::Local { names, values } if names.len() == 1 && names[0] == key_var && values.len() == 1 => {
                if let Expr::Str(k) = &values[0] { Some(k.clone()) } else { None }
            }
            _ => None,
        });
        let pos_init = block.iter().any(|x| matches!(x, Stat::Local { names, values }
            if names.len() == 1 && names[0] == pos && values.len() == 1 && is_one(&values[0])));
        if let (Some(key), true) = (key, pos_init) {
            if !assigned.contains(&key_var) {
                cipher = Some(Cipher { f3: f3.to_string(), key, pos, xor });
                break;
            }
        }
    }
    let Some(c) = cipher else { return };

    // POS is only written by F3 (its one step) and read nowhere else.
    let mut pos_writes = 0;
    visit_stats(block, &mut |s| if let Stat::Assign { lhs, .. } = s {
        pos_writes += lhs.iter().filter(|l| name(l) == Some(c.pos.as_str())).count();
    });
    if pos_writes != 1 { return; }
    let f3_body_refs = block.iter().find_map(|s| local_fn(s).filter(|(n, _)| *n == c.f3))
        .map(|(_, fb)| count_refs(&fb.body, &c.pos)).unwrap_or(0);
    if count_refs(block, &c.pos) != 1 + f3_body_refs { return; }

    // Wrappers, in order: definition immediately followed by its store.
    let mut plain: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();
    let mut tbl: Option<String> = None;
    let mut wrapper_stmts: Vec<usize> = Vec::new();
    let mut n = 0usize;
    let mut i = 0;
    while i + 1 < block.len() {
        if let Some((w, ct)) = wrapper(&block[i], &c.f3) {
            if let Some((t, id)) = table_store(&block[i + 1], &w) {
                if tbl.get_or_insert_with(|| t.clone()) != &t { return; }
                let Some(&kb) = c.key.get(n) else { return };
                let mask = c.xor ^ kb;
                plain.insert(id, ct.iter().map(|&b| b ^ mask).collect());
                wrapper_stmts.extend([i, i + 1]);
                n += 1;
                i += 2;
                continue;
            }
        }
        i += 1;
    }
    let Some(tbl) = tbl else { return };
    // F3 is called by the wrappers only.
    if count_refs(block, &c.f3) != 1 + n { return; }
    // TBL is written only by the wrapper stores.
    let mut tbl_writes = 0;
    visit_stats(block, &mut |s| if let Stat::Assign { lhs, .. } = s {
        for l in lhs {
            if let Expr::Index { table, .. } = l { if name(table) == Some(tbl.as_str()) { tbl_writes += 1; } }
            if name(l) == Some(tbl.as_str()) { tbl_writes += 1000; }
        }
    });
    if tbl_writes != n || assigned.contains(&tbl) { return; }

    // F4: the bytes→string function, plus aliases of F4 and TBL.
    let f4s: Vec<String> = block.iter().filter_map(|s| {
        let (f, fb) = local_fn(s)?;
        (fb.params.len() == 1 && is_bytes_to_string(&fb.body) && !assigned.contains(f)).then(|| f.to_string())
    }).collect();
    if f4s.is_empty() { return; }
    let alias = |of: &[String]| -> Vec<String> {
        block.iter().filter_map(|s| match s {
            Stat::Local { names, values } if names.len() == 1 && values.len() == 1 && !assigned.contains(&names[0]) => {
                name(&values[0]).filter(|v| of.iter().any(|o| o == v)).map(|_| names[0].clone())
            }
            _ => None,
        }).collect()
    };
    let mut f4_names = f4s.clone();
    f4_names.extend(alias(&f4s));
    let mut tbl_names = vec![tbl.clone()];
    tbl_names.extend(alias(&[tbl.clone()]));

    // Substitute F4(TBL["id"]) after the wrappers.
    let last = *wrapper_stmts.last().unwrap();
    for s in block.iter_mut().skip(last + 1) {
        let mut one = vec![std::mem::replace(s, Stat::Break)];
        lua_ast::transform_block(&mut one, &mut |e| {
            if let Expr::Call { func, args } = e {
                if args.len() == 1 && name(func).map_or(false, |f| f4_names.iter().any(|x| x == f)) {
                    if let Expr::Index { table, key } = &args[0] {
                        if name(table).map_or(false, |t| tbl_names.iter().any(|x| x == t)) {
                            if let Expr::Str(id) = key.as_ref() {
                                if let Some(p) = plain.get(id) { *e = Expr::Str(p.clone()); }
                            }
                        }
                    }
                }
            }
        });
        *s = one.pop().unwrap();
    }

    // Remove the wrappers once TBL is only referenced by them (and aliases).
    let tbl_refs: usize = tbl_names.iter().map(|t| count_refs(block, t)).sum();
    if tbl_refs == 1 + n + 2 * (tbl_names.len() - 1) {
        for &k in wrapper_stmts.iter().rev() { block.remove(k); }
    }
}

/// `local s = "" ; for ... do s = s .. CHARS[v] end ; return s`.
fn is_bytes_to_string(body: &Block) -> bool {
    let has_concat = body.iter().any(|s| match s {
        Stat::GenFor { body: lb, .. } | Stat::While { body: lb, .. } => lb.iter().any(|x| matches!(x,
            Stat::Assign { rhs, .. } if matches!(rhs.first(), Some(Expr::BinOp { op: BinOp::Concat, .. })))),
        _ => false,
    });
    has_concat && matches!(body.last(), Some(Stat::Return(v)) if v.len() == 1 && matches!(v[0], Expr::Name(_)))
}
