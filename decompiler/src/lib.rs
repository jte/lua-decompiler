//! Lua bytecode decompiler.
//!
//! Pipeline per function:
//! 1. [`ir::decode`] – version-independent instructions,
//! 2. [`flow::Flow`] – basic blocks, dominators, loops,
//! 3. [`webs::analyze`] – liveness and variables (webs),
//! 4. [`lift`] – statements over variables,
//! 5. [`simplify`] – fold temporaries, rebuild table constructors,
//! 6. [`structure`] – loops / if / and-or conditions,
//! 7. [`astpass`] – value expressions, guard clauses, elseif,
//! 8. [`declare`] + [`names`] – `local` placement and naming,
//! 9. nested closures, decompiled with their captured variables' names.

pub mod cfg;
pub mod linearize;

mod astpass;
mod declare;
mod flow;
mod ir;
mod lift;
mod names;
mod simplify;
mod structure;
mod webs;

use std::collections::{BTreeMap, BTreeSet};

use disassembler::Proto;
use lua_ast::{print_block, Block, Expr, FuncBody};

use crate::flow::{Flow, Term};
use crate::ir::{Cap, Ins, Rk};
use crate::lift::{pseudo_args, Lifter};
use crate::simplify::VarFacts;
use crate::webs::VarId;

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct Options {
    /// Keep functions under Lua's 200-locals limit by reusing dead locals'
    /// names (and spilling into a table as a last resort).  The deobfuscator
    /// turns this off — it needs one name per variable — and applies the
    /// limit itself afterwards.
    pub reuse_locals: bool,
}

impl Default for Options {
    fn default() -> Self { Options { reuse_locals: true } }
}

/// Decompile a top-level `Proto` to a Lua AST block.
pub fn decompile_to_block(proto: &Proto) -> Block {
    decompile_to_block_with(proto, Options::default())
}

pub fn decompile_to_block_with(proto: &Proto, opts: Options) -> Block {
    let mut globals = BTreeSet::new();
    let env = main_env(proto);
    scan_globals(proto, &env, &mut globals);
    let upnames: Vec<String> = env.iter().map(|&e| if e { "_ENV".to_string() } else { "_upv".to_string() }).collect();
    let ctx = Ctx { globals, opts };
    decompile_fn(proto, &upnames, &env, &[], &ctx, false, false).body
}

/// Decompile a CFF-obfuscated `Proto` to an AST block, with options.
pub fn decompile_cff_to_block_with(proto: &Proto, opts: Options) -> Block {
    decompile_to_block_with(&linearize::linearize_tree(proto), opts)
}

/// Decompile a `Proto` to a Lua source string.
pub fn decompile(proto: &Proto) -> String {
    print_block(&decompile_to_block(proto), 0)
}

/// Decompile a CFF-obfuscated `Proto` to an AST block.
pub fn decompile_cff_to_block(proto: &Proto) -> Block {
    decompile_to_block(&linearize::linearize_tree(proto))
}

/// Decompile a CFF-obfuscated `Proto` to a Lua source string.
pub fn decompile_cff(proto: &Proto) -> String {
    print_block(&decompile_cff_to_block(proto), 0)
}

/// Graphviz DOT of `proto`'s control-flow graph as the decompiler sees it
/// (every Lua version; [`cfg::Cfg`] covers 5.1–5.3 only).
pub fn flow_dot(proto: &Proto) -> String {
    let d = ir::decode(proto);
    let flow = Flow::build(&d);
    let mut s = String::from("digraph {\n");
    for (id, n) in flow.nodes.iter().enumerate() {
        let pcs: Vec<usize> = n.ops.iter().filter_map(|o| if let flow::Op::Pc(p) = o { Some(*p) } else { None }).collect();
        let range = match (pcs.first(), pcs.last()) {
            (Some(a), Some(b)) => format!("pc {}..{}", a, b),
            _ => "(no code)".to_string(),
        };
        s.push_str(&format!("    {} [ label=\"BB{}\\n{}\", shape=box ]\n", id, id, range));
    }
    for (id, n) in flow.nodes.iter().enumerate() {
        for (k, t) in n.succs.iter().enumerate() {
            let label = match (&n.term, k) {
                (Term::Cond { .. }, 0) => "true",
                (Term::Cond { .. }, _) => "false",
                (Term::NumFor { .. } | Term::GenFor { .. }, 0) => "body",
                (Term::NumFor { .. } | Term::GenFor { .. }, _) => "exit",
                _ => "",
            };
            s.push_str(&format!("    {} -> {} [ label=\"{}\" ]\n", id, t, label));
        }
    }
    s.push_str("}\n");
    s
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

struct Ctx {
    /// Global names referenced anywhere in the chunk; locals must not
    /// shadow them.
    globals: BTreeSet<String>,
    opts: Options,
}

/// In 5.2+ the main chunk's single upvalue is the global environment.
fn main_env(proto: &Proto) -> Vec<bool> {
    if proto.version >= 0x52 {
        (0..proto.num_upvalues.max(1)).map(|i| i == 0).collect()
    } else {
        Vec::new()
    }
}

fn scan_globals(proto: &Proto, is_env: &[bool], out: &mut BTreeSet<String>) {
    let d = ir::decode(proto);
    let mut add = |k: u32| {
        if let Expr::Str(b) = lift::const_expr(proto.constants.get(k as usize)) {
            if let Ok(s) = String::from_utf8(b) {
                if lua_ast::is_lua_ident(&s) { out.insert(s); }
            }
        }
    };
    let env = |up: u16| is_env.get(up as usize).copied().unwrap_or(false);
    let mut children = Vec::new();
    let mut dynamic_env = false;
    for ins in &d.ins {
        match ins {
            Ins::GetTabUp { up, key: Rk::K(k), .. } | Ins::SetTabUp { up, key: Rk::K(k), .. } if env(*up) => add(*k),
            // Global names loaded into a register first (common in
            // obfuscated code): any string constant may be one.
            Ins::GetTabUp { up, key: Rk::R(_), .. } | Ins::SetTabUp { up, key: Rk::R(_), .. } if env(*up) => dynamic_env = true,
            Ins::GetGlobal { k, .. } | Ins::SetGlobal { k, .. } => add(*k),
            Ins::Closure { idx, caps, .. } => {
                let child_env: Vec<bool> = caps.iter().map(|c| match c {
                    Cap::Up(j) => env(*j),
                    Cap::Reg(_) | Cap::Val(_) => false,
                }).collect();
                children.push((*idx, child_env));
            }
            _ => {}
        }
    }
    if dynamic_env {
        for k in 0..proto.constants.len() { add(k as u32); }
    }
    for (idx, child_env) in children {
        if let Some(p) = proto.p.get(idx) { scan_globals(p, &child_env, out); }
    }
}

/// A variable holding *all* results of a call or `...` (multret) that could
/// not be folded into its consumer: keep every value by packing them into a
/// table and unpacking at the use.
fn materialize_packs(body: &mut Block, pack: &[bool], version: u8, luau: bool) {
    let is_pack = |e: &Expr| crate::lift::var_id(e).map_or(false, |v| v < pack.len() && pack[v]);
    let call = |f: &str, args: Vec<Expr>| Expr::Call { func: Box::new(Expr::Name(f.to_string())), args };
    let index = |t: Expr, k: &str| Expr::Index { table: Box::new(t), key: Box::new(Expr::Str(k.as_bytes().to_vec())) };
    // `table.pack`/`table.unpack` (5.2+ and Luau), else `unpack`.
    let has_table_pack = version >= 0x52 || luau;
    // Uses first (every expression position): every value, nils included...
    lua_ast::transform_block(body, &mut |e: &mut Expr| {
        if is_pack(e) {
            let p = e.clone();
            *e = call("@unpack", vec![p.clone(), Expr::Integer(1), index(p, "n")]);
        }
    });
    // ...then turn the definitions back into packs with their count `n`.
    fn fix(b: &mut Block, has_table_pack: bool) {
        for s in b.iter_mut() {
            if let lua_ast::Stat::Assign { lhs, rhs } = s {
                if lhs.len() == 1 && rhs.len() == 1 {
                    if let Some(args) = pseudo_args(&lhs[0], "@unpack").cloned() {
                        lhs[0] = args[0].clone();
                        let e = std::mem::replace(&mut rhs[0], Expr::Nil);
                        rhs[0] = if has_table_pack {
                            Expr::Call {
                                func: Box::new(Expr::Index { table: Box::new(Expr::Name("table".into())), key: Box::new(Expr::Str(b"pack".to_vec())) }),
                                args: vec![e],
                            }
                        } else {
                            // 5.1: `(function(...) return {n = select("#", ...), ...} end)(e)`
                            let count = Expr::Call {
                                func: Box::new(Expr::Name("select".into())),
                                args: vec![Expr::Str(b"#".to_vec()), Expr::Vararg],
                            };
                            let packer = FuncBody {
                                params: vec![],
                                has_vararg: true,
                                vararg_name: None,
                                body: vec![lua_ast::Stat::Return(vec![Expr::Table(vec![
                                    lua_ast::TableField::NameField("n".into(), count),
                                    lua_ast::TableField::ValueField(Expr::Vararg),
                                ])])],
                            };
                            Expr::Call { func: Box::new(Expr::Function(Box::new(packer))), args: vec![e] }
                        };
                    }
                }
            }
            astpass::for_each_child_mut(s, &mut |c| fix(c, has_table_pack));
        }
    }
    fix(body, has_table_pack);
    // The remaining `@unpack` calls become real ones.
    lua_ast::transform_block(body, &mut |e: &mut Expr| {
        if let Expr::Call { func, .. } = e {
            if matches!(func.as_ref(), Expr::Name(n) if n == "@unpack") {
                **func = if has_table_pack {
                    Expr::Index { table: Box::new(Expr::Name("table".into())), key: Box::new(Expr::Str(b"unpack".to_vec())) }
                } else {
                    Expr::Name("unpack".into())
                };
            }
        }
    });
}

/// `_ENV["name"]` → `name` for known global names.
fn env_to_globals(body: &mut Block, globals: &BTreeSet<String>) {
    lua_ast::transform_block(body, &mut |e: &mut Expr| {
        if let Expr::Index { table, key } = e {
            if matches!(table.as_ref(), Expr::Name(n) if n == "_ENV") {
                if let Some(k) = key.as_str_utf8() {
                    if globals.contains(k) { *e = Expr::Name(k.to_string()); }
                }
            }
        }
    });
}

/// `method`: the function is stored into a table field, so an unnamed first
/// parameter is presumably `self`.  `boxed_up`: which upvalues hold boxes
/// (see [`Lifter::box_op`]).  `force_flat`: skip structuring.
fn decompile_fn(
    proto: &Proto,
    upnames: &[String],
    is_env: &[bool],
    boxed_up: &[bool],
    ctx: &Ctx,
    method: bool,
    force_flat: bool,
) -> FuncBody {
    // Testing aid: LUADEC_FORCE_FLAT decompiles every function goto-based.
    let force_flat = force_flat || std::env::var_os("LUADEC_FORCE_FLAT").is_some();
    let d = ir::decode(proto);
    let flow = Flow::build(&d);
    // A 5.5 named vararg parameter (`...t`) is one more register parameter.
    let named_vararg = ir::named_vararg(proto);
    let an = webs::analyze(&d, &flow, proto.numparams as u16 + named_vararg as u16);
    let mut debug = names::debug_names(proto, &an);
    if method && !upnames.iter().any(|n| n == "self") {
        if let Some(&p0) = an.param_vars.first() {
            debug.entry(p0).or_insert_with(|| "self".to_string());
        }
    }

    // Unstructured (goto) output hoists every local to the top, which would
    // make closures created on different passes share variables; there the
    // captured variables live in boxes instead.
    let flat_mode = force_flat || flow.irreducible;
    let boxed_vars: BTreeSet<VarId> = if flat_mode {
        (0..an.vars.len()).filter(|&v| an.vars[v].captured && an.vars[v].param.is_none()).collect()
    } else {
        BTreeSet::new()
    };
    let nv = an.vars.len();
    let mut lifter = Lifter {
        proto, d: &d, flow: &flow, an: &an, upnames, is_env,
        boxed_vars: boxed_vars.clone(), boxed_up, next_var: nv,
        closure_boxes: BTreeMap::new(),
        skip_pc: BTreeSet::new(),
        method_at: BTreeMap::new(),
        flat: flat_mode,
        val_copies: Vec::new(),
    };
    let mut blocks = lifter.lift_all();
    let after_lift = lifter.next_var;
    let closure_boxes = std::mem::take(&mut lifter.closure_boxes);

    // Fold temporaries and rebuild table constructors.
    let mut facts = VarFacts {
        defs: an.vars.iter().map(|v| v.defs).collect(),
        uses: an.vars.iter().map(|v| v.uses).collect(),
        pinned: (0..nv).map(|v| {
            let i = &an.vars[v];
            i.captured || i.param.is_some() || debug.contains_key(&v)
        }).collect(),
        pack: pack_vars(&d, &flow, &an),
        positional_keys: proto.jit > 0,
    };
    // Luau by-value captures name a variable for the closure: keep it.
    for v in val_captured(&d, &flow, &an) { facts.pinned[v] = true; }
    // Temporaries made by the lifter stay put.
    facts.defs.resize(after_lift, 0);
    facts.uses.resize(after_lift, 0);
    facts.pinned.resize(after_lift, true);
    facts.pack.resize(after_lift, false);
    simplify::count_blocks(&blocks, &mut facts.defs, &mut facts.uses);
    for _ in 0..4 {
        let mut changed = false;
        for b in blocks.iter_mut() {
            changed |= simplify::fold_block(b, &mut facts);
            changed |= simplify::build_constructors(b, &mut facts);
            changed |= simplify::fold_forgen(b, &mut facts);
            changed |= simplify::fold_block(b, &mut facts);
        }
        if !changed { break; }
    }

    // Structure.
    let mut flow = flow;
    structure::merge_conditions(&mut flow, &mut blocks);
    let empty: Vec<bool> = blocks.iter().zip(&flow.nodes).map(|(b, n)| {
        b.stmts.is_empty() && b.cond.is_none() && n.term == Term::Goto
    }).collect();
    let flow = Flow::rebuild(flow.nodes, flow.entry, &empty);
    let mut next_var = after_lift;
    let mut body = if flat_mode || flow.irreducible {
        structure::flat(&flow, &blocks, &mut next_var, &boxed_vars, proto.luau)
    } else {
        let mut s = structure::Structurer::new(&flow, &blocks, &an.live_in_vars);
        let b = s.run();
        if s.failed {
            return decompile_fn(proto, upnames, is_env, boxed_up, ctx, method, true);
        }
        b
    };
    // Hidden loop variables of the flat fallback.
    facts.defs.resize(next_var, 0);
    facts.uses.resize(next_var, 0);
    facts.pinned.resize(next_var, true);
    facts.pack.resize(next_var, false);
    let nv = next_var;
    astpass::prune_labels(&mut body);
    astpass::simplify(&mut body);
    // Fold temporaries that crossed control flow (e.g. around `a or b`).
    for _ in 0..3 {
        let mut defs = vec![0u32; nv];
        let mut uses = vec![0u32; nv];
        let mut loop_vars = BTreeSet::new();
        simplify::count_ast(&body, &mut defs, &mut uses, &mut loop_vars);
        facts.defs = defs;
        facts.uses = uses;
        for v in loop_vars { facts.pinned[v] = true; }
        if !simplify::fold_ast(&mut body, &mut facts) { break; }
        astpass::simplify(&mut body);
    }
    env_to_globals(&mut body, &ctx.globals);
    materialize_packs(&mut body, &facts.pack, proto.version, proto.luau);
    astpass::raise_generic_for(&mut body);
    astpass::scope_tbc(&mut body);

    // Declarations and names.
    let params: Vec<VarId> = an.param_vars.clone();
    let skip: BTreeSet<VarId> = params.iter().copied().collect();
    declare::place(&mut body, &skip);
    declare::hoist_for_labels(&mut body);
    if ctx.opts.reuse_locals {
        declare::coalesce(&mut body, params.len());
        declare::spill(&mut body, params.len(), nv);
    }
    let mut kinds = BTreeMap::new();
    declare::init_kinds(&body, &mut kinds);
    let mut all = BTreeSet::new();
    collect_vars(&body, &mut all);
    let mut avoid: BTreeSet<String> = ctx.globals.clone();
    avoid.extend(upnames.iter().cloned());
    // Names the decompiler itself may emit as globals.
    for g in ["_ENV", "_G", "table", "unpack", "next", "select"] { avoid.insert(g.into()); }
    if proto.luau {
        // Used by the flat form of generalized iteration.
        for g in ["type", "getmetatable"] { avoid.insert(g.into()); }
    }
    if proto.jit > 0 {
        // LuaJIT bit operator instructions are printed as `bit.*` calls.
        avoid.insert("bit".into());
    }
    let names = names::assign(&all, &params, &debug, &kinds, &avoid);
    declare::rename(&mut body, &names);

    // Nested functions.
    fill_closures(&mut body, proto, ctx, &closure_boxes);

    astpass::finalize(&mut body, true);
    // Luau has no goto: `continue`, else a dispatch loop over flat code.
    if proto.luau {
        astpass::luau_continue(&mut body);
        if astpass::has_goto(&body) {
            if !force_flat {
                return decompile_fn(proto, upnames, is_env, boxed_up, ctx, method, true);
            }
            astpass::luau_dispatch(&mut body);
        }
    }
    astpass::rename_labels(&mut body);

    let mut param_names: Vec<String> = params.iter().map(|v| names[v].clone()).collect();
    let vararg_name = if named_vararg { param_names.pop() } else { None };
    FuncBody {
        params: param_names,
        has_vararg: proto.is_vararg != 0,
        vararg_name,
        body,
    }
}

/// Variables a closure captures by value (Luau CAPTURE VAL): the leading
/// uses of each closure op (captured registers come last).
fn val_captured(d: &ir::Decoded, flow: &Flow, an: &webs::Analysis) -> Vec<VarId> {
    let mut out = Vec::new();
    for (b, node) in flow.nodes.iter().enumerate() {
        for (i, op) in node.ops.iter().enumerate() {
            let flow::Op::Pc(pc) = op else { continue };
            let Ins::Closure { caps, .. } = &d.ins[*pc] else { continue };
            let nval = caps.iter().filter(|c| matches!(c, Cap::Val(_))).count();
            if let Some(info) = an.ops.get(b).and_then(|o| o.get(i)) {
                out.extend(info.use_var.iter().take(nval).copied());
            }
        }
    }
    out
}

/// Variables that hold every result of a call or `...` (multret).
fn pack_vars(d: &ir::Decoded, flow: &Flow, an: &webs::Analysis) -> Vec<bool> {
    let mut pack = vec![false; an.vars.len()];
    for (b, node) in flow.nodes.iter().enumerate() {
        for (i, op) in node.ops.iter().enumerate() {
            let flow::Op::Pc(pc) = *op else { continue };
            let multret = matches!(d.ins[pc], Ins::Call { nret: None, .. } | Ins::VarArg { n: None, .. });
            if multret {
                if let Some(&v) = an.ops[b].get(i).and_then(|o| o.def_var.first()) { pack[v] = true; }
            }
        }
    }
    pack
}

fn collect_vars(b: &Block, out: &mut BTreeSet<VarId>) {
    let mut add_name = |n: &str, out: &mut BTreeSet<VarId>| {
        if let Some(v) = n.strip_prefix("@v").and_then(|s| s.parse().ok()) { out.insert(v); }
    };
    for s in b {
        match s {
            lua_ast::Stat::Local { names, .. } => { for n in names { add_name(n, out); } }
            lua_ast::Stat::NumFor { var, .. } => add_name(var, out),
            lua_ast::Stat::GenFor { vars, .. } => { for n in vars { add_name(n, out); } }
            _ => {}
        }
        let mut sub = |c: &Vec<lua_ast::Stat>| collect_vars(c, out);
        astpass::for_each_child(s, &mut sub);
    }
}

/// Closures stored as `t.name = function`: candidates for method syntax.
fn method_closures(b: &Block, out: &mut BTreeSet<usize>) {
    for s in b {
        if let lua_ast::Stat::Assign { lhs, rhs } = s {
            if lhs.len() == 1 && rhs.len() == 1 {
                let field = matches!(&lhs[0], Expr::Index { key, .. }
                    if key.as_str_utf8().map_or(false, lua_ast::is_lua_ident));
                if let Some(args) = pseudo_args(&rhs[0], "@closure") {
                    if field { out.insert(args[0].as_integer().unwrap_or(-1) as usize); }
                }
            }
        }
        let mut sub = |c: &Vec<lua_ast::Stat>| method_closures(c, out);
        astpass::for_each_child(s, &mut sub);
    }
}

fn fill_closures(body: &mut Block, proto: &Proto, ctx: &Ctx, boxes: &BTreeMap<usize, Vec<bool>>) {
    let mut methods = BTreeSet::new();
    method_closures(body, &mut methods);
    lua_ast::transform_block(body, &mut |e: &mut Expr| {
        let Some(args) = pseudo_args(e, "@closure") else { return };
        let idx = args[0].as_integer().unwrap_or(0) as usize;
        let Some(child) = proto.p.get(idx) else { return };
        let upnames: Vec<String> = args[1..].iter().map(|a| match a {
            Expr::Name(n) => n.clone(),
            _ => "_upv".to_string(),
        }).collect();
        let is_env: Vec<bool> = upnames.iter().map(|n| n == "_ENV").collect();
        let boxed: Vec<bool> = boxes.get(&idx).cloned().unwrap_or_default();
        let f = decompile_fn(child, &upnames, &is_env, &boxed, ctx, methods.contains(&idx), false);
        *e = Expr::Function(Box::new(f));
    });
}
