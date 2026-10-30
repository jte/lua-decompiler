//! Variable naming: debug-info names where available, generated otherwise.

use std::collections::{BTreeMap, BTreeSet};

use disassembler::Proto;
use lua_ast::is_lua_ident;

use crate::webs::{Analysis, VarId};

/// Register of each debug local: the number of locals still active when it
/// starts (locals are allocated in declaration order).
fn local_regs(proto: &Proto) -> Vec<u16> {
    let locs = &proto.locals;
    let mut regs = vec![0u16; locs.len()];
    let mut active: Vec<usize> = Vec::new();
    for i in 0..locs.len() {
        let s = locs[i].start_pc;
        active.retain(|&j| locs[j].end_pc > s);
        regs[i] = active.len() as u16;
        active.push(i);
    }
    regs
}

/// Source names from the debug info, by variable.
pub fn debug_names(proto: &Proto, an: &Analysis) -> BTreeMap<VarId, String> {
    let mut out = BTreeMap::new();
    if proto.locals.is_empty() { return out; }
    let regs = local_regs(proto);
    let find = |reg: u16, pc: usize, def: bool| -> Option<&str> {
        let mut best: Option<usize> = None;
        for (i, l) in proto.locals.iter().enumerate() {
            if regs[i] != reg || l.name.starts_with('(') { continue; }
            let active = if def { l.start_pc <= pc + 1 && pc < l.end_pc } else { l.start_pc <= pc && pc < l.end_pc };
            if active && best.map_or(true, |b| proto.locals[b].start_pc <= l.start_pc) { best = Some(i); }
        }
        best.map(|i| proto.locals[i].name.as_str())
    };
    for (v, info) in an.vars.iter().enumerate() {
        let name = if let Some(p) = info.param {
            // A 5.5 vararg parameter starts after VARARGPREP.
            find(p, 0, false).or_else(|| find(p, 1, false))
        } else {
            info.def_pcs.iter().find_map(|&pc| find(info.reg, pc, true))
                .or_else(|| info.use_pcs.iter().find_map(|&pc| find(info.reg, pc, false)))
        };
        if let Some(n) = name {
            if is_lua_ident(n) { out.insert(v, n.to_string()); }
        }
    }
    out
}

/// Pick final names.  `kinds` says what each variable holds ('t' table,
/// 'f' function, 'i'/'k'/'v' loop variables, otherwise plain).
pub fn assign(
    vars: &BTreeSet<VarId>,
    params: &[VarId],
    debug: &BTreeMap<VarId, String>,
    kinds: &BTreeMap<VarId, char>,
    avoid: &BTreeSet<String>,
) -> BTreeMap<VarId, String> {
    let mut taken: BTreeSet<String> = avoid.clone();
    let mut out = BTreeMap::new();
    let fresh = |base: &str, taken: &mut BTreeSet<String>| -> String {
        let mut k = 2;
        loop {
            let n = format!("{}_{}", base, k);
            if !taken.contains(&n) { taken.insert(n.clone()); return n; }
            k += 1;
        }
    };
    let mut counters: BTreeMap<&str, usize> = BTreeMap::new();
    let mut generated = |prefix: &'static str, taken: &mut BTreeSet<String>| -> String {
        let c = counters.entry(prefix).or_insert(0);
        loop {
            let n = format!("{}{}", prefix, *c);
            *c += 1;
            if !taken.contains(&n) { taken.insert(n.clone()); return n; }
        }
    };
    let order: Vec<VarId> = params.iter().copied().chain(vars.iter().copied().filter(|v| !params.contains(v))).collect();
    for v in order {
        let name = if let Some(d) = debug.get(&v) {
            if taken.contains(d) { fresh(d, &mut taken) } else { taken.insert(d.clone()); d.clone() }
        } else if params.contains(&v) {
            generated("_p", &mut taken)
        } else {
            let prefix = match kinds.get(&v) {
                Some('t') => "_t",
                Some('f') => "_f",
                Some('i') => "_i",
                Some('k') => "_k",
                _ => "_v",
            };
            generated(prefix, &mut taken)
        };
        out.insert(v, name);
    }
    out
}
