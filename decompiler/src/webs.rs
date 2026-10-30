//! Register dataflow: liveness and *webs*.
//!
//! A web is a maximal set of definitions and uses of one register connected
//! by def-use chains; each web becomes one variable in the output.  Splitting
//! registers into webs is what lets a reused temporary register turn into
//! several independent variables, while a register written on both arms of
//! an `if` stays one variable.
//!
//! Closures capture registers by reference.  While a captured register's
//! upvalue is open (until the scope closes), every later write to that
//! register is visible to the closure, so such writes are merged into the
//! captured web.

use std::collections::HashMap;

use crate::flow::{Flow, Op, Term};
use crate::ir::{Cap, Decoded, Ins, Reg, Rk};

pub type VarId = usize;

#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct RegSet([u64; 4]);

impl RegSet {
    pub fn has(&self, r: Reg) -> bool { r < 256 && self.0[r as usize / 64] >> (r % 64) & 1 == 1 }
    pub fn add(&mut self, r: Reg) { if r < 256 { self.0[r as usize / 64] |= 1 << (r % 64); } }
    pub fn del(&mut self, r: Reg) { if r < 256 { self.0[r as usize / 64] &= !(1 << (r % 64)); } }
    pub fn clear_from(&mut self, r: Reg) { for x in r..256 { self.del(x); } }
    pub fn union(&mut self, o: &RegSet) -> bool {
        let mut ch = false;
        for i in 0..4 { let v = self.0[i] | o.0[i]; ch |= v != self.0[i]; self.0[i] = v; }
        ch
    }
    pub fn iter(&self) -> impl Iterator<Item = Reg> + '_ {
        (0..256u16).filter(move |&r| self.has(r))
    }
}

/// Uses/defs of one op plus the variables they resolved to.
#[derive(Clone, Debug, Default)]
pub struct OpInfo {
    pub uses: Vec<Reg>,
    /// How many of the trailing `uses` are closure captures.
    pub ncaps: usize,
    pub defs: Vec<Reg>,
    pub use_var: Vec<VarId>,
    pub def_var: Vec<VarId>,
    /// Per def: false if the register was captured and still open, i.e. the
    /// write continues the same variable instead of starting a fresh one.
    pub def_fresh: Vec<bool>,
}

impl OpInfo {
    pub fn use_of(&self, r: Reg) -> Option<VarId> {
        self.uses.iter().position(|&u| u == r).map(|i| self.use_var[i])
    }
    pub fn def_of(&self, r: Reg) -> Option<VarId> {
        self.defs.iter().position(|&u| u == r).map(|i| self.def_var[i])
    }
}

#[derive(Clone, Debug, Default)]
pub struct VarInfo {
    pub reg: Reg,
    pub defs: u32,
    pub uses: u32,
    pub captured: bool,
    /// Parameter index if this web includes the incoming parameter.
    pub param: Option<u16>,
    /// Read somewhere before any definition (starts out nil).
    pub undefined: bool,
    /// pcs of the defining instructions.
    pub def_pcs: Vec<usize>,
    /// pcs of some reading instructions.
    pub use_pcs: Vec<usize>,
}

pub struct Analysis {
    pub ops: Vec<Vec<OpInfo>>,
    pub vars: Vec<VarInfo>,
    /// Variables live at entry of each node (register → var).
    pub live_in_vars: Vec<Vec<(Reg, VarId)>>,
    /// Multret consumer pc → producer pc.
    pub pack_producer: HashMap<usize, usize>,
    pub param_vars: Vec<VarId>,
}

fn rk_regs(v: &mut Vec<Reg>, x: Rk) {
    if let Rk::R(r) = x { v.push(r); }
}

/// Registers read/written by one op.  `canon` marks canonical for-loop
/// headers whose register traffic is modelled by the init pseudo-ops.
fn uses_defs(
    d: &Decoded,
    op: Op,
    canon_header: bool,
    pack: &HashMap<usize, usize>,
) -> (Vec<Reg>, usize, Vec<Reg>) {
    let mut u = Vec::new();
    let mut df = Vec::new();
    let mut ncaps = 0;
    let range_to_top = |start: Reg, pc: usize, u: &mut Vec<Reg>| {
        if let Some(&pp) = pack.get(&pc) {
            let top = pack_reg(&d.ins[pp]);
            for r in start..top { u.push(r); }
            u.push(top);
        }
    };
    match op {
        Op::Copy { dst, src } => { u.push(src); df.push(dst); }
        Op::NumForInit { a } => { u.extend([a, a + 1, a + 2]); }
        Op::GenForInit { a, n } => { u.extend(a..a + n); }
        Op::Pc(pc) => match &d.ins[pc] {
            Ins::Move { a, b } => { u.push(*b); df.push(*a); }
            Ins::LoadK { a, .. } | Ins::LoadImm { a, .. } | Ins::LoadBool { a, .. } | Ins::GetUpval { a, .. }
            | Ins::GetGlobal { a, .. } | Ins::NewTable { a } => df.push(*a),
            Ins::LoadNil { a, last } => { for r in *a..=*last { df.push(r); } }
            Ins::GetTabUp { a, key, .. } => { rk_regs(&mut u, *key); df.push(*a); }
            Ins::GetTable { a, t, key } => { u.push(*t); rk_regs(&mut u, *key); df.push(*a); }
            Ins::SetTabUp { key, val, .. } => { rk_regs(&mut u, *key); rk_regs(&mut u, *val); }
            Ins::SetGlobal { a, .. } | Ins::SetUpval { a, .. } => u.push(*a),
            Ins::SetTable { t, key, val } => { u.push(*t); rk_regs(&mut u, *key); rk_regs(&mut u, *val); }
            // Lifted as `A+1 = obj; A = obj[key]`: two reads of obj.
            Ins::SelfOp { a, obj, key } => { u.push(*obj); u.push(*obj); rk_regs(&mut u, *key); df.push(*a + 1); df.push(*a); }
            Ins::Arith { a, l, r, .. } => { rk_regs(&mut u, *l); rk_regs(&mut u, *r); df.push(*a); }
            Ins::Unary { a, b, .. } => { u.push(*b); df.push(*a); }
            Ins::Concat { a, b, c } => { for r in *b..=*c { u.push(r); } df.push(*a); }
            Ins::Cmp { l, r, .. } => { rk_regs(&mut u, *l); rk_regs(&mut u, *r); }
            Ins::Test { a, .. } => u.push(*a),
            Ins::TestSet { b, .. } => u.push(*b),
            Ins::Call { a, nargs, nret } => {
                u.push(*a);
                match nargs {
                    Some(k) => { for r in a + 1..=a + k { u.push(r); } }
                    None => range_to_top(a + 1, pc, &mut u),
                }
                match nret {
                    Some(k) => { for r in *a..a + k { df.push(r); } }
                    None => df.push(*a),
                }
            }
            Ins::TailCall { a, nargs } => {
                u.push(*a);
                match nargs {
                    Some(k) => { for r in a + 1..=a + k { u.push(r); } }
                    None => range_to_top(a + 1, pc, &mut u),
                }
            }
            Ins::Return { a, n } => match n {
                Some(k) => { for r in *a..a + k { u.push(r); } }
                None => range_to_top(*a, pc, &mut u),
            },
            Ins::SetList { a, n, .. } => {
                u.push(*a);
                match n {
                    Some(k) => { for r in a + 1..=a + k { u.push(r); } }
                    None => range_to_top(a + 1, pc, &mut u),
                }
            }
            Ins::ForPrep { .. } => {}
            Ins::ForLoop { var, .. } => df.push(*var),
            Ins::TForCall { a, nvars, base, ctl } => {
                if !canon_header { u.extend([*a, a + 1, a + ctl]); }
                for r in a + base..a + base + nvars { df.push(r); }
            }
            Ins::TForLoop { src, .. } => { if !canon_header { u.push(*src); } }
            Ins::Tbc { a } | Ins::ErrNNil { a, .. } => u.push(*a),
            Ins::TForLoop51 { a, nvars } => {
                // Lowered form tests the R(a+3) it just defined; the lifter
                // refers to that def directly.
                if !canon_header { u.extend([*a, a + 1, a + 2]); }
                for r in a + 3..a + 3 + nvars { df.push(r); }
            }
            Ins::Closure { a, caps, .. } => {
                for c in caps { if let Cap::Reg(r) = c { u.push(*r); ncaps += 1; } }
                df.push(*a);
            }
            Ins::VarArg { a, n } => match n {
                Some(k) => { for r in *a..a + k { df.push(r); } }
                None => df.push(*a),
            },
            Ins::Jmp { .. } | Ins::Close { .. } | Ins::Data | Ins::Unknown => {}
        },
    }
    (u, ncaps, df)
}

/// Register holding a multret pack produced by `ins`.
pub fn pack_reg(ins: &Ins) -> Reg {
    match ins {
        Ins::Call { a, .. } | Ins::VarArg { a, .. } => *a,
        _ => 0,
    }
}

fn sets_top(ins: &Ins) -> bool {
    matches!(ins, Ins::Call { nret: None, .. } | Ins::VarArg { n: None, .. })
}

fn uses_top(ins: &Ins) -> bool {
    matches!(ins,
        Ins::Call { nargs: None, .. } | Ins::TailCall { nargs: None, .. }
        | Ins::Return { n: None, .. } | Ins::SetList { n: None, .. })
}

struct Dsu { p: Vec<usize> }
impl Dsu {
    fn new() -> Self { Dsu { p: Vec::new() } }
    fn make(&mut self) -> usize { self.p.push(self.p.len()); self.p.len() - 1 }
    fn find(&mut self, mut x: usize) -> usize {
        while self.p[x] != x { self.p[x] = self.p[self.p[x]]; x = self.p[x]; }
        x
    }
    fn union(&mut self, a: usize, b: usize) { let (a, b) = (self.find(a), self.find(b)); if a != b { self.p[b] = a; } }
}

pub fn analyze(d: &Decoded, flow: &Flow, numparams: u16) -> Analysis {
    let nn = flow.nodes.len();

    // ── Multret pairing ──────────────────────────────────────────────────
    // A CALL/VARARG that leaves its results "up to top" is consumed by the
    // next top-using instruction.  Jumps don't touch top, so a pending
    // producer carries into a node whose only predecessor ends with it.
    let mut pack: HashMap<usize, usize> = HashMap::new();
    let mut top_out: Vec<Option<usize>> = vec![None; nn];
    for &n in &flow.rpo {
        let node = &flow.nodes[n];
        let mut last_top: Option<usize> = match node.preds.as_slice() {
            [p] if flow.nodes[*p].succs.len() == 1 => top_out[*p],
            _ => None,
        };
        for op in &node.ops {
            if let Op::Pc(pc) = *op {
                let ins = &d.ins[pc];
                if uses_top(ins) {
                    if let Some(p) = last_top.take() { pack.insert(pc, p); }
                }
                if sets_top(ins) { last_top = Some(pc); }
            }
        }
        top_out[n] = last_top;
    }

    // Canonical generic-for header pcs.
    let canon: Vec<bool> = flow.nodes.iter().map(|n| matches!(n.term, Term::GenFor { .. })).collect();

    let mut ops: Vec<Vec<OpInfo>> = flow.nodes.iter().enumerate().map(|(id, node)| {
        node.ops.iter().map(|&op| {
            let (uses, ncaps, defs) = uses_defs(d, op, canon[id], &pack);
            OpInfo { uses, ncaps, defs, use_var: vec![], def_var: vec![], def_fresh: vec![] }
        }).collect()
    }).collect();

    // Upvalue closing points.
    let closes = |op: Op| -> Option<Reg> {
        match op {
            Op::Pc(pc) => match &d.ins[pc] {
                Ins::Jmp { close: Some(c), .. } => Some(*c),
                Ins::Close { a } => Some(*a),
                Ins::Return { .. } | Ins::TailCall { .. } => Some(0),
                _ => None,
            },
            _ => None,
        }
    };

    // ── Open-capture analysis (forward) ──────────────────────────────────
    let mut open_in = vec![RegSet::default(); nn];
    let mut open_out = vec![RegSet::default(); nn];
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &flow.rpo {
            let mut s = RegSet::default();
            for &p in &flow.nodes[b].preds { s.union(&open_out[p]); }
            open_in[b] = s;
            for (i, &op) in flow.nodes[b].ops.iter().enumerate() {
                let info = &ops[b][i];
                for &r in &info.uses[info.uses.len() - info.ncaps..] { s.add(r); }
                if let Some(c) = closes(op) { s.clear_from(c); }
            }
            if s != open_out[b] { open_out[b] = s; changed = true; }
        }
    }

    // Defs made while the register is captured also read it (merge-use).
    let mut merge: Vec<Vec<Vec<bool>>> = Vec::with_capacity(nn);
    for b in 0..nn {
        let mut s = open_in[b];
        let mut mb = Vec::new();
        for (i, &op) in flow.nodes[b].ops.iter().enumerate() {
            let info = &ops[b][i];
            for &r in &info.uses[info.uses.len() - info.ncaps..] { s.add(r); }
            mb.push(info.defs.iter().map(|&r| s.has(r)).collect());
            if let Some(c) = closes(op) { s.clear_from(c); }
        }
        merge.push(mb);
    }

    // ── Liveness (backward) ──────────────────────────────────────────────
    let mut gen_set = vec![RegSet::default(); nn];
    let mut kill = vec![RegSet::default(); nn];
    for b in 0..nn {
        let mut g = RegSet::default();
        let mut k = RegSet::default();
        for (i, info) in ops[b].iter().enumerate() {
            for &r in &info.uses { if !k.has(r) { g.add(r); } }
            for (j, &r) in info.defs.iter().enumerate() {
                if merge[b][i][j] && !k.has(r) { g.add(r); }
                k.add(r);
            }
        }
        gen_set[b] = g;
        kill[b] = k;
    }
    let mut live_in = vec![RegSet::default(); nn];
    let mut changed = true;
    while changed {
        changed = false;
        for &b in flow.rpo.iter().rev() {
            let mut out = RegSet::default();
            for &s in &flow.nodes[b].succs { out.union(&live_in[s]); }
            let mut inn = gen_set[b];
            for i in 0..4 { inn.0[i] |= out.0[i] & !kill[b].0[i]; }
            if inn != live_in[b] { live_in[b] = inn; changed = true; }
        }
    }

    // ── Webs ─────────────────────────────────────────────────────────────
    let mut dsu = Dsu::new();
    let mut uninit: HashMap<Reg, usize> = HashMap::new();
    let mut entry_web: HashMap<(usize, Reg), usize> = HashMap::new();
    let mut get_uninit = |dsu: &mut Dsu, r: Reg| *uninit.entry(r).or_insert_with(|| dsu.make());
    // Parameters get their own roots.
    let param_web: Vec<usize> = (0..numparams).map(|_| dsu.make()).collect();
    let mut web_reg: HashMap<usize, Reg> = HashMap::new();
    for (i, &w) in param_web.iter().enumerate() { web_reg.insert(w, i as Reg); }

    let mut use_web: Vec<Vec<Vec<usize>>> = vec![Vec::new(); nn];
    let mut def_web: Vec<Vec<Vec<usize>>> = vec![Vec::new(); nn];
    let mut def_site_pc: HashMap<usize, usize> = HashMap::new();
    let mut cap_webs: Vec<usize> = Vec::new();
    let mut undefined_webs: Vec<usize> = Vec::new();

    for &b in &flow.rpo {
        let mut cur: HashMap<Reg, usize> = HashMap::new();
        for r in live_in[b].iter() {
            let w = *entry_web.entry((b, r)).or_insert_with(|| dsu.make());
            web_reg.insert(w, r);
            cur.insert(r, w);
        }
        let node_ops = flow.nodes[b].ops.clone();
        for (i, &op) in node_ops.iter().enumerate() {
            let info = &ops[b][i];
            let mut uw = Vec::with_capacity(info.uses.len());
            for (k, &r) in info.uses.iter().enumerate() {
                let w = match cur.get(&r) {
                    Some(&w) => w,
                    None => {
                        let w = get_uninit(&mut dsu, r);
                        web_reg.insert(w, r);
                        undefined_webs.push(w);
                        cur.insert(r, w);
                        w
                    }
                };
                if k >= info.uses.len() - info.ncaps { cap_webs.push(w); }
                uw.push(w);
            }
            let mut dw = Vec::with_capacity(info.defs.len());
            for (j, &r) in info.defs.iter().enumerate() {
                let w = dsu.make();
                web_reg.insert(w, r);
                if let Op::Pc(pc) = op { def_site_pc.insert(w, pc); }
                if merge[b][i][j] {
                    let prev = match cur.get(&r) {
                        Some(&p) => p,
                        None => { let p = get_uninit(&mut dsu, r); undefined_webs.push(p); p }
                    };
                    dsu.union(prev, w);
                }
                cur.insert(r, w);
                dw.push(w);
            }
            use_web[b].push(uw);
            def_web[b].push(dw);
        }
        for &s in &flow.nodes[b].succs {
            for r in live_in[s].iter() {
                let ew = *entry_web.entry((s, r)).or_insert_with(|| dsu.make());
                web_reg.insert(ew, r);
                let w = match cur.get(&r) {
                    Some(&w) => w,
                    None => { let w = get_uninit(&mut dsu, r); undefined_webs.push(w); w }
                };
                dsu.union(w, ew);
            }
        }
    }
    // Function entry: incoming parameters (or undefined registers).
    for r in live_in[flow.entry].iter() {
        if let Some(&ew) = entry_web.get(&(flow.entry, r)) {
            if (r as u16) < numparams {
                dsu.union(param_web[r as usize], ew);
            } else {
                let u = get_uninit(&mut dsu, r);
                undefined_webs.push(u);
                dsu.union(u, ew);
            }
        }
    }

    // ── Compress webs into variables ─────────────────────────────────────
    let mut var_of_root: HashMap<usize, VarId> = HashMap::new();
    let mut vars: Vec<VarInfo> = Vec::new();
    let mut var_of = |dsu: &mut Dsu, w: usize, vars: &mut Vec<VarInfo>| -> VarId {
        let root = dsu.find(w);
        *var_of_root.entry(root).or_insert_with(|| {
            vars.push(VarInfo { reg: web_reg.get(&w).copied().unwrap_or(0), ..Default::default() });
            vars.len() - 1
        })
    };
    let param_vars: Vec<VarId> = param_web.iter().enumerate().map(|(i, &w)| {
        let v = var_of(&mut dsu, w, &mut vars);
        vars[v].param = Some(i as u16);
        vars[v].reg = i as Reg;
        v
    }).collect();
    for b in 0..nn {
        for i in 0..ops[b].len() {
            if use_web[b].len() <= i { continue; }
            let uv: Vec<VarId> = use_web[b][i].iter().map(|&w| var_of(&mut dsu, w, &mut vars)).collect();
            let dv: Vec<VarId> = def_web[b][i].iter().map(|&w| var_of(&mut dsu, w, &mut vars)).collect();
            let op_pc = match flow.nodes[b].ops[i] { Op::Pc(pc) => Some(pc), _ => None };
            for &v in &uv {
                vars[v].uses += 1;
                if let Some(pc) = op_pc {
                    if vars[v].use_pcs.len() < 8 { vars[v].use_pcs.push(pc); }
                }
            }
            for (k, &v) in dv.iter().enumerate() {
                vars[v].defs += 1;
                if let Some(&pc) = def_site_pc.get(&def_web[b][i][k]) {
                    if vars[v].def_pcs.len() < 8 { vars[v].def_pcs.push(pc); }
                }
            }
            ops[b][i].def_fresh = merge[b][i].iter().map(|&m| !m).collect();
            ops[b][i].use_var = uv;
            ops[b][i].def_var = dv;
        }
    }
    for w in cap_webs { let v = var_of(&mut dsu, w, &mut vars); vars[v].captured = true; }
    for w in undefined_webs { let v = var_of(&mut dsu, w, &mut vars); vars[v].undefined = true; }
    for v in &param_vars { vars[*v].undefined = false; }

    let live_in_vars: Vec<Vec<(Reg, VarId)>> = (0..nn).map(|b| {
        live_in[b].iter().filter_map(|r| {
            entry_web.get(&(b, r)).map(|&w| (r, var_of(&mut dsu, w, &mut vars)))
        }).collect()
    }).collect();

    Analysis { ops, vars, live_in_vars, pack_producer: pack, param_vars }
}
