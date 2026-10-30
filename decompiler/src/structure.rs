//! Turn the lifted control-flow graph into structured Lua statements.

use std::collections::{BTreeMap, BTreeSet};

use lua_ast::{BinOp, Expr, Stat};

use crate::flow::{post_dominators, Flow, NodeId, PostDom, Term};
use crate::lift::{negate, pseudo, pseudo_args, var, IrBlock};
use crate::webs::VarId;

pub fn node_label(n: NodeId) -> String { format!("@n{}", n) }
pub fn cont_label(l: usize) -> String { format!("@c{}", l) }

// ---------------------------------------------------------------------------
// Compound conditions
// ---------------------------------------------------------------------------

/// Merge chains of condition-only nodes into single `and`/`or` conditions.
/// Returns the per-node "empty" flags for flow rebuilding.
pub fn merge_conditions(flow: &mut Flow, blocks: &mut [IrBlock]) {
    let n = flow.nodes.len();
    let mut changed = true;
    while changed {
        changed = false;
        for x in 0..n {
            if !flow.reachable(x) || !matches!(flow.nodes[x].term, Term::Cond { .. }) { continue; }
            if flow.nodes[x].succs.len() != 2 { continue; }
            let (xt, xf) = (flow.nodes[x].succs[0], flow.nodes[x].succs[1]);
            for (y, y_is_t) in [(xt, true), (xf, false)] {
                if y == x || !matches!(flow.nodes[y].term, Term::Cond { .. }) { continue; }
                if !blocks[y].stmts.is_empty() || flow.nodes[y].succs.len() != 2 { continue; }
                let preds: BTreeSet<NodeId> = flow.nodes[y].preds.iter().copied().collect();
                if preds.len() != 1 || !preds.contains(&x) { continue; }
                let (yt, yf) = (flow.nodes[y].succs[0], flow.nodes[y].succs[1]);
                if yt == y || yf == y { continue; }
                let cx = blocks[x].cond.clone().unwrap_or(Expr::True);
                let cy = blocks[y].cond.clone().unwrap_or(Expr::True);
                let other = if y_is_t { xf } else { xt };
                let (cond, t, f) = if y_is_t && yf == other {
                    (and(cx, cy), yt, xf)
                } else if y_is_t && yt == other {
                    (and(cx, negate(cy)), yf, xf)
                } else if !y_is_t && yt == other {
                    (or(cx, cy), xt, yf)
                } else if !y_is_t && yf == other {
                    (or(cx, negate(cy)), xt, yt)
                } else {
                    continue;
                };
                blocks[x].cond = Some(cond);
                flow.nodes[x].succs = vec![t, f];
                // y becomes unreachable; fix pred lists incrementally.
                flow.nodes[y].preds.clear();
                for s in [yt, yf] {
                    flow.nodes[s].preds.retain(|&p| p != y);
                    flow.nodes[s].preds.push(x);
                }
                flow.nodes[y].succs.clear();
                blocks[y] = IrBlock::default();
                changed = true;
                break;
            }
        }
    }
}

fn and(a: Expr, b: Expr) -> Expr { Expr::BinOp { op: BinOp::And, lhs: Box::new(a), rhs: Box::new(b) } }
fn or(a: Expr, b: Expr) -> Expr { Expr::BinOp { op: BinOp::Or, lhs: Box::new(a), rhs: Box::new(b) } }

// ---------------------------------------------------------------------------
// Loops
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Kind {
    NumFor,
    GenFor,
    While,
    Repeat { latch: NodeId },
    Infinite,
}

#[derive(Clone, Debug)]
struct Shape {
    header: NodeId,
    kind: Kind,
    follow: Option<NodeId>,
    /// Reaching this node ends an iteration.
    cont: NodeId,
}

pub struct Structurer<'a> {
    flow: &'a Flow,
    blocks: &'a [IrBlock],
    live_in: &'a [Vec<(u16, VarId)>],
    shapes: Vec<Shape>,
    /// Loop bodies extended with their break/return blocks.
    in_body: Vec<Vec<bool>>,
    /// Innermost (extended) loop of each node.
    loop_of: Vec<Option<usize>>,
    fn_pdom: PostDom,
    loop_pdom: BTreeMap<usize, PostDom>,
    emitted: usize,
    budget: usize,
    pub failed: bool,
}

impl<'a> Structurer<'a> {
    pub fn new(flow: &'a Flow, blocks: &'a [IrBlock], live_in: &'a [Vec<(u16, VarId)>]) -> Self {
        let total: usize = blocks.iter().map(|b| b.stmts.len() + 1).sum();
        let shapes: Vec<Shape> = (0..flow.loops.len()).map(|l| classify(flow, blocks, l)).collect();

        // A natural loop only holds nodes that can loop back.  Blocks that
        // leave the loop (`x = 1; break`, `return`) belong inside it too:
        // everything the header dominates except the code after the loop.
        let n = flow.nodes.len();
        let mut dom_children: Vec<Vec<NodeId>> = vec![Vec::new(); n];
        for &x in &flow.rpo {
            let p = flow.idom[x];
            if p != x && p != usize::MAX { dom_children[p].push(x); }
        }
        let mut in_body: Vec<Vec<bool>> = flow.loops.iter().map(|l| l.in_body.clone()).collect();
        for (l, sh) in shapes.iter().enumerate() {
            let mut stack = vec![sh.header];
            while let Some(x) = stack.pop() {
                if Some(x) == sh.follow { continue; }
                in_body[l][x] = true;
                stack.extend(dom_children[x].iter().copied());
            }
        }
        // Innermost loop per node: smallest extended body containing it.
        let mut order: Vec<usize> = (0..flow.loops.len()).collect();
        order.sort_by_key(|&l| in_body[l].iter().filter(|&&b| b).count());
        let mut loop_of: Vec<Option<usize>> = vec![None; n];
        for &l in &order {
            for x in 0..n {
                if in_body[l][x] && loop_of[x].is_none() { loop_of[x] = Some(l); }
            }
        }
        let fn_pdom = post_dominators(
            flow,
            &|x| flow.reachable(x),
            &|x| {
                let node = &flow.nodes[x];
                if node.succs.is_empty() { vec![None] } else { node.succs.iter().map(|&s| Some(s)).collect() }
            },
        );
        let mut loop_pdom = BTreeMap::new();
        for (l, sh) in shapes.iter().enumerate() {
            let body = &in_body[l];
            let cont = sh.cont;
            let latch_sink = matches!(sh.kind, Kind::Repeat { .. });
            let pd = post_dominators(
                flow,
                &|x| body[x],
                &|x| {
                    if latch_sink && x == cont { return vec![None]; }
                    flow.nodes[x].succs.iter().filter_map(|&s| {
                        if s == cont { Some(None) }
                        else if body[s] { Some(Some(s)) }
                        else { None }
                    }).collect()
                },
            );
            loop_pdom.insert(l, pd);
        }
        Structurer {
            flow, blocks, live_in, shapes, in_body, loop_of, fn_pdom, loop_pdom,
            emitted: 0,
            budget: total * 4 + 4000,
            failed: false,
        }
    }

    pub fn run(&mut self) -> Vec<Stat> {
        let mut ctx = Vec::new();
        self.seq(self.flow.entry, None, &mut ctx, false)
    }

    /// Where control rejoins after the two-way branch at `n`.
    fn follow(&self, n: NodeId, stop: Option<NodeId>) -> Option<NodeId> {
        let scope = self.loop_of[n];
        let pd = match scope { Some(l) => &self.loop_pdom[&l], None => &self.fn_pdom };
        let f = match pd.ipdom[n] {
            None => return None,
            Some(None) => return scope.map(|l| self.shapes[l].cont),
            Some(Some(f)) => f,
        };
        if let Some(s) = stop {
            if s != f {
                let s_is_scope_end = scope.map_or(false, |l| self.shapes[l].cont == s);
                if !s_is_scope_end && !pd.post_dominates(Some(s), f) {
                    return Some(s);
                }
            }
        }
        Some(f)
    }

    /// `break`/`goto` needed to reach `n` from inside the current loops.
    fn loop_jump(&self, n: NodeId, ctx: &[usize]) -> Option<Stat> {
        for (depth, &l) in ctx.iter().rev().enumerate() {
            let sh = &self.shapes[l];
            if Some(n) == sh.follow {
                return Some(if depth == 0 { Stat::Break } else { Stat::Goto(node_label(n)) });
            }
            if n == sh.cont {
                return Some(Stat::Goto(cont_label(l)));
            }
        }
        if let Some(&l) = ctx.last() {
            if !self.in_body[l][n] {
                return Some(Stat::Goto(node_label(n)));
            }
        }
        None
    }

    fn seq(&mut self, start: NodeId, stop: Option<NodeId>, ctx: &mut Vec<usize>, header_first: bool) -> Vec<Stat> {
        let mut out = Vec::new();
        let mut n = start;
        let mut first = true;
        let mut seen = BTreeSet::new();
        loop {
            if self.failed { break; }
            let at_header = first && header_first;
            first = false;
            if !at_header {
                if Some(n) == stop { break; }
                if let Some(j) = self.loop_jump(n, ctx) { out.push(j); break; }
                if let Some(&l) = self.flow.loop_by_header.get(&n) {
                    if !ctx.contains(&l) {
                        match self.emit_loop(l, ctx, &mut out) {
                            Some(f) => { n = f; continue; }
                            None => break,
                        }
                    }
                }
            }
            if !seen.insert(n) {
                out.push(Stat::Goto(node_label(n)));
                break;
            }
            out.push(Stat::Label(node_label(n)));
            let blk = &self.blocks[n];
            self.emitted += blk.stmts.len() + 1;
            if self.emitted > self.budget { self.failed = true; break; }
            out.extend(blk.stmts.iter().cloned());
            let node = &self.flow.nodes[n];
            match node.term {
                Term::Cond { .. } if node.succs.len() == 2 => {
                    let cond = blk.cond.clone().unwrap_or(Expr::True);
                    let (t, f) = (node.succs[0], node.succs[1]);
                    let fol = self.follow(n, stop);
                    let inner = fol.or(stop);
                    let then_b = self.seq(t, inner, ctx, false);
                    let else_b = self.seq(f, inner, ctx, false);
                    out.push(Stat::If { branches: vec![(cond, then_b)], else_body: Some(else_b) });
                    match fol { Some(x) => n = x, None => break }
                }
                _ => match node.succs.first() {
                    Some(&s) => n = s,
                    None => break,
                },
            }
        }
        out
    }

    fn emit_loop(&mut self, l: usize, ctx: &mut Vec<usize>, out: &mut Vec<Stat>) -> Option<NodeId> {
        let sh = self.shapes[l].clone();
        let h = sh.header;
        let hb = &self.blocks[h];
        let succs = self.flow.nodes[h].succs.clone();
        let in_body = self.in_body[l].clone();
        let carried: Vec<Expr> = self.live_in[h].iter().map(|&(_, v)| var(v)).collect();

        // For-loop init pseudo-statement (from the node that enters the loop).
        let take_init = |out: &mut Vec<Stat>, name: &str| -> Option<Vec<Expr>> {
            let pos = out.iter().rposition(|s| matches!(s, Stat::Call(e) if pseudo_args(e, name).is_some()))?;
            if out[pos + 1..].iter().any(|s| !matches!(s, Stat::Label(_))) { return None; }
            match out.remove(pos) {
                Stat::Call(e) => pseudo_args(&e, name).cloned(),
                _ => None,
            }
        };

        ctx.push(l);
        let stat = match sh.kind {
            Kind::NumFor => {
                let init = take_init(out, "@fornum").unwrap_or_else(|| vec![Expr::Nil, Expr::Nil, Expr::Nil]);
                let mut body = self.seq(succs[0], Some(h), ctx, false);
                body.push(Stat::Label(cont_label(l)));
                let step = init[2].clone();
                let step = if matches!(step, Expr::Integer(1)) || matches!(step, Expr::Float(f) if f == 1.0) { None } else { Some(step) };
                let v = hb.loop_vars.first().map(|&v| format!("@v{}", v)).unwrap_or_else(|| "_".into());
                Stat::NumFor { var: v, from: init[0].clone(), to: init[1].clone(), step, body }
            }
            Kind::GenFor => {
                let mut iters = take_init(out, "@forgen").unwrap_or_else(|| vec![Expr::Nil]);
                while iters.len() > 1 && matches!(iters.last(), Some(Expr::Nil)) { iters.pop(); }
                let mut body = self.seq(succs[0], Some(h), ctx, false);
                body.push(Stat::Label(cont_label(l)));
                let vars = hb.loop_vars.iter().map(|&v| format!("@v{}", v)).collect();
                Stat::GenFor { vars, iters, body }
            }
            Kind::While => {
                let cond = hb.cond.clone().unwrap_or(Expr::True);
                let (cond, entry) = if in_body[succs[0]] { (cond, succs[0]) } else { (negate(cond), succs[1]) };
                let mut body = self.seq(entry, Some(h), ctx, false);
                body.push(Stat::Label(cont_label(l)));
                Stat::While { cond, body }
            }
            Kind::Repeat { latch } => {
                let mut body = if latch == h {
                    vec![]
                } else {
                    self.seq(h, Some(latch), ctx, false)
                };
                body.push(Stat::Label(cont_label(l)));
                body.push(Stat::Label(node_label(latch)));
                body.extend(self.blocks[latch].stmts.iter().cloned());
                self.emitted += self.blocks[latch].stmts.len();
                let lc = self.blocks[latch].cond.clone().unwrap_or(Expr::True);
                let exits_on_true = Some(self.flow.nodes[latch].succs[0]) == sh.follow;
                let cond = if exits_on_true { lc } else { negate(lc) };
                Stat::Repeat { body, cond }
            }
            Kind::Infinite => {
                let mut body = self.seq(h, Some(h), ctx, true);
                body.push(Stat::Label(cont_label(l)));
                Stat::While { cond: Expr::True, body }
            }
        };
        ctx.pop();
        if !carried.is_empty() {
            out.push(Stat::Call(pseudo("@uses", carried)));
        }
        out.push(stat);
        sh.follow
    }
}

fn classify(flow: &Flow, blocks: &[IrBlock], l: usize) -> Shape {
    let lp = &flow.loops[l];
    let h = lp.header;
    let node = &flow.nodes[h];
    match node.term {
        Term::NumFor { .. } if node.succs.len() == 2 => {
            return Shape { header: h, kind: Kind::NumFor, follow: Some(node.succs[1]), cont: h };
        }
        Term::GenFor { .. } if node.succs.len() == 2 => {
            return Shape { header: h, kind: Kind::GenFor, follow: Some(node.succs[1]), cont: h };
        }
        _ => {}
    }
    if matches!(node.term, Term::Cond { .. }) && node.succs.len() == 2 && blocks[h].stmts.is_empty() {
        let (a, b) = (node.succs[0], node.succs[1]);
        if lp.in_body[a] != lp.in_body[b] {
            let out = if lp.in_body[a] { b } else { a };
            return Shape { header: h, kind: Kind::While, follow: Some(out), cont: h };
        }
    }
    if lp.latches.len() == 1 {
        let latch = lp.latches[0];
        let ln = &flow.nodes[latch];
        if matches!(ln.term, Term::Cond { .. }) && ln.succs.len() == 2 {
            let (a, b) = (ln.succs[0], ln.succs[1]);
            let out = if a == h && !lp.in_body[b] { Some(b) } else if b == h && !lp.in_body[a] { Some(a) } else { None };
            if let Some(out) = out {
                return Shape { header: h, kind: Kind::Repeat { latch }, follow: Some(out), cont: latch };
            }
        }
    }
    // while true: pick the most common exit target.
    let mut exits: BTreeMap<NodeId, usize> = BTreeMap::new();
    for &x in &lp.body {
        for &s in &flow.nodes[x].succs {
            if !lp.in_body[s] { *exits.entry(s).or_default() += 1; }
        }
    }
    let follow = exits.iter()
        .max_by(|a, b| a.1.cmp(b.1).then(flow.rpo_index[*b.0].cmp(&flow.rpo_index[*a.0])))
        .map(|(&s, _)| s);
    Shape { header: h, kind: Kind::Infinite, follow, cont: h }
}

/// Luau FORGPREP: a non-function iterator is iterated by its `__iter`
/// metamethod, or like `next` (the built-in table traversal).
///
/// ```lua
/// if type(f) ~= "function" then
///   local __mt = getmetatable(f)
///   if __mt and __mt.__iter then f, s, c = __mt.__iter(f) else f, s, c = next, f, nil end
/// end
/// ```
fn luau_iter_setup([f, s, c]: [Expr; 3]) -> Stat {
    let name = |n: &str| Expr::Name(n.into());
    let call = |func: Expr, args: Vec<Expr>| Expr::Call { func: Box::new(func), args };
    let field = |t: Expr, k: &str| Expr::Index { table: Box::new(t), key: Box::new(Expr::Str(k.as_bytes().to_vec())) };
    let triple = vec![f.clone(), s, c];
    let is_fn = Expr::BinOp {
        op: BinOp::Ne,
        lhs: Box::new(call(name("type"), vec![f.clone()])),
        rhs: Box::new(Expr::Str(b"function".to_vec())),
    };
    let has_iter = Expr::BinOp { op: BinOp::And, lhs: Box::new(name("__mt")), rhs: Box::new(field(name("__mt"), "__iter")) };
    Stat::If {
        branches: vec![(is_fn, vec![
            Stat::Local { names: vec!["__mt".into()], values: vec![call(name("getmetatable"), vec![f.clone()])] },
            Stat::If {
                branches: vec![(has_iter, vec![Stat::Assign { lhs: triple.clone(), rhs: vec![call(field(name("__mt"), "__iter"), vec![f.clone()])] }])],
                else_body: Some(vec![Stat::Assign { lhs: triple, rhs: vec![name("next"), f, Expr::Nil] }]),
            },
        ])],
        else_body: None,
    }
}

/// Fallback for irreducible or unstructurable code: one label per node and
/// explicit gotos (valid Lua 5.2+).  For loops are lowered to their VM
/// semantics using hidden variables numbered from `next_var`.  `luau`: a
/// generic for's iterator may be a table (generalized iteration).
pub fn flat(flow: &Flow, blocks: &[IrBlock], next_var: &mut usize, boxed: &BTreeSet<VarId>, luau: bool) -> Vec<Stat> {
    let new_box = |e: Expr| Expr::Table(vec![lua_ast::TableField::ValueField(e)]);
    let v = |id: usize| Expr::Name(format!("@v{}", id));
    let bin = |op: BinOp, a: Expr, b: Expr| Expr::BinOp { op, lhs: Box::new(a), rhs: Box::new(b) };
    // Hidden loop state per for-loop header.
    let mut hidden: BTreeMap<NodeId, [usize; 3]> = BTreeMap::new();
    for &n in &flow.rpo {
        if matches!(flow.nodes[n].term, Term::NumFor { .. } | Term::GenFor { .. }) {
            hidden.insert(n, [*next_var, *next_var + 1, *next_var + 2]);
            *next_var += 3;
        }
    }
    let mut out = Vec::new();
    let order = &flow.rpo;
    for (i, &n) in order.iter().enumerate() {
        out.push(Stat::Label(node_label(n)));
        let node = &flow.nodes[n];
        let succ_hidden = node.succs.first().and_then(|s| hidden.get(s)).copied();
        for s in &blocks[n].stmts {
            let init = match s {
                Stat::Call(e) => pseudo_args(e, "@fornum").map(|a| (true, a.clone()))
                    .or_else(|| pseudo_args(e, "@forgen").map(|a| (false, a.clone()))),
                _ => None,
            };
            match (init, succ_hidden) {
                (Some((numeric, args)), Some(h)) => {
                    out.push(Stat::Assign { lhs: vec![v(h[0]), v(h[1]), v(h[2])], rhs: args });
                    if numeric {
                        // FORPREP: idx = idx - step
                        out.push(Stat::Assign { lhs: vec![v(h[0])], rhs: vec![bin(BinOp::Sub, v(h[0]), v(h[2]))] });
                    } else if luau {
                        out.push(luau_iter_setup([v(h[0]), v(h[1]), v(h[2])]));
                    }
                }
                _ => out.push(s.clone()),
            }
        }
        let next = order.get(i + 1).copied();
        let goto = |t: NodeId| if Some(t) == next { vec![] } else { vec![Stat::Goto(node_label(t))] };
        match node.term {
            Term::Cond { .. } if node.succs.len() == 2 => {
                let c = blocks[n].cond.clone().unwrap_or(Expr::True);
                let (t, f) = (node.succs[0], node.succs[1]);
                out.push(Stat::If { branches: vec![(c, vec![Stat::Goto(node_label(t))])], else_body: None });
                out.extend(goto(f));
            }
            Term::NumFor { .. } if node.succs.len() == 2 => {
                // FORLOOP: idx += step; if in range then var = idx; goto body
                let h = hidden[&n];
                let (body, exit) = (node.succs[0], node.succs[1]);
                out.push(Stat::Assign { lhs: vec![v(h[0])], rhs: vec![bin(BinOp::Add, v(h[0]), v(h[2]))] });
                let up = bin(BinOp::And, bin(BinOp::Lt, Expr::Integer(0), v(h[2])), bin(BinOp::Le, v(h[0]), v(h[1])));
                let down = bin(BinOp::And, bin(BinOp::Le, v(h[2]), Expr::Integer(0)), bin(BinOp::Le, v(h[1]), v(h[0])));
                let mut then_b = Vec::new();
                if let Some(&lv) = blocks[n].loop_vars.first() {
                    // A captured loop variable is a fresh variable per iteration.
                    let val = if boxed.contains(&lv) { new_box(v(h[0])) } else { v(h[0]) };
                    then_b.push(Stat::Assign { lhs: vec![v(lv)], rhs: vec![val] });
                }
                then_b.push(Stat::Goto(node_label(body)));
                out.push(Stat::If { branches: vec![(bin(BinOp::Or, up, down), then_b)], else_body: None });
                out.extend(goto(exit));
            }
            Term::GenFor { .. } if node.succs.len() == 2 => {
                // vars = f(s, c); if vars[1] == nil then exit; c = vars[1]; goto body
                let h = hidden[&n];
                let (body, exit) = (node.succs[0], node.succs[1]);
                // Captured loop variables get fresh boxes, filled from temporaries.
                let mut boxes = Vec::new();
                let lvs: Vec<Expr> = blocks[n].loop_vars.iter().map(|&x| {
                    if boxed.contains(&x) {
                        let t = *next_var;
                        *next_var += 1;
                        boxes.push((x, t));
                        v(t)
                    } else {
                        v(x)
                    }
                }).collect();
                let first = lvs.first().cloned().unwrap_or(Expr::Nil);
                out.push(Stat::Assign {
                    lhs: lvs.clone(),
                    rhs: vec![Expr::Call { func: Box::new(v(h[0])), args: vec![v(h[1]), v(h[2])] }],
                });
                out.push(Stat::If {
                    branches: vec![(bin(BinOp::Eq, first.clone(), Expr::Nil), vec![Stat::Goto(node_label(exit))])],
                    else_body: None,
                });
                out.push(Stat::Assign { lhs: vec![v(h[2])], rhs: vec![first] });
                for (x, t) in boxes {
                    out.push(Stat::Assign { lhs: vec![v(x)], rhs: vec![new_box(v(t))] });
                }
                out.extend(goto(body));
            }
            _ => {
                if let Some(&s) = node.succs.first() { out.extend(goto(s)); }
            }
        }
    }
    out
}
