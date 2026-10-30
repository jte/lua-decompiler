//! Basic blocks, dominators, post-dominators and loops for one function.

use std::collections::BTreeMap;

use crate::ir::{self, Decoded, Ins, Reg};

pub type NodeId = usize;

/// One operation inside a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    /// The instruction at this pc.
    Pc(usize),
    /// `dst := src` on one edge of a TESTSET (or a lowered TFORLOOP).
    Copy { dst: Reg, src: Reg },
    /// Start of a canonical numeric for: consumes R(a), R(a+1), R(a+2).
    NumForInit { a: Reg },
    /// Start of a canonical generic for: consumes R(a)..R(a+n-1) (n = 3, or 4
    /// in 5.4 with the closing value).
    GenForInit { a: Reg, n: u16 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// One successor (or none, for a dangling jump out of the code).
    Goto,
    /// Two-way branch decided by the last op (`succs[0]` when the condition
    /// expression is true, `succs[1]` otherwise).  `cond_pc` is the deciding
    /// instruction.
    Cond { cond_pc: usize },
    /// `return` / tail call (or falls off the end).
    Exit,
    /// Canonical FORLOOP header: `succs = [body, exit]`.
    NumFor { a: Reg, pc: usize },
    /// Canonical generic-for header: `succs = [body, exit]`.
    GenFor { a: Reg, nvars: u16, pc: usize },
}

#[derive(Clone, Debug)]
pub struct Node {
    pub ops: Vec<Op>,
    pub term: Term,
    pub succs: Vec<NodeId>,
    pub preds: Vec<NodeId>,
    /// First pc of the node (for ordering/diagnostics); synthetic nodes use
    /// the pc of the instruction that created them.
    pub pc: usize,
}

pub struct Flow {
    pub nodes: Vec<Node>,
    pub entry: NodeId,
    /// Reverse postorder of reachable nodes.
    pub rpo: Vec<NodeId>,
    /// `rpo_index[n]` (usize::MAX if unreachable).
    pub rpo_index: Vec<usize>,
    /// Immediate dominators (entry maps to itself; unreachable = usize::MAX).
    pub idom: Vec<NodeId>,
    pub loops: Vec<Loop>,
    /// Innermost loop containing each node.
    pub loop_of: Vec<Option<usize>>,
    /// Loop index by header.
    pub loop_by_header: BTreeMap<NodeId, usize>,
    /// True if some cycle has no dominating header.
    pub irreducible: bool,
}

#[derive(Clone, Debug)]
pub struct Loop {
    pub header: NodeId,
    /// Sources of back edges into the header.
    pub latches: Vec<NodeId>,
    /// Body nodes (including the header), sorted.
    pub body: Vec<NodeId>,
    pub in_body: Vec<bool>,
    pub parent: Option<usize>,
    pub depth: usize,
}

impl Flow {
    pub fn build(d: &Decoded) -> Flow {
        let n = d.ins.len();
        let mut nodes: Vec<Node> = Vec::new();
        if n == 0 {
            nodes.push(Node { ops: vec![], term: Term::Exit, succs: vec![], preds: vec![], pc: 0 });
            return Flow::finish(nodes, 0);
        }

        // Generic-for headers: TFORCALL immediately followed by its TFORLOOP
        // (5.2/5.3), or a 5.1 TFORLOOP followed by the back JMP.
        // pc -> (a, nvars, body, exit, number of setup registers)
        let mut genfor_at: BTreeMap<usize, (Reg, u16, usize, usize, u16)> = BTreeMap::new();
        for pc in 0..n {
            match &d.ins[pc] {
                Ins::TForCall { a, nvars, base, ctl } => {
                    let q = d.next[pc];
                    if let Some(Ins::TForLoop { a: la, target, .. }) = d.ins.get(q) {
                        if *la == a + ctl && *target < n {
                            // 5.4+ explists fill four registers (the 4th is
                            // the closing value).
                            let setup = if *base == 3 && *ctl == 2 { 3 } else { 4 };
                            genfor_at.insert(pc, (*a, *nvars, *target, d.next[q], setup));
                        }
                    }
                }
                Ins::TForLoop51 { a, nvars } => {
                    let q = d.next[pc];
                    if let Some(Ins::Jmp { target, .. }) = d.ins.get(q) {
                        if *target < n {
                            genfor_at.insert(pc, (*a, *nvars, *target, d.next[q], 3));
                        }
                    }
                }
                _ => {}
            }
        }

        // ── Leaders ────────────────────────────────────────────────────────
        let mut leader = vec![false; n];
        // Execution starts at the first real instruction (5.4 functions open
        // with VARARGPREP, which is data here).
        let first = (0..n).find(|&pc| !matches!(d.ins[pc], Ins::Data)).unwrap_or(0);
        leader[first] = true;
        for pc in 0..n {
            if matches!(d.ins[pc], Ins::Data) { continue; }
            if let Some(&(_, _, body, exit, _)) = genfor_at.get(&pc) {
                leader[pc] = true;
                if body < n { leader[body] = true; }
                if exit < n { leader[exit] = true; }
                continue;
            }
            let succs = ir::successors(d, pc);
            if ir::ends_block(&d.ins[pc]) {
                for &s in &succs { leader[s] = true; }
                if d.next[pc] < n { leader[d.next[pc]] = true; }
            }
        }
        // The second instruction of a generic-for header is never a leader.
        for (&pc, _) in &genfor_at {
            let q = d.next[pc];
            if q < n { leader[q] = false; }
        }

        // ── Nodes ──────────────────────────────────────────────────────────
        let mut node_at: Vec<usize> = vec![usize::MAX; n];
        let mut pc = 0;
        while pc < n {
            if matches!(d.ins[pc], Ins::Data) && !leader[pc] { pc += 1; continue; }
            let id = nodes.len();
            let start = pc;
            let mut ops = Vec::new();
            let mut q = pc;
            loop {
                node_at[q] = id;
                if !matches!(d.ins[q], Ins::Data) { ops.push(Op::Pc(q)); }
                if genfor_at.contains_key(&q) {
                    let r = d.next[q];
                    if r < n { node_at[r] = id; ops.push(Op::Pc(r)); }
                    q = r;
                    break;
                }
                if ir::ends_block(&d.ins[q]) { break; }
                let nx = d.next[q];
                // Trailing data words belong to this node.
                for w in q + 1..nx.min(n) { node_at[w] = id; }
                if nx >= n || leader[nx] { break; }
                q = nx;
            }
            nodes.push(Node { ops, term: Term::Goto, succs: vec![], preds: vec![], pc: start });
            pc = d.next.get(q).copied().unwrap_or(n).max(q + 1);
        }

        // Resolve a pc to its node, skipping data words.
        let node_of = |pc: usize| -> Option<NodeId> {
            if pc >= n { return None; }
            let id = node_at[pc];
            if id == usize::MAX { None } else { Some(id) }
        };

        // ── Terminators and successors ─────────────────────────────────────
        let count = nodes.len();
        let mut extra: Vec<Node> = Vec::new();
        for id in 0..count {
            let last = match nodes[id].ops.iter().rev().find_map(|o| if let Op::Pc(p) = o { Some(*p) } else { None }) {
                Some(p) => p,
                None => { continue; }
            };
            // Generic-for header?
            let first_pc = nodes[id].ops.iter().find_map(|o| if let Op::Pc(p) = o { Some(*p) } else { None }).unwrap();
            if let Some(&(a, nvars, body, exit, _)) = genfor_at.get(&first_pc) {
                nodes[id].term = Term::GenFor { a, nvars, pc: first_pc };
                nodes[id].succs = [Some(body), Some(exit)].iter().filter_map(|&p| p.and_then(|p| node_of(p))).collect();
                if nodes[id].succs.len() != 2 { nodes[id].term = Term::Exit; nodes[id].succs.clear(); }
                continue;
            }
            let succ_pcs = ir::successors(d, last);
            match &d.ins[last] {
                Ins::Return { .. } | Ins::TailCall { .. } => {
                    nodes[id].term = Term::Exit;
                }
                Ins::Cmp { expect, .. } | Ins::Test { expect, .. } => {
                    let nx = d.next[last];
                    let skip = if nx < n { d.next[nx] } else { nx };
                    // cond true → (expect ? next : skip)
                    let (t, f) = if *expect { (nx, skip) } else { (skip, nx) };
                    match (node_of(t), node_of(f)) {
                        (Some(t), Some(f)) => {
                            nodes[id].term = Term::Cond { cond_pc: last };
                            nodes[id].succs = vec![t, f];
                        }
                        (Some(x), None) | (None, Some(x)) => nodes[id].succs = vec![x],
                        _ => nodes[id].term = Term::Exit,
                    }
                }
                Ins::TestSet { a, b, expect } => {
                    let nx = d.next[last];
                    let skip = if nx < n { d.next[nx] } else { nx };
                    match (node_of(nx), node_of(skip)) {
                        (Some(nx_node), Some(skip_node)) => {
                            let copy = count + extra.len();
                            extra.push(Node {
                                ops: vec![Op::Copy { dst: *a, src: *b }],
                                term: Term::Goto,
                                succs: vec![nx_node],
                                preds: vec![],
                                pc: last,
                            });
                            let (t, f) = if *expect { (copy, skip_node) } else { (skip_node, copy) };
                            nodes[id].term = Term::Cond { cond_pc: last };
                            nodes[id].succs = vec![t, f];
                        }
                        (Some(x), None) | (None, Some(x)) => nodes[id].succs = vec![x],
                        _ => nodes[id].term = Term::Exit,
                    }
                }
                Ins::ForLoop { a, target, .. } => {
                    match (node_of(*target), node_of(d.next[last])) {
                        (Some(body), Some(exit)) => {
                            nodes[id].term = Term::NumFor { a: *a, pc: last };
                            nodes[id].succs = vec![body, exit];
                        }
                        (Some(x), None) | (None, Some(x)) => nodes[id].succs = vec![x],
                        _ => nodes[id].term = Term::Exit,
                    }
                }
                Ins::TForLoop { .. } | Ins::TForLoop51 { .. } => {
                    // Non-canonical generic-for pieces, lowered to
                    // `if R(x) ~= nil then R(ctl) = R(x); <continue> end`.
                    let nx = d.next[last];
                    let (cont, stop, dst, src) = match &d.ins[last] {
                        Ins::TForLoop { a, src, target } => (*target, nx, *a, *src),
                        Ins::TForLoop51 { a, .. } => {
                            (nx, if nx < n { d.next[nx] } else { nx }, *a + 2, *a + 3)
                        }
                        _ => unreachable!(),
                    };
                    match (node_of(cont), node_of(stop)) {
                        (Some(cont), Some(stop)) => {
                            let copy = count + extra.len();
                            extra.push(Node {
                                ops: vec![Op::Copy { dst, src }],
                                term: Term::Goto,
                                succs: vec![cont],
                                preds: vec![],
                                pc: last,
                            });
                            nodes[id].term = Term::Cond { cond_pc: last };
                            nodes[id].succs = vec![copy, stop];
                        }
                        (Some(x), None) | (None, Some(x)) => nodes[id].succs = vec![x],
                        _ => nodes[id].term = Term::Exit,
                    }
                }
                _ => {
                    nodes[id].succs = succ_pcs.iter().filter_map(|&p| node_of(p)).take(1).collect();
                    if nodes[id].succs.is_empty() { nodes[id].term = Term::Exit; }
                }
            }
        }
        nodes.extend(extra);

        // Generic-for setup jumps and numeric FORPREPs get init pseudo-ops.
        for id in 0..nodes.len() {
            let Some(Op::Pc(last)) = nodes[id].ops.last().copied() else { continue };
            match &d.ins[last] {
                Ins::Jmp { target, .. } => {
                    // Only the jump right before the body enters the loop;
                    // other jumps to the header are `continue`s.
                    if let Some(&(a, _, body, _, setup)) = genfor_at.get(target) {
                        if d.next[last] == body {
                            nodes[id].ops.push(Op::GenForInit { a, n: setup });
                        }
                    }
                }
                Ins::ForPrep { a, target } => {
                    if matches!(d.ins.get(*target), Some(Ins::ForLoop { a: la, .. }) if la == a) {
                        nodes[id].ops.push(Op::NumForInit { a: *a });
                    }
                }
                _ => {}
            }
        }

        let entry = node_of(first).unwrap_or(0);
        Flow::finish(nodes, entry)
    }

    fn finish(nodes: Vec<Node>, entry: NodeId) -> Flow {
        let empty: Vec<bool> = nodes.iter().map(|n| n.ops.is_empty()).collect();
        Flow::rebuild(nodes, entry, &empty)
    }

    /// Recompute edges, orders, dominators and loops.  `empty[n]` marks
    /// nodes with no code, which jumps are threaded through.
    pub fn rebuild(mut nodes: Vec<Node>, entry: NodeId, empty: &[bool]) -> Flow {
        for n in nodes.iter_mut() { n.preds.clear(); }
        thread_jumps(&mut nodes, entry, empty);
        for id in 0..nodes.len() {
            let succs = nodes[id].succs.clone();
            for s in succs { nodes[s].preds.push(id); }
        }
        let (rpo, rpo_index) = compute_rpo(&nodes, entry);
        // Drop edges from unreachable nodes so preds only list reachable nodes.
        for n in 0..nodes.len() {
            let keep: Vec<NodeId> = nodes[n].preds.iter().copied()
                .filter(|&p| rpo_index[p] != usize::MAX).collect();
            nodes[n].preds = keep;
        }
        let idom = dominators(&nodes, &rpo, &rpo_index, entry);
        let mut flow = Flow {
            nodes, entry, rpo, rpo_index, idom,
            loops: vec![], loop_of: vec![], loop_by_header: BTreeMap::new(), irreducible: false,
        };
        flow.find_loops();
        flow
    }

    pub fn reachable(&self, n: NodeId) -> bool {
        self.rpo_index[n] != usize::MAX
    }

    pub fn dominates(&self, a: NodeId, mut b: NodeId) -> bool {
        if !self.reachable(b) { return false; }
        loop {
            if a == b { return true; }
            let p = self.idom[b];
            if p == b || p == usize::MAX { return false; }
            b = p;
        }
    }

    fn find_loops(&mut self) {
        let n = self.nodes.len();
        let mut headers: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
        for &u in &self.rpo {
            for &h in &self.nodes[u].succs {
                if self.rpo_index[h] <= self.rpo_index[u] {
                    // Retreating edge.
                    if self.dominates(h, u) {
                        headers.entry(h).or_default().push(u);
                    } else {
                        self.irreducible = true;
                    }
                }
            }
        }
        // For-loop headers whose body never loops back (e.g. it always
        // returns) are still loops syntactically.
        for &x in &self.rpo {
            if matches!(self.nodes[x].term, Term::NumFor { .. } | Term::GenFor { .. }) {
                headers.entry(x).or_default();
            }
        }
        let mut loops: Vec<Loop> = Vec::new();
        for (h, latches) in headers {
            let mut in_body = vec![false; n];
            in_body[h] = true;
            let mut stack: Vec<NodeId> = latches.clone();
            while let Some(x) = stack.pop() {
                if in_body[x] { continue; }
                in_body[x] = true;
                for &p in &self.nodes[x].preds {
                    if !in_body[p] { stack.push(p); }
                }
            }
            if latches.is_empty() {
                // No back edge: the body is what the body entry dominates.
                if let Some(&b) = self.nodes[h].succs.first() {
                    for x in 0..n {
                        if self.dominates(b, x) { in_body[x] = true; }
                    }
                }
            }
            let body: Vec<NodeId> = (0..n).filter(|&i| in_body[i]).collect();
            loops.push(Loop { header: h, latches, body, in_body, parent: None, depth: 0 });
        }
        // Nesting: parent = smallest strictly larger loop containing the header.
        let mut order: Vec<usize> = (0..loops.len()).collect();
        order.sort_by_key(|&i| loops[i].body.len());
        for (k, &i) in order.iter().enumerate() {
            for &j in &order[k + 1..] {
                if loops[j].in_body[loops[i].header] && loops[j].header != loops[i].header {
                    loops[i].parent = Some(j);
                    break;
                }
            }
        }
        for i in 0..loops.len() {
            let mut d = 0;
            let mut p = loops[i].parent;
            while let Some(q) = p { d += 1; p = loops[q].parent; }
            loops[i].depth = d;
        }
        let mut loop_of: Vec<Option<usize>> = vec![None; n];
        for &i in &order {
            for &b in &loops[i].body {
                if loop_of[b].is_none() { loop_of[b] = Some(i); }
            }
        }
        self.loop_by_header = loops.iter().enumerate().map(|(i, l)| (l.header, i)).collect();
        self.loops = loops;
        self.loop_of = loop_of;
    }
}

/// Redirect edges through empty `Goto` nodes (jump chains).
fn thread_jumps(nodes: &mut [Node], entry: NodeId, empty: &[bool]) {
    let n = nodes.len();
    let resolve = |nodes: &[Node], mut x: NodeId| -> NodeId {
        let mut hops = 0;
        while hops < n
            && x != entry
            && empty[x]
            && nodes[x].term == Term::Goto
            && nodes[x].succs.len() == 1
            && nodes[x].succs[0] != x
        {
            x = nodes[x].succs[0];
            hops += 1;
        }
        x
    };
    for id in 0..n {
        let succs = nodes[id].succs.clone();
        nodes[id].succs = succs.into_iter().map(|s| resolve(nodes, s)).collect();
    }
}

fn compute_rpo(nodes: &[Node], entry: NodeId) -> (Vec<NodeId>, Vec<usize>) {
    let n = nodes.len();
    let mut visited = vec![false; n];
    let mut post = Vec::with_capacity(n);
    // Iterative DFS: (node, next successor index).
    let mut stack: Vec<(NodeId, usize)> = vec![(entry, 0)];
    visited[entry] = true;
    while let Some(&mut (x, ref mut i)) = stack.last_mut() {
        if *i < nodes[x].succs.len() {
            let s = nodes[x].succs[*i];
            *i += 1;
            if !visited[s] {
                visited[s] = true;
                stack.push((s, 0));
            }
        } else {
            post.push(x);
            stack.pop();
        }
    }
    post.reverse();
    let mut idx = vec![usize::MAX; n];
    for (i, &x) in post.iter().enumerate() { idx[x] = i; }
    (post, idx)
}

/// Cooper–Harvey–Kennedy iterative dominators.
fn dominators(nodes: &[Node], rpo: &[NodeId], rpo_index: &[usize], entry: NodeId) -> Vec<NodeId> {
    let n = nodes.len();
    let mut idom = vec![usize::MAX; n];
    idom[entry] = entry;
    let intersect = |idom: &Vec<NodeId>, mut a: NodeId, mut b: NodeId| -> NodeId {
        while a != b {
            while rpo_index[a] > rpo_index[b] { a = idom[a]; }
            while rpo_index[b] > rpo_index[a] { b = idom[b]; }
        }
        a
    };
    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo.iter().skip(1) {
            let mut new = usize::MAX;
            for &p in &nodes[b].preds {
                if idom[p] == usize::MAX { continue; }
                new = if new == usize::MAX { p } else { intersect(&idom, p, new) };
            }
            if new != usize::MAX && idom[b] != new {
                idom[b] = new;
                changed = true;
            }
        }
    }
    idom
}

/// Post-dominator tree of a scope (a subgraph with a virtual exit).
pub struct PostDom {
    /// `None`: cannot reach the exit.  `Some(None)`: the virtual exit.
    pub ipdom: Vec<Option<Option<NodeId>>>,
    pre: Vec<u32>,
    post: Vec<u32>,
}

impl PostDom {
    /// Does `a` post-dominate `b` (`None` = the virtual exit)?
    pub fn post_dominates(&self, a: Option<NodeId>, b: NodeId) -> bool {
        let n = self.ipdom.len();
        let ai = a.unwrap_or(n);
        if self.pre[ai] == u32::MAX || self.pre[b] == u32::MAX { return false; }
        self.pre[ai] <= self.pre[b] && self.post[b] <= self.post[ai]
    }
}

/// Immediate post-dominators of the nodes for which `in_scope` holds.
/// `succs(x)` gives each node's successors inside the scope, `None` standing
/// for the virtual exit.
pub fn post_dominators(
    flow: &Flow,
    in_scope: &dyn Fn(NodeId) -> bool,
    succs: &dyn Fn(NodeId) -> Vec<Option<NodeId>>,
) -> PostDom {
    let n = flow.nodes.len();
    let exit = n; // virtual node index
    let fsuccs = |x: NodeId| -> Vec<NodeId> {
        succs(x).into_iter().map(|s| s.unwrap_or(exit)).collect()
    };
    // Reverse graph (edges flipped) for the DFS from the exit.
    let mut rpreds: Vec<Vec<NodeId>> = vec![Vec::new(); n + 1];
    for x in 0..n {
        if !in_scope(x) || !flow.reachable(x) { continue; }
        for s in fsuccs(x) { rpreds[s].push(x); }
    }
    let mut visited = vec![false; n + 1];
    let mut post = Vec::new();
    let mut stack: Vec<(usize, usize)> = vec![(exit, 0)];
    visited[exit] = true;
    while let Some(&mut (x, ref mut i)) = stack.last_mut() {
        if *i < rpreds[x].len() {
            let s = rpreds[x][*i];
            *i += 1;
            if !visited[s] { visited[s] = true; stack.push((s, 0)); }
        } else {
            post.push(x);
            stack.pop();
        }
    }
    post.reverse();
    let mut ord = vec![usize::MAX; n + 1];
    for (i, &x) in post.iter().enumerate() { ord[x] = i; }
    let mut ipdom = vec![usize::MAX; n + 1];
    ipdom[exit] = exit;
    let intersect = |ip: &Vec<usize>, mut a: usize, mut b: usize| -> usize {
        while a != b {
            while ord[a] > ord[b] { a = ip[a]; }
            while ord[b] > ord[a] { b = ip[b]; }
        }
        a
    };
    let mut changed = true;
    while changed {
        changed = false;
        for &x in post.iter().skip(1) {
            let mut new = usize::MAX;
            for s in fsuccs(x) {
                if ipdom[s] == usize::MAX { continue; }
                new = if new == usize::MAX { s } else { intersect(&ipdom, s, new) };
            }
            if new != usize::MAX && ipdom[x] != new {
                ipdom[x] = new;
                changed = true;
            }
        }
    }
    // Euler-tour numbering of the tree for O(1) ancestor queries.
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
    for x in 0..n {
        if ipdom[x] != usize::MAX && x != exit { children[ipdom[x]].push(x); }
    }
    let mut pre = vec![u32::MAX; n + 1];
    let mut post = vec![u32::MAX; n + 1];
    let mut clock = 0u32;
    let mut stack: Vec<(usize, usize)> = vec![(exit, 0)];
    pre[exit] = clock;
    clock += 1;
    while let Some(&mut (x, ref mut i)) = stack.last_mut() {
        if *i < children[x].len() {
            let c = children[x][*i];
            *i += 1;
            pre[c] = clock;
            clock += 1;
            stack.push((c, 0));
        } else {
            post[x] = clock;
            clock += 1;
            stack.pop();
        }
    }
    let ipdom = (0..n).map(|x| {
        if ipdom[x] == usize::MAX { None }
        else if ipdom[x] == exit { Some(None) }
        else { Some(Some(ipdom[x])) }
    }).collect();
    PostDom { ipdom, pre, post }
}
