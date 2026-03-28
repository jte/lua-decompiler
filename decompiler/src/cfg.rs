//! Control-flow graph (CFG) recovery for a single Lua function prototype.
//!
//! # Pipeline
//!
//! ```text
//! Proto (bytecode)
//!   └─► Cfg::build()          — basic-block partitioning + edge wiring
//!         ├─► dominators()    — Lengauer-Tarjan dominator tree (petgraph)
//!         ├─► dominance_frontiers() — Cooper et al. DF sets
//!         └─► natural_loops() — back-edge based loop detection
//! ```

use std::collections::{HashMap, HashSet};

use petgraph::{
    algo::dominators::{self, Dominators},
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
    Direction,
};

use disassembler::{get_opcode, getarg_sbx, OpCode, Proto};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A maximal straight-line sequence of instructions with no internal branches.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Index of the first instruction in this block (inclusive).
    pub start: usize,
    /// Index of the last instruction in this block (inclusive).
    pub end: usize,
}

/// The semantic reason an edge exists between two basic blocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeKind {
    /// Sequential fall-through (no jump taken).
    FallThrough,
    /// An explicit forward jump was taken.
    Jump,
    /// A loop back-edge (target PC ≤ source block start PC).
    Back,
}

// ---------------------------------------------------------------------------
// CFG
// ---------------------------------------------------------------------------

/// Control-flow graph for one Lua function prototype.
///
/// Nodes are `BasicBlock` values; edges carry an `EdgeKind`.
pub struct Cfg {
    /// The directed graph.  Index with `NodeIndex` to get a `BasicBlock`.
    pub graph: DiGraph<BasicBlock, EdgeKind>,

    /// Entry node — always wraps `pc = 0`.
    pub entry: NodeIndex,

    /// `block_of[pc]` gives the `NodeIndex` of the block that owns instruction `pc`.
    pub block_of: Vec<NodeIndex>,
}

impl Cfg {
    // -----------------------------------------------------------------------
    // Construction
    // -----------------------------------------------------------------------

    /// Build a CFG from `proto`'s bytecode.
    ///
    /// ## Algorithm
    /// 1. **Leader identification** — an instruction is a *leader* if it is:
    ///    - the first instruction (`pc = 0`), or
    ///    - the target of any jump / branch, or
    ///    - the instruction immediately after any jump, branch, or `RETURN`.
    /// 2. **Block creation** — each run of instructions `[leader, next_leader)` becomes a node.
    /// 3. **Edge wiring** — we inspect the last instruction of each block to add successor edges.
    pub fn build(proto: &Proto) -> Self {
        let code = &proto.code;
        let n = code.len();

        if n == 0 {
            let mut graph = DiGraph::new();
            let entry = graph.add_node(BasicBlock { start: 0, end: 0 });
            return Self { graph, entry, block_of: vec![] };
        }

        // ── 1. Find leaders ──────────────────────────────────────────────────
        let mut is_leader = vec![false; n];
        is_leader[0] = true;

        for pc in 0..n {
            let op = get_opcode(code[pc]);
            let sbx = getarg_sbx(code[pc]);

            match op {
                // Unconditional forward/backward jump.
                OpCode::Jmp => {
                    mark_leader(&mut is_leader, n, jump_target(pc, sbx)); // jump destination
                    mark_leader(&mut is_leader, n, pc + 1);               // instruction after JMP
                }

                // ForPrep jumps *forward* to the ForLoop instruction.
                OpCode::ForPrep => {
                    mark_leader(&mut is_leader, n, jump_target(pc, sbx));
                    mark_leader(&mut is_leader, n, pc + 1);
                }

                // ForLoop: back-edge to loop body *or* fall-through to exit.
                OpCode::ForLoop => {
                    mark_leader(&mut is_leader, n, jump_target(pc, sbx)); // back target (sbx < 0)
                    mark_leader(&mut is_leader, n, pc + 1);               // loop exit
                }

                // TForLoop (lua52/53): same structure as ForLoop.
                OpCode::TForLoop => {
                    mark_leader(&mut is_leader, n, jump_target(pc, sbx));
                    mark_leader(&mut is_leader, n, pc + 1);
                }

                // Function exits — anything after them is unreachable but may still
                // be a jump target, so mark it as a potential leader.
                OpCode::Return | OpCode::TailCall => {
                    mark_leader(&mut is_leader, n, pc + 1);
                }

                // Everything else falls through; no new leaders from here.
                _ => {}
            }
        }

        // ── 2. Create nodes ──────────────────────────────────────────────────
        let leaders: Vec<usize> = (0..n).filter(|&i| is_leader[i]).collect();

        let mut graph: DiGraph<BasicBlock, EdgeKind> = DiGraph::new();
        let mut block_of = vec![NodeIndex::new(0); n];
        let mut leader_to_node: HashMap<usize, NodeIndex> = HashMap::new();

        for (i, &start) in leaders.iter().enumerate() {
            let end = leaders.get(i + 1).map(|&l| l - 1).unwrap_or(n - 1);
            let node = graph.add_node(BasicBlock { start, end });
            leader_to_node.insert(start, node);
            for pc in start..=end {
                block_of[pc] = node;
            }
        }

        let entry = leader_to_node[&0];

        // ── 3. Wire edges ────────────────────────────────────────────────────
        for (i, &start) in leaders.iter().enumerate() {
            let end = leaders.get(i + 1).map(|&l| l - 1).unwrap_or(n - 1);
            let src = leader_to_node[&start];

            let last_op  = get_opcode(code[end]);
            let last_sbx = getarg_sbx(code[end]);

            match last_op {
                // ── Unconditional jump ───────────────────────────────────────
                OpCode::Jmp => {
                    let target = jump_target(end, last_sbx);
                    let kind = if target <= start { EdgeKind::Back } else { EdgeKind::Jump };
                    add_edge_to(&mut graph, src, &leader_to_node, target, kind);

                    // If the JMP is preceded by a conditional skip instruction
                    // (Eq/Lt/Le/Test/TestSet/LuaDecTForLoop), the skipped path
                    // falls through to pc = end + 1.
                    if end > start && is_skip_instr(get_opcode(code[end - 1])) {
                        add_edge_to(&mut graph, src, &leader_to_node, end + 1, EdgeKind::FallThrough);
                    }
                }

                // ── ForPrep: init loop, jump forward to ForLoop ──────────────
                //
                // The VM always takes the jump; there is no fall-through.
                OpCode::ForPrep => {
                    let target = jump_target(end, last_sbx);
                    add_edge_to(&mut graph, src, &leader_to_node, target, EdgeKind::Jump);
                }

                // ── ForLoop: back-edge *or* loop exit ────────────────────────
                OpCode::ForLoop => {
                    let back = jump_target(end, last_sbx); // sBx < 0 → backward
                    add_edge_to(&mut graph, src, &leader_to_node, back,    EdgeKind::Back);
                    add_edge_to(&mut graph, src, &leader_to_node, end + 1, EdgeKind::FallThrough);
                }

                // ── TForLoop (lua52/53): back-edge or fall-through ────────────
                OpCode::TForLoop => {
                    let back = jump_target(end, last_sbx);
                    add_edge_to(&mut graph, src, &leader_to_node, back,    EdgeKind::Back);
                    add_edge_to(&mut graph, src, &leader_to_node, end + 1, EdgeKind::FallThrough);
                }

                // ── Function exits: no successors ────────────────────────────
                OpCode::Return | OpCode::TailCall => {}

                // ── Everything else: fall through ────────────────────────────
                _ => {
                    add_edge_to(&mut graph, src, &leader_to_node, end + 1, EdgeKind::FallThrough);
                }
            }
        }

        Self { graph, entry, block_of }
    }

    // -----------------------------------------------------------------------
    // Dominator tree
    // -----------------------------------------------------------------------

    /// Compute the dominator tree with Lengauer-Tarjan (`petgraph::algo::dominators::simple_fast`).
    ///
    /// The returned `Dominators` object supports:
    /// - `doms.immediate_dominator(node)` → `Option<NodeIndex>`
    /// - `doms.dominators(node)` → `Option<impl Iterator<Item = NodeIndex>>`
    pub fn dominators(&self) -> Dominators<NodeIndex> {
        dominators::simple_fast(&self.graph, self.entry)
    }

    // -----------------------------------------------------------------------
    // Dominance frontiers
    // -----------------------------------------------------------------------

    /// Compute dominance frontiers using the Cooper et al. (2001) algorithm.
    ///
    /// `DF(n)` is the set of nodes where `n`'s dominance *ends*: nodes that
    /// have a predecessor dominated by `n` but are not themselves strictly
    /// dominated by `n`.  Dominance frontiers drive SSA φ-node placement.
    pub fn dominance_frontiers(
        &self,
        doms: &Dominators<NodeIndex>,
    ) -> HashMap<NodeIndex, HashSet<NodeIndex>> {
        let mut df: HashMap<NodeIndex, HashSet<NodeIndex>> = self
            .graph
            .node_indices()
            .map(|n| (n, HashSet::new()))
            .collect();

        for n in self.graph.node_indices() {
            let preds: Vec<_> = self
                .graph
                .neighbors_directed(n, Direction::Incoming)
                .collect();

            // Frontier nodes only arise where control flow merges (≥ 2 predecessors).
            if preds.len() < 2 {
                continue;
            }

            let idom_n = match doms.immediate_dominator(n) {
                Some(d) => d,
                None => continue,
            };

            for pred in preds {
                let mut runner = pred;
                while runner != idom_n {
                    df.get_mut(&runner).unwrap().insert(n);
                    match doms.immediate_dominator(runner) {
                        Some(d) => runner = d,
                        None => break,
                    }
                }
            }
        }

        df
    }

    // -----------------------------------------------------------------------
    // Loop detection
    // -----------------------------------------------------------------------

    /// Identify natural loops from back-edges.
    ///
    /// Returns a `Vec` of `(header, body)` pairs where `body` is the full set of
    /// nodes in the natural loop, including `header`.
    pub fn natural_loops(&self) -> Vec<(NodeIndex, HashSet<NodeIndex>)> {
        self.graph
            .edge_references()
            .filter(|e| *e.weight() == EdgeKind::Back)
            .map(|e| {
                let header = e.target();
                let body   = self.loop_body(header, e.source());
                (header, body)
            })
            .collect()
    }

    /// Compute the body of the natural loop whose back-edge runs `tail → header`.
    ///
    /// Walks backwards from `tail` through the CFG, collecting all nodes that
    /// can reach `tail` without going through `header`.
    fn loop_body(&self, header: NodeIndex, tail: NodeIndex) -> HashSet<NodeIndex> {
        let mut body = HashSet::from([header]);
        let mut worklist = vec![tail];

        while let Some(n) = worklist.pop() {
            if body.insert(n) {
                for pred in self.graph.neighbors_directed(n, Direction::Incoming) {
                    if !body.contains(&pred) {
                        worklist.push(pred);
                    }
                }
            }
        }

        body
    }

    // -----------------------------------------------------------------------
    // Debug helpers
    // -----------------------------------------------------------------------

    /// Dump a human-readable description of the CFG to a `String`.
    pub fn dump(&self) -> String {
        let mut out = String::new();
        for node in self.graph.node_indices() {
            let bb = &self.graph[node];
            out.push_str(&format!(
                "BB{} [pc {}..{}]\n",
                node.index(),
                bb.start,
                bb.end,
            ));
            for edge in self.graph.edges(node) {
                out.push_str(&format!(
                    "  -> BB{}  ({:?})\n",
                    edge.target().index(),
                    edge.weight(),
                ));
            }
        }
        out
    }

    /// Render the CFG as a Graphviz DOT string.
    ///
    /// Pipe the output to `dot -Tsvg -o cfg.svg` or open it in any DOT viewer
    /// (e.g. Graphviz, VSCode extension, <https://dreampuf.github.io/GraphvizOnline>).
    ///
    /// Node labels show the block index and its PC range.
    /// Edge labels show the `EdgeKind`.
    pub fn to_dot(&self) -> String {
        use petgraph::dot::{Config, Dot};

        format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.graph,
                &[Config::EdgeNoLabel],
                &|_, edge| format!("label=\"{:?}\"", edge.weight()),
                &|_, (node, bb)| format!(
                    "label=\"BB{}\\npc {}..{}\", shape=box",
                    node.index(),
                    bb.start,
                    bb.end,
                ),
            )
        )
    }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// `pc + 1 + sbx` — the standard Lua branch-target formula.
#[inline]
fn jump_target(pc: usize, sbx: i32) -> usize {
    (pc as i64 + 1 + sbx as i64) as usize
}

/// Mark `pc` as a leader if it is within bounds.
#[inline]
fn mark_leader(is_leader: &mut Vec<bool>, n: usize, pc: usize) {
    if pc < n {
        is_leader[pc] = true;
    }
}

/// Add an edge `src → target_pc` if `target_pc` maps to a known node.
fn add_edge_to(
    graph: &mut DiGraph<BasicBlock, EdgeKind>,
    src: NodeIndex,
    leader_to_node: &HashMap<usize, NodeIndex>,
    target_pc: usize,
    kind: EdgeKind,
) {
    if let Some(&dst) = leader_to_node.get(&target_pc) {
        graph.add_edge(src, dst, kind);
    }
}

/// Returns `true` for instructions that *skip the very next instruction*
/// (always a `JMP`) when their condition is satisfied.
///
/// These form a two-instruction conditional branch together with the
/// following `JMP`:
/// - taken path  → execute the `JMP`  (jump to its target)
/// - skipped path → fall through past the `JMP`  (pc = jmp_pc + 1)
#[inline]
fn is_skip_instr(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Eq
            | OpCode::Lt
            | OpCode::Le
            | OpCode::Test
            | OpCode::TestSet
            | OpCode::LuaDecTForLoop // lua51 TFORLOOP: skips JMP on loop exit
    )
}
