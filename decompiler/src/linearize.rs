//! JMP-spaghetti (control-flow flattening) linearization pass.
//!
//! ThanhDieuLua Byte V3 and similar obfuscators scatter every original
//! instruction to a random PC and connect them with *relay JMPs*.  Two relay
//! patterns arise in practice:
//!
//! ```text
//! Pattern A – pure relay block:
//!   PC_r: JMP → PC_next_real      ← single-instruction relay
//!
//! Pattern B – relay-tail block:
//!   PC_k:   REAL_INSTR            ← original instruction
//!   PC_k+1: JMP → PC_next_real    ← unconditional relay JMP (no skip before)
//! ```
//!
//! Between relay JMPs, unreachable padding fills the gaps:
//! ```text
//!   PC_p, PC_p+1, PC_p+2: RETURN R0 1   ← fake "return" padding
//! ```
//!
//! # Algorithm
//!
//! 1. Build the CFG.
//! 2. Classify every basic block as one of:
//!    - **relay**       – single unconditional JMP (Pattern A); omitted entirely.
//!    - **relay-tail**  – ends with unconditional JMP not preceded by a
//!      conditional skip (Pattern B); the terminal JMP is omitted but the
//!      preceding real instructions are kept.
//!    - **padding**     – every instruction is a bare `RETURN R0 1`; omitted.
//!    - **real**        – all other blocks; emitted verbatim (after patching
//!      any ForPrep / ForLoop / TForLoop / conditional-JMP offsets).
//! 3. DFS from the real entry (first non-relay block reachable from PC 0),
//!    prioritising each block's "natural successor" so it lands immediately
//!    next in the new bytecode:
//!    - relay-tail block → natural successor = JMP target (after relay chain)
//!    - other block      → natural successor = fall-through target (if any)
//! 4. Insert synthetic trailing JMPs for any block whose natural successor
//!    is not immediately adjacent in the new layout.
//! 5. Emit each block's "real" instructions (relay-tail: skip terminal JMP;
//!    real/conditional: emit all; relay/padding: skip entirely).
//! 6. Patch ForPrep / ForLoop / TForLoop / conditional-JMP offsets so they
//!    target the correct new PCs.
//! 7. Recursively apply to all sub-protos that also exhibit the pattern.

use std::collections::{HashMap, HashSet};

use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;

use disassembler::{get_opcode, getarg_a, getarg_b, getarg_sbx, OpCode, Proto};

use crate::cfg::{BasicBlock, Cfg, EdgeKind};

// ── Instruction-encoding constants (Lua 5.x iABC/iABx/iAsBx layout) ──────────

const POS_C: u32 = 14;
const MAXARG_SBX: i32 = (1 << 17) - 1; // 131 071

// ── Thresholds ────────────────────────────────────────────────────────────────

/// Minimum fraction of spaghetti-like blocks to trigger linearization.
const SPAGHETTI_THRESHOLD: f64 = 0.35;
/// Minimum total block count before the threshold test applies.
const MIN_BLOCKS: usize = 5;
/// Maximum hops before we break a relay cycle.
const MAX_RELAY_HOPS: usize = 2_000;

// ── Helpers ───────────────────────────────────────────────────────────────────

/// `pc + 1 + sbx` — the standard Lua branch-target formula.
#[inline]
fn jump_target(pc: usize, sbx: i32) -> usize {
    (pc as i64 + 1 + sbx as i64) as usize
}

/// Rewrite the sBx field of a branch instruction.
fn set_sbx(instr: u32, sbx: i32) -> u32 {
    let bx = (sbx + MAXARG_SBX) as u32;
    let bx_mask: u32 = ((1u32 << 18).wrapping_sub(1)) << POS_C;
    (instr & !bx_mask) | ((bx << POS_C) & bx_mask)
}

/// Build a bare `JMP A=0 sBx=sbx` by taking the opcode bits from the first
/// JMP found in `code`.
fn make_jmp(code: &[u32], sbx: i32) -> Option<u32> {
    let op_bits = code
        .iter()
        .find(|&&i| get_opcode(i) == OpCode::Jmp)
        .map(|&i| i & 0x3F)?;
    Some(set_sbx(op_bits, sbx))
}

/// Returns `true` for opcodes that *skip* the very next instruction when their
/// condition holds — i.e. comparison/test ops that always precede a JMP.
#[inline]
fn is_skip_opcode(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Eq
            | OpCode::Lt
            | OpCode::Le
            | OpCode::Test
            | OpCode::TestSet
            | OpCode::LuaDecTForLoop
    )
}

// ── Block classification ──────────────────────────────────────────────────────

/// True for a TFORLOOP whose computed back-target is out of bounds.
///
/// Lua 5.2 semantics: `if R(A+1) ~= nil then { R(A) = R(A+1); pc += sBx }`,
/// otherwise fall through. If `pc + 1 + sBx` is not a valid PC, then any
/// runtime branch would crash — so either `R(A+1)` is always nil at this
/// point (the instruction is a no-op fall-through), or this PC is unreachable.
/// In both cases the instruction is dead weight from a control-flow standpoint
/// and can be elided without changing semantics.
///
/// Used by anti-decompilation packers as an opaque-no-op at function entry
/// (the AST builder choked on its empty `OpCode::TForLoop` arm).
#[inline]
fn is_junk_tforloop(code: &[u32], pc: usize) -> bool {
    if get_opcode(code[pc]) != OpCode::TForLoop {
        return false;
    }
    let sbx = getarg_sbx(code[pc]);
    // jump_target uses i64 then casts to usize; an OOB (incl. negative)
    // target compares false against `< code.len()`.
    let target_i64 = pc as i64 + 1 + sbx as i64;
    target_i64 < 0 || (target_i64 as usize) >= code.len()
}

/// True for the JMP that enters a generic `for` (to its TFORCALL, or the 5.1
/// TFORLOOP).  The decompiler recognises the loop by this jump sitting right
/// before the body, so it is never treated as a relay.
fn is_forgen_entry(code: &[u32], pc: usize) -> bool {
    if get_opcode(code[pc]) != OpCode::Jmp {
        return false;
    }
    let target = pc as i64 + 1 + getarg_sbx(code[pc]) as i64;
    (0..code.len() as i64).contains(&target) && get_opcode(code[target as usize]) == OpCode::LuaDecTForLoop
}

/// True for *pure relay* blocks: a single-instruction block that contains
/// either an unconditional JMP or a junk-TFORLOOP.  Both fall through to
/// "somewhere else" with no real side effect; the block is skipped entirely
/// (nothing emitted, not placed in the layout).
fn is_relay(bb: &BasicBlock, code: &[u32]) -> bool {
    if bb.start != bb.end || is_forgen_entry(code, bb.start) {
        return false;
    }
    is_plain_jmp(code[bb.start]) || is_junk_tforloop(code, bb.start)
}

/// A JMP that only jumps: in Lua 5.2+ `A > 0` also closes upvalues.
fn is_plain_jmp(instr: u32) -> bool {
    get_opcode(instr) == OpCode::Jmp && getarg_a(instr) == 0
}

/// True for *relay-tail* blocks: the terminal instruction is an unconditional
/// JMP (not preceded by a conditional-skip) **or** a junk-TFORLOOP.
///
/// The terminal instruction is the **last** instruction; everything before
/// it is real.  During emission the terminal is omitted; the predecessor is
/// adjusted so that the natural successor follows immediately (or a synthetic
/// JMP is inserted).
fn has_relay_tail(bb: &BasicBlock, code: &[u32]) -> bool {
    if is_plain_jmp(code[bb.end]) && !is_forgen_entry(code, bb.end) {
        // The JMP must NOT be preceded by a conditional-skip in the same block.
        if bb.end > bb.start && is_skip_opcode(get_opcode(code[bb.end - 1])) {
            return false;
        }
        return true;
    }
    if is_junk_tforloop(code, bb.end) {
        return true;
    }
    false
}

/// Edge kind that carries the natural successor for a relay-tail block.
/// - JMP-tail   → the Jump (or Back) edge target,
/// - TFORLOOP-junk-tail → the FallThrough edge target (the TFORLOOP never
///   branches at runtime, so removing it leaves a plain fall-through).
#[inline]
fn relay_tail_natural_kind(bb: &BasicBlock, code: &[u32]) -> EdgeKind {
    if is_junk_tforloop(code, bb.end) {
        EdgeKind::FallThrough
    } else {
        // Default: JMP-tail. We treat Back the same way as Jump at the call
        // site (both are explicit branches).
        EdgeKind::Jump
    }
}

/// True for *padding* blocks: every instruction is a bare `RETURN R0 1`.
fn is_padding(bb: &BasicBlock, code: &[u32]) -> bool {
    (bb.start..=bb.end).all(|pc| {
        get_opcode(code[pc]) == OpCode::Return && getarg_b(code[pc]) == 1
    })
}

// ── Relay-chain following ─────────────────────────────────────────────────────

/// Follow a chain of *pure relay* blocks from `start`, returning the first
/// non-relay block reachable through them.
///
/// Relay-tail blocks are **not** transparent — they carry real instructions
/// and appear in the layout.  Only pure-relay single-JMP blocks are skipped.
fn follow_relay(cfg: &Cfg, relay_set: &HashSet<NodeIndex>, start: NodeIndex) -> NodeIndex {
    let mut node = start;
    for _ in 0..MAX_RELAY_HOPS {
        if !relay_set.contains(&node) {
            break;
        }
        match cfg.graph.edges(node).next() {
            Some(e) => node = e.target(),
            None => break,
        }
    }
    node
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Returns `true` when `proto`'s bytecode looks like JMP-spaghetti control-flow
/// flattening.
///
/// Heuristic: at least `SPAGHETTI_THRESHOLD` of basic blocks are relay, relay-
/// tail, or pure-padding blocks.
pub fn has_spaghetti(proto: &Proto) -> bool {
    if proto.code.is_empty() {
        return false;
    }
    let cfg = Cfg::build(proto);
    let total = cfg.graph.node_count();
    if total < MIN_BLOCKS {
        return false;
    }
    let code = &proto.code;
    let spaghetti_count = cfg
        .graph
        .node_indices()
        .filter(|&n| {
            let bb = &cfg.graph[n];
            is_relay(bb, code) || has_relay_tail(bb, code) || is_padding(bb, code)
        })
        .count();
    (spaghetti_count as f64 / total as f64) >= SPAGHETTI_THRESHOLD
}

/// Linearize `proto`, removing relay JMPs and padding, and returning a new
/// `Proto` whose bytecode is in clean sequential execution order.
///
/// Sub-protos that also exhibit the spaghetti pattern are linearized
/// recursively.
pub fn linearize(proto: &Proto) -> Proto {
    let code = &proto.code;
    if code.is_empty() {
        return proto.clone();
    }

    let cfg = Cfg::build(proto);

    // ── 1. Build relay set (pure single-JMP blocks) ──────────────────────────
    let relay_set: HashSet<NodeIndex> = cfg
        .graph
        .node_indices()
        .filter(|&n| is_relay(&cfg.graph[n], code))
        .collect();

    // ── 2. DFS layout ────────────────────────────────────────────────────────
    //
    // Priority rule: every block should be immediately followed by its
    // "natural successor" — the block that requires no explicit JMP to reach:
    //   • relay-tail block  → its (removed) JMP target
    //   • all other blocks  → their FallThrough successor (if any)
    // Placing the natural successor next minimises the number of synthetic
    // trailing JMPs we have to insert.

    let real_entry = follow_relay(&cfg, &relay_set, cfg.entry);

    let mut layout: Vec<NodeIndex> = Vec::new();
    let mut visited_dfs: HashSet<NodeIndex> = HashSet::new();
    let mut stack: Vec<NodeIndex> = vec![real_entry];

    while let Some(node) = stack.pop() {
        // Skip relay blocks (pure {JMP}) and already-placed nodes.
        if relay_set.contains(&node) || visited_dfs.contains(&node) {
            continue;
        }
        visited_dfs.insert(node);
        layout.push(node);

        let bb = &cfg.graph[node];
        let is_rt = has_relay_tail(bb, code);

        let mut ft_succ: Option<NodeIndex> = None;
        let mut jmp_succ: Option<NodeIndex> = None;

        for edge in cfg.graph.edges(node) {
            let real = follow_relay(&cfg, &relay_set, edge.target());
            if is_rt {
                // relay-tail: treat the outgoing JMP edge as the natural
                // (fall-through priority) successor.
                ft_succ = Some(real);
            } else {
                match edge.weight() {
                    EdgeKind::FallThrough => ft_succ = Some(real),
                    EdgeKind::Jump | EdgeKind::Back => {
                        if jmp_succ.is_none() || !visited_dfs.contains(&real) {
                            jmp_succ = Some(real);
                        }
                    }
                }
            }
        }

        // A generic-for entry jump must be followed by the loop body (the
        // instruction after it), even though nothing falls through to it.
        if is_forgen_entry(code, bb.end) && bb.end + 1 < code.len() {
            let body = cfg.block_of[bb.end + 1];
            if !relay_set.contains(&body) {
                ft_succ = Some(body);
            }
        }

        // Push jump-side first (lower priority = processed later), then
        // fall-through last (higher priority = popped next).
        if let Some(jt) = jmp_succ {
            if !visited_dfs.contains(&jt) {
                stack.push(jt);
            }
        }
        if let Some(ft) = ft_succ {
            if !visited_dfs.contains(&ft) {
                stack.push(ft);
            }
        }
    }

    // ── 3. Decide which blocks need a synthetic trailing JMP ─────────────────
    //
    // A block needs one when its natural successor (ft_real) is not the
    // immediately next block in the layout.

    let needs_extra_jmp: Vec<bool> = layout
        .iter()
        .enumerate()
        .map(|(i, &node)| {
            let bb = &cfg.graph[node];
            let is_rt = has_relay_tail(bb, code);

            // Compute ft_real (the natural successor).
            let ft_real: Option<NodeIndex> = if is_rt {
                // Natural successor depends on what the terminal instruction is:
                // - JMP-tail: the Jump (or Back) edge target.
                // - junk-TFORLOOP-tail: the FallThrough edge target (the
                //   TFORLOOP never branches at runtime).
                let kind = relay_tail_natural_kind(bb, code);
                cfg.graph
                    .edges(node)
                    .filter(|e| match kind {
                        EdgeKind::Jump => matches!(e.weight(), EdgeKind::Jump | EdgeKind::Back),
                        EdgeKind::FallThrough => *e.weight() == EdgeKind::FallThrough,
                        EdgeKind::Back => *e.weight() == EdgeKind::Back,
                    })
                    .map(|e| follow_relay(&cfg, &relay_set, e.target()))
                    .next()
            } else {
                // Natural successor = FallThrough.
                cfg.graph
                    .edges(node)
                    .filter(|e| *e.weight() == EdgeKind::FallThrough)
                    .map(|e| follow_relay(&cfg, &relay_set, e.target()))
                    .next()
            };

            if let Some(ft) = ft_real {
                layout.get(i + 1).copied() != Some(ft)
            } else {
                false
            }
        })
        .collect();

    // ── 4. Assign new start PCs ──────────────────────────────────────────────
    let mut new_start: HashMap<NodeIndex, usize> = HashMap::new();
    let mut cur_pc = 0usize;

    for (i, &node) in layout.iter().enumerate() {
        let bb = &cfg.graph[node];
        new_start.insert(node, cur_pc);

        // Number of instructions emitted for this block.
        let emitted = if has_relay_tail(bb, code) {
            // Omit terminal relay JMP.
            bb.end - bb.start // = end - start instructions (all but last)
        } else {
            bb.end - bb.start + 1 // all instructions
        };

        cur_pc += emitted;
        if needs_extra_jmp[i] {
            cur_pc += 1; // synthetic trailing JMP
        }
    }

    // ── 5. Emit and patch ────────────────────────────────────────────────────
    let mut new_code: Vec<u32> = Vec::with_capacity(cur_pc);

    for (i, &node) in layout.iter().enumerate() {
        let bb = &cfg.graph[node];
        let is_rt = has_relay_tail(bb, code);
        let block_base = new_start[&node];

        // Inclusive end of what we emit.
        let emit_end = if is_rt { bb.end - 1 } else { bb.end };

        for pc in bb.start..=emit_end {
            let instr = code[pc];
            let new_instr = patch_branch(
                instr,
                get_opcode(instr),
                pc,
                block_base + (pc - bb.start),
                &cfg,
                &relay_set,
                &new_start,
            );
            new_code.push(new_instr);
        }

        // Synthetic trailing JMP for a non-adjacent natural successor.
        if needs_extra_jmp[i] {
            let ft_real = if is_rt {
                let kind = relay_tail_natural_kind(bb, code);
                cfg.graph
                    .edges(node)
                    .filter(|e| match kind {
                        EdgeKind::Jump => matches!(e.weight(), EdgeKind::Jump | EdgeKind::Back),
                        EdgeKind::FallThrough => *e.weight() == EdgeKind::FallThrough,
                        EdgeKind::Back => *e.weight() == EdgeKind::Back,
                    })
                    .map(|e| follow_relay(&cfg, &relay_set, e.target()))
                    .next()
            } else {
                cfg.graph
                    .edges(node)
                    .filter(|e| *e.weight() == EdgeKind::FallThrough)
                    .map(|e| follow_relay(&cfg, &relay_set, e.target()))
                    .next()
            }
            .expect("needs_extra_jmp=true but no natural successor");

            let jmp_pc = block_base + (emit_end - bb.start + 1);
            let target_pc = new_start
                .get(&ft_real)
                .copied()
                .unwrap_or(cur_pc); // target not in layout → jump past end (unreachable)
            let sbx = target_pc as i32 - (jmp_pc as i32 + 1);
            if let Some(jmp_instr) = make_jmp(code, sbx) {
                new_code.push(jmp_instr);
            }
        }
    }

    // ── 6. Recursively linearize sub-protos ──────────────────────────────────
    let new_p: Vec<Proto> = proto
        .p
        .iter()
        .map(|sub| linearize_tree(sub))
        .collect();

    Proto {
        sizecode:      new_code.len(),
        code:          new_code,
        sizep:         new_p.len(),
        p:             new_p,
        // Debug locals refer to the old pcs.
        locals:        Vec::new(),
        ..proto.clone()
    }
}

/// Recursively linearize `proto` and all of its sub-protos, applying the
/// linearization pass only where spaghetti is detected.
pub fn linearize_tree(proto: &Proto) -> Proto {
    if has_spaghetti(proto) {
        // `linearize` already calls `linearize_tree` on its sub-protos.
        linearize(proto)
    } else {
        // Not spaghetti at this level: keep code as-is, but still recurse.
        let new_p: Vec<Proto> = proto.p.iter().map(linearize_tree).collect();
        Proto {
            sizep: new_p.len(),
            p:     new_p,
            ..proto.clone()
        }
    }
}

// ── Instruction patching ──────────────────────────────────────────────────────

/// Rewrite the branch offset of a JMP / ForPrep / ForLoop / TForLoop
/// instruction so it targets the correct new PC.
///
/// Returns the instruction unchanged for all other opcodes.
fn patch_branch(
    instr: u32,
    op: OpCode,
    old_pc: usize,
    new_pc: usize,
    cfg: &Cfg,
    relay_set: &HashSet<NodeIndex>,
    new_start: &HashMap<NodeIndex, usize>,
) -> u32 {
    match op {
        OpCode::Jmp | OpCode::ForPrep | OpCode::ForLoop | OpCode::TForLoop => {
            let old_sbx = getarg_sbx(instr);
            let old_target = jump_target(old_pc, old_sbx);

            if old_target >= cfg.block_of.len() {
                return instr;
            }
            let target_block = cfg.block_of[old_target];
            let real_target = follow_relay(cfg, relay_set, target_block);

            match new_start.get(&real_target) {
                Some(&new_target_pc) => {
                    let new_sbx = new_target_pc as i32 - (new_pc as i32 + 1);
                    set_sbx(instr, new_sbx)
                }
                None => instr, // target not in layout (unreachable)
            }
        }
        _ => instr,
    }
}
