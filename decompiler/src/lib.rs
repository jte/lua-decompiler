pub mod cfg;

use std::collections::HashSet;

use petgraph::algo::dominators::Dominators;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;

use disassembler::{
    Proto, OpCode,
    get_opcode, getarg_a, getarg_b, getarg_c, getarg_bx, getarg_sbx, getarg_ax,
    decompile_constant, global_,
};

use crate::cfg::{Cfg, EdgeKind};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Decompile a top-level `Proto` into a Lua source string.
pub fn decompile(proto: &Proto) -> String {
    let mut ctx = DecompileCtx::new(proto, 0);
    ctx.run();
    ctx.finish()
}

// ---------------------------------------------------------------------------
// Decompiler context
// ---------------------------------------------------------------------------

pub struct DecompileCtx<'p> {
    pub proto: &'p Proto,
    pub indent: usize,
    pub output: Vec<String>,
    /// `regs[i]` holds the last expression string assigned to register i.
    pub regs: Vec<String>,
    /// Registers that are loop-carried accumulators in the innermost active loop.
    /// Expression-building ops that write to these emit an assignment statement
    /// instead of (silently) updating the register expression string.
    pub loop_carried_regs: HashSet<usize>,
    /// Resolved upvalue names supplied by the parent context when creating this
    /// sub-context for a closure.  When non-empty, takes precedence over
    /// `proto.upvalue_names` for naming upvalue operands.
    pub upvalue_names: Vec<String>,
    /// Registers whose values were consumed by a SETLIST instruction.
    /// Their values are kept intact so arithmetic instructions that follow can
    /// still read them, but CALL/TAILCALL/RETURN B=0 sweeps skip these registers
    /// to avoid treating SETLIST sources as phantom call arguments.
    /// Cleared when any instruction writes to the register again.
    pub setlist_cleared: HashSet<usize>,
    /// Names that were assigned to for-loop variables (by `emit_generic_for` or
    /// the ForPrep handler).  These names are only valid inside the loop body;
    /// after the loop they are out-of-scope in Lua source.
    /// Used by `op_closure` to detect when a captured register holds a stale
    /// loop-variable name — even if the name reached the register via a MOVE
    /// rather than directly from the for-loop header — and needs a new shared
    /// `local` variable instead.
    pub loop_var_names: HashSet<String>,
}

impl<'p> DecompileCtx<'p> {
    pub fn new(proto: &'p Proto, indent: usize) -> Self {
        let maxstack = proto.maxstacksize as usize;
        Self {
            proto,
            indent,
            output: Vec::new(),
            regs: vec![String::new(); maxstack.max(1)],
            loop_carried_regs: HashSet::new(),
            upvalue_names: Vec::new(),
            setlist_cleared: HashSet::new(),
            loop_var_names: HashSet::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Output helpers
    // -----------------------------------------------------------------------

    pub fn emit(&mut self, line: impl Into<String>) {
        let indent = "  ".repeat(self.indent);
        self.output.push(format!("{}{}", indent, line.into()));
    }

    pub fn emit_raw(&mut self, line: impl Into<String>) {
        self.output.push(line.into());
    }

    pub fn finish(self) -> String {
        collapse_inline_tables(self.output).join("\n")
    }

    // -----------------------------------------------------------------------
    // Register helpers
    // -----------------------------------------------------------------------

    pub fn reg(&self, r: usize) -> &str {
        self.regs.get(r).map(|s| s.as_str()).unwrap_or("nil")
    }

    pub fn set_reg(&mut self, r: usize, expr: impl Into<String>) {
        if r < self.regs.len() {
            self.regs[r] = expr.into();
            self.setlist_cleared.remove(&r);
        }
    }

    /// Clone `self.regs`, but blank out any registers that are flagged as
    /// `setlist_cleared`.  Used when taking a pre-loop snapshot for
    /// loop-carried accumulator detection: a SETLIST-consumed register should
    /// not be mistaken for a live pre-loop value.
    pub fn regs_snapshot(&self) -> Vec<String> {
        let mut snap = self.regs.clone();
        for &r in &self.setlist_cleared {
            if r < snap.len() {
                snap[r] = String::new();
            }
        }
        snap
    }

    /// Like `set_reg`, but when `r` is a loop-carried accumulator, emits an
    /// assignment statement (`_accR = expr`) and keeps the stable name in the
    /// register instead of replacing it with the raw expression.
    fn set_reg_or_emit_assign(&mut self, r: usize, expr: impl Into<String>) {
        let expr = expr.into();
        let name = self.reg(r).to_string();
        // Only emit an assignment when the register already has a stable named
        // variable (e.g. `_accN`).  Reject anything that isn't a valid Lua lvalue:
        // empty strings, the out-of-bounds sentinel "nil", boolean/nil keywords,
        // and arithmetic/operator expressions (which start with a digit or operator).
        if self.loop_carried_regs.contains(&r) && is_valid_lvalue(&name) {
            self.emit(format!("{} = {}", name, expr));
            // Leave self.regs[r] as the stable name; don't overwrite it.
        } else {
            self.set_reg(r, expr);
        }
    }

    /// Scan the blocks reachable from `body_start` (up to but not including
    /// `stop_node`) for registers that are **read-before-write** accumulators:
    ///   1. had a non-empty expression *before* the loop, AND
    ///   2. are read (as a source operand of an expression-building op) inside the
    ///      loop body *before* being overwritten.
    ///
    /// A register that is merely overwritten without being read first is a
    /// scratch/temp variable — not a carried accumulator — and is excluded.
    /// Scan a generic-for loop body for MOVE instructions that copy a loop
    /// variable into another register, then check whether any of those
    /// destination registers are captured as on-stack upvalues by a CLOSURE in
    /// the loop's exit node.  Returns a set of registers that need a pre-declared
    /// shared `local _upvrN` variable so that (a) the loop body can emit
    /// `_upvrN = _vK` on each iteration and (b) the closure captures the live
    /// updated value rather than the nil that the loop variable holds after exit.
    fn find_promoted_loop_var_regs(
        &self,
        cfg: &Cfg,
        body_node: Option<NodeIndex>,
        stop_node: NodeIndex,
        exit_node: Option<NodeIndex>,
        ctrl_reg: usize,
        loop_var_count: usize,
    ) -> HashSet<usize> {
        // Step 1 — find registers that receive loop-variable values in the body.
        let loop_var_set: HashSet<usize> =
            (ctrl_reg + 1..=ctrl_reg + loop_var_count).collect();
        let mut derived: HashSet<usize> = HashSet::new();
        if let Some(start) = body_node {
            let mut worklist = vec![start];
            let mut seen: HashSet<NodeIndex> = HashSet::new();
            while let Some(n) = worklist.pop() {
                if n == stop_node || seen.contains(&n) { continue; }
                seen.insert(n);
                let bb = &cfg.graph[n];
                for pc in bb.start..=bb.end {
                    let instr = self.proto.code[pc];
                    if get_opcode(instr) == OpCode::Move {
                        let a = getarg_a(instr) as usize;
                        let b = getarg_b(instr) as usize;
                        if loop_var_set.contains(&b) {
                            derived.insert(a);
                        }
                    }
                }
                for succ in cfg.graph.neighbors(n) {
                    worklist.push(succ);
                }
            }
        }
        if derived.is_empty() { return HashSet::new(); }

        // Step 2 — scan the exit node for CLOSURE instructions whose upvalue
        // descriptors reference any of the derived registers.
        let mut promoted: HashSet<usize> = HashSet::new();
        if let Some(exit) = exit_node {
            let bb = &cfg.graph[exit];
            for pc in bb.start..=bb.end {
                let instr = self.proto.code[pc];
                if get_opcode(instr) == OpCode::Closure {
                    let bx = getarg_bx(instr) as usize;
                    if let Some(sub) = self.proto.p.get(bx) {
                        for desc in &sub.upvalue_infos {
                            if desc.on_stack && derived.contains(&(desc.idx as usize)) {
                                promoted.insert(desc.idx as usize);
                            }
                        }
                    }
                }
            }
        }
        promoted
    }

    fn find_loop_carried_regs(
        &self,
        cfg: &Cfg,
        body_start: NodeIndex,
        stop_node: NodeIndex,
        pre_loop_regs: &[String],
        exclude: &[usize],
    ) -> HashSet<usize> {
        let mut carried: HashSet<usize> = HashSet::new();
        let mut worklist = vec![body_start];
        let mut seen: HashSet<NodeIndex> = HashSet::new();
        while let Some(node) = worklist.pop() {
            if node == stop_node || seen.contains(&node) {
                continue;
            }
            seen.insert(node);
            let bb = &cfg.graph[node];
            // Per-block write tracking: once a register is written inside this
            // block's instruction sequence it is no longer a "pre-loop value".
            let mut written: HashSet<usize> = HashSet::new();
            for pc in bb.start..=bb.end {
                let instr = self.proto.code[pc];
                let op = get_opcode(instr);
                let a  = getarg_a(instr) as usize;
                let b  = getarg_b(instr) as usize;
                let c  = getarg_c(instr) as usize;
                // Always record any write to register A — even non-expr ops like
                // NEWTABLE, CALL, CLOSURE, VARARG write a fresh value to A, so
                // the register is no longer carrying its pre-loop expression.
                if writes_to_a(op) {
                    written.insert(a);
                }
                if !is_expr_op(op) {
                    continue;
                }
                // Check whether any SOURCE register carries a pre-loop value that
                // has not yet been overwritten in this block.
                for src in instr_source_regs(op, b, c) {
                    if !exclude.contains(&src)
                        && !self.loop_carried_regs.contains(&src)
                        && !written.contains(&src)
                        && src < pre_loop_regs.len()
                        && !pre_loop_regs[src].is_empty()
                    {
                        carried.insert(src);
                    }
                }
            }
            for succ in cfg.graph.neighbors(node) {
                worklist.push(succ);
            }
        }
        carried
    }

    // -----------------------------------------------------------------------
    // Constant helpers
    // -----------------------------------------------------------------------

    pub fn constant(&self, idx: usize) -> String {
        decompile_constant(self.proto, idx)
    }

    /// Resolve an RK operand to a source expression.
    /// If the high bit is set it's a constant index; otherwise it's a register.
    pub fn rk_expr(&self, v: usize) -> String {
        if v & 0x100 != 0 {
            // Constant: strip the marker bit and look up K table
            decompile_constant(self.proto, v & !0x100)
        } else {
            // Register: return the expression currently held there
            let s = self.reg(v);
            if s.is_empty() { format!("_r{}", v) } else { s.to_string() }
        }
    }

    pub fn global_name(&self, idx: usize) -> String {
        global_(self.proto, idx)
    }

    /// Resolve an upvalue index to a name string.
    /// Priority: resolved names from parent context → proto debug names → `_upvN`.
    pub fn upvalue_name(&self, idx: usize) -> String {
        self.upvalue_names
            .get(idx)
            .filter(|s| !s.is_empty())
            .cloned()
            .or_else(|| {
                self.proto.upvalue_names
                    .get(idx)
                    .filter(|s| !s.is_empty())
                    .cloned()
            })
            .unwrap_or_else(|| format!("_upv{}", idx))
    }

    // -----------------------------------------------------------------------
    // Main entry point
    // -----------------------------------------------------------------------

    pub fn run(&mut self) {
        let cfg = Cfg::build(self.proto);
        if cfg.graph.node_count() == 0 {
            return;
        }

        let doms = cfg.dominators();
        let mut visited: HashSet<NodeIndex> = HashSet::new();
        self.emit_node(&cfg, &doms, cfg.entry, None, &mut visited);
    }

    // -----------------------------------------------------------------------
    // Structural CFG traversal
    // -----------------------------------------------------------------------

    fn emit_node(
        &mut self,
        cfg: &Cfg,
        doms: &Dominators<NodeIndex>,
        node: NodeIndex,
        stop_at: Option<NodeIndex>,
        visited: &mut HashSet<NodeIndex>,
    ) {
        if Some(node) == stop_at || visited.contains(&node) {
            return;
        }
        visited.insert(node);

        let bb = cfg.graph[node].clone();
        let last_instr = self.proto.code[bb.end];
        let last_op = get_opcode(last_instr);

        match last_op {
            // ── Numeric for loop ───────────────────────────────────────────────
            OpCode::ForPrep => {
                // Emit setup instructions (everything before ForPrep)
                for pc in bb.start..bb.end {
                    self.emit_instr(pc);
                }

                let a = getarg_a(last_instr) as usize;
                let sbx = getarg_sbx(last_instr);
                let forloop_pc = jump_target(bb.end, sbx);
                let forloop_node = cfg.block_of[forloop_pc];

                // Collect edges from the ForLoop node
                let mut body_node = None;
                let mut exit_node = None;
                for edge in cfg.graph.edges(forloop_node) {
                    match edge.weight() {
                        EdgeKind::Back        => body_node = Some(edge.target()),
                        EdgeKind::FallThrough => exit_node = Some(edge.target()),
                        _ => {}
                    }
                }

                let start_expr = self.reg(a).to_string();
                let limit_expr = self.reg(a + 1).to_string();
                let step_expr  = self.reg(a + 2).to_string();
                let var_name   = format!("_i{}", a);

                // Pre-scan body for loop-carried accumulators.
                // Exclude the for-loop's own state registers (start/limit/step/var).
                let pre_loop_regs = self.regs_snapshot();
                let exclude_for = [a, a + 1, a + 2, a + 3];
                let carried = if let Some(body) = body_node {
                    self.find_loop_carried_regs(
                        cfg, body, forloop_node, &pre_loop_regs, &exclude_for,
                    )
                } else {
                    HashSet::new()
                };
                for &r in &carried {
                    let acc = format!("_acc{}", r);
                    self.emit(format!("local {} = {}", acc, pre_loop_regs[r]));
                    self.set_reg(r, acc);
                }

                let for_header = if step_expr == "1" {
                    format!("for {} = {}, {} do", var_name, start_expr, limit_expr)
                } else {
                    format!("for {} = {}, {}, {} do", var_name, start_expr, limit_expr, step_expr)
                };
                self.emit(for_header);
                self.indent += 1;
                self.set_reg(a + 3, var_name.clone());
                self.loop_var_names.insert(var_name);

                let mut merged = self.loop_carried_regs.clone();
                merged.extend(carried.iter().copied());
                let prev_carried = std::mem::replace(&mut self.loop_carried_regs, merged);
                if let Some(body) = body_node {
                    self.emit_node(cfg, doms, body, Some(forloop_node), visited);
                }
                self.loop_carried_regs = prev_carried;

                self.indent -= 1;
                self.emit("end");

                // Mark ForLoop block as visited so it is not re-emitted
                visited.insert(forloop_node);

                if let Some(exit) = exit_node {
                    self.emit_node(cfg, doms, exit, stop_at, visited);
                }
            }

            // ── ForLoop: handled by ForPrep above ─────────────────────────────
            OpCode::ForLoop => {}

            // ── Generic for loop (lua52/53): reached directly — fallback only.
            // The normal path is detected from the setup JMP below.
            OpCode::TForLoop => {}

            // ── Function exits ─────────────────────────────────────────────────
            OpCode::Return | OpCode::TailCall => {
                for pc in bb.start..=bb.end {
                    self.emit_instr(pc);
                }
            }

            // ── Jump (unconditional or conditional-paired) ─────────────────────
            OpCode::Jmp => {
                let sbx = getarg_sbx(last_instr);
                let target_pc   = jump_target(bb.end, sbx);
                let target_node = cfg.block_of[target_pc];

                let is_conditional = bb.end > bb.start
                    && is_skip_instr(get_opcode(self.proto.code[bb.end - 1]));

                if is_conditional {
                    self.emit_if(cfg, doms, node, stop_at, visited);
                } else if target_pc > bb.end
                    && get_opcode(self.proto.code[cfg.graph[target_node].end])
                        == OpCode::TForLoop
                {
                    // Unconditional forward JMP into a TForLoop block:
                    // this is the generic-for setup block.
                    self.emit_generic_for(cfg, doms, node, target_node, stop_at, visited);
                } else {
                    // Plain unconditional JMP: emit instructions, follow target.
                    // Guard re-entry with the visited set rather than a raw PC
                    // comparison: genuine loop back-edges are handled by the
                    // ForPrep/ForLoop/TForLoop cases above, so any unvisited
                    // backward-JMP target here is JMP-spaghetti obfuscation
                    // (scattered real instructions linked by unconditional JMPs)
                    // and should be followed normally.
                    for pc in bb.start..bb.end {
                        self.emit_instr(pc);
                    }
                    if !visited.contains(&target_node) {
                        self.emit_node(cfg, doms, target_node, stop_at, visited);
                    }
                }
            }

            // ── Normal sequential block ────────────────────────────────────────
            _ => {
                for pc in bb.start..=bb.end {
                    self.emit_instr(pc);
                }

                // Follow the single fall-through successor
                let succs: Vec<_> = cfg.graph.neighbors(node).collect();
                if let Some(&succ) = succs.first() {
                    self.emit_node(cfg, doms, succ, stop_at, visited);
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Generic for loop (lua 5.2/5.3)
    // -----------------------------------------------------------------------

    /// Called when we see an unconditional forward JMP whose target ends with TForLoop.
    /// `setup_node`    = the block containing the iterator-setup + JMP
    /// `tforloop_node` = the block ending with TFORLOOP (contains TFORCALL + TFORLOOP)
    fn emit_generic_for(
        &mut self,
        cfg: &Cfg,
        doms: &Dominators<NodeIndex>,
        setup_node: NodeIndex,
        tforloop_node: NodeIndex,
        stop_at: Option<NodeIndex>,
        visited: &mut HashSet<NodeIndex>,
    ) {
        visited.insert(setup_node);
        visited.insert(tforloop_node);

        let setup_bb = cfg.graph[setup_node].clone();
        let tfl_bb   = cfg.graph[tforloop_node].clone();

        // In Lua 5.3:
        //   TFORCALL A C  — func=R(A), state=R(A+1), ctrl=R(A+2), results=R(A+3)..R(A+2+C)
        //   TFORLOOP A sBx — A is the CONTROL register (= TFORCALL_A + 2)
        //                    loop vars start at R(A+1) = R(TFORCALL_A + 3)
        //
        // So TFORLOOP.A = ctrl register, and func register = TFORLOOP.A - 2.
        let tfl_instr = self.proto.code[tfl_bb.end];
        let ctrl_reg  = getarg_a(tfl_instr) as usize;  // TFORLOOP A
        let func_reg  = ctrl_reg.saturating_sub(2);    // TFORCALL A

        // Find body / exit edges from the TForLoop node
        let mut body_node = None;
        let mut exit_node = None;
        for edge in cfg.graph.edges(tforloop_node) {
            match edge.weight() {
                EdgeKind::Back        => body_node = Some(edge.target()),
                EdgeKind::FallThrough => exit_node = Some(edge.target()),
                _ => {}
            }
        }

        // Number of loop variables: C field of TFORCALL (LuaDecTForLoop),
        // which sits just before TFORLOOP in the same block.
        let loop_var_count = if tfl_bb.end > tfl_bb.start {
            let tforcall = self.proto.code[tfl_bb.end - 1];
            if get_opcode(tforcall) == OpCode::LuaDecTForLoop {
                (getarg_c(tforcall) as usize).max(1)
            } else {
                1
            }
        } else {
            1
        };

        // Walk the setup block instruction-by-instruction.
        // When we find CALL func_reg _ _ (the iterator-setup call), capture
        // the call expression directly instead of emitting it as a temp-var.
        let mut iter_expr = String::new();
        for pc in setup_bb.start..setup_bb.end {  // bb.end is the JMP — skip it
            let instr = self.proto.code[pc];
            let op    = get_opcode(instr);
            let ia    = getarg_a(instr) as usize;

            if iter_expr.is_empty() && op == OpCode::Call && ia == func_reg {
                // Only use as iterator setup if func_reg is NOT overwritten by a
                // later instruction in the same setup block.  If it is overwritten,
                // the CALL is a standalone statement and the actual iterator comes
                // from whatever writes func_reg afterward.
                let overwritten = (pc + 1..setup_bb.end).any(|later_pc| {
                    let li = self.proto.code[later_pc];
                    writes_to_a(get_opcode(li)) && getarg_a(li) as usize == func_reg
                });
                if !overwritten {
                    // Registers for func and its args are ready; build the expression.
                    let call_b = getarg_b(instr) as usize;
                    let func   = self.reg(func_reg).to_string();
                    let args   = if call_b <= 1 {
                        String::new()
                    } else {
                        (func_reg + 1..func_reg + call_b)
                            .map(|r| self.reg(r).to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    };
                    iter_expr = format!("{}({})", func, args);
                    // Consume this CALL silently — do NOT emit it as a local statement.
                } else {
                    // func_reg is overwritten later: this is a standalone call.
                    self.emit_instr(pc);
                }
            } else {
                self.emit_instr(pc);
            }
        }

        // Fallback: no CALL → iterator is supplied as explicit (func, state, ctrl).
        // Trim trailing nils for readability.
        if iter_expr.is_empty() {
            let f = self.reg(func_reg).to_string();
            let s = self.reg(func_reg + 1).to_string();
            let c = self.reg(func_reg + 2).to_string();
            let c_empty = c == "nil" || c.is_empty();
            let s_empty = s == "nil" || s.is_empty();
            iter_expr = if c_empty && s_empty {
                f
            } else if c_empty {
                format!("{}, {}", f, s)
            } else {
                format!("{}, {}, {}", f, s, c)
            };
        }

        // Pre-scan body for loop-carried accumulators before setting loop-var names.
        // Exclude the TFORCALL/TFORLOOP managed registers (func..loop-vars).
        let pre_loop_regs = self.regs_snapshot();
        let exclude_tfor: Vec<usize> = (func_reg..=ctrl_reg + loop_var_count).collect();
        let carried = if let Some(body) = body_node {
            self.find_loop_carried_regs(
                cfg, body, tforloop_node, &pre_loop_regs, &exclude_tfor,
            )
        } else {
            HashSet::new()
        };
        for &r in &carried {
            let acc = format!("_acc{}", r);
            self.emit(format!("local {} = {}", acc, pre_loop_regs[r]));
            self.set_reg(r, acc);
        }

        // Find registers that copy a loop variable and are then captured as
        // upvalues by a closure in the exit block.  These need a shared `local`
        // so the closure sees the live value from each iteration.
        let promoted = self.find_promoted_loop_var_regs(
            cfg, body_node, tforloop_node, exit_node, ctrl_reg, loop_var_count,
        );
        for &r in &promoted {
            let upv_name = format!("_upvr{}", r);
            self.emit(format!("local {} = nil", upv_name));
            self.set_reg(r, upv_name);
        }

        // Loop variables live at R(ctrl_reg+1), R(ctrl_reg+2), …
        let vars: Vec<String> = (0..loop_var_count)
            .map(|i| format!("_v{}", ctrl_reg + 1 + i))
            .collect();
        for (i, v) in vars.iter().enumerate() {
            let r = ctrl_reg + 1 + i;
            self.set_reg(r, v.clone());
            self.loop_var_names.insert(v.clone());
        }

        self.emit(format!("for {} in {} do", vars.join(", "), iter_expr));
        self.indent += 1;

        let mut merged = self.loop_carried_regs.clone();
        merged.extend(carried.iter().copied());
        // Promoted registers act as loop-carried variables so that MOVE
        // instructions inside the body emit `_upvrN = _vK` assignments.
        merged.extend(promoted.iter().copied());
        let prev_carried = std::mem::replace(&mut self.loop_carried_regs, merged);
        if let Some(body) = body_node {
            self.emit_node(cfg, doms, body, Some(tforloop_node), visited);
        }
        self.loop_carried_regs = prev_carried;

        self.indent -= 1;
        self.emit("end");

        if let Some(exit) = exit_node {
            self.emit_node(cfg, doms, exit, stop_at, visited);
        }
    }

    // -----------------------------------------------------------------------
    // If / else structure
    // -----------------------------------------------------------------------

    fn emit_if(
        &mut self,
        cfg: &Cfg,
        doms: &Dominators<NodeIndex>,
        node: NodeIndex,
        stop_at: Option<NodeIndex>,
        visited: &mut HashSet<NodeIndex>,
    ) {
        let bb = cfg.graph[node].clone();

        // Emit non-branch instructions in this block (everything before cond + JMP)
        for pc in bb.start..bb.end.saturating_sub(1) {
            self.emit_instr(pc);
        }

        let cond_pc  = bb.end - 1;
        let condition = self.condition_expr(cond_pc);

        // JMP target = "else" block or "end" (if no else)
        let jmp_instr      = self.proto.code[bb.end];
        let jmp_target_pc  = jump_target(bb.end, getarg_sbx(jmp_instr));
        let jmp_target     = cfg.block_of[jmp_target_pc];

        // Fall-through = "then" body
        let ft_pc = bb.end + 1;
        if ft_pc >= cfg.block_of.len() {
            self.emit(format!("if {} then", condition));
            self.indent -= 0; // no-op
            self.emit("end");
            return;
        }
        let fall_through = cfg.block_of[ft_pc];

        // Determine whether there is an else branch.
        // Walk the THEN region (blocks reachable from fall_through, stopping at jmp_target).
        // If the last block of the THEN region ends with a JMP whose target is AFTER jmp_target,
        // then jmp_target is the else-start and that JMP's target is the real "end".
        let then_region = self.collect_region(cfg, fall_through, jmp_target);
        let end_node    = self.find_region_end(cfg, &then_region, jmp_target);
        let has_else    = end_node != jmp_target;

        self.emit(format!("if {} then", condition));
        self.indent += 1;
        // When the condition is a compile-time constant false/nil the then-branch
        // is dead code that can never execute.  Snapshot the register state so we
        // can restore it afterwards: non-loop-carried registers written inside a
        // dead branch must not contaminate the join-point state.
        let dead_branch = condition == "nil" || condition == "false";
        let regs_before_dead = if dead_branch { Some(self.regs.clone()) } else { None };
        self.emit_node(cfg, doms, fall_through, Some(jmp_target), visited);
        self.indent -= 1;

        if has_else {
            self.emit("else");
            self.indent += 1;
            if let Some(ref snap) = regs_before_dead {
                self.regs = snap.clone();
            }
            self.emit_node(cfg, doms, jmp_target, Some(end_node), visited);
            self.indent -= 1;
        } else if let Some(snap) = regs_before_dead {
            // No else: restore so the continuation uses pre-dead-branch values.
            self.regs = snap;
        }

        self.emit("end");

        self.emit_node(cfg, doms, end_node, stop_at, visited);
    }

    /// Given a set of blocks forming the THEN region and the default end candidate,
    /// scan for any block that jumps past `default_end`; its target is the real end.
    fn find_region_end(
        &self,
        cfg: &Cfg,
        region: &HashSet<NodeIndex>,
        default_end: NodeIndex,
    ) -> NodeIndex {
        let default_pc = cfg.graph[default_end].start;
        for &n in region {
            let b    = &cfg.graph[n];
            let last = get_opcode(self.proto.code[b.end]);
            if last == OpCode::Jmp {
                let sbx       = getarg_sbx(self.proto.code[b.end]);
                let target_pc = jump_target(b.end, sbx);
                if target_pc > default_pc && target_pc < self.proto.sizecode {
                    return cfg.block_of[target_pc];
                }
            }
        }
        default_end
    }

    /// Collect all nodes reachable from `start` without passing through `stop`.
    fn collect_region(
        &self,
        cfg: &Cfg,
        start: NodeIndex,
        stop: NodeIndex,
    ) -> HashSet<NodeIndex> {
        let mut result   = HashSet::new();
        let mut worklist = vec![start];
        while let Some(n) = worklist.pop() {
            if n == stop || result.contains(&n) {
                continue;
            }
            result.insert(n);
            for succ in cfg.graph.neighbors(n) {
                worklist.push(succ);
            }
        }
        result
    }

    // -----------------------------------------------------------------------
    // Condition expression from a skip instruction
    // -----------------------------------------------------------------------

    fn condition_expr(&mut self, cond_pc: usize) -> String {
        let instr = self.proto.code[cond_pc];
        let op    = get_opcode(instr);
        let a     = getarg_a(instr) as usize;
        let b     = getarg_b(instr) as usize;
        let c     = getarg_c(instr) as usize;

        match op {
            OpCode::Eq => {
                let lhs = self.rk_expr(b);
                let rhs = self.rk_expr(c);
                if a == 0 { format!("{} == {}", lhs, rhs) }
                else       { format!("{} ~= {}", lhs, rhs) }
            }
            OpCode::Lt => {
                let lhs = self.rk_expr(b);
                let rhs = self.rk_expr(c);
                if a == 0 { format!("{} < {}", lhs, rhs) }
                else       { format!("{} >= {}", lhs, rhs) }
            }
            OpCode::Le => {
                let lhs = self.rk_expr(b);
                let rhs = self.rk_expr(c);
                if a == 0 { format!("{} <= {}", lhs, rhs) }
                else       { format!("{} > {}", lhs, rhs) }
            }
            OpCode::Test => {
                let r = self.reg(a).to_string();
                // C=0: if R[A] is truthy  (skip JMP → THEN)
                // C=1: if R[A] is falsy
                if c == 0 { r } else { format!("not {}", r) }
            }
            OpCode::TestSet => {
                let r = self.reg(b).to_string();
                if c == 0 { r } else { format!("not {}", r) }
            }
            OpCode::LuaDecTForLoop => {
                // lua51 generic for: condition is "iterator returned a value"
                format!("_v{} ~= nil", a + 1)
            }
            _ => "???".to_string(),
        }
    }

    // -----------------------------------------------------------------------
    // Single instruction emission
    // -----------------------------------------------------------------------

    fn emit_instr(&mut self, pc: usize) {
        let i   = self.proto.code[pc];
        let op  = get_opcode(i);
        let a   = getarg_a(i)  as usize;
        let b   = getarg_b(i)  as usize;
        let c   = getarg_c(i)  as usize;
        let bx  = getarg_bx(i) as usize;
        let _sbx = getarg_sbx(i);
        let _ax  = getarg_ax(i) as usize;

        match op {
            OpCode::Move           => self.op_move(a, b),
            OpCode::LoadK          => self.op_loadk(a, bx),
            OpCode::LoadKx         => self.op_loadkx(a),
            OpCode::LoadBool       => self.op_loadbool(a, b, c),
            OpCode::LoadNil        => self.op_loadnil(a, b),
            OpCode::GetUpVal       => self.op_getupval(a, b),
            OpCode::GetGlobal      => self.op_getglobal(a, bx),
            OpCode::GetTabUp       => self.op_gettabup(a, b, c),
            OpCode::GetTable       => self.op_gettable(a, b, c),
            OpCode::SetGlobal      => self.op_setglobal(a, bx),
            OpCode::SetTabUp       => self.op_settabup(a, b, c),
            OpCode::SetUpVal       => self.op_setupval(a, b),
            OpCode::SetTable       => self.op_settable(a, b, c),
            OpCode::NewTable       => self.op_newtable(pc, a),
            OpCode::Self_          => self.op_self(a, b, c),
            OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div
            | OpCode::Pow | OpCode::Mod | OpCode::IDiv | OpCode::Band
            | OpCode::Bor | OpCode::BXor | OpCode::Shl | OpCode::Shr
                                   => self.op_arith(a, b, c, op),
            OpCode::Unm            => self.op_unm(a, b),
            OpCode::Not            => self.op_not(a, b),
            OpCode::Len            => self.op_len(a, b),
            OpCode::BNot           => self.op_bnot(a, b),
            OpCode::Concat         => self.op_concat(a, b, c),
            OpCode::Call           => self.op_call(a, b, c),
            OpCode::TailCall       => self.op_tailcall(a, b),
            OpCode::Return         => self.op_return(a, b),
            OpCode::SetList        => self.op_setlist(a, b, c),
            OpCode::Closure        => self.op_closure(a, bx),
            OpCode::VarArg         => self.op_vararg(a, b),
            // These are all handled structurally by emit_node / emit_if:
            OpCode::Jmp | OpCode::ForLoop | OpCode::ForPrep
            | OpCode::TForLoop | OpCode::LuaDecTForLoop
            | OpCode::Eq | OpCode::Lt | OpCode::Le
            | OpCode::Test | OpCode::TestSet
            | OpCode::Close | OpCode::ExtraArg | OpCode::Unknown => {}
        }
    }

    // -----------------------------------------------------------------------
    // Per-opcode handlers
    // -----------------------------------------------------------------------

    /// MOVE  A B   →  R[A] = R[B]
    fn op_move(&mut self, a: usize, b: usize) {
        let val = self.reg(b).to_string();
        self.set_reg_or_emit_assign(a, val);
    }

    /// LOADK  A Bx   →  R[A] = K[Bx]
    fn op_loadk(&mut self, a: usize, bx: usize) {
        let val = self.constant(bx);
        self.set_reg_or_emit_assign(a, val);
    }

    /// LOADKX  A   →  R[A] = K[next.Ax]  (constant index in following EXTRAARG)
    fn op_loadkx(&mut self, a: usize) {
        self.set_reg_or_emit_assign(a, "???");
    }

    /// LOADBOOL  A B C   →  R[A] = (bool)B; if C then pc++
    fn op_loadbool(&mut self, a: usize, b: usize, _c: usize) {
        self.set_reg_or_emit_assign(a, if b != 0 { "true" } else { "false" });
    }

    /// LOADNIL  A B   →  R[A..A+B] = nil
    fn op_loadnil(&mut self, a: usize, b: usize) {
        for r in a..=a + b {
            self.set_reg_or_emit_assign(r, "nil");
        }
    }

    /// GETUPVAL  A B   →  R[A] = UpValue[B]
    fn op_getupval(&mut self, a: usize, b: usize) {
        let name = self.upvalue_name(b);
        self.set_reg_or_emit_assign(a, name);
    }

    /// GETGLOBAL  A Bx   →  R[A] = Gbl[K[Bx]]   (lua51)
    fn op_getglobal(&mut self, a: usize, bx: usize) {
        let name = self.global_name(bx);
        self.set_reg_or_emit_assign(a, name);
    }

    /// GETTABUP  A B C   →  R[A] = UpValue[B][RK(C)]
    fn op_gettabup(&mut self, a: usize, b: usize, c: usize) {
        let upv = self.upvalue_name(b);
        let key = self.rk_expr(c);
        // _ENV is Lua 5.2/5.3's global table
        let expr = if upv == "_ENV" { key } else { format!("{}[{}]", upv, key) };
        self.set_reg_or_emit_assign(a, expr);
    }

    /// GETTABLE  A B C   →  R[A] = R[B][RK(C)]
    fn op_gettable(&mut self, a: usize, b: usize, c: usize) {
        let tbl = reg_or_placeholder(&self.regs, b);
        let key = self.rk_expr(c);
        self.set_reg_or_emit_assign(a, format!("{}[{}]", tbl, key));
    }

    /// SETGLOBAL  A Bx   →  Gbl[K[Bx]] = R[A]   (lua51)
    fn op_setglobal(&mut self, a: usize, bx: usize) {
        let name = self.global_name(bx);
        let val  = self.reg(a).to_string();
        self.emit(format!("{} = {}", name, val));
    }

    /// SETTABUP  A B C   →  UpValue[A][RK(B)] = RK(C)
    fn op_settabup(&mut self, a: usize, b: usize, c: usize) {
        let upv = self.upvalue_name(a);
        let key = self.rk_expr(b);
        let val = self.rk_expr(c);
        if upv == "_ENV" {
            self.emit(format!("{} = {}", key, val));
        } else {
            self.emit(format!("{}[{}] = {}", upv, key, val));
        }
    }

    /// SETUPVAL  A B   →  UpValue[B] = R[A]
    fn op_setupval(&mut self, a: usize, b: usize) {
        let name = self.upvalue_name(b);
        let val = self.reg(a).to_string();
        self.emit(format!("{} = {}", name, val));
    }

    /// SETTABLE  A B C   →  R[A][RK(B)] = RK(C)
    fn op_settable(&mut self, a: usize, b: usize, c: usize) {
        let tbl = reg_or_placeholder(&self.regs, a);
        let key = self.rk_expr(b);
        let val = self.rk_expr(c);
        self.emit(format!("{}[{}] = {}", tbl, key, val));
    }

    /// NEWTABLE  A B C   →  R[A] = {}
    fn op_newtable(&mut self, pc: usize, a: usize) {
        let name = format!("_t{}", pc);
        self.emit(format!("local {} = {{}}", name));
        self.set_reg(a, name);
        // A NEWTABLE creates a fresh variable; the register is no longer
        // acting as a loop-carried accumulator from this point on.  Removing
        // it prevents subsequent scalar assignments from being emitted as
        // `_tN = "string"` statements.
        self.loop_carried_regs.remove(&a);
    }

    /// SELF  A B C   →  R[A+1] = R[B]; R[A] = R[B][RK(C)]
    fn op_self(&mut self, a: usize, b: usize, c: usize) {
        let obj    = self.reg(b).to_string();
        let method = self.rk_expr(c);
        self.set_reg_or_emit_assign(a + 1, obj.clone());
        self.set_reg_or_emit_assign(a, format!("{}[{}]", obj, method));
    }

    /// Binary arithmetic / bitwise   R[A] = RK(B) op RK(C)
    fn op_arith(&mut self, a: usize, b: usize, c: usize, op: OpCode) {
        let lhs = self.rk_expr(b);
        let rhs = self.rk_expr(c);
        let sym = match op {
            OpCode::Add  => "+",  OpCode::Sub  => "-",
            OpCode::Mul  => "*",  OpCode::Div  => "/",
            OpCode::Pow  => "^",  OpCode::Mod  => "%",
            OpCode::IDiv => "//", OpCode::Band => "&",
            OpCode::Bor  => "|",  OpCode::BXor => "~",
            OpCode::Shl  => "<<", OpCode::Shr  => ">>",
            _            => "?",
        };
        // Parenthesise operands when operator precedence requires it.
        // Lua precedence (low→high): or, and, comparison, |, ~, &, <<>>, .., +-, *//%^
        let lhs = match op {
            // Arithmetic ops (+,-,*,/,//,%): bitwise ops (|,~,&,<<,>>) have LOWER precedence,
            // so wrap lhs when it contains any of them.
            OpCode::Add | OpCode::Sub
                if has_toplevel_bitwise(&lhs) => format!("({})", lhs),
            // * / // % also bind tighter than + -: wrap lhs if it contains bare + or -
            // or any bitwise operator.
            OpCode::Mul | OpCode::Div | OpCode::IDiv | OpCode::Mod
                if has_toplevel_additive(&lhs) || has_toplevel_bitwise(&lhs) => format!("({})", lhs),
            // << >> bind tighter than &, ~, |: wrap lhs containing those.
            OpCode::Shl | OpCode::Shr
                if has_toplevel_bxor_or_bor(&lhs) => format!("({})", lhs),
            // & binds tighter than ~ and |.
            OpCode::Band if has_toplevel_bxor_or_bor(&lhs) => format!("({})", lhs),
            // ~ (BXor) binds tighter than |.
            OpCode::BXor if has_toplevel_bor(&lhs) => format!("({})", lhs),
            // ^ binds tighter than everything binary: wrap lhs if it has any binary op
            OpCode::Pow if has_toplevel_binary(&lhs) => format!("({})", lhs),
            _ => lhs,
        };
        let rhs = match op {
            // For subtraction, a - (b + c) ≠ a - b + c, so wrap rhs that has bare + or -
            // or bitwise ops.
            OpCode::Sub if has_toplevel_additive(&rhs) || has_toplevel_bitwise(&rhs) => format!("({})", rhs),
            // For Add: rhs with bitwise ops also needs wrapping (a + b ~ c = (a+b)~c wrong).
            OpCode::Add if has_toplevel_bitwise(&rhs) => format!("({})", rhs),
            // Same for * / // %
            OpCode::Mul | OpCode::Div | OpCode::IDiv | OpCode::Mod
                if has_toplevel_additive(&rhs) || has_toplevel_bitwise(&rhs) => format!("({})", rhs),
            // << >> rhs: wrap if it contains &, ~, |.
            OpCode::Shl | OpCode::Shr
                if has_toplevel_bxor_or_bor(&rhs) => format!("({})", rhs),
            // & rhs: wrap if it contains ~ or |.
            OpCode::Band if has_toplevel_bxor_or_bor(&rhs) => format!("({})", rhs),
            // ~ (BXor) rhs: wrap if it contains |.
            OpCode::BXor if has_toplevel_bor(&rhs) => format!("({})", rhs),
            // ^ is right-associative so rhs needs no parens for ^, but wrap other binary ops
            OpCode::Pow if has_toplevel_binary(&rhs) => format!("({})", rhs),
            _ => rhs,
        };
        self.set_reg_or_emit_assign(a, format!("{} {} {}", lhs, sym, rhs));
    }

    fn op_unm(&mut self, a: usize, b: usize) {
        let val = self.reg(b).to_string();
        self.set_reg_or_emit_assign(a, format!("-{}", val));
    }

    fn op_not(&mut self, a: usize, b: usize) {
        let val = self.reg(b).to_string();
        self.set_reg_or_emit_assign(a, format!("not {}", val));
    }

    fn op_len(&mut self, a: usize, b: usize) {
        let val = self.reg(b).to_string();
        self.set_reg_or_emit_assign(a, format!("#{}", val));
    }

    fn op_bnot(&mut self, a: usize, b: usize) {
        let val = self.reg(b).to_string();
        self.set_reg_or_emit_assign(a, format!("~{}", val));
    }

    fn op_concat(&mut self, a: usize, b: usize, c: usize) {
        let parts: Vec<String> = (b..=c).map(|r| self.reg(r).to_string()).collect();
        self.set_reg_or_emit_assign(a, parts.join(" .. "));
    }

    /// CALL  A B C   →  R[A..A+C-2] = R[A](R[A+1..A+B-1])
    fn op_call(&mut self, a: usize, b: usize, c: usize) {
        let func = self.reg(a).to_string();

        // Build argument string
        let args = if b == 0 {
            // Variable args: use all non-empty regs above A as best-effort.
            // Skip registers that were consumed by a preceding SETLIST — those
            // values are stale table-constructor sources, not call arguments.
            (a + 1..self.regs.len())
                .filter(|&r| !self.setlist_cleared.contains(&r))
                .map(|r| self.reg(r).to_string())
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>()
                .join(", ")
        } else {
            (a + 1..a + b)
                .map(|r| self.reg(r).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        };

        let call_expr = format!("{}({})", func, args);

        match c {
            1 => {
                // No results — emit as a standalone statement.
                self.emit(call_expr);
            }
            0 => {
                // Variable results (C=0): the VM places result(s) starting at R[A],
                // overwriting the function and its arguments.  Store the call
                // expression in R[A] (treating it as "at least one result") so the
                // next CALL/RETURN with B=0 can forward it correctly.
                // Clear the argument registers — they are consumed by the call and
                // their old values must not leak into subsequent B=0 collections.
                if b > 1 {
                    for r in (a + 1)..(a + b) {
                        self.set_reg(r, String::new());
                    }
                }
                self.set_reg_or_emit_assign(a, call_expr);
            }
            2 => {
                // 1 result → store in R[A]
                self.set_reg_or_emit_assign(a, call_expr);
            }
            _ => {
                // Multiple results → R[A..A+C-2]
                let count = c - 1;
                let names: Vec<String> = (a..a + count)
                    .map(|r| format!("_r{}", r))
                    .collect();
                for (i, name) in names.iter().enumerate() {
                    self.set_reg(a + i, name.clone());
                }
                self.emit(format!("local {} = {}", names.join(", "), call_expr));
            }
        }
    }

    /// TAILCALL  A B   →  return R[A](R[A+1..A+B-1])
    fn op_tailcall(&mut self, a: usize, b: usize) {
        let func = self.reg(a).to_string();
        let args = if b == 0 {
            (a + 1..self.regs.len())
                .filter(|&r| !self.setlist_cleared.contains(&r))
                .map(|r| self.reg(r).to_string())
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>()
                .join(", ")
        } else {
            (a + 1..a + b)
                .map(|r| self.reg(r).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        };
        self.emit(format!("return {}({})", func, args));
    }

    /// RETURN  A B   →  return R[A..A+B-2]
    fn op_return(&mut self, a: usize, b: usize) {
        let line = match b {
            0 => {
                // return everything from A upward
                let vals: Vec<_> = (a..self.regs.len())
                    .filter(|&r| !self.setlist_cleared.contains(&r))
                    .map(|r| self.reg(r).to_string())
                    .filter(|s| !s.is_empty())
                    .collect();
                if vals.is_empty() { "return".to_string() }
                else               { format!("return {}", vals.join(", ")) }
            }
            1 => "return".to_string(),
            _ => {
                let vals: Vec<_> = (a..a + b - 1)
                    .map(|r| self.reg(r).to_string())
                    .collect();
                format!("return {}", vals.join(", "))
            }
        };
        self.emit(line);
    }

    /// SETLIST  A B C   →  R[A][(C-1)*FPF+i] = R[A+i], 1<=i<=B
    fn op_setlist(&mut self, a: usize, b: usize, c: usize) {
        let base = (c.saturating_sub(1)) * 50; // LFIELDS_PER_FLUSH
        let tbl  = self.reg(a).to_string();
        let count = if b == 0 {
            // b=0 means the previous instruction (CALL/VARARG) produced a variable
            // number of results. Trim trailing empty registers so we don't emit
            // phantom ", , ," entries for registers that were never actually filled.
            (a + 1..self.regs.len())
                .rev()
                .find(|&r| !self.reg(r).is_empty())
                .map_or(0, |r| r - a)
        } else {
            b
        };
        for i in 1..=count {
            if a + i < self.regs.len() {
                let raw = self.reg(a + i);
                let val = if raw.is_empty() { "nil".to_string() } else { raw.to_string() };
                self.emit(format!("{}[{}] = {}", tbl, base + i, val));
            }
        }
        // Mark the source registers as "setlist-consumed".  We keep their
        // values so arithmetic instructions after this point can still read
        // them (e.g. a constant 1 loaded for a table literal that is also used
        // in a loop accumulator), but CALL/TAILCALL/RETURN B=0 sweeps will
        // skip these registers so they don't appear as phantom call arguments.
        for i in 1..=count {
            if a + i < self.regs.len() {
                self.setlist_cleared.insert(a + i);
            }
        }
    }

    /// CLOSURE  A Bx   →  R[A] = function(proto[Bx])
    fn op_closure(&mut self, a: usize, bx: usize) {
        if let Some(sub) = self.proto.p.get(bx) {
            // Build parameter list
            let mut params: Vec<String> = (0..sub.numparams as usize)
                .map(|i| format!("_p{}", i))
                .collect();
            if sub.is_vararg != 0 {
                params.push("...".to_string());
            }

            // Resolve each upvalue of the sub-proto to a name using the upvalue
            // descriptor (`on_stack` + `idx`) and the current register / upvalue state.
            let resolved: Vec<String> = sub.upvalue_infos.iter().enumerate().map(|(i, desc)| {
                if desc.on_stack {
                    // Captured from a register in the current (parent) frame.
                    let s = self.reg(desc.idx as usize).to_string();
                    // Only propagate names that are valid Lua lvalues; fall back
                    // to _upvN for literals like "false"/"true"/arithmetic exprs.
                    if is_valid_lvalue(&s) { s } else { format!("_upv{}", i) }
                } else {
                    // Inherited from the current frame's own upvalue.
                    self.upvalue_name(desc.idx as usize)
                }
            }).collect();

            let fname = format!("_f{}", bx);
            self.emit(format!("local {} = function({})", fname, params.join(", ")));
            self.indent += 1;

            // Decompile the sub-prototype at the current indent level
            let saved_indent = self.indent;
            let mut sub_ctx = DecompileCtx::new(sub, saved_indent);
            sub_ctx.upvalue_names = resolved;
            // Seed parameter registers so ops like LEN/GETTABLE inside the
            // sub-function see the correct names instead of empty strings.
            for i in 0..sub.numparams as usize {
                sub_ctx.set_reg(i, format!("_p{}", i));
            }
            sub_ctx.run();
            let body = sub_ctx.finish();
            for line in body.lines() {
                self.emit_raw(line.to_string());
            }

            self.indent -= 1;
            self.emit("end");
            self.set_reg(a, fname);
            // Same as NEWTABLE: fresh variable, end the accumulator lifetime.
            self.loop_carried_regs.remove(&a);
        } else {
            self.set_reg(a, format!("<closure {}>", bx));
        }
    }

    /// VARARG  A B   →  R[A..A+B-2] = vararg
    fn op_vararg(&mut self, a: usize, b: usize) {
        let count = if b <= 1 { 1 } else { b - 1 };
        for i in 0..count {
            self.set_reg(a + i, "...".to_string());
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Inline table constructor collapsing
// ---------------------------------------------------------------------------

/// Post-process the emitted lines and replace patterns like
///
/// ```lua
/// local _tN = {}
/// _tN[1] = v1
/// _tN[2] = v2
/// ...
/// ```
///
/// with the compact constructor form:
///
/// ```lua
/// local _tN = {v1, v2, ...}          -- up to 6 items: single line
/// local _tN = {                       -- 7+ items: multi-line, 8 per row
///   v1, v2, v3, v4, v5, v6, v7, v8,
///   ...
/// }
/// ```
///
/// Non-consecutive or non-integer keys are left unchanged.
fn collapse_inline_tables(lines: Vec<String>) -> Vec<String> {
    let mut out: Vec<String> = Vec::with_capacity(lines.len());
    let mut i = 0;

    while i < lines.len() {
        // Try to match `<indent>local <name> = {}`
        if let Some((indent, name)) = parse_newtable_line(&lines[i]) {
            // Greedily consume `<indent><name>[k] = <val>` lines (k = 1, 2, …)
            let mut vals: Vec<String> = Vec::new();
            let mut j = i + 1;
            loop {
                let expected_key = vals.len() + 1;
                match lines.get(j).and_then(|l| parse_settable_line(l, &indent, &name, expected_key)) {
                    Some(val) => { vals.push(val); j += 1; }
                    None      => break,
                }
            }

            if vals.is_empty() {
                out.push(lines[i].clone());
            } else {
                out.extend(build_table_constructor(&indent, &name, &vals));
            }
            i = j;
        } else {
            out.push(lines[i].clone());
            i += 1;
        }
    }

    out
}

/// Match `<indent>local <name> = {}` → `Some((indent, name))`.
fn parse_newtable_line(line: &str) -> Option<(String, String)> {
    let trimmed = line.trim_start();
    let indent  = &line[..line.len() - trimmed.len()];
    let rest    = trimmed.strip_prefix("local ")?;
    let (name, tail) = rest.split_once(" = {}")?;
    if !tail.is_empty() || name.is_empty() { return None; }
    Some((indent.to_owned(), name.to_owned()))
}

/// Match `<indent><name>[<key>] = <value>` → `Some(value_str)`.
fn parse_settable_line(line: &str, indent: &str, name: &str, key: usize) -> Option<String> {
    let prefix = format!("{}{}[{}] = ", indent, name, key);
    line.strip_prefix(&prefix).map(str::to_owned)
}

/// Emit a table constructor, single-line for ≤ 6 values, multi-line otherwise.
fn build_table_constructor(indent: &str, name: &str, vals: &[String]) -> Vec<String> {
    const SINGLE_LINE_MAX: usize = 6;
    const PER_ROW: usize = 8;

    if vals.len() <= SINGLE_LINE_MAX {
        return vec![format!("{}local {} = {{{}}}", indent, name, vals.join(", "))];
    }

    let inner = format!("{}  ", indent);
    let mut lines = vec![format!("{}local {} = {{", indent, name)];
    for chunk in vals.chunks(PER_ROW) {
        lines.push(format!("{}{},", inner, chunk.join(", ")));
    }
    lines.push(format!("{}}}", indent));
    lines
}

/// Returns the register indices that this expression-building instruction reads
/// as *source* operands (i.e., not the destination A).
/// Used to detect read-before-write accumulator patterns in loop bodies.
fn instr_source_regs(op: OpCode, b: usize, c: usize) -> Vec<usize> {
    match op {
        // Single source in B
        OpCode::Move | OpCode::Unm | OpCode::Not | OpCode::Len | OpCode::BNot => vec![b],
        // Table[key]: B is the table register; C is RK (register if < 256)
        OpCode::GetTable | OpCode::Self_ => {
            let mut srcs = vec![b];
            if c & 0x100 == 0 { srcs.push(c); }
            srcs
        }
        // UpValue[RK(C)]: B is an upvalue index (not a register); C is RK
        OpCode::GetTabUp => {
            if c & 0x100 == 0 { vec![c] } else { vec![] }
        }
        // Binary ops: B and C are both RK
        OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div | OpCode::Pow
        | OpCode::Mod | OpCode::IDiv | OpCode::Band | OpCode::Bor | OpCode::BXor
        | OpCode::Shl | OpCode::Shr => {
            let mut srcs = vec![];
            if b & 0x100 == 0 { srcs.push(b); }
            if c & 0x100 == 0 { srcs.push(c); }
            srcs
        }
        // CONCAT reads the whole register range [B..=C]
        OpCode::Concat => (b..=c).collect(),
        // LoadK, LoadKx, LoadBool, LoadNil, GetUpVal, GetGlobal: no register sources
        _ => vec![],
    }
}

/// Returns true for opcodes that write a new value into register A.
/// Used to track "written" registers in loop-carried accumulator detection so
/// that statement-emitting ops (NEWTABLE, CALL, CLOSURE, VARARG, …) correctly
/// mark their destination as no longer carrying a pre-loop value.
fn writes_to_a(op: OpCode) -> bool {
    !matches!(
        op,
        // Instructions that do NOT write register A:
        OpCode::SetGlobal | OpCode::SetTabUp | OpCode::SetUpVal | OpCode::SetTable
        | OpCode::SetList | OpCode::Jmp | OpCode::ForLoop | OpCode::ForPrep
        | OpCode::TForLoop | OpCode::LuaDecTForLoop | OpCode::TailCall
        | OpCode::Return | OpCode::Unknown
    )
}

/// Returns true for opcodes that write an expression into a single destination
/// register without emitting a Lua statement — these are the candidates for
/// loop-carried accumulator detection.
fn is_expr_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Move
            | OpCode::LoadK
            | OpCode::LoadKx
            | OpCode::LoadBool
            | OpCode::LoadNil
            | OpCode::GetUpVal
            | OpCode::GetGlobal
            | OpCode::GetTabUp
            | OpCode::GetTable
            | OpCode::Self_
            | OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Div
            | OpCode::Pow
            | OpCode::Mod
            | OpCode::IDiv
            | OpCode::Band
            | OpCode::Bor
            | OpCode::BXor
            | OpCode::Shl
            | OpCode::Shr
            | OpCode::Unm
            | OpCode::Not
            | OpCode::Len
            | OpCode::BNot
            | OpCode::Concat
    )
}

/// Return true iff `name` is a valid Lua lvalue (can appear on the left-hand
/// side of an assignment).  Rules:
///   1. Non-empty.
///   2. First character is `_` or an ASCII letter (rejects digits, operators,
///      `#`, `"`, etc.).
///   3. The leading identifier token (chars up to the first non-`[_a-zA-Z0-9]`)
///      must not be a Lua reserved keyword.  This catches exact keywords
///      (`"nil"`, `"false"`) as well as compound expressions that start with
///      one (`"nil - nil"`, `"not _x"`, `"true or false"`, …).
fn is_valid_lvalue(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    if !name.starts_with(|c: char| c == '_' || c.is_ascii_alphabetic()) {
        return false;
    }
    // Extract leading identifier token.
    let end = name.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(name.len());
    let tok = &name[..end];
    if matches!(
        tok,
        "nil" | "true" | "false" | "not" | "and" | "or"
        | "if" | "then" | "else" | "elseif" | "end"
        | "do" | "while" | "repeat" | "until"
        | "for" | "in" | "local" | "function" | "return" | "break" | "goto"
    ) {
        return false;
    }
    // After the identifier, only `[` (table index) or `.` (field) or end-of-string
    // are valid lvalue continuations.  Spaces, operators, `#`, `"`, etc. mean the
    // whole thing is a compound expression, not an lvalue.
    match name.as_bytes().get(end) {
        None | Some(b'[') | Some(b'.') => true,
        _ => false,
    }
}

/// True if `expr` is a simple literal that can safely be kept in a register
/// after SETLIST (number, quoted string, boolean, nil).  Complex expressions
/// (variable names, table accesses, calls) are cleared so they don't leak
/// into unrelated CALL argument lists.
fn is_simple_literal(expr: &str) -> bool {
    if expr.is_empty() { return false; }
    // nil / true / false
    if matches!(expr, "nil" | "true" | "false") { return true; }
    // quoted string: starts and ends with "
    if expr.starts_with('"') && expr.ends_with('"') { return true; }
    // number literal: optional minus then digits / hex / float
    let s = expr.strip_prefix('-').unwrap_or(expr);
    s.starts_with(|c: char| c.is_ascii_digit())
        || s.starts_with("0x") || s.starts_with("0X")
}

/// True if `expr` contains a `+` or `-` binary operator at the top level
/// (i.e., not inside parentheses/brackets).  Used for precedence-aware
/// parenthesisation in `op_arith`.
fn has_toplevel_additive(expr: &str) -> bool {
    let mut depth: i32 = 0;
    let bytes = expr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'+' | b'-' if depth == 0 && i > 0 => return true,
            _ => {}
        }
        i += 1;
    }
    false
}

/// True if `expr` contains ANY binary operator at the top level.
fn has_toplevel_binary(expr: &str) -> bool {
    if has_toplevel_additive(expr) {
        return true;
    }
    let mut depth: i32 = 0;
    let bytes = expr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'*' | b'/' | b'%' | b'^' | b'&' | b'|' | b'~'
                if depth == 0 && i > 0 => return true,
            _ => {}
        }
        i += 1;
    }
    false
}

/// True if `expr` contains a bitwise/shift operator (`&`, `|`, `~`, `<<`, `>>`)
/// at the top level.  These all have lower precedence than arithmetic (+,-,*,/,//,%),
/// so arithmetic operands containing them need parentheses.
fn has_toplevel_bitwise(expr: &str) -> bool {
    let mut depth: i32 = 0;
    let bytes = expr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'&' | b'|' if depth == 0 && i > 0 => return true,
            b'~' if depth == 0 && i > 0 => return true,
            b'<' if depth == 0 && i > 0
                && bytes.get(i + 1) == Some(&b'<') => return true,
            b'>' if depth == 0 && i > 0
                && bytes.get(i + 1) == Some(&b'>') => return true,
            _ => {}
        }
        i += 1;
    }
    false
}

/// True if `expr` contains `~` (BXor) or `|` (Bor) at the top level.
/// Used to parenthesise operands of `<<`/`>>` and `&`.
fn has_toplevel_bxor_or_bor(expr: &str) -> bool {
    let mut depth: i32 = 0;
    let bytes = expr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'~' | b'|' if depth == 0 && i > 0 => return true,
            _ => {}
        }
        i += 1;
    }
    false
}

/// True if `expr` contains `|` (Bor) at the top level.
/// Used to parenthesise operands of `~` (BXor).
fn has_toplevel_bor(expr: &str) -> bool {
    let mut depth: i32 = 0;
    let bytes = expr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'|' if depth == 0 && i > 0 => return true,
            _ => {}
        }
        i += 1;
    }
    false
}

/// Return the register's current expression string, or `_r{r}` if unset.
fn reg_or_placeholder(regs: &[String], r: usize) -> String {
    match regs.get(r) {
        Some(s) if !s.is_empty() => s.clone(),
        _ => format!("_r{}", r),
    }
}

/// Standard Lua branch-target formula: pc + 1 + sbx.
#[inline]
fn jump_target(pc: usize, sbx: i32) -> usize {
    (pc as i64 + 1 + sbx as i64) as usize
}

/// Returns true for instructions that skip the immediately following JMP
/// when their condition is satisfied — forming a two-instruction conditional branch.
#[inline]
fn is_skip_instr(op: OpCode) -> bool {
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
