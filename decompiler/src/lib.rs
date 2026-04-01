pub mod cfg;
pub mod linearize;

use std::collections::BTreeSet;

use petgraph::algo::dominators::Dominators;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;

use disassembler::{
    Proto, OpCode, LuaConstant, LuaNumber,
    get_opcode, getarg_a, getarg_b, getarg_c, getarg_bx, getarg_sbx, getarg_ax,
    global_,
};

use lua_ast::{
    Block, Expr, Stat, BinOp, UnOp, FuncBody, TableField,
    print_block,
};

use crate::cfg::{Cfg, EdgeKind};

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Decompile a top-level `Proto` to a Lua AST block.
pub fn decompile_to_block(proto: &Proto) -> Block {
    let mut ctx = DecompileCtx::new(proto);
    ctx.run();
    consolidate_tables(&mut ctx.output);
    ctx.output
}

/// Decompile a `Proto` to a Lua source string.
pub fn decompile(proto: &Proto) -> String {
    print_block(&decompile_to_block(proto), 0)
}

/// Decompile a CFF-obfuscated `Proto` to an AST block.
pub fn decompile_cff_to_block(proto: &Proto) -> Block {
    let linearized = linearize::linearize_tree(proto);
    let mut ctx = DecompileCtx::new(&linearized);
    ctx.run();
    consolidate_tables(&mut ctx.output);
    ctx.output
}

/// Decompile a CFF-obfuscated `Proto` to a Lua source string.
pub fn decompile_cff(proto: &Proto) -> String {
    print_block(&decompile_cff_to_block(proto), 0)
}

// ---------------------------------------------------------------------------
// Decompiler context
// ---------------------------------------------------------------------------

pub struct DecompileCtx<'p> {
    pub proto: &'p Proto,
    /// Emitted statements for this function scope.
    pub output: Block,
    /// `regs[i]` holds the last expression assigned to register `i`.
    /// `None` = not yet assigned (will appear as `_rN` if used).
    pub regs: Vec<Option<Expr>>,
    /// Registers that are loop-carried accumulators.
    pub loop_carried_regs: BTreeSet<usize>,
    /// Resolved upvalue names from parent context.
    pub upvalue_names: Vec<String>,
    /// Registers consumed by SETLIST (values kept but skipped in B=0 sweeps).
    pub setlist_cleared: BTreeSet<usize>,
    /// Names assigned to for-loop variables (to detect stale captures).
    pub loop_var_names: BTreeSet<String>,
}

impl<'p> DecompileCtx<'p> {
    pub fn new(proto: &'p Proto) -> Self {
        let maxstack = proto.maxstacksize as usize;
        Self {
            proto,
            output: Vec::new(),
            regs: vec![None; maxstack.max(1)],
            loop_carried_regs: BTreeSet::new(),
            upvalue_names: Vec::new(),
            setlist_cleared: BTreeSet::new(),
            loop_var_names: BTreeSet::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Register helpers
    // -----------------------------------------------------------------------

    /// Get the expression in register `r`, or `None` if unset/out-of-bounds.
    pub fn reg(&self, r: usize) -> Option<&Expr> {
        self.regs.get(r)?.as_ref()
    }

    /// Get the expression in `r`, or `Expr::Name("_rN")` as placeholder.
    pub fn reg_or_placeholder(&self, r: usize) -> Expr {
        self.regs.get(r)
            .and_then(|e| e.clone())
            .unwrap_or_else(|| Expr::Name(format!("_r{}", r)))
    }

    pub fn set_reg(&mut self, r: usize, expr: Expr) {
        if r < self.regs.len() {
            self.regs[r] = Some(expr);
            self.setlist_cleared.remove(&r);
        }
    }

    pub fn clear_reg(&mut self, r: usize) {
        if r < self.regs.len() {
            self.regs[r] = None;
        }
    }

    /// Snapshot registers for pre-loop analysis, blanking setlist-consumed ones.
    pub fn regs_snapshot(&self) -> Vec<Option<Expr>> {
        let mut snap = self.regs.clone();
        for &r in &self.setlist_cleared {
            if r < snap.len() { snap[r] = None; }
        }
        snap
    }

    /// Set register, but when it's a loop-carried accumulator with a named lvalue,
    /// emit an assignment statement instead of updating the register silently.
    fn set_reg_or_emit_assign(&mut self, r: usize, expr: Expr) {
        if self.loop_carried_regs.contains(&r) {
            if let Some(Some(lval)) = self.regs.get(r) {
                if is_expr_lvalue(lval) {
                    let lval = lval.clone();
                    self.output.push(Stat::Assign { lhs: vec![lval], rhs: vec![expr] });
                    return;
                }
            }
        }
        self.set_reg(r, expr);
    }

    // -----------------------------------------------------------------------
    // Constant / name helpers
    // -----------------------------------------------------------------------

    pub fn constant_expr(&self, idx: usize) -> Expr {
        match self.proto.constants.get(idx) {
            None => Expr::Nil,
            Some(c) => lua_const_to_expr(c),
        }
    }

    /// Resolve an RK operand to an expression.
    pub fn rk_expr(&self, v: usize) -> Expr {
        if v & 0x100 != 0 {
            self.constant_expr(v & !0x100)
        } else {
            self.reg_or_placeholder(v)
        }
    }

    pub fn global_name(&self, idx: usize) -> String {
        global_(self.proto, idx)
    }

    /// Resolve an upvalue index to a name string.
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
    // Loop analysis
    // -----------------------------------------------------------------------

    fn find_loop_carried_regs(
        &self,
        cfg: &Cfg,
        body_start: NodeIndex,
        stop_node: NodeIndex,
        pre_loop_regs: &[Option<Expr>],
        exclude: &[usize],
    ) -> BTreeSet<usize> {
        let mut body_nodes: Vec<NodeIndex> = Vec::new();
        let mut seen: BTreeSet<NodeIndex> = BTreeSet::new();
        let mut worklist = vec![body_start];
        while let Some(node) = worklist.pop() {
            if node == stop_node || seen.contains(&node) { continue; }
            seen.insert(node);
            body_nodes.push(node);
            for succ in cfg.graph.neighbors(node) { worklist.push(succ); }
        }
        body_nodes.sort_by_key(|&n| cfg.graph[n].start);

        let mut carried: BTreeSet<usize> = BTreeSet::new();
        let mut written: BTreeSet<usize> = BTreeSet::new();

        for node in body_nodes {
            let bb = &cfg.graph[node];
            for pc in bb.start..=bb.end {
                let instr = self.proto.code[pc];
                let op = get_opcode(instr);
                let a  = getarg_a(instr) as usize;
                let b  = getarg_b(instr) as usize;
                let c  = getarg_c(instr) as usize;
                if writes_to_a(op) { written.insert(a); }
                if !is_expr_op(op) { continue; }
                for src in instr_source_regs(op, b, c) {
                    if !exclude.contains(&src)
                        && !self.loop_carried_regs.contains(&src)
                        && !written.contains(&src)
                        && src < pre_loop_regs.len()
                        && pre_loop_regs[src].is_some()
                    {
                        carried.insert(src);
                    }
                }
            }
        }
        carried
    }

    fn find_promoted_loop_var_regs(
        &self,
        cfg: &Cfg,
        body_node: Option<NodeIndex>,
        stop_node: NodeIndex,
        exit_node: Option<NodeIndex>,
        ctrl_reg: usize,
        loop_var_count: usize,
    ) -> BTreeSet<usize> {
        let loop_var_set: BTreeSet<usize> =
            (ctrl_reg + 1..=ctrl_reg + loop_var_count).collect();
        let mut derived: BTreeSet<usize> = BTreeSet::new();
        if let Some(start) = body_node {
            let mut worklist = vec![start];
            let mut seen: BTreeSet<NodeIndex> = BTreeSet::new();
            while let Some(n) = worklist.pop() {
                if n == stop_node || seen.contains(&n) { continue; }
                seen.insert(n);
                let bb = &cfg.graph[n];
                for pc in bb.start..=bb.end {
                    let instr = self.proto.code[pc];
                    if get_opcode(instr) == OpCode::Move {
                        let a = getarg_a(instr) as usize;
                        let b = getarg_b(instr) as usize;
                        if loop_var_set.contains(&b) { derived.insert(a); }
                    }
                }
                for succ in cfg.graph.neighbors(n) { worklist.push(succ); }
            }
        }
        if derived.is_empty() { return BTreeSet::new(); }

        let mut promoted: BTreeSet<usize> = BTreeSet::new();
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

    // -----------------------------------------------------------------------
    // Main entry point
    // -----------------------------------------------------------------------

    pub fn run(&mut self) {
        if self.proto.code.is_empty() { return; }
        let cfg = Cfg::build(self.proto);
        if cfg.graph.node_count() == 0 { return; }
        let doms = cfg.dominators();
        let mut visited: BTreeSet<NodeIndex> = BTreeSet::new();
        self.emit_node(&cfg, &doms, cfg.entry, None, &mut visited);
    }

    // -----------------------------------------------------------------------
    // Statement collection helper
    // -----------------------------------------------------------------------

    /// Temporarily swap `output`, run `emit_node`, and return the collected stmts.
    fn collect_node_stmts(
        &mut self,
        cfg: &Cfg,
        doms: &Dominators<NodeIndex>,
        node: NodeIndex,
        stop_at: Option<NodeIndex>,
        visited: &mut BTreeSet<NodeIndex>,
    ) -> Block {
        let saved = std::mem::take(&mut self.output);
        self.emit_node(cfg, doms, node, stop_at, visited);
        std::mem::replace(&mut self.output, saved)
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
        visited: &mut BTreeSet<NodeIndex>,
    ) {
        if Some(node) == stop_at || visited.contains(&node) { return; }
        visited.insert(node);

        let bb = cfg.graph[node].clone();
        let last_instr = self.proto.code[bb.end];
        let last_op = get_opcode(last_instr);

        match last_op {
            // ── Numeric for loop ───────────────────────────────────────────
            OpCode::ForPrep => {
                for pc in bb.start..bb.end { self.emit_instr(pc); }

                let a    = getarg_a(last_instr) as usize;
                let sbx  = getarg_sbx(last_instr);
                let forloop_pc   = jump_target(bb.end, sbx);
                let forloop_node = cfg.block_of[forloop_pc];

                let mut body_node = None;
                let mut exit_node = None;
                for edge in cfg.graph.edges(forloop_node) {
                    match edge.weight() {
                        EdgeKind::Back        => body_node = Some(edge.target()),
                        EdgeKind::FallThrough => exit_node = Some(edge.target()),
                        _ => {}
                    }
                }

                let start_expr = self.reg_or_placeholder(a);
                let limit_expr = self.reg_or_placeholder(a + 1);
                let step_expr  = self.reg_or_placeholder(a + 2);
                let var_name   = format!("_i{}", a);

                let pre_loop_regs = self.regs_snapshot();
                let exclude_for = [a, a + 1, a + 2, a + 3];
                let carried = if let Some(body) = body_node {
                    self.find_loop_carried_regs(cfg, body, forloop_node, &pre_loop_regs, &exclude_for)
                } else { BTreeSet::new() };

                for &r in &carried {
                    let acc = format!("_acc{}", r);
                    let init = pre_loop_regs[r].clone().unwrap_or(Expr::Nil);
                    self.output.push(Stat::Local { names: vec![acc.clone()], values: vec![init] });
                    self.set_reg(r, Expr::Name(acc));
                }

                let step_opt = if step_expr == Expr::Integer(1) { None } else { Some(step_expr) };

                self.set_reg(a + 3, Expr::Name(var_name.clone()));
                self.loop_var_names.insert(var_name.clone());

                let mut merged = self.loop_carried_regs.clone();
                merged.extend(carried.iter().copied());
                let prev_carried = std::mem::replace(&mut self.loop_carried_regs, merged);

                let body_stmts = if let Some(body) = body_node {
                    let mut v = visited.clone();
                    self.collect_node_stmts(cfg, doms, body, Some(forloop_node), &mut v)
                } else { vec![] };
                // Mark all visited nodes from body traversal
                if let Some(body) = body_node {
                    let mut dummy_v = visited.clone();
                    self.emit_node_mark_only(cfg, body, forloop_node, &mut dummy_v);
                    visited.extend(dummy_v);
                }

                self.loop_carried_regs = prev_carried;

                self.output.push(Stat::NumFor {
                    var: var_name,
                    from: start_expr,
                    to: limit_expr,
                    step: step_opt,
                    body: body_stmts,
                });

                visited.insert(forloop_node);

                if let Some(exit) = exit_node {
                    self.emit_node(cfg, doms, exit, stop_at, visited);
                }
            }

            OpCode::ForLoop => {}
            OpCode::TForLoop => {}

            // ── Function exits ─────────────────────────────────────────────
            OpCode::Return | OpCode::TailCall => {
                for pc in bb.start..=bb.end { self.emit_instr(pc); }
            }

            // ── Jump ───────────────────────────────────────────────────────
            OpCode::Jmp => {
                let sbx         = getarg_sbx(last_instr);
                let target_pc   = jump_target(bb.end, sbx);
                let target_node = cfg.block_of[target_pc];

                let is_conditional = bb.end > bb.start
                    && is_skip_instr(get_opcode(self.proto.code[bb.end - 1]));

                let is_tfor_setup = is_conditional
                    && get_opcode(self.proto.code[bb.end - 1]) == OpCode::LuaDecTForLoop
                    && target_pc > bb.end
                    && get_opcode(self.proto.code[cfg.graph[target_node].end]) == OpCode::TForLoop;

                if is_tfor_setup {
                    self.emit_generic_for(cfg, doms, node, target_node, stop_at, visited);
                } else if is_conditional {
                    self.emit_if(cfg, doms, node, stop_at, visited);
                } else if target_pc > bb.end
                    && get_opcode(self.proto.code[cfg.graph[target_node].end]) == OpCode::TForLoop
                {
                    self.emit_generic_for(cfg, doms, node, target_node, stop_at, visited);
                } else {
                    for pc in bb.start..bb.end { self.emit_instr(pc); }
                    if !visited.contains(&target_node) {
                        self.emit_node(cfg, doms, target_node, stop_at, visited);
                    }
                }
            }

            // ── Normal sequential block ────────────────────────────────────
            _ => {
                for pc in bb.start..=bb.end { self.emit_instr(pc); }
                let succs: Vec<_> = cfg.graph.neighbors(node).collect();
                if let Some(&succ) = succs.first() {
                    self.emit_node(cfg, doms, succ, stop_at, visited);
                }
            }
        }
    }

    /// Mark nodes as visited without actually emitting instructions.
    /// Used to synchronize visited sets after a collect_node_stmts call.
    fn emit_node_mark_only(
        &self,
        cfg: &Cfg,
        node: NodeIndex,
        stop_node: NodeIndex,
        visited: &mut BTreeSet<NodeIndex>,
    ) {
        if node == stop_node || visited.contains(&node) { return; }
        visited.insert(node);
        for succ in cfg.graph.neighbors(node) {
            self.emit_node_mark_only(cfg, succ, stop_node, visited);
        }
    }

    // -----------------------------------------------------------------------
    // Generic for loop
    // -----------------------------------------------------------------------

    fn emit_generic_for(
        &mut self,
        cfg: &Cfg,
        doms: &Dominators<NodeIndex>,
        setup_node: NodeIndex,
        tforloop_node: NodeIndex,
        stop_at: Option<NodeIndex>,
        visited: &mut BTreeSet<NodeIndex>,
    ) {
        visited.insert(setup_node);
        visited.insert(tforloop_node);

        let setup_bb = cfg.graph[setup_node].clone();
        let tfl_bb   = cfg.graph[tforloop_node].clone();

        let tfl_instr = self.proto.code[tfl_bb.end];
        let ctrl_reg  = getarg_a(tfl_instr) as usize;
        let func_reg  = ctrl_reg.saturating_sub(2);

        let mut body_node = None;
        let mut exit_node = None;
        for edge in cfg.graph.edges(tforloop_node) {
            match edge.weight() {
                EdgeKind::Back        => body_node = Some(edge.target()),
                EdgeKind::FallThrough => exit_node = Some(edge.target()),
                _ => {}
            }
        }

        let loop_var_count = {
            let c_tfl = if tfl_bb.end > tfl_bb.start {
                let instr = self.proto.code[tfl_bb.end - 1];
                if get_opcode(instr) == OpCode::LuaDecTForLoop { Some(getarg_c(instr) as usize) } else { None }
            } else { None };
            let c_setup = if setup_bb.end > setup_bb.start {
                let instr = self.proto.code[setup_bb.end - 1];
                if get_opcode(instr) == OpCode::LuaDecTForLoop { Some(getarg_c(instr) as usize) } else { None }
            } else { None };
            c_tfl.or(c_setup).unwrap_or(1).max(1)
        };

        let mut iter_exprs: Vec<Expr> = Vec::new();
        for pc in setup_bb.start..setup_bb.end {
            let instr = self.proto.code[pc];
            let op    = get_opcode(instr);
            let ia    = getarg_a(instr) as usize;

            if iter_exprs.is_empty() && op == OpCode::Call && ia == func_reg {
                let overwritten = (pc + 1..setup_bb.end).any(|lpc| {
                    let li = self.proto.code[lpc];
                    writes_to_a(get_opcode(li)) && getarg_a(li) as usize == func_reg
                });
                if !overwritten {
                    let call_b = getarg_b(instr) as usize;
                    let func   = self.reg_or_placeholder(func_reg);
                    let args: Vec<Expr> = if call_b <= 1 { vec![] } else {
                        (func_reg + 1..func_reg + call_b).map(|r| self.reg_or_placeholder(r)).collect()
                    };
                    iter_exprs.push(Expr::Call { func: Box::new(func), args });
                } else {
                    self.emit_instr(pc);
                }
            } else {
                self.emit_instr(pc);
            }
        }

        if iter_exprs.is_empty() {
            let f = self.reg_or_placeholder(func_reg);
            let s = self.reg_or_placeholder(func_reg + 1);
            let c_expr = self.reg_or_placeholder(func_reg + 2);
            let c_nil = matches!(c_expr, Expr::Nil) || matches!(&self.regs.get(func_reg + 2), Some(None));
            let s_nil = matches!(s, Expr::Nil) || matches!(&self.regs.get(func_reg + 1), Some(None));
            if c_nil && s_nil { iter_exprs.push(f); }
            else if c_nil    { iter_exprs = vec![f, s]; }
            else             { iter_exprs = vec![f, s, c_expr]; }
        }

        let pre_loop_regs = self.regs_snapshot();
        let exclude_tfor: Vec<usize> = (func_reg..=ctrl_reg + loop_var_count).collect();
        let carried = if let Some(body) = body_node {
            self.find_loop_carried_regs(cfg, body, tforloop_node, &pre_loop_regs, &exclude_tfor)
        } else { BTreeSet::new() };

        for &r in &carried {
            let acc = format!("_acc{}", r);
            let init = pre_loop_regs[r].clone().unwrap_or(Expr::Nil);
            self.output.push(Stat::Local { names: vec![acc.clone()], values: vec![init] });
            self.set_reg(r, Expr::Name(acc));
        }

        let promoted = self.find_promoted_loop_var_regs(
            cfg, body_node, tforloop_node, exit_node, ctrl_reg, loop_var_count,
        );
        for &r in &promoted {
            let upv_name = format!("_upvr{}", r);
            self.output.push(Stat::Local { names: vec![upv_name.clone()], values: vec![Expr::Nil] });
            self.set_reg(r, Expr::Name(upv_name));
        }

        let vars: Vec<String> = (0..loop_var_count).map(|i| format!("_v{}", ctrl_reg + 1 + i)).collect();
        for (i, v) in vars.iter().enumerate() {
            let r = ctrl_reg + 1 + i;
            self.set_reg(r, Expr::Name(v.clone()));
            self.loop_var_names.insert(v.clone());
        }

        let mut merged = self.loop_carried_regs.clone();
        merged.extend(carried.iter().copied());
        merged.extend(promoted.iter().copied());
        let prev_carried = std::mem::replace(&mut self.loop_carried_regs, merged);

        let body_stmts = if let Some(body) = body_node {
            self.collect_node_stmts(cfg, doms, body, Some(tforloop_node), visited)
        } else { vec![] };
        if let Some(body) = body_node {
            let mut dummy_v = visited.clone();
            self.emit_node_mark_only(cfg, body, tforloop_node, &mut dummy_v);
            visited.extend(dummy_v);
        }

        self.loop_carried_regs = prev_carried;

        self.output.push(Stat::GenFor {
            vars,
            iters: iter_exprs,
            body: body_stmts,
        });

        if let Some(exit) = exit_node {
            self.emit_node(cfg, doms, exit, stop_at, visited);
        }
    }

    // -----------------------------------------------------------------------
    // If / else
    // -----------------------------------------------------------------------

    fn emit_if(
        &mut self,
        cfg: &Cfg,
        doms: &Dominators<NodeIndex>,
        node: NodeIndex,
        stop_at: Option<NodeIndex>,
        visited: &mut BTreeSet<NodeIndex>,
    ) {
        let bb = cfg.graph[node].clone();

        for pc in bb.start..bb.end.saturating_sub(1) { self.emit_instr(pc); }

        let cond_pc  = bb.end - 1;
        let cond_expr = self.condition_expr(cond_pc);

        let jmp_instr     = self.proto.code[bb.end];
        let jmp_target_pc = jump_target(bb.end, getarg_sbx(jmp_instr));
        let jmp_target    = cfg.block_of[jmp_target_pc];

        let ft_pc = bb.end + 1;
        if ft_pc >= cfg.block_of.len() {
            self.output.push(Stat::If { branches: vec![(cond_expr, vec![])], else_body: None });
            return;
        }
        let fall_through = cfg.block_of[ft_pc];

        let then_region = self.collect_region(cfg, fall_through, jmp_target);
        let end_node    = self.find_region_end(cfg, &then_region, jmp_target);
        let has_else    = end_node != jmp_target;

        let dead_branch = matches!(cond_expr, Expr::Nil | Expr::False);
        let regs_before_dead = if dead_branch { Some(self.regs.clone()) } else { None };

        let then_stmts = self.collect_node_stmts(cfg, doms, fall_through, Some(jmp_target), visited);

        let else_stmts = if has_else {
            if let Some(ref snap) = regs_before_dead { self.regs = snap.clone(); }
            Some(self.collect_node_stmts(cfg, doms, jmp_target, Some(end_node), visited))
        } else {
            if let Some(snap) = regs_before_dead { self.regs = snap; }
            None
        };

        self.output.push(Stat::If {
            branches: vec![(cond_expr, then_stmts)],
            else_body: else_stmts,
        });

        self.emit_node(cfg, doms, end_node, stop_at, visited);
    }

    fn find_region_end(
        &self,
        cfg: &Cfg,
        region: &BTreeSet<NodeIndex>,
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

    fn collect_region(&self, cfg: &Cfg, start: NodeIndex, stop: NodeIndex) -> BTreeSet<NodeIndex> {
        let mut result   = BTreeSet::new();
        let mut worklist = vec![start];
        while let Some(n) = worklist.pop() {
            if n == stop || result.contains(&n) { continue; }
            result.insert(n);
            for succ in cfg.graph.neighbors(n) { worklist.push(succ); }
        }
        result
    }

    // -----------------------------------------------------------------------
    // Condition expression
    // -----------------------------------------------------------------------

    fn condition_expr(&mut self, cond_pc: usize) -> Expr {
        let instr = self.proto.code[cond_pc];
        let op    = get_opcode(instr);
        let a     = getarg_a(instr) as usize;
        let b     = getarg_b(instr) as usize;
        let c     = getarg_c(instr) as usize;

        match op {
            OpCode::Eq => {
                let lhs = self.rk_expr(b);
                let rhs = self.rk_expr(c);
                let bop = if a == 0 { BinOp::Eq } else { BinOp::Ne };
                Expr::BinOp { op: bop, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
            OpCode::Lt => {
                let lhs = self.rk_expr(b);
                let rhs = self.rk_expr(c);
                let bop = if a == 0 { BinOp::Lt } else { BinOp::Ge };
                Expr::BinOp { op: bop, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
            OpCode::Le => {
                let lhs = self.rk_expr(b);
                let rhs = self.rk_expr(c);
                let bop = if a == 0 { BinOp::Le } else { BinOp::Gt };
                Expr::BinOp { op: bop, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
            OpCode::Test => {
                let r = self.reg_or_placeholder(a);
                if c == 0 { r } else { Expr::UnOp { op: UnOp::Not, operand: Box::new(r) } }
            }
            OpCode::TestSet => {
                let r = self.reg_or_placeholder(b);
                if c == 0 { r } else { Expr::UnOp { op: UnOp::Not, operand: Box::new(r) } }
            }
            OpCode::LuaDecTForLoop => {
                Expr::BinOp {
                    op: BinOp::Ne,
                    lhs: Box::new(Expr::Name(format!("_v{}", a + 1))),
                    rhs: Box::new(Expr::Nil),
                }
            }
            _ => Expr::Name("???".to_string()),
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
            OpCode::Move      => self.op_move(a, b),
            OpCode::LoadK     => self.op_loadk(a, bx),
            OpCode::LoadKx    => self.set_reg_or_emit_assign(a, Expr::Name("???".to_string())),
            OpCode::LoadBool  => self.op_loadbool(a, b),
            OpCode::LoadNil   => self.op_loadnil(a, b),
            OpCode::GetUpVal  => self.op_getupval(a, b),
            OpCode::GetGlobal => self.op_getglobal(a, bx),
            OpCode::GetTabUp  => self.op_gettabup(a, b, c),
            OpCode::GetTable  => self.op_gettable(a, b, c),
            OpCode::SetGlobal => self.op_setglobal(a, bx),
            OpCode::SetTabUp  => self.op_settabup(a, b, c),
            OpCode::SetUpVal  => self.op_setupval(a, b),
            OpCode::SetTable  => self.op_settable(a, b, c),
            OpCode::NewTable  => self.op_newtable(pc, a),
            OpCode::Self_     => self.op_self(a, b, c),
            OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div
            | OpCode::Pow | OpCode::Mod | OpCode::IDiv | OpCode::Band
            | OpCode::Bor | OpCode::BXor | OpCode::Shl | OpCode::Shr
                              => self.op_arith(a, b, c, op),
            OpCode::Unm       => self.op_unm(a, b),
            OpCode::Not       => self.op_not(a, b),
            OpCode::Len       => self.op_len(a, b),
            OpCode::BNot      => self.op_bnot(a, b),
            OpCode::Concat    => self.op_concat(a, b, c),
            OpCode::Call      => self.op_call(a, b, c),
            OpCode::TailCall  => self.op_tailcall(a, b),
            OpCode::Return    => self.op_return(a, b),
            OpCode::SetList   => self.op_setlist(a, b, c),
            OpCode::Closure   => self.op_closure(a, bx),
            OpCode::VarArg    => self.op_vararg(a, b),
            _ => {}
        }
    }

    // -----------------------------------------------------------------------
    // Per-opcode handlers
    // -----------------------------------------------------------------------

    fn op_move(&mut self, a: usize, b: usize) {
        let val = self.reg_or_placeholder(b);
        self.set_reg_or_emit_assign(a, val);
    }

    fn op_loadk(&mut self, a: usize, bx: usize) {
        let val = self.constant_expr(bx);
        self.set_reg_or_emit_assign(a, val);
    }

    fn op_loadbool(&mut self, a: usize, b: usize) {
        let val = if b != 0 { Expr::True } else { Expr::False };
        self.set_reg_or_emit_assign(a, val);
    }

    fn op_loadnil(&mut self, a: usize, b: usize) {
        for r in a..=a + b { self.set_reg_or_emit_assign(r, Expr::Nil); }
    }

    fn op_getupval(&mut self, a: usize, b: usize) {
        let name = self.upvalue_name(b);
        self.set_reg_or_emit_assign(a, Expr::Name(name));
    }

    fn op_getglobal(&mut self, a: usize, bx: usize) {
        let name = self.global_name(bx);
        self.set_reg_or_emit_assign(a, Expr::Name(name));
    }

    fn op_gettabup(&mut self, a: usize, b: usize, c: usize) {
        let upv = self.upvalue_name(b);
        let key = self.rk_expr(c);
        let expr = if upv == "_ENV" {
            // _ENV["name"] → just the name
            match &key {
                Expr::Str(bytes) => Expr::Name(String::from_utf8_lossy(bytes).into_owned()),
                Expr::Name(n)    => Expr::Name(n.clone()),
                other => Expr::Index { table: Box::new(Expr::Name(upv)), key: Box::new(other.clone()) },
            }
        } else {
            Expr::Index { table: Box::new(Expr::Name(upv)), key: Box::new(key) }
        };
        self.set_reg_or_emit_assign(a, expr);
    }

    fn op_gettable(&mut self, a: usize, b: usize, c: usize) {
        let tbl = self.reg_or_placeholder(b);
        let key = self.rk_expr(c);
        self.set_reg_or_emit_assign(a, Expr::Index { table: Box::new(tbl), key: Box::new(key) });
    }

    fn op_setglobal(&mut self, a: usize, bx: usize) {
        let name = self.global_name(bx);
        let val  = self.reg_or_placeholder(a);
        self.output.push(Stat::Assign { lhs: vec![Expr::Name(name)], rhs: vec![val] });
    }

    fn op_settabup(&mut self, a: usize, b: usize, c: usize) {
        let upv = self.upvalue_name(a);
        let key = self.rk_expr(b);
        let val = self.rk_expr(c);
        let lhs = if upv == "_ENV" {
            match &key {
                Expr::Str(bytes) => Expr::Name(String::from_utf8_lossy(bytes).into_owned()),
                Expr::Name(n)    => Expr::Name(n.clone()),
                other => Expr::Index { table: Box::new(Expr::Name(upv)), key: Box::new(other.clone()) },
            }
        } else {
            Expr::Index { table: Box::new(Expr::Name(upv)), key: Box::new(key) }
        };
        self.output.push(Stat::Assign { lhs: vec![lhs], rhs: vec![val] });
    }

    fn op_setupval(&mut self, a: usize, b: usize) {
        let name = self.upvalue_name(b);
        let val  = self.reg_or_placeholder(a);
        self.output.push(Stat::Assign { lhs: vec![Expr::Name(name)], rhs: vec![val] });
    }

    fn op_settable(&mut self, a: usize, b: usize, c: usize) {
        let tbl = self.reg_or_placeholder(a);
        let key = self.rk_expr(b);
        let val = self.rk_expr(c);
        self.output.push(Stat::Assign {
            lhs: vec![Expr::Index { table: Box::new(tbl), key: Box::new(key) }],
            rhs: vec![val],
        });
    }

    fn op_newtable(&mut self, pc: usize, a: usize) {
        let name = format!("_t{}", pc);
        self.output.push(Stat::Local { names: vec![name.clone()], values: vec![Expr::Table(vec![])] });
        self.set_reg(a, Expr::Name(name));
        self.loop_carried_regs.remove(&a);
    }

    fn op_self(&mut self, a: usize, b: usize, c: usize) {
        let obj    = self.reg_or_placeholder(b);
        let method = self.rk_expr(c);
        self.set_reg_or_emit_assign(a + 1, obj.clone());
        self.set_reg_or_emit_assign(a, Expr::Index { table: Box::new(obj), key: Box::new(method) });
    }

    fn op_arith(&mut self, a: usize, b: usize, c: usize, op: OpCode) {
        let lhs = self.rk_expr(b);
        let rhs = self.rk_expr(c);
        let bop = match op {
            OpCode::Add  => BinOp::Add,  OpCode::Sub  => BinOp::Sub,
            OpCode::Mul  => BinOp::Mul,  OpCode::Div  => BinOp::Div,
            OpCode::Pow  => BinOp::Pow,  OpCode::Mod  => BinOp::Mod,
            OpCode::IDiv => BinOp::IDiv, OpCode::Band => BinOp::BAnd,
            OpCode::Bor  => BinOp::BOr,  OpCode::BXor => BinOp::BXor,
            OpCode::Shl  => BinOp::Shl,  OpCode::Shr  => BinOp::Shr,
            _ => BinOp::Add,
        };
        self.set_reg_or_emit_assign(a, Expr::BinOp { op: bop, lhs: Box::new(lhs), rhs: Box::new(rhs) });
    }

    fn op_unm(&mut self, a: usize, b: usize) {
        let val = self.reg_or_placeholder(b);
        self.set_reg_or_emit_assign(a, Expr::UnOp { op: UnOp::Neg, operand: Box::new(val) });
    }

    fn op_not(&mut self, a: usize, b: usize) {
        let val = self.reg_or_placeholder(b);
        self.set_reg_or_emit_assign(a, Expr::UnOp { op: UnOp::Not, operand: Box::new(val) });
    }

    fn op_len(&mut self, a: usize, b: usize) {
        let val = self.reg_or_placeholder(b);
        self.set_reg_or_emit_assign(a, Expr::UnOp { op: UnOp::Len, operand: Box::new(val) });
    }

    fn op_bnot(&mut self, a: usize, b: usize) {
        let val = self.reg_or_placeholder(b);
        self.set_reg_or_emit_assign(a, Expr::UnOp { op: UnOp::BNot, operand: Box::new(val) });
    }

    fn op_concat(&mut self, a: usize, b: usize, c: usize) {
        let parts: Vec<Expr> = (b..=c).map(|r| self.reg_or_placeholder(r)).collect();
        let expr = parts.into_iter().reduce(|acc, rhs| {
            Expr::BinOp { op: BinOp::Concat, lhs: Box::new(acc), rhs: Box::new(rhs) }
        }).unwrap_or(Expr::Str(vec![]));
        self.set_reg_or_emit_assign(a, expr);
    }

    fn op_call(&mut self, a: usize, b: usize, c: usize) {
        let func = self.reg_or_placeholder(a);
        let args: Vec<Expr> = if b == 0 {
            (a + 1..self.regs.len())
                .take_while(|&r| self.regs.get(r).map_or(false, |e| e.is_some()))
                .filter(|&r| !self.setlist_cleared.contains(&r))
                .map(|r| self.reg_or_placeholder(r))
                .collect()
        } else {
            (a + 1..a + b).map(|r| self.reg_or_placeholder(r)).collect()
        };

        let call_expr = Expr::Call { func: Box::new(func), args };

        match c {
            1 => {
                // No results — standalone call statement.
                self.output.push(Stat::Call(call_expr));
            }
            0 => {
                // Variable results: store in R[A], clear arg registers.
                if b > 1 {
                    for r in (a + 1)..(a + b) { self.clear_reg(r); }
                }
                self.set_reg_or_emit_assign(a, call_expr);
            }
            2 => {
                // 1 result → R[A].
                self.set_reg_or_emit_assign(a, call_expr);
            }
            _ => {
                // Multiple results → local r0, r1, ... = call(...)
                let count = c - 1;
                let names: Vec<String> = (a..a + count).map(|r| format!("_r{}", r)).collect();
                for (i, name) in names.iter().enumerate() {
                    self.set_reg(a + i, Expr::Name(name.clone()));
                }
                self.output.push(Stat::Local { names, values: vec![call_expr] });
            }
        }
    }

    fn op_tailcall(&mut self, a: usize, b: usize) {
        let func = self.reg_or_placeholder(a);
        let args: Vec<Expr> = if b == 0 {
            (a + 1..self.regs.len())
                .take_while(|&r| self.regs.get(r).map_or(false, |e| e.is_some()))
                .filter(|&r| !self.setlist_cleared.contains(&r))
                .map(|r| self.reg_or_placeholder(r))
                .collect()
        } else {
            (a + 1..a + b).map(|r| self.reg_or_placeholder(r)).collect()
        };
        self.output.push(Stat::Return(vec![Expr::Call { func: Box::new(func), args }]));
    }

    fn op_return(&mut self, a: usize, b: usize) {
        let vals: Vec<Expr> = match b {
            0 => (a..self.regs.len())
                .filter(|&r| !self.setlist_cleared.contains(&r) && self.regs.get(r).map_or(false, |e| e.is_some()))
                .map(|r| self.reg_or_placeholder(r))
                .collect(),
            1 => vec![],
            _ => (a..a + b - 1).map(|r| self.reg_or_placeholder(r)).collect(),
        };
        self.output.push(Stat::Return(vals));
    }

    fn op_setlist(&mut self, a: usize, b: usize, c: usize) {
        let base = c.saturating_sub(1) * 50;
        let tbl  = self.reg_or_placeholder(a);
        let count = if b == 0 {
            (a + 1..self.regs.len()).rev()
                .find(|&r| self.regs.get(r).map_or(false, |e| e.is_some()))
                .map_or(0, |r| r - a)
        } else { b };
        for i in 1..=count {
            if a + i < self.regs.len() {
                let val = self.reg_or_placeholder(a + i);
                self.output.push(Stat::Assign {
                    lhs: vec![Expr::Index { table: Box::new(tbl.clone()), key: Box::new(Expr::Integer((base + i) as i64)) }],
                    rhs: vec![val],
                });
            }
        }
        for i in 1..=count {
            if a + i < self.regs.len() { self.setlist_cleared.insert(a + i); }
        }
    }

    fn op_closure(&mut self, a: usize, bx: usize) {
        if let Some(sub) = self.proto.p.get(bx) {
            let params: Vec<String> = (0..sub.numparams as usize).map(|i| format!("_p{}", i)).collect();
            let has_vararg = sub.is_vararg != 0;

            let descs: Vec<(bool, usize)> = sub.upvalue_infos.iter()
                .map(|d| (d.on_stack, d.idx as usize))
                .collect();

            // Spill non-lvalue on-stack captures to named locals.
            for (i, (on_stack, reg_idx)) in descs.iter().enumerate() {
                if *on_stack {
                    if let Some(Some(expr)) = self.regs.get(*reg_idx) {
                        let expr = expr.clone();
                        if !expr.is_empty_reg() && !matches!(expr, Expr::Nil) && !is_expr_lvalue(&expr) {
                            let name = format!("_upv{}", i);
                            self.output.push(Stat::Local { names: vec![name.clone()], values: vec![expr] });
                            self.set_reg(*reg_idx, Expr::Name(name));
                        }
                    }
                }
            }

            let resolved: Vec<String> = descs.iter().enumerate().map(|(i, (on_stack, idx))| {
                if *on_stack {
                    match self.regs.get(*idx).and_then(|e| e.as_ref()) {
                        Some(Expr::Name(n)) => n.clone(),
                        Some(_) | None => sub.upvalue_names
                            .get(i)
                            .filter(|n| !n.is_empty())
                            .cloned()
                            .unwrap_or_else(|| format!("_upv{}", i)),
                    }
                } else {
                    self.upvalue_name(*idx)
                }
            }).collect();

            let fname = format!("_f{}", bx);

            let mut sub_ctx = DecompileCtx::new(sub);
            sub_ctx.upvalue_names = resolved;
            for i in 0..sub.numparams as usize {
                sub_ctx.set_reg(i, Expr::Name(format!("_p{}", i)));
            }
            sub_ctx.run();
            consolidate_tables(&mut sub_ctx.output);
            let body = sub_ctx.output;

            self.output.push(Stat::Local {
                names: vec![fname.clone()],
                values: vec![Expr::Function(Box::new(FuncBody { params, has_vararg, body }))],
            });

            self.set_reg(a, Expr::Name(fname));
            self.loop_carried_regs.remove(&a);
        } else {
            self.set_reg(a, Expr::Name(format!("<closure {}>", bx)));
        }
    }

    fn op_vararg(&mut self, a: usize, b: usize) {
        let count = if b <= 1 { 1 } else { b - 1 };
        for i in 0..count { self.set_reg(a + i, Expr::Vararg); }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// True if `expr` can appear on the left of an assignment (is a valid lvalue).
fn is_expr_lvalue(expr: &Expr) -> bool {
    matches!(expr, Expr::Name(_) | Expr::Index { .. })
}

/// Extension to check "empty" register (placeholder name `_rN`).
trait ExprExt {
    fn is_empty_reg(&self) -> bool;
}
impl ExprExt for Expr {
    fn is_empty_reg(&self) -> bool {
        matches!(self, Expr::Name(n) if n.starts_with("_r") && n[2..].parse::<usize>().is_ok())
    }
}

/// Convert a `LuaConstant` from the parser into an `Expr`.
fn lua_const_to_expr(c: &LuaConstant) -> Expr {
    match c {
        LuaConstant::Null         => Expr::Nil,
        LuaConstant::Bool(b)      => if *b { Expr::True } else { Expr::False },
        LuaConstant::Number(n)    => match n {
            LuaNumber::Integer(i) => Expr::Integer(*i),
            LuaNumber::Float(f)   => Expr::Float(*f),
        },
        LuaConstant::String(bytes) => Expr::Str(bytes.to_vec()),
        _ => Expr::Name("<const>".to_string()),
    }
}

/// Merge `local _tN = {} / _tN[1] = v1 / _tN[2] = v2 / …` into
/// `local _tN = {v1, v2, …}` inline table constructors.
/// Recursively processes all nested blocks and function bodies.
fn consolidate_tables(block: &mut Block) {
    // First, recurse into all nested blocks so inner constructors are built
    // before we process the outer block (bottom-up).
    for stat in block.iter_mut() {
        match stat {
            Stat::Do(b) => consolidate_tables(b),
            Stat::While { body, .. } => consolidate_tables(body),
            Stat::Repeat { body, .. } => consolidate_tables(body),
            Stat::NumFor { body, .. } => consolidate_tables(body),
            Stat::GenFor { body, .. } => consolidate_tables(body),
            Stat::If { branches, else_body } => {
                for (_, b) in branches { consolidate_tables(b); }
                if let Some(b) = else_body { consolidate_tables(b); }
            }
            Stat::Local { values, .. } | Stat::Return(values) => {
                for v in values.iter_mut() {
                    consolidate_in_expr(v);
                }
            }
            Stat::Assign { lhs, rhs } => {
                for e in lhs.iter_mut().chain(rhs.iter_mut()) {
                    consolidate_in_expr(e);
                }
            }
            Stat::Call(e) => consolidate_in_expr(e),
            _ => {}
        }
    }
    // Then process this block's own table constructions.
    let mut i = 0;
    while i < block.len() {
        // Look for `local _tN = {}`
        let name = match &block[i] {
            Stat::Local { names, values }
                if names.len() == 1
                    && values.len() == 1
                    && values[0] == Expr::Table(vec![]) => names[0].clone(),
            _ => { i += 1; continue; }
        };

        // Collect consecutive integer-keyed assignments _tN[k] = val (k = 1, 2, …)
        let mut vals: Vec<Expr> = Vec::new();
        let mut j = i + 1;
        loop {
            let expected = vals.len() + 1;
            match block.get(j) {
                Some(Stat::Assign { lhs, rhs })
                    if lhs.len() == 1 && rhs.len() == 1 =>
                {
                    if let Expr::Index { table, key } = &lhs[0] {
                        if **table == Expr::Name(name.clone())
                            && **key == Expr::Integer(expected as i64)
                        {
                            vals.push(rhs[0].clone());
                            j += 1;
                            continue;
                        }
                    }
                    break;
                }
                _ => break,
            }
        }

        if vals.is_empty() { i += 1; continue; }

        let fields: Vec<TableField> = vals.into_iter().map(TableField::ValueField).collect();
        block[i] = Stat::Local { names: vec![name], values: vec![Expr::Table(fields)] };
        block.drain(i + 1..j);
        // Don't advance i — the newly consolidated entry may itself participate
        // in a further consolidation pass (though that's rare).
        i += 1;
    }
}

/// Recurse into function-literal bodies embedded in expressions.
fn consolidate_in_expr(e: &mut Expr) {
    match e {
        Expr::Function(fb) => consolidate_tables(&mut fb.body),
        Expr::Call { func, args } => {
            consolidate_in_expr(func);
            for a in args { consolidate_in_expr(a); }
        }
        Expr::Index { table, key } => {
            consolidate_in_expr(table);
            consolidate_in_expr(key);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            consolidate_in_expr(lhs);
            consolidate_in_expr(rhs);
        }
        Expr::UnOp { operand, .. } => consolidate_in_expr(operand),
        Expr::Table(fields) => {
            for f in fields {
                match f {
                    TableField::IndexField(k, v) => { consolidate_in_expr(k); consolidate_in_expr(v); }
                    TableField::NameField(_, v) | TableField::ValueField(v) => consolidate_in_expr(v),
                }
            }
        }
        _ => {}
    }
}

fn instr_source_regs(op: OpCode, b: usize, c: usize) -> Vec<usize> {
    match op {
        OpCode::Move | OpCode::Unm | OpCode::Not | OpCode::Len | OpCode::BNot => vec![b],
        OpCode::GetTable | OpCode::Self_ => {
            let mut srcs = vec![b];
            if c & 0x100 == 0 { srcs.push(c); }
            srcs
        }
        OpCode::GetTabUp => {
            if c & 0x100 == 0 { vec![c] } else { vec![] }
        }
        OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div | OpCode::Pow
        | OpCode::Mod | OpCode::IDiv | OpCode::Band | OpCode::Bor | OpCode::BXor
        | OpCode::Shl | OpCode::Shr => {
            let mut srcs = vec![];
            if b & 0x100 == 0 { srcs.push(b); }
            if c & 0x100 == 0 { srcs.push(c); }
            srcs
        }
        OpCode::Concat => (b..=c).collect(),
        _ => vec![],
    }
}

fn writes_to_a(op: OpCode) -> bool {
    !matches!(op,
        OpCode::SetGlobal | OpCode::SetTabUp | OpCode::SetUpVal | OpCode::SetTable
        | OpCode::SetList | OpCode::Jmp | OpCode::ForLoop | OpCode::ForPrep
        | OpCode::TForLoop | OpCode::LuaDecTForLoop | OpCode::TailCall
        | OpCode::Return | OpCode::Unknown
    )
}

fn is_expr_op(op: OpCode) -> bool {
    matches!(op,
        OpCode::Move | OpCode::LoadK | OpCode::LoadKx | OpCode::LoadBool | OpCode::LoadNil
        | OpCode::GetUpVal | OpCode::GetGlobal | OpCode::GetTabUp | OpCode::GetTable | OpCode::Self_
        | OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div | OpCode::Pow | OpCode::Mod
        | OpCode::IDiv | OpCode::Band | OpCode::Bor | OpCode::BXor | OpCode::Shl | OpCode::Shr
        | OpCode::Unm | OpCode::Not | OpCode::Len | OpCode::BNot | OpCode::Concat
    )
}

#[inline]
fn jump_target(pc: usize, sbx: i32) -> usize {
    (pc as i64 + 1 + sbx as i64) as usize
}

#[inline]
fn is_skip_instr(op: OpCode) -> bool {
    matches!(op,
        OpCode::Eq | OpCode::Lt | OpCode::Le | OpCode::Test | OpCode::TestSet | OpCode::LuaDecTForLoop
    )
}
