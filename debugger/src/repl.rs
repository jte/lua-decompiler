/// GDB-like interactive REPL for stepping through Lua bytecode.

use std::collections::HashSet;
use std::io::{self, BufRead, Write};

use disassembler::{
    get_opcode, getarg_a, getarg_b, getarg_c, getarg_bx, getarg_sbx,
    lua_p_opnames, opstr, operators, Proto,
};

use crate::stdlib::build_globals;
use crate::vm::{parse_value, step, LuaTable, LuaValue, StepResult, VmState};

// ---------------------------------------------------------------------------
// Helpers — single-instruction disassembly to string
// ---------------------------------------------------------------------------

fn disasm_one(proto: &Proto, pc: usize) -> String {
    let i = proto.code[pc];
    let op = get_opcode(i);
    let a = getarg_a(i) as usize;
    let b = getarg_b(i) as usize;
    let c = getarg_c(i) as usize;
    let bc = getarg_bx(i) as usize;
    let sbc = getarg_sbx(i);

    let mnemonic = lua_p_opnames(op);

    use disassembler::OpCode::*;
    let operands = match op {
        Move | Not | Unm | Len | BNot => {
            format!("R{} R{}", a, b)
        }
        LoadK => {
            let k = disassembler::decompile_constant(proto, bc);
            format!("R{} K{} ; {}", a, bc, k)
        }
        LoadKx => format!("R{}", a),
        LoadBool => format!("R{} {} {}", a, b, c),
        LoadNil => format!("R{}..R{}", a, a + b),
        GetUpVal => {
            let uname = proto.upvalue_names.get(b).map(|s| s.as_str()).unwrap_or("?");
            format!("R{} U{}        ; R{} := {}", a, b, a, uname)
        }
        SetUpVal => {
            let uname = proto.upvalue_names.get(b).map(|s| s.as_str()).unwrap_or("?");
            format!("R{} U{}        ; {} := R{}", a, b, uname, a)
        }
        GetTabUp => {
            let uname = proto.upvalue_names.get(b).map(|s| s.as_str()).unwrap_or("?");
            format!("R{} U{} {}  ; R{} := {}[{}]", a, b, rk_str(proto, c), a, uname, rk_str(proto, c))
        }
        SetTabUp => {
            let uname = proto.upvalue_names.get(a).map(|s| s.as_str()).unwrap_or("?");
            format!("U{} {} {}  ; {}[{}] := {}", a, rk_str(proto, b), rk_str(proto, c), uname, rk_str(proto, b), rk_str(proto, c))
        }
        GetTable => format!("R{} R{} {}  ; R{} := R{}[{}]", a, b, rk_str(proto, c), a, b, rk_str(proto, c)),
        SetTable => format!("R{} {} {}  ; R{}[{}] := {}", a, rk_str(proto, b), rk_str(proto, c), a, rk_str(proto, b), rk_str(proto, c)),
        GetGlobal => {
            let k = disassembler::decompile_constant(proto, bc);
            format!("R{} K{}       ; R{} := {}", a, bc, a, k)
        }
        SetGlobal => {
            let k = disassembler::decompile_constant(proto, bc);
            format!("R{} K{}       ; {} := R{}", a, bc, k, a)
        }
        NewTable => format!("R{} {} {}", a, b, c),
        Self_ => format!("R{} R{} {}", a, b, rk_str(proto, c)),
        Add | Sub | Mul | Div | Mod | Pow | IDiv
        | Band | Bor | BXor | Shl | Shr => {
            let op_sym = operators(op);
            format!(
                "R{} {} {}  ; R{} := {} {} {}",
                a, rk_str(proto, b), rk_str(proto, c),
                a, rk_str(proto, b), op_sym, rk_str(proto, c)
            )
        }
        Concat => format!("R{} R{}..R{}", a, b, c),
        Jmp => format!("R{} {}  ; PC += {} (goto {})", a, sbc, sbc, pc as i32 + 1 + sbc),
        Eq | Lt | Le => {
            format!(
                "{} {} {}  ; if {} {} {} goto {}",
                a, rk_str(proto, b), rk_str(proto, c),
                rk_str(proto, b), opstr(op), rk_str(proto, c),
                pc as i32 + 2 + sbc
            )
        }
        Test => format!("R{} {}  ; if R{} then goto ...", a, c, a),
        TestSet => format!("R{} R{} {}  ; if R{} then R{} := R{}", a, b, c, b, a, b),
        Call => format!("R{} {} {}", a, b, c),
        TailCall => format!("R{} {}", a, b),
        Return => {
            if b == 1 {
                format!("R{} {}  ; return", a, b)
            } else if b == 2 {
                format!("R{} {}  ; return R{}", a, b, a)
            } else {
                format!("R{} {}  ; return R{}..R{}", a, b, a, a + b - 2)
            }
        }
        ForPrep => format!("R{} {}  ; R{} -= R{}; PC += {}", a, sbc, a, a + 2, sbc),
        ForLoop => format!("R{} {}  ; R{} += R{}; if loop goto {}", a, sbc, a, a + 2, pc as i32 + 1 + sbc),
        LuaDecTForLoop => format!("R{} {}", a, c),
        TForLoop => format!("R{} {}  ; if R{} ~= nil goto {}", a, sbc, a + 2, pc as i32 + 1 + sbc),
        SetList => format!("R{} {} {}", a, b, c),
        Closure => format!("R{} {}  ; R{} := closure(proto {})", a, bc, a, bc),
        VarArg => format!("R{} {}", a, b),
        Close => format!("R{}", a),
        ExtraArg => format!("{}", bc),
        Unknown => format!("??? {:08x}", i),
    };

    format!("{:<12} {}", mnemonic, operands)
}

fn rk_str(proto: &Proto, rk: usize) -> String {
    const BITRK: usize = 1 << 8;
    if rk & BITRK != 0 {
        let idx = rk & !BITRK;
        let k = disassembler::decompile_constant(proto, idx);
        format!("K{}(={})", idx, k)
    } else {
        format!("R{}", rk)
    }
}

// ---------------------------------------------------------------------------
// Display — listing a window of instructions
// ---------------------------------------------------------------------------

fn print_listing(proto: &Proto, pc: usize, regs: Option<&VmState>, count: usize, start: usize) {
    let half = count / 2;
    let from = start.saturating_sub(half);
    let to = (start + half + 1).min(proto.sizecode);

    // Find the furthest PC we need to print (the current one's JMP target might be far)
    for p in from..to {
        let marker = if p == pc { "=>" } else { "  " };
        let instr = disasm_one(proto, p);
        println!("{} {:4}:  {}", marker, p, instr);

        // If we have register state and this is the current instruction, show it
        if let Some(state) = regs {
            if p == pc {
                // Show any registers that are non-nil and non-unknown, briefly
                let hints: Vec<String> = state
                    .regs
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| !matches!(v, LuaValue::Nil))
                    .map(|(i, v)| format!("R{}={}", i, v))
                    .collect();
                if !hints.is_empty() {
                    let line = hints.join("  ");
                    // wrap at ~100 chars
                    if line.len() <= 100 {
                        println!("        ; {}", line);
                    } else {
                        println!("        ; {}...", &line[..97]);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Debugger session
// ---------------------------------------------------------------------------

pub struct Debugger<'p> {
    /// Root proto (index 0) and all child protos flattened.
    protos: Vec<&'p Proto>,
    /// Index into `protos` of the currently active function.
    current: usize,
    /// Per-proto VM states (lazily created).
    states: Vec<Option<VmState>>,
    breakpoints: HashSet<(usize, usize)>, // (proto_idx, pc)
    last_cmd: String,
    /// Shared globals table (_G) seeded into every new VmState.
    globals: LuaTable,
}

fn collect_protos<'p>(proto: &'p Proto, out: &mut Vec<&'p Proto>) {
    out.push(proto);
    for child in &proto.p {
        collect_protos(child, out);
    }
}

impl<'p> Debugger<'p> {
    pub fn new(root: &'p Proto) -> Self {
        let mut protos = Vec::new();
        collect_protos(root, &mut protos);
        let n = protos.len();
        Debugger {
            protos,
            current: 0,
            states: (0..n).map(|_| None).collect(),
            breakpoints: HashSet::new(),
            last_cmd: String::new(),
            globals: build_globals(),
        }
    }

    fn proto(&self) -> &'p Proto {
        self.protos[self.current]
    }

    fn state(&mut self) -> &mut VmState {
        let proto = self.protos[self.current];
        if self.states[self.current].is_none() {
            self.states[self.current] = Some(VmState::new(proto, &self.globals));
        }
        self.states[self.current].as_mut().unwrap()
    }

    fn state_ref(&self) -> Option<&VmState> {
        self.states[self.current].as_ref()
    }

    // -----------------------------------------------------------------------
    // Public entry point
    // -----------------------------------------------------------------------

    pub fn run_repl(&mut self) {
        println!("Lua bytecode debugger  (type 'help' for commands)");
        println!("Active: proto 0 ({} instructions)", self.proto().sizecode);
        self.print_current();

        let stdin = io::stdin();
        loop {
            print!("(ldb) ");
            let _ = io::stdout().flush();

            let mut line = String::new();
            match stdin.lock().read_line(&mut line) {
                Ok(0) => break, // EOF
                Err(e) => {
                    eprintln!("input error: {}", e);
                    break;
                }
                Ok(_) => {}
            }

            let input = line.trim().to_string();
            let cmd = if input.is_empty() {
                self.last_cmd.clone()
            } else {
                self.last_cmd = input.clone();
                input
            };

            if !self.dispatch(&cmd) {
                break;
            }
        }
    }

    // Returns false to quit.
    fn dispatch(&mut self, cmd: &str) -> bool {
        let parts: Vec<&str> = cmd.splitn(3, ' ').collect();
        let verb = parts[0];

        match verb {
            "q" | "quit" | "exit" => return false,

            "help" | "h" | "?" => self.cmd_help(),

            // ---- stepping -----------------------------------------------
            "r" | "run" => self.cmd_run(),
            "s" | "step" => {
                let n: usize = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(1);
                self.cmd_step(n);
            }
            "n" | "next" => self.cmd_step(1), // no call stack yet — same as step
            "c" | "continue" => self.cmd_continue(),
            "finish" | "fin" => self.cmd_continue(), // alias

            // ---- breakpoints --------------------------------------------
            "b" | "break" => {
                if let Some(pc_str) = parts.get(1) {
                    if let Ok(pc) = pc_str.parse::<usize>() {
                        let key = (self.current, pc);
                        self.breakpoints.insert(key);
                        println!("Breakpoint set at proto {} PC {}", self.current, pc);
                    } else {
                        println!("Usage: break <PC>");
                    }
                } else {
                    println!("Usage: break <PC>");
                }
            }
            "d" | "delete" => {
                if let Some(pc_str) = parts.get(1) {
                    if let Ok(pc) = pc_str.parse::<usize>() {
                        if self.breakpoints.remove(&(self.current, pc)) {
                            println!("Breakpoint at PC {} deleted", pc);
                        } else {
                            println!("No breakpoint at PC {}", pc);
                        }
                    } else {
                        println!("Usage: delete <PC>");
                    }
                } else {
                    // delete all
                    self.breakpoints.retain(|(pi, _)| *pi != self.current);
                    println!("All breakpoints for proto {} cleared", self.current);
                }
            }

            // ---- inspect / modify registers -----------------------------
            "i" | "info" => {
                let sub = parts.get(1).copied().unwrap_or("reg");
                self.cmd_info(sub, parts.get(2).copied());
            }
            "p" | "print" => {
                if let Some(target) = parts.get(1) {
                    self.cmd_print(target);
                } else {
                    println!("Usage: print $rN | $uN");
                }
            }
            "set" => self.cmd_set(parts.get(1..)),

            // ---- branch override (after UnknownBranch stop) -------------
            "branch" | "assume" => {
                let dir = parts.get(1).copied().unwrap_or("");
                self.cmd_branch(dir);
            }

            // ---- disassembly / listing ----------------------------------
            "x" | "disas" | "disassemble" | "list" | "l" => {
                let arg = parts.get(1).copied().unwrap_or("");
                self.cmd_disas(arg);
            }

            // ---- proto navigation ---------------------------------------
            "func" | "f" => {
                if let Some(n_str) = parts.get(1) {
                    if let Ok(n) = n_str.parse::<usize>() {
                        self.cmd_func(n);
                    } else {
                        println!("Usage: func <N>");
                    }
                } else {
                    println!("Current proto: {}", self.current);
                }
            }
            "funcs" | "protos" => self.cmd_list_funcs(),

            // ---- stack --------------------------------------------------
            "bt" | "backtrace" => {
                println!("(single-frame debugger — no call stack tracking)");
                println!("  #0  proto {} PC {}", self.current,
                    self.state_ref().map(|s| s.pc).unwrap_or(0));
            }

            "" => {}
            _ => println!("Unknown command '{}'. Type 'help'.", verb),
        }
        true
    }

    // -----------------------------------------------------------------------
    // Commands
    // -----------------------------------------------------------------------

    fn cmd_help(&self) {
        println!("Commands:");
        println!("  run / r               Reset state and restart from PC 0");
        println!("  step [N] / s [N]      Execute N instructions (default 1)");
        println!("  next / n              Same as step (single-frame)");
        println!("  continue / c          Run until breakpoint, RETURN, or end");
        println!("  break <PC> / b <PC>   Set breakpoint at instruction PC");
        println!("  delete [PC] / d [PC]  Delete breakpoint (all if no PC given)");
        println!("  info reg / i r        Show all registers");
        println!("  info upv / i u        Show all upvalues");
        println!("  info bp  / i b        List breakpoints");
        println!("  info func / i f       Show current function info");
        println!("  print $rN             Print register N  (e.g. print $r0)");
        println!("  print $uN             Print upvalue N");
        println!("  set $pc = N           Set program counter to N");
        println!("  set $rN = <val>       Set register N to value");
        println!("  set $uN = <val>       Set upvalue N to value");
        println!("    <val> can be: nil, true, false, 42, 3.14, \"hello\", 0xff");
        println!("  branch true|false     After an unknown-branch stop, force a direction");
        println!("  assume true|false     Alias for 'branch'");
        println!("  disas [N] / x [N]     Disassemble N instrs around PC (default 11)");
        println!("  disas PC+N            Disassemble N instrs starting at PC");
        println!("  func <N>              Switch to proto N");
        println!("  funcs / protos        List all proto indices");
        println!("  quit / q              Quit");
        println!("  (empty line repeats last command)");
    }

    fn cmd_run(&mut self) {
        let proto = self.protos[self.current];
        self.states[self.current] = Some(VmState::new(proto, &self.globals));
        println!("Restarted proto {} at PC 0", self.current);
        self.print_current();
    }

    fn cmd_step(&mut self, count: usize) {
        for _ in 0..count {
            let pc_before = self.state().pc;
            let proto = self.protos[self.current];
            let result = step(self.state(), proto);
            let _pc_after = self.state().pc;

            match result {
                StepResult::Ok => {
                    if count == 1 {
                        self.print_current();
                    }
                }
                StepResult::Jumped { from, to } => {
                    if count == 1 {
                        println!("  Jumped: PC {} -> {}", from, to);
                        self.print_current();
                    }
                }
                StepResult::Returned(vals) => {
                    if vals.is_empty() {
                        println!("  RETURN (no values)");
                    } else {
                        let s: Vec<String> = vals.iter().map(|v| v.to_string()).collect();
                        println!("  RETURN  {}", s.join(", "));
                    }
                    return;
                }
                StepResult::Halted => {
                    println!("  Already halted. Use 'run' to restart.");
                    return;
                }
                StepResult::UnknownBranch(msg) => {
                    println!("  ! Unknown branch condition: {}", msg);
                    println!("  Use 'branch true' or 'branch false' to force a direction,");
                    println!("  or 'set $rN = <val>' to fix the register and 'step' again.");
                    if count == 1 {
                        self.print_current();
                    }
                }
            }

            let _ = pc_before; // suppress unused
        }
        if count > 1 {
            self.print_current();
        }
    }

    fn cmd_continue(&mut self) {
        let proto = self.protos[self.current];
        loop {
            let pc = self.state().pc;

            // Check breakpoint before executing
            if self.breakpoints.contains(&(self.current, pc)) {
                println!("Breakpoint hit at PC {}", pc);
                self.print_current();
                return;
            }

            let result = step(self.state(), proto);
            match result {
                StepResult::Ok | StepResult::Jumped { .. } => {}
                StepResult::Returned(vals) => {
                    if vals.is_empty() {
                        println!("  RETURN (no values)");
                    } else {
                        let s: Vec<String> = vals.iter().map(|v| v.to_string()).collect();
                        println!("  RETURN  {}", s.join(", "));
                    }
                    return;
                }
                StepResult::Halted => {
                    println!("  Halted. Use 'run' to restart.");
                    return;
                }
                StepResult::UnknownBranch(msg) => {
                    println!("  ! Stopped: unknown branch condition: {}", msg);
                    println!("  Use 'branch true|false' to force a direction, or 'set $rN = <val>'.");
                    self.print_current();
                    return;
                }
            }
        }
    }

    fn cmd_info(&mut self, sub: &str, _extra: Option<&str>) {
        match sub {
            "r" | "reg" | "regs" | "registers" => {
                let cur = self.current;
                let state = self.state();
                let pc = state.pc;
                let regs: Vec<_> = state.regs.iter().cloned().collect();
                println!("Registers (proto {} PC {}):", cur, pc);
                for (i, v) in regs.iter().enumerate() {
                    let marker = match v {
                        LuaValue::Nil => " ",
                        LuaValue::Unknown(_) => "~",
                        _ => "*",
                    };
                    println!("  {} R{:<3} = {}  ({})", marker, i, v, v.type_name());
                }
            }
            "u" | "upv" | "upvalues" => {
                let cur = self.current;
                let state = self.state();
                let upvalues: Vec<LuaValue> = state.upvalues.iter()
                    .map(|cell| cell.borrow().clone())
                    .collect();
                let upv_names: Vec<_> = self.protos[cur].upvalue_names.clone();
                println!("Upvalues (proto {}):", cur);
                for (i, v) in upvalues.iter().enumerate() {
                    let name = upv_names.get(i).map(|s| s.as_str()).unwrap_or("?");
                    println!("  U{:<3} {} = {}  ({})", i, name, v, v.type_name());
                }
            }
            "b" | "bp" | "breakpoints" => {
                let mut bps: Vec<_> = self.breakpoints.iter().collect();
                bps.sort();
                if bps.is_empty() {
                    println!("No breakpoints.");
                } else {
                    println!("Breakpoints:");
                    for (pi, pc) in bps {
                        println!("  proto {} PC {}", pi, pc);
                    }
                }
            }
            "f" | "func" | "function" => {
                let proto = self.protos[self.current];
                let pc = self.state_ref().map(|s| s.pc).unwrap_or(0);
                println!("Proto:         {}", self.current);
                println!("Defined line:  {}", proto.linedefined);
                println!("Parameters:    {}", proto.numparams);
                println!("Is vararg:     {}", proto.is_vararg);
                println!("Max stack:     {}", proto.maxstacksize);
                println!("Instructions:  {}", proto.sizecode);
                println!("Constants:     {}", proto.constants.len());
                println!("Upvalues:      {}", proto.num_upvalues);
                println!("Child protos:  {}", proto.p.len());
                println!("PC:            {}", pc);
            }
            _ => println!("Unknown info sub-command '{}'. Try: reg, upv, bp, func", sub),
        }
    }

    fn cmd_print(&mut self, target: &str) {
        if let Some(n_str) = target.strip_prefix("$r").or_else(|| target.strip_prefix("$R")) {
            if let Ok(n) = n_str.parse::<usize>() {
                let v = self.state().reg(n).clone();
                println!("R{} = {}  ({})", n, v, v.type_name());
            } else {
                println!("Bad register: '{}'", target);
            }
        } else if let Some(n_str) = target.strip_prefix("$u").or_else(|| target.strip_prefix("$U")) {
            if let Ok(n) = n_str.parse::<usize>() {
                let proto = self.protos[self.current];
                let name = proto.upvalue_names.get(n).map(|s| s.as_str()).unwrap_or("?");
                let v = self.state().upv(n);
                println!("U{} ({}) = {}  ({})", n, name, v, v.type_name());
            } else {
                println!("Bad upvalue: '{}'", target);
            }
        } else {
            println!("Usage: print $rN  or  print $uN");
        }
    }

    fn cmd_set(&mut self, parts: Option<&[&str]>) {
        // set $rN = <val>  or  set $uN = <val>
        let parts = match parts {
            Some(p) => p,
            None => {
                println!("Usage: set $rN = <val>  |  set $uN = <val>");
                return;
            }
        };

        // Reconstruct full argument (may have been split)
        let full = parts.join(" ");
        // Expect: "$rN = <val>" or "$uN = <val>"
        let full = full.trim();
        if let Some(eq) = full.find('=') {
            let lhs = full[..eq].trim();
            let rhs = full[eq + 1..].trim();
            let val = parse_value(rhs);

            if lhs == "$pc" || lhs == "$PC" {
                if let Ok(n) = rhs.parse::<usize>() {
                    let proto = self.protos[self.current];
                    if n < proto.sizecode {
                        self.state().pc = n;
                        println!("PC = {}", n);
                        self.print_current();
                    } else {
                        println!("PC {} out of range (0..{})", n, proto.sizecode - 1);
                    }
                } else {
                    println!("Bad PC value: '{}'", rhs);
                }
            } else if let Some(n_str) = lhs.strip_prefix("$r").or_else(|| lhs.strip_prefix("$R")) {
                if let Ok(n) = n_str.parse::<usize>() {
                    self.state().set_reg(n, val.clone());
                    println!("R{} = {}", n, val);
                } else {
                    println!("Bad register: '{}'", lhs);
                }
            } else if let Some(n_str) = lhs.strip_prefix("$u").or_else(|| lhs.strip_prefix("$U")) {
                if let Ok(n) = n_str.parse::<usize>() {
                    let state = self.state();
                    if n < state.upvalues.len() {
                        state.set_upv(n, val.clone());
                        println!("U{} = {}", n, val);
                    } else {
                        println!("Upvalue index {} out of range", n);
                    }
                } else {
                    println!("Bad upvalue: '{}'", lhs);
                }
            } else {
                println!("Usage: set $pc = N  |  set $rN = <val>  |  set $uN = <val>");
            }
        } else {
            println!("Usage: set $pc = N  |  set $rN = <val>  |  set $uN = <val>");
        }
    }

    /// Force a branch direction after an UnknownBranch stop.
    ///
    /// The VM stops at the JMP that immediately follows a TEST/EQ/LT/LE.
    /// `branch true`  → take the jump (same as if the condition was truthy).
    /// `branch false` → skip the jump and fall through (condition was falsy).
    fn cmd_branch(&mut self, dir: &str) {
        use disassembler::{get_opcode, getarg_sbx, OpCode};

        let take_jump = match dir {
            "t" | "true" | "1" | "yes" => true,
            "f" | "false" | "0" | "no" => false,
            _ => {
                println!("Usage: branch true|false  (t/f also accepted)");
                println!("  true  — take the jump (as if condition was met)");
                println!("  false — fall through (as if condition was not met)");
                return;
            }
        };

        let proto = self.protos[self.current];
        let pc = self.state().pc;

        // Expect a JMP at current PC
        let instr = proto.code.get(pc).copied().unwrap_or(0);
        if get_opcode(instr) != OpCode::Jmp {
            println!(
                "PC {} is not a JMP instruction — 'branch' only works after an UnknownBranch stop.",
                pc
            );
            return;
        }

        if take_jump {
            let sbx = getarg_sbx(instr);
            let to = (pc as i32 + 1 + sbx) as usize;
            self.state().pc = to;
            println!("  Assumed truthy → jumped to PC {}", to);
        } else {
            self.state().pc = pc + 1;
            println!("  Assumed falsy → fell through to PC {}", pc + 1);
        }
        self.print_current();
    }

    fn cmd_disas(&mut self, arg: &str) {
        let proto = self.protos[self.current];
        let pc = self.state_ref().map(|s| s.pc).unwrap_or(0);

        // Parse "PC+N" or just "N"
        let (start, count) = if let Some(plus) = arg.find('+') {
            let start: usize = arg[..plus].parse().unwrap_or(pc);
            let count: usize = arg[plus + 1..].parse().unwrap_or(11);
            (start, count)
        } else if let Ok(n) = arg.parse::<usize>() {
            (pc, n)
        } else {
            (pc, 11)
        };

        print_listing(proto, pc, self.state_ref(), count, start);
    }

    fn cmd_func(&mut self, n: usize) {
        if n >= self.protos.len() {
            println!("Proto {} does not exist (0..{})", n, self.protos.len() - 1);
            return;
        }
        self.current = n;
        println!("Switched to proto {} ({} instructions)", n, self.proto().sizecode);
        self.print_current();
    }

    fn cmd_list_funcs(&self) {
        println!("Available protos:");
        for (i, p) in self.protos.iter().enumerate() {
            println!(
                "  {:3}  line {:4}  params={}  instrs={}  upvalues={}",
                i, p.linedefined, p.numparams, p.sizecode, p.num_upvalues
            );
        }
    }

    // -----------------------------------------------------------------------
    // Display current position
    // -----------------------------------------------------------------------

    fn print_current(&mut self) {
        let proto = self.protos[self.current];
        let pc = self.state_ref().map(|s| s.pc).unwrap_or(0);

        if pc >= proto.sizecode {
            println!("  [end of function]");
            return;
        }

        let instr = disasm_one(proto, pc);
        println!("=> {:4}:  {}", pc, instr);
    }
}
