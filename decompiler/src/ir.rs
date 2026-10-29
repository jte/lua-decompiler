//! Version-independent instruction decoding.
//!
//! Lua 5.1, 5.2 and 5.3 encode the same operations slightly differently
//! (LOADNIL ranges, closure upvalue lists, SETLIST/LOADKX extra words, the
//! generic-for opcodes).  [`decode`] turns a [`Proto`]'s raw code into a list
//! of [`Ins`] with all operands explicit, so later stages never look at
//! version-specific encodings again.

use disassembler::{
    get_opcode, getarg_a, getarg_ax, getarg_b, getarg_bx, getarg_c, getarg_sbx, OpCode, Proto,
};
use lua_ast::{BinOp, UnOp};

pub type Reg = u16;

/// A register-or-constant operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rk {
    R(Reg),
    K(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Lt,
    Le,
}

/// How a closure captures one upvalue.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cap {
    /// A register of the enclosing function.
    Reg(Reg),
    /// An upvalue of the enclosing function.
    Up(u16),
}

#[derive(Clone, Debug)]
pub enum Ins {
    Move { a: Reg, b: Reg },
    LoadK { a: Reg, k: u32 },
    LoadBool { a: Reg, val: bool, skip: bool },
    /// Registers `a..=last` := nil.
    LoadNil { a: Reg, last: Reg },
    GetUpval { a: Reg, up: u16 },
    GetTabUp { a: Reg, up: u16, key: Rk },
    GetGlobal { a: Reg, k: u32 },
    GetTable { a: Reg, t: Reg, key: Rk },
    SetTabUp { up: u16, key: Rk, val: Rk },
    SetGlobal { a: Reg, k: u32 },
    SetUpval { a: Reg, up: u16 },
    SetTable { t: Reg, key: Rk, val: Rk },
    NewTable { a: Reg },
    SelfOp { a: Reg, obj: Reg, key: Rk },
    Arith { a: Reg, op: BinOp, l: Rk, r: Rk },
    Unary { a: Reg, op: UnOp, b: Reg },
    Concat { a: Reg, b: Reg, c: Reg },
    /// `close`: registers >= this are closed (upvalues) when jumping.
    Jmp { target: usize, close: Option<Reg> },
    /// Skips the next instruction when `(l op r) != expect`.
    Cmp { op: CmpOp, expect: bool, l: Rk, r: Rk },
    /// Skips the next instruction when `truthy(a) != expect`.
    Test { a: Reg, expect: bool },
    /// If `truthy(b) == expect` then `a := b` else skip the next instruction.
    TestSet { a: Reg, b: Reg, expect: bool },
    /// `nargs`/`nret`: `None` means "up to top" / "all results".
    Call { a: Reg, nargs: Option<u16>, nret: Option<u16> },
    TailCall { a: Reg, nargs: Option<u16> },
    Return { a: Reg, n: Option<u16> },
    ForPrep { a: Reg, target: usize },
    ForLoop { a: Reg, target: usize },
    /// 5.2/5.3 TFORCALL: R(a+3..a+2+nvars) := R(a)(R(a+1), R(a+2)).
    TForCall { a: Reg, nvars: u16 },
    /// 5.2/5.3 TFORLOOP (`a` is the control register, i.e. TFORCALL's a+2).
    TForLoop { a: Reg, target: usize },
    /// 5.1 TFORLOOP: call + test; skips the next instruction (the back JMP)
    /// when the loop ends.
    TForLoop51 { a: Reg, nvars: u16 },
    /// `n`: `None` = up to top.  `first` is the 1-based index of the first item.
    SetList { a: Reg, n: Option<u16>, first: u64 },
    Close { a: Reg },
    Closure { a: Reg, idx: usize, caps: Vec<Cap> },
    /// `n`: `None` = all varargs.
    VarArg { a: Reg, n: Option<u16> },
    /// An operand word belonging to the previous instruction (EXTRAARG,
    /// 5.1 closure upvalue pseudo-instructions, 5.1 SETLIST block number).
    Data,
    Unknown,
}

pub struct Decoded {
    pub ins: Vec<Ins>,
    /// The pc execution continues at after `ins[pc]` when it doesn't jump
    /// (skips trailing data words).
    pub next: Vec<usize>,
}

fn rk(v: u32) -> Rk {
    if v & 0x100 != 0 { Rk::K(v & 0xFF) } else { Rk::R(v as Reg) }
}

fn target(pc: usize, sbx: i32) -> usize {
    let t = pc as i64 + 1 + sbx as i64;
    if t < 0 { usize::MAX } else { t as usize }
}

pub fn decode(proto: &Proto) -> Decoded {
    let v51 = proto.version == 0x51;
    let code = &proto.code;
    let n = code.len();
    let mut ins: Vec<Ins> = vec![Ins::Unknown; n];
    let mut data = vec![false; n];

    let mut pc = 0;
    while pc < n {
        if data[pc] {
            pc += 1;
            continue;
        }
        let i = code[pc];
        let op = get_opcode(i);
        let a = getarg_a(i) as Reg;
        let b = getarg_b(i);
        let c = getarg_c(i);
        let bx = getarg_bx(i);
        let sbx = getarg_sbx(i);
        let opt = |v: u32| if v == 0 { None } else { Some((v - 1) as u16) };

        ins[pc] = match op {
            OpCode::Move => Ins::Move { a, b: b as Reg },
            OpCode::LoadK => Ins::LoadK { a, k: bx },
            OpCode::LoadKx => {
                let k = code.get(pc + 1).map(|&w| getarg_ax(w)).unwrap_or(0);
                if pc + 1 < n { data[pc + 1] = true; }
                Ins::LoadK { a, k }
            }
            OpCode::LoadBool => Ins::LoadBool { a, val: b != 0, skip: c != 0 },
            OpCode::LoadNil => {
                let last = if v51 { b as Reg } else { a + b as Reg };
                Ins::LoadNil { a, last: last.max(a) }
            }
            OpCode::GetUpVal => Ins::GetUpval { a, up: b as u16 },
            OpCode::GetTabUp => Ins::GetTabUp { a, up: b as u16, key: rk(c) },
            OpCode::GetGlobal => Ins::GetGlobal { a, k: bx },
            OpCode::GetTable => Ins::GetTable { a, t: b as Reg, key: rk(c) },
            OpCode::SetTabUp => Ins::SetTabUp { up: a as u16, key: rk(b), val: rk(c) },
            OpCode::SetGlobal => Ins::SetGlobal { a, k: bx },
            OpCode::SetUpVal => Ins::SetUpval { a, up: b as u16 },
            OpCode::SetTable => Ins::SetTable { t: a, key: rk(b), val: rk(c) },
            OpCode::NewTable => Ins::NewTable { a },
            OpCode::Self_ => Ins::SelfOp { a, obj: b as Reg, key: rk(c) },
            OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Div | OpCode::Pow
            | OpCode::Mod | OpCode::IDiv | OpCode::Band | OpCode::Bor | OpCode::BXor
            | OpCode::Shl | OpCode::Shr => {
                let bop = match op {
                    OpCode::Add => BinOp::Add,
                    OpCode::Sub => BinOp::Sub,
                    OpCode::Mul => BinOp::Mul,
                    OpCode::Div => BinOp::Div,
                    OpCode::Pow => BinOp::Pow,
                    OpCode::Mod => BinOp::Mod,
                    OpCode::IDiv => BinOp::IDiv,
                    OpCode::Band => BinOp::BAnd,
                    OpCode::Bor => BinOp::BOr,
                    OpCode::BXor => BinOp::BXor,
                    OpCode::Shl => BinOp::Shl,
                    _ => BinOp::Shr,
                };
                Ins::Arith { a, op: bop, l: rk(b), r: rk(c) }
            }
            OpCode::Unm => Ins::Unary { a, op: UnOp::Neg, b: b as Reg },
            OpCode::Not => Ins::Unary { a, op: UnOp::Not, b: b as Reg },
            OpCode::Len => Ins::Unary { a, op: UnOp::Len, b: b as Reg },
            OpCode::BNot => Ins::Unary { a, op: UnOp::BNot, b: b as Reg },
            OpCode::Concat => Ins::Concat { a, b: b as Reg, c: c as Reg },
            OpCode::Jmp => {
                let close = if !v51 && a > 0 { Some(a - 1) } else { None };
                Ins::Jmp { target: target(pc, sbx), close }
            }
            OpCode::Eq | OpCode::Lt | OpCode::Le => {
                let cop = match op {
                    OpCode::Eq => CmpOp::Eq,
                    OpCode::Lt => CmpOp::Lt,
                    _ => CmpOp::Le,
                };
                Ins::Cmp { op: cop, expect: a != 0, l: rk(b), r: rk(c) }
            }
            OpCode::Test => Ins::Test { a, expect: c != 0 },
            OpCode::TestSet => Ins::TestSet { a, b: b as Reg, expect: c != 0 },
            OpCode::Call => Ins::Call { a, nargs: opt(b), nret: opt(c) },
            OpCode::TailCall => Ins::TailCall { a, nargs: opt(b) },
            OpCode::Return => Ins::Return { a, n: opt(b) },
            OpCode::ForPrep => Ins::ForPrep { a, target: target(pc, sbx) },
            OpCode::ForLoop => Ins::ForLoop { a, target: target(pc, sbx) },
            OpCode::LuaDecTForLoop => {
                if v51 {
                    Ins::TForLoop51 { a, nvars: c.max(1) as u16 }
                } else {
                    Ins::TForCall { a, nvars: c.max(1) as u16 }
                }
            }
            OpCode::TForLoop => Ins::TForLoop { a, target: target(pc, sbx) },
            OpCode::SetList => {
                let block = if c == 0 {
                    if pc + 1 < n { data[pc + 1] = true; }
                    let w = code.get(pc + 1).copied().unwrap_or(1);
                    if v51 { w } else { getarg_ax(w) }
                } else {
                    c
                };
                let first = (block.max(1) as u64 - 1) * 50 + 1;
                Ins::SetList { a, n: if b == 0 { None } else { Some(b as u16) }, first }
            }
            OpCode::Close => Ins::Close { a },
            OpCode::Closure => {
                let idx = bx as usize;
                let caps = if v51 {
                    // Lua 5.1: one MOVE/GETUPVAL pseudo-instruction per upvalue.
                    let nups = proto.p.get(idx).map_or(0, |p| p.num_upvalues as usize);
                    let mut caps = Vec::with_capacity(nups);
                    for k in 0..nups {
                        let Some(&w) = code.get(pc + 1 + k) else { break };
                        data[pc + 1 + k] = true;
                        if get_opcode(w) == OpCode::Move {
                            caps.push(Cap::Reg(getarg_b(w) as Reg));
                        } else {
                            caps.push(Cap::Up(getarg_b(w) as u16));
                        }
                    }
                    caps
                } else {
                    proto.p.get(idx).map_or(Vec::new(), |p| {
                        p.upvalue_infos.iter().map(|u| {
                            if u.on_stack { Cap::Reg(u.idx as Reg) } else { Cap::Up(u.idx as u16) }
                        }).collect()
                    })
                };
                Ins::Closure { a, idx, caps }
            }
            OpCode::VarArg => Ins::VarArg { a, n: opt(b) },
            OpCode::ExtraArg => Ins::Data,
            OpCode::Unknown => Ins::Unknown,
        };
        pc += 1;
    }

    for pc in 0..n {
        if data[pc] { ins[pc] = Ins::Data; }
    }
    let mut next = vec![0; n];
    for pc in 0..n {
        let mut q = pc + 1;
        while q < n && data[q] { q += 1; }
        next[pc] = q;
    }
    Decoded { ins, next }
}

/// Control-flow successors of the instruction at `pc` (empty for returns).
/// Targets outside the code are dropped.
pub fn successors(d: &Decoded, pc: usize) -> Vec<usize> {
    let n = d.ins.len();
    let nx = d.next[pc];
    let skip = if nx < n { d.next[nx] } else { nx };
    let mut v = match &d.ins[pc] {
        Ins::Jmp { target, .. } => vec![*target],
        Ins::Cmp { .. } | Ins::Test { .. } | Ins::TestSet { .. } => vec![nx, skip],
        Ins::LoadBool { skip: true, .. } => vec![skip],
        Ins::ForPrep { target, .. } => vec![*target],
        Ins::ForLoop { target, .. } | Ins::TForLoop { target, .. } => vec![*target, nx],
        Ins::TForLoop51 { .. } => vec![nx, skip],
        Ins::Return { .. } | Ins::TailCall { .. } => vec![],
        _ => vec![nx],
    };
    v.retain(|&t| t < n);
    v
}

/// True if `ins` always ends a basic block.
pub fn ends_block(ins: &Ins) -> bool {
    matches!(ins,
        Ins::Jmp { .. } | Ins::Cmp { .. } | Ins::Test { .. } | Ins::TestSet { .. }
        | Ins::LoadBool { skip: true, .. } | Ins::ForPrep { .. } | Ins::ForLoop { .. }
        | Ins::TForLoop { .. } | Ins::TForLoop51 { .. } | Ins::Return { .. }
        | Ins::TailCall { .. })
}
