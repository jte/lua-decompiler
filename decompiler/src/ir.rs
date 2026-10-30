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

/// A register, constant or immediate operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rk {
    R(Reg),
    K(u32),
    /// 5.4 immediate integer.
    Int(i64),
    /// 5.4 immediate float (bits of an `f64`).
    Flt(u64),
    /// Luau JUMPXEQKNIL / JUMPXEQKB operands.
    Nil,
    Bool(bool),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Lt,
    Le,
}

/// Condition of a Luau conditional jump.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BranchCond {
    /// R(a) is neither nil nor false.
    Truthy(Reg),
    Cmp { op: CmpOp, l: Rk, r: Rk },
}

/// How a closure captures one upvalue.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cap {
    /// A register of the enclosing function.
    Reg(Reg),
    /// Luau CAPTURE VAL: a copy of the register's current value (for locals
    /// never assigned again; no upvalue stays open).
    Val(Reg),
    /// An upvalue of the enclosing function.
    Up(u16),
}

#[derive(Clone, Debug)]
pub enum Ins {
    Move { a: Reg, b: Reg },
    LoadK { a: Reg, k: u32 },
    /// 5.4 LOADI / LOADF.
    LoadImm { a: Reg, v: Rk },
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
    /// `init`: the registers holding (start, limit, step) — R(a), R(a+1),
    /// R(a+2) except in Luau (R(a+2), R(a), R(a+1)).
    ForPrep { a: Reg, target: usize, init: [Reg; 3] },
    /// `var` is the visible loop variable: R(a+3), or R(a+2) in 5.5.
    ForLoop { a: Reg, var: Reg, target: usize },
    /// 5.2+ TFORCALL: R(a+base..) := R(a)(R(a+1), R(a+ctl)), `nvars`
    /// results.  base/ctl: 3/2 up to 5.3, 4/2 in 5.4 (R(a+3) holds the
    /// closing value), 3/3 in 5.5 (the first variable is the control).
    TForCall { a: Reg, nvars: u16, base: u16, ctl: u16 },
    /// 5.2+ TFORLOOP: if R(src) ~= nil then R(a) := R(src) and jump.  `a`
    /// is the control register (TFORCALL's a+ctl), `src` the first variable.
    TForLoop { a: Reg, src: Reg, target: usize },
    /// 5.1 TFORLOOP: call + test; skips the next instruction (the back JMP)
    /// when the loop ends.
    TForLoop51 { a: Reg, nvars: u16 },
    /// `n`: `None` = up to top.  `first` is the 1-based index of the first
    /// item; the items are in `src..` (R(a+1).. except in Luau).
    SetList { a: Reg, src: Reg, n: Option<u16>, first: u64 },
    Close { a: Reg },
    /// 5.4 TBC: R(a) becomes a to-be-closed variable.
    Tbc { a: Reg },
    /// 5.5 ERRNNIL (`global x = ...`): error unless R(a) is nil; `name` is
    /// the constant holding the global's name.
    ErrNNil { a: Reg, name: Option<u32> },
    /// Luau conditional jump: to `target` if `cond` holds (does not hold,
    /// with `negate`), else to the next instruction.
    Branch { cond: BranchCond, negate: bool, target: usize },
    /// Luau LOADB with a jump: `a := val`, then continue at `target`.
    LoadBoolJump { a: Reg, val: bool, target: usize },
    /// Luau GETIMPORT: `a := name1.name2.name3` (constant string indices).
    GetImport { a: Reg, path: Vec<u32> },
    /// Luau DUPTABLE: `a :=` a new table from the constant template `k`.
    DupTable { a: Reg, k: u32 },
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
    if proto.luau { return decode_luau(proto); }
    if proto.version >= 0x54 { return decode54(proto); }
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
            OpCode::ForPrep => Ins::ForPrep { a, target: target(pc, sbx), init: [a, a + 1, a + 2] },
            OpCode::ForLoop => Ins::ForLoop { a, var: a + 3, target: target(pc, sbx) },
            OpCode::LuaDecTForLoop => {
                if v51 {
                    Ins::TForLoop51 { a, nvars: c.max(1) as u16 }
                } else {
                    Ins::TForCall { a, nvars: c.max(1) as u16, base: 3, ctl: 2 }
                }
            }
            OpCode::TForLoop => Ins::TForLoop { a, src: a + 1, target: target(pc, sbx) },
            OpCode::SetList => {
                let block = if c == 0 {
                    if pc + 1 < n { data[pc + 1] = true; }
                    let w = code.get(pc + 1).copied().unwrap_or(1);
                    if v51 { w } else { getarg_ax(w) }
                } else {
                    c
                };
                let first = (block.max(1) as u64 - 1) * 50 + 1;
                Ins::SetList { a, src: a + 1, n: if b == 0 { None } else { Some(b as u16) }, first }
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

    finish(ins, data)
}

fn finish(mut ins: Vec<Ins>, data: Vec<bool>) -> Decoded {
    let n = ins.len();
    for pc in 0..n {
        if data[pc] { ins[pc] = Ins::Data; }
    }
    // A jump onto a no-op (a Luau FASTCALL hint) continues after it.
    let real = |mut t: usize| { while t < n && data[t] { t += 1; } t };
    for i in ins.iter_mut() {
        match i {
            Ins::Jmp { target, .. } | Ins::Branch { target, .. } | Ins::LoadBoolJump { target, .. }
            | Ins::ForPrep { target, .. } | Ins::ForLoop { target, .. } | Ins::TForLoop { target, .. } => {
                *target = real(*target);
            }
            _ => {}
        }
    }
    let mut next = vec![0; n];
    for pc in 0..n {
        let mut q = pc + 1;
        while q < n && data[q] { q += 1; }
        next[pc] = q;
    }
    Decoded { ins, next }
}

/// Lua 5.4 tag-method events (ltm.h), as used by MMBIN*.
fn tm_binop(ev: u32) -> Option<BinOp> {
    Some(match ev {
        6 => BinOp::Add, 7 => BinOp::Sub, 8 => BinOp::Mul, 9 => BinOp::Mod,
        10 => BinOp::Pow, 11 => BinOp::Div, 12 => BinOp::IDiv, 13 => BinOp::BAnd,
        14 => BinOp::BOr, 15 => BinOp::BXor, 16 => BinOp::Shl, 17 => BinOp::Shr,
        _ => return None,
    })
}

/// 5.5 opcodes numbered as in 5.4: SHLI/SHRI swapped places, and GETVARG and
/// ERRNNIL (here 200, 201) came in before VARARGPREP.
fn op55_as_54(op: u32) -> u32 {
    match op {
        32 => 33,
        33 => 32,
        81 => 200,
        82 => 201,
        83 => 81,
        84 => 82,
        x => x,
    }
}

/// Does this 5.5 function have a named vararg parameter (`...t`) that its
/// code reads?  It lives in the register after the fixed parameters: a real
/// table (PF_VATAB), or only indexed through GETVARG.
pub fn named_vararg(proto: &Proto) -> bool {
    proto.version >= 0x55 && proto.is_vararg != 0
        && (proto.flags & 2 != 0 || proto.code.iter().any(|&i| i & 0x7F == 81))
}

/// Lua 5.4 and 5.5 (lopcodes.h): 7-bit opcode, A 8, k 1, B 8, C 8; Bx 17;
/// sJ 25 (5.5 NEWTABLE/SETLIST: vB 6, vC 10).
fn decode54(proto: &Proto) -> Decoded {
    let v55 = proto.version >= 0x55;
    const OFFSET_SC: i64 = 127;
    const OFFSET_SBX: i64 = 65535;
    const OFFSET_SJ: i64 = 16_777_215;
    let code = &proto.code;
    let n = code.len();
    let mut ins: Vec<Ins> = vec![Ins::Unknown; n];
    let mut data = vec![false; n];
    let op_of = |i: u32| i & 0x7F;
    let a_of = |i: u32| ((i >> 7) & 0xFF) as Reg;
    let k_of = |i: u32| (i >> 15) & 1 != 0;
    let b_of = |i: u32| (i >> 16) & 0xFF;
    let c_of = |i: u32| (i >> 24) & 0xFF;
    let sc = |v: u32| v as i64 - OFFSET_SC;
    let to = |pc: usize, off: i64| {
        let t = pc as i64 + 1 + off;
        if t < 0 { usize::MAX } else { t as usize }
    };
    let rkc = |i: u32| if k_of(i) { Rk::K(c_of(i)) } else { Rk::R(c_of(i) as Reg) };
    // Immediate of EQI & co.: C says whether it stands for a float.
    let imm = |i: u32| {
        let v = sc(b_of(i));
        if c_of(i) != 0 { Rk::Flt((v as f64).to_bits()) } else { Rk::Int(v) }
    };

    for pc in 0..n {
        if data[pc] { continue; }
        let i = code[pc];
        let (a, b, c, k) = (a_of(i), b_of(i), c_of(i), k_of(i));
        let bx = i >> 15;
        let sbx = bx as i64 - OFFSET_SBX;
        let opt = |v: u32| if v == 0 { None } else { Some((v - 1) as u16) };
        // The EXTRAARG word after `pc` (its Ax).
        let extra = |data: &mut Vec<bool>| -> u32 {
            if pc + 1 < n { data[pc + 1] = true; }
            code.get(pc + 1).map_or(0, |&w| w >> 7)
        };
        // An arithmetic op is followed by its MMBIN* fallback, which names
        // the source operator and operand order (`x - 1` is ADDI x -1).
        let arith = |op: BinOp, l: Rk, r: Rk, data: &mut Vec<bool>| -> Ins {
            if let Some(&w) = code.get(pc + 1) {
                let (mop, ma, mb, mc, mk) = (op_of(w), a_of(w), b_of(w), c_of(w), k_of(w));
                let ev = tm_binop(mc);
                let found = match mop {
                    46 => ev.map(|o| (o, Rk::R(ma), Rk::R(mb as Reg))),
                    47 => ev.map(|o| {
                        let x = Rk::Int(sc(mb));
                        if mk { (o, x, Rk::R(ma)) } else { (o, Rk::R(ma), x) }
                    }),
                    48 => ev.map(|o| {
                        let x = Rk::K(mb);
                        if mk { (o, x, Rk::R(ma)) } else { (o, Rk::R(ma), x) }
                    }),
                    _ => None,
                };
                if let Some((o, l, r)) = found {
                    data[pc + 1] = true;
                    return Ins::Arith { a, op: o, l, r };
                }
            }
            Ins::Arith { a, op, l, r }
        };
        let op = if v55 { op55_as_54(op_of(i)) } else { op_of(i) };
        ins[pc] = match op {
            0 => Ins::Move { a, b: b as Reg },
            1 => Ins::LoadImm { a, v: Rk::Int(sbx) },
            2 => Ins::LoadImm { a, v: Rk::Flt((sbx as f64).to_bits()) },
            3 => Ins::LoadK { a, k: bx },
            4 => Ins::LoadK { a, k: extra(&mut data) },
            5 => Ins::LoadBool { a, val: false, skip: false },
            6 => Ins::LoadBool { a, val: false, skip: true },
            7 => Ins::LoadBool { a, val: true, skip: false },
            8 => Ins::LoadNil { a, last: a + b as Reg },
            9 => Ins::GetUpval { a, up: b as u16 },
            10 => Ins::SetUpval { a, up: b as u16 },
            11 => Ins::GetTabUp { a, up: b as u16, key: Rk::K(c) },
            12 => Ins::GetTable { a, t: b as Reg, key: Rk::R(c as Reg) },
            13 => Ins::GetTable { a, t: b as Reg, key: Rk::Int(c as i64) },
            14 => Ins::GetTable { a, t: b as Reg, key: Rk::K(c) },
            15 => Ins::SetTabUp { up: a as u16, key: Rk::K(b), val: rkc(i) },
            16 => Ins::SetTable { t: a, key: Rk::R(b as Reg), val: rkc(i) },
            17 => Ins::SetTable { t: a, key: Rk::Int(b as i64), val: rkc(i) },
            18 => Ins::SetTable { t: a, key: Rk::K(b), val: rkc(i) },
            19 => { extra(&mut data); Ins::NewTable { a } }
            // 5.5: the key is always a constant.
            20 => Ins::SelfOp { a, obj: b as Reg, key: if v55 { Rk::K(c) } else { rkc(i) } },
            21 => arith(BinOp::Add, Rk::R(b as Reg), Rk::Int(sc(c)), &mut data),
            22..=31 => {
                let op = [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Mod, BinOp::Pow, BinOp::Div,
                          BinOp::IDiv, BinOp::BAnd, BinOp::BOr, BinOp::BXor][(op - 22) as usize].clone();
                arith(op, Rk::R(b as Reg), Rk::K(c), &mut data)
            }
            32 => arith(BinOp::Shr, Rk::R(b as Reg), Rk::Int(sc(c)), &mut data),
            33 => arith(BinOp::Shl, Rk::Int(sc(c)), Rk::R(b as Reg), &mut data),
            34..=45 => {
                let op = [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Mod, BinOp::Pow, BinOp::Div,
                          BinOp::IDiv, BinOp::BAnd, BinOp::BOr, BinOp::BXor, BinOp::Shl, BinOp::Shr][(op - 34) as usize].clone();
                arith(op, Rk::R(b as Reg), Rk::R(c as Reg), &mut data)
            }
            // A fallback not right after its arithmetic op.
            46..=48 => Ins::Data,
            49 => Ins::Unary { a, op: UnOp::Neg, b: b as Reg },
            50 => Ins::Unary { a, op: UnOp::BNot, b: b as Reg },
            51 => Ins::Unary { a, op: UnOp::Not, b: b as Reg },
            52 => Ins::Unary { a, op: UnOp::Len, b: b as Reg },
            53 => Ins::Concat { a, b: a, c: (a + b as Reg).saturating_sub(1) },
            54 => Ins::Close { a },
            55 => Ins::Tbc { a },
            56 => Ins::Jmp { target: to(pc, (i >> 7) as i64 - OFFSET_SJ), close: None },
            57 => Ins::Cmp { op: CmpOp::Eq, expect: k, l: Rk::R(a), r: Rk::R(b as Reg) },
            58 => Ins::Cmp { op: CmpOp::Lt, expect: k, l: Rk::R(a), r: Rk::R(b as Reg) },
            59 => Ins::Cmp { op: CmpOp::Le, expect: k, l: Rk::R(a), r: Rk::R(b as Reg) },
            60 => Ins::Cmp { op: CmpOp::Eq, expect: k, l: Rk::R(a), r: Rk::K(b) },
            61 => Ins::Cmp { op: CmpOp::Eq, expect: k, l: Rk::R(a), r: imm(i) },
            62 => Ins::Cmp { op: CmpOp::Lt, expect: k, l: Rk::R(a), r: imm(i) },
            63 => Ins::Cmp { op: CmpOp::Le, expect: k, l: Rk::R(a), r: imm(i) },
            64 => Ins::Cmp { op: CmpOp::Lt, expect: k, l: imm(i), r: Rk::R(a) },
            65 => Ins::Cmp { op: CmpOp::Le, expect: k, l: imm(i), r: Rk::R(a) },
            66 => Ins::Test { a, expect: k },
            67 => Ins::TestSet { a, b: b as Reg, expect: k },
            68 => Ins::Call { a, nargs: opt(b), nret: opt(c) },
            69 => Ins::TailCall { a, nargs: opt(b) },
            70 => Ins::Return { a, n: opt(b) },
            71 => Ins::Return { a: 0, n: Some(0) },
            72 => Ins::Return { a, n: Some(1) },
            // FORLOOP jumps back to the body; FORPREP is treated as jumping
            // to FORLOOP (as in 5.3): same loop, test placed differently.
            73 => Ins::ForLoop { a, var: if v55 { a + 2 } else { a + 3 }, target: to(pc, -(bx as i64)) },
            74 => Ins::ForPrep { a, target: to(pc, bx as i64), init: [a, a + 1, a + 2] },
            75 => Ins::Jmp { target: to(pc, bx as i64), close: None },
            // 5.5's TFORPREP swaps control and closing value: the call reads
            // R(a+3) and its first result is the control.
            76 if v55 => Ins::TForCall { a, nvars: c.max(1) as u16, base: 3, ctl: 3 },
            76 => Ins::TForCall { a, nvars: c.max(1) as u16, base: 4, ctl: 2 },
            77 if v55 => Ins::TForLoop { a: a + 3, src: a + 3, target: to(pc, -(bx as i64)) },
            77 => Ins::TForLoop { a: a + 2, src: a + 4, target: to(pc, -(bx as i64)) },
            78 => {
                let (n, mut first) = if v55 {
                    ((i >> 16) & 0x3F, ((i >> 22) & 0x3FF) as u64)
                } else {
                    (b, c as u64)
                };
                let scale = if v55 { 1024 } else { 256 };
                if k { first += extra(&mut data) as u64 * scale; }
                Ins::SetList { a, src: a + 1, n: if n == 0 { None } else { Some(n as u16) }, first: first + 1 }
            }
            // GETVARG: R(b) is the vararg parameter, indexed like a table.
            200 => Ins::GetTable { a, t: b as Reg, key: Rk::R(c as Reg) },
            201 => Ins::ErrNNil { a, name: if bx > 0 { Some(bx - 1) } else { None } },
            79 => {
                let idx = bx as usize;
                let caps = proto.p.get(idx).map_or(Vec::new(), |p| {
                    p.upvalue_infos.iter().map(|u| {
                        if u.on_stack { Cap::Reg(u.idx as Reg) } else { Cap::Up(u.idx as u16) }
                    }).collect()
                });
                Ins::Closure { a, idx, caps }
            }
            80 => Ins::VarArg { a, n: opt(c) },
            // VARARGPREP and EXTRAARG carry nothing for the decompiler.
            81 | 82 => Ins::Data,
            _ => Ins::Unknown,
        };
        if matches!(ins[pc], Ins::Data) { data[pc] = true; }
    }
    finish(ins, data)
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
        Ins::LoadBoolJump { target, .. } => vec![*target],
        Ins::Branch { target, .. } => vec![nx, *target],
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
        | Ins::TailCall { .. } | Ins::Branch { .. } | Ins::LoadBoolJump { .. })
}

/// Roblox clients store each Luau opcode multiplied by 227 (mod 256).
pub const LUAU_OP_KEY: u8 = 227;

/// Luau opcode numbers (Common/include/Luau/Bytecode.h).
mod lop {
    pub const NOP: u32 = 0; pub const BREAK: u32 = 1; pub const LOADNIL: u32 = 2; pub const LOADB: u32 = 3;
    pub const LOADN: u32 = 4; pub const LOADK: u32 = 5; pub const MOVE: u32 = 6; pub const GETGLOBAL: u32 = 7;
    pub const SETGLOBAL: u32 = 8; pub const GETUPVAL: u32 = 9; pub const SETUPVAL: u32 = 10;
    pub const CLOSEUPVALS: u32 = 11; pub const GETIMPORT: u32 = 12; pub const GETTABLE: u32 = 13;
    pub const SETTABLE: u32 = 14; pub const GETTABLEKS: u32 = 15; pub const SETTABLEKS: u32 = 16;
    pub const GETTABLEN: u32 = 17; pub const SETTABLEN: u32 = 18; pub const NEWCLOSURE: u32 = 19;
    pub const NAMECALL: u32 = 20; pub const CALL: u32 = 21; pub const RETURN: u32 = 22; pub const JUMP: u32 = 23;
    pub const JUMPBACK: u32 = 24; pub const JUMPIF: u32 = 25; pub const JUMPIFNOT: u32 = 26;
    pub const JUMPIFEQ: u32 = 27; pub const JUMPIFLE: u32 = 28; pub const JUMPIFLT: u32 = 29;
    pub const JUMPIFNOTEQ: u32 = 30; pub const JUMPIFNOTLE: u32 = 31; pub const JUMPIFNOTLT: u32 = 32;
    pub const ADD: u32 = 33; pub const POW: u32 = 38; pub const ADDK: u32 = 39; pub const POWK: u32 = 44;
    pub const AND: u32 = 45; pub const OR: u32 = 46; pub const ANDK: u32 = 47; pub const ORK: u32 = 48;
    pub const CONCAT: u32 = 49; pub const NOT: u32 = 50; pub const MINUS: u32 = 51; pub const LENGTH: u32 = 52;
    pub const NEWTABLE: u32 = 53; pub const DUPTABLE: u32 = 54; pub const SETLIST: u32 = 55;
    pub const FORNPREP: u32 = 56; pub const FORNLOOP: u32 = 57; pub const FORGLOOP: u32 = 58;
    pub const FORGPREP_INEXT: u32 = 59; pub const FASTCALL3: u32 = 60; pub const FORGPREP_NEXT: u32 = 61;
    pub const NATIVECALL: u32 = 62; pub const GETVARARGS: u32 = 63; pub const DUPCLOSURE: u32 = 64;
    pub const PREPVARARGS: u32 = 65; pub const LOADKX: u32 = 66; pub const JUMPX: u32 = 67;
    pub const FASTCALL: u32 = 68; pub const COVERAGE: u32 = 69; pub const CAPTURE: u32 = 70;
    pub const SUBRK: u32 = 71; pub const DIVRK: u32 = 72; pub const FASTCALL1: u32 = 73;
    pub const FASTCALL2: u32 = 74; pub const FASTCALL2K: u32 = 75; pub const FORGPREP: u32 = 76;
    pub const JUMPXEQKNIL: u32 = 77; pub const JUMPXEQKB: u32 = 78; pub const JUMPXEQKN: u32 = 79;
    pub const JUMPXEQKS: u32 = 80; pub const IDIV: u32 = 81; pub const IDIVK: u32 = 82;
    pub const GETUDATAKS: u32 = 83; pub const SETUDATAKS: u32 = 84; pub const NAMECALLUDATA: u32 = 85;
    pub const FASTPCALL: u32 = 89;

    /// Instructions followed by an AUX word (Luau/BytecodeUtils.h).
    pub fn has_aux(op: u32) -> bool {
        matches!(op, GETGLOBAL | SETGLOBAL | GETIMPORT | GETTABLEKS | SETTABLEKS | NAMECALL
            | JUMPIFEQ..=JUMPIFNOTLT | NEWTABLE | SETLIST | FORGLOOP | LOADKX | FASTCALL2 | FASTCALL2K
            | FASTCALL3 | JUMPXEQKNIL..=JUMPXEQKS | GETUDATAKS..=NAMECALLUDATA | 86..=88 | 90 | 91 | 93 | 94)
    }
}

/// Luau: an 8-bit opcode, then A, B, C bytes (or A and a signed 16-bit D, or
/// a signed 24-bit E); some instructions take one AUX word.  Jump targets are
/// `pc + 1 + D`, counting AUX words.
fn decode_luau(proto: &Proto) -> Decoded {
    let code = &proto.code;
    let n = code.len();
    let mut ins: Vec<Ins> = vec![Ins::Unknown; n];
    let mut data = vec![false; n];

    let mut pc = 0;
    while pc < n {
        let i = code[pc];
        let op = i & 0xFF;
        let a = ((i >> 8) & 0xFF) as Reg;
        let b = (i >> 16) & 0xFF;
        let c = (i >> 24) & 0xFF;
        let d = (i as i32) >> 16;
        let aux = code.get(pc + 1).copied().unwrap_or(0);
        let to = |off: i64| {
            let t = pc as i64 + 1 + off;
            if t < 0 { usize::MAX } else { t as usize }
        };
        let jd = to(d as i64);
        let opt = |v: u32| if v == 0 { None } else { Some((v - 1) as u16) };
        let arith = |o: u32| [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Mod, BinOp::Pow][o as usize].clone();
        let mut len = if lop::has_aux(op) { 2 } else { 1 };
        ins[pc] = match op {
            lop::LOADNIL => Ins::LoadNil { a, last: a },
            lop::LOADB if c == 0 => Ins::LoadBool { a, val: b != 0, skip: false },
            lop::LOADB => Ins::LoadBoolJump { a, val: b != 0, target: to(c as i64) },
            lop::LOADN => Ins::LoadImm { a, v: Rk::Int(d as i64) },
            lop::LOADK => Ins::LoadK { a, k: d as u16 as u32 },
            lop::LOADKX => Ins::LoadK { a, k: aux },
            lop::MOVE => Ins::Move { a, b: b as Reg },
            lop::GETGLOBAL => Ins::GetGlobal { a, k: aux },
            lop::SETGLOBAL => Ins::SetGlobal { a, k: aux },
            lop::GETUPVAL => Ins::GetUpval { a, up: b as u16 },
            lop::SETUPVAL => Ins::SetUpval { a, up: b as u16 },
            lop::CLOSEUPVALS => Ins::Close { a },
            lop::GETIMPORT => {
                let count = aux >> 30;
                let path = [(aux >> 20) & 1023, (aux >> 10) & 1023, aux & 1023];
                Ins::GetImport { a, path: path[..count.min(3) as usize].to_vec() }
            }
            lop::GETTABLE => Ins::GetTable { a, t: b as Reg, key: Rk::R(c as Reg) },
            lop::SETTABLE => Ins::SetTable { t: b as Reg, key: Rk::R(c as Reg), val: Rk::R(a) },
            lop::GETTABLEKS => Ins::GetTable { a, t: b as Reg, key: Rk::K(aux) },
            lop::SETTABLEKS => Ins::SetTable { t: b as Reg, key: Rk::K(aux), val: Rk::R(a) },
            // Runtime rewrites of the KS forms; the AUX keeps the constant in its low half.
            lop::GETUDATAKS => Ins::GetTable { a, t: b as Reg, key: Rk::K(aux & 0xFFFF) },
            lop::SETUDATAKS => Ins::SetTable { t: b as Reg, key: Rk::K(aux & 0xFFFF), val: Rk::R(a) },
            lop::GETTABLEN => Ins::GetTable { a, t: b as Reg, key: Rk::Int(c as i64 + 1) },
            lop::SETTABLEN => Ins::SetTable { t: b as Reg, key: Rk::Int(c as i64 + 1), val: Rk::R(a) },
            lop::NEWCLOSURE | lop::DUPCLOSURE => {
                // DUPCLOSURE's constant names the child proto.
                let idx = if op == lop::NEWCLOSURE {
                    d as u16 as usize
                } else {
                    match proto.constants.get(d as u16 as usize) {
                        Some(disassembler::LuaConstant::Proto(p)) => *p,
                        _ => usize::MAX,
                    }
                };
                let nups = proto.p.get(idx).map_or(0, |p| p.num_upvalues as usize);
                let mut caps = Vec::with_capacity(nups);
                for k in 0..nups {
                    let Some(&w) = code.get(pc + 1 + k) else { break };
                    if w & 0xFF != lop::CAPTURE { break; }
                    let (kind, r) = ((w >> 8) & 0xFF, (w >> 16) & 0xFF);
                    caps.push(match kind {
                        0 => Cap::Val(r as Reg),
                        1 => Cap::Reg(r as Reg),
                        _ => Cap::Up(r as u16),
                    });
                    len += 1;
                }
                Ins::Closure { a, idx, caps }
            }
            lop::NAMECALL => Ins::SelfOp { a, obj: b as Reg, key: Rk::K(aux) },
            lop::NAMECALLUDATA => Ins::SelfOp { a, obj: b as Reg, key: Rk::K(aux & 0xFFFF) },
            lop::CALL => Ins::Call { a, nargs: opt(b), nret: opt(c) },
            lop::RETURN => Ins::Return { a, n: opt(b) },
            lop::JUMP | lop::JUMPBACK => Ins::Jmp { target: jd, close: None },
            lop::JUMPX => Ins::Jmp { target: to(((i as i32) >> 8) as i64), close: None },
            lop::JUMPIF => Ins::Branch { cond: BranchCond::Truthy(a), negate: false, target: jd },
            lop::JUMPIFNOT => Ins::Branch { cond: BranchCond::Truthy(a), negate: true, target: jd },
            lop::JUMPIFEQ..=lop::JUMPIFNOTLT => {
                let k = op - lop::JUMPIFEQ;
                let cop = [CmpOp::Eq, CmpOp::Le, CmpOp::Lt][(k % 3) as usize];
                let cond = BranchCond::Cmp { op: cop, l: Rk::R(a), r: Rk::R(aux as Reg) };
                Ins::Branch { cond, negate: k >= 3, target: jd }
            }
            lop::JUMPXEQKNIL..=lop::JUMPXEQKS => {
                let r = match op {
                    lop::JUMPXEQKNIL => Rk::Nil,
                    lop::JUMPXEQKB => Rk::Bool(aux & 1 != 0),
                    _ => Rk::K(aux & 0xFF_FFFF),
                };
                let cond = BranchCond::Cmp { op: CmpOp::Eq, l: Rk::R(a), r };
                Ins::Branch { cond, negate: aux >> 31 != 0, target: jd }
            }
            lop::ADD..=lop::POW => Ins::Arith { a, op: arith(op - lop::ADD), l: Rk::R(b as Reg), r: Rk::R(c as Reg) },
            lop::ADDK..=lop::POWK => Ins::Arith { a, op: arith(op - lop::ADDK), l: Rk::R(b as Reg), r: Rk::K(c) },
            lop::SUBRK => Ins::Arith { a, op: BinOp::Sub, l: Rk::K(b), r: Rk::R(c as Reg) },
            lop::DIVRK => Ins::Arith { a, op: BinOp::Div, l: Rk::K(b), r: Rk::R(c as Reg) },
            lop::IDIV => Ins::Arith { a, op: BinOp::IDiv, l: Rk::R(b as Reg), r: Rk::R(c as Reg) },
            lop::IDIVK => Ins::Arith { a, op: BinOp::IDiv, l: Rk::R(b as Reg), r: Rk::K(c) },
            // Both operands are already computed registers/constants, so the
            // source-level short circuit selects the same value.
            lop::AND => Ins::Arith { a, op: BinOp::And, l: Rk::R(b as Reg), r: Rk::R(c as Reg) },
            lop::OR => Ins::Arith { a, op: BinOp::Or, l: Rk::R(b as Reg), r: Rk::R(c as Reg) },
            lop::ANDK => Ins::Arith { a, op: BinOp::And, l: Rk::R(b as Reg), r: Rk::K(c) },
            lop::ORK => Ins::Arith { a, op: BinOp::Or, l: Rk::R(b as Reg), r: Rk::K(c) },
            lop::CONCAT => Ins::Concat { a, b: b as Reg, c: c as Reg },
            lop::NOT => Ins::Unary { a, op: UnOp::Not, b: b as Reg },
            lop::MINUS => Ins::Unary { a, op: UnOp::Neg, b: b as Reg },
            lop::LENGTH => Ins::Unary { a, op: UnOp::Len, b: b as Reg },
            lop::NEWTABLE => Ins::NewTable { a },
            lop::DUPTABLE => Ins::DupTable { a, k: d as u16 as u32 },
            lop::SETLIST => Ins::SetList { a, src: b as Reg, n: opt(c), first: aux as u64 },
            // FORNPREP falls into the body or jumps past FORNLOOP; modelled
            // (as for 5.4) as a jump to FORNLOOP, which tests and loops.
            lop::FORNPREP => Ins::ForPrep { a, target: jd.wrapping_sub(1), init: [a + 2, a, a + 1] },
            lop::FORNLOOP => Ins::ForLoop { a, var: a + 2, target: jd },
            lop::FORGPREP | lop::FORGPREP_INEXT | lop::FORGPREP_NEXT => Ins::Jmp { target: jd, close: None },
            // FORGLOOP: the call (at pc) and the test-and-jump (in the AUX slot).
            lop::FORGLOOP => {
                let nvars = ((aux & 0xFF) as u16).max(1);
                if pc + 1 < n {
                    ins[pc + 1] = Ins::TForLoop { a: a + 2, src: a + 3, target: jd };
                }
                len = 1; // the AUX slot holds the TFORLOOP part
                Ins::TForCall { a, nvars, base: 3, ctl: 2 }
            }
            lop::GETVARARGS => Ins::VarArg { a, n: opt(b) },
            // Hints and no-ops: the fast calls fall back to the following
            // CALL, which computes the same result.
            lop::NOP | lop::BREAK | lop::NATIVECALL | lop::PREPVARARGS | lop::COVERAGE | lop::CAPTURE
            | lop::FASTCALL | lop::FASTCALL1 | lop::FASTCALL2 | lop::FASTCALL2K | lop::FASTCALL3
            | lop::FASTPCALL => Ins::Data,
            _ => Ins::Unknown,
        };
        if matches!(ins[pc], Ins::Data) { data[pc] = true; }
        for w in pc + 1..(pc + len).min(n) { data[w] = true; }
        if op == lop::FORGLOOP && pc + 1 < n {
            pc += 2;
        } else {
            pc += len.max(1);
        }
    }
    finish(ins, data)
}
