pub use luac_parser::{LuaConstant, LuaNumber};

mod lua54;
mod luau;

/// Words taken by a Luau instruction with this opcode (1, or 2 with AUX).
pub fn luau_op_length(op: u32) -> usize {
    if luau::has_aux(op) { 2 } else { 1 }
}
use luac_parser::{LuaChunk, UpVal};
use std::cell::Cell;

thread_local! {
    static LUA_VERSION: Cell<u8> = Cell::new(0x53);
}

/// Call this before disassembling to select the right opcode table.
/// Pass `parsed.header.lua_version` from luac_parser.
pub fn set_lua_version(v: u8) {
    LUA_VERSION.with(|c| c.set(v));
}

/// Header version byte of Luau bytecode (`luac_parser::LUAU`).
pub const LUAU_VERSION: u8 = 0xB0;

pub fn lua_version() -> u8 {
    LUA_VERSION.with(|c| c.get())
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

pub const LFIELDS_PER_FLUSH: usize = 50;

const SIZE_OP: u32 = 6;
const SIZE_A: u32 = 8;
const SIZE_B: u32 = 9;
const SIZE_C: u32 = 9;
const POS_OP: u32 = 0;
const POS_A: u32 = 6;
const POS_C: u32 = 14;
const POS_B: u32 = 23;
const MAXARG_SBX: i32 = (1 << 17) - 1; // 131071
const BITRK: usize = 1 << 8; // bit marking RK as a constant index

#[inline]
fn mask1(n: u32) -> u32 {
    (1u32 << n).wrapping_sub(1)
}

// ---------------------------------------------------------------------------
// Opcode enum (superset of lua51/52/53)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OpCode {
    Move,
    LoadK,
    LoadKx,
    LoadBool,
    LoadNil,
    GetUpVal,
    GetGlobal,  // lua51 only
    GetTabUp,
    GetTable,
    SetGlobal,  // lua51 only
    SetTabUp,
    SetUpVal,
    SetTable,
    NewTable,
    Self_,
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Mod,
    IDiv,   // lua53+
    Band,   // lua53+
    Bor,    // lua53+
    BXor,   // lua53+
    Shl,    // lua53+
    Shr,    // lua53+
    Unm,
    Not,
    Len,
    BNot,   // lua53+
    Concat,
    Jmp,
    Eq,
    Lt,
    Le,
    Test,
    TestSet,
    Call,
    TailCall,
    Return,
    ForLoop,
    ForPrep,
    /// TFORLOOP in lua51, TFORCALL in lua52/53
    LuaDecTForLoop,
    TForLoop,   // lua52/53
    SetList,
    Close,      // lua51
    Closure,
    VarArg,
    ExtraArg,   // lua52/53
    Unknown,
}

// ---------------------------------------------------------------------------
// Instruction decoding
// ---------------------------------------------------------------------------

fn lua51_opcode(op: u32) -> OpCode {
    match op {
        0  => OpCode::Move,
        1  => OpCode::LoadK,
        2  => OpCode::LoadBool,
        3  => OpCode::LoadNil,
        4  => OpCode::GetUpVal,
        5  => OpCode::GetGlobal,
        6  => OpCode::GetTable,
        7  => OpCode::SetGlobal,
        8  => OpCode::SetUpVal,
        9  => OpCode::SetTable,
        10 => OpCode::NewTable,
        11 => OpCode::Self_,
        12 => OpCode::Add,
        13 => OpCode::Sub,
        14 => OpCode::Mul,
        15 => OpCode::Div,
        16 => OpCode::Mod,
        17 => OpCode::Pow,
        18 => OpCode::Unm,
        19 => OpCode::Not,
        20 => OpCode::Len,
        21 => OpCode::Concat,
        22 => OpCode::Jmp,
        23 => OpCode::Eq,
        24 => OpCode::Lt,
        25 => OpCode::Le,
        26 => OpCode::Test,
        27 => OpCode::TestSet,
        28 => OpCode::Call,
        29 => OpCode::TailCall,
        30 => OpCode::Return,
        31 => OpCode::ForLoop,
        32 => OpCode::ForPrep,
        33 => OpCode::LuaDecTForLoop,
        34 => OpCode::SetList,
        35 => OpCode::Close,
        36 => OpCode::Closure,
        37 => OpCode::VarArg,
        _  => OpCode::Unknown,
    }
}

fn lua52_opcode(op: u32) -> OpCode {
    match op {
        0  => OpCode::Move,
        1  => OpCode::LoadK,
        2  => OpCode::LoadKx,
        3  => OpCode::LoadBool,
        4  => OpCode::LoadNil,
        5  => OpCode::GetUpVal,
        6  => OpCode::GetTabUp,
        7  => OpCode::GetTable,
        8  => OpCode::SetTabUp,
        9  => OpCode::SetUpVal,
        10 => OpCode::SetTable,
        11 => OpCode::NewTable,
        12 => OpCode::Self_,
        13 => OpCode::Add,
        14 => OpCode::Sub,
        15 => OpCode::Mul,
        16 => OpCode::Div,
        17 => OpCode::Mod,
        18 => OpCode::Pow,
        19 => OpCode::Unm,
        20 => OpCode::Not,
        21 => OpCode::Len,
        22 => OpCode::Concat,
        23 => OpCode::Jmp,
        24 => OpCode::Eq,
        25 => OpCode::Lt,
        26 => OpCode::Le,
        27 => OpCode::Test,
        28 => OpCode::TestSet,
        29 => OpCode::Call,
        30 => OpCode::TailCall,
        31 => OpCode::Return,
        32 => OpCode::ForLoop,
        33 => OpCode::ForPrep,
        34 => OpCode::LuaDecTForLoop,
        35 => OpCode::TForLoop,
        36 => OpCode::SetList,
        37 => OpCode::Closure,
        38 => OpCode::VarArg,
        39 => OpCode::ExtraArg,
        // Extended opcodes present in this runtime (Lua 5.2 chunk format, Lua 5.3 runtime)
        40 => OpCode::IDiv,
        41 => OpCode::BNot,
        42 => OpCode::Band,
        43 => OpCode::Bor,
        44 => OpCode::BXor,
        45 => OpCode::Shl,
        46 => OpCode::Shr,
        _  => OpCode::Unknown,
    }
}

/// Opcode numbering of stock Lua 5.3 (lopcodes.h), which renumbers everything
/// after SELF relative to 5.2.
fn lua53_opcode(op: u32) -> OpCode {
    match op {
        0  => OpCode::Move,
        1  => OpCode::LoadK,
        2  => OpCode::LoadKx,
        3  => OpCode::LoadBool,
        4  => OpCode::LoadNil,
        5  => OpCode::GetUpVal,
        6  => OpCode::GetTabUp,
        7  => OpCode::GetTable,
        8  => OpCode::SetTabUp,
        9  => OpCode::SetUpVal,
        10 => OpCode::SetTable,
        11 => OpCode::NewTable,
        12 => OpCode::Self_,
        13 => OpCode::Add,
        14 => OpCode::Sub,
        15 => OpCode::Mul,
        16 => OpCode::Mod,
        17 => OpCode::Pow,
        18 => OpCode::Div,
        19 => OpCode::IDiv,
        20 => OpCode::Band,
        21 => OpCode::Bor,
        22 => OpCode::BXor,
        23 => OpCode::Shl,
        24 => OpCode::Shr,
        25 => OpCode::Unm,
        26 => OpCode::BNot,
        27 => OpCode::Not,
        28 => OpCode::Len,
        29 => OpCode::Concat,
        30 => OpCode::Jmp,
        31 => OpCode::Eq,
        32 => OpCode::Lt,
        33 => OpCode::Le,
        34 => OpCode::Test,
        35 => OpCode::TestSet,
        36 => OpCode::Call,
        37 => OpCode::TailCall,
        38 => OpCode::Return,
        39 => OpCode::ForLoop,
        40 => OpCode::ForPrep,
        41 => OpCode::LuaDecTForLoop,
        42 => OpCode::TForLoop,
        43 => OpCode::SetList,
        44 => OpCode::Closure,
        45 => OpCode::VarArg,
        46 => OpCode::ExtraArg,
        _  => OpCode::Unknown,
    }
}

pub fn get_opcode(i: u32) -> OpCode {
    let op = (i >> POS_OP) & mask1(SIZE_OP);
    match lua_version() {
        0x51 => lua51_opcode(op),
        0x52 => lua52_opcode(op),
        0x53 => lua53_opcode(op),
        // 5.4 has its own layout; see `ir::decode` and `lua54::disassemble_to`.
        _    => OpCode::Unknown,
    }
}

pub fn getarg_a(i: u32) -> u32 {
    (i >> POS_A) & mask1(SIZE_A)
}

pub fn getarg_b(i: u32) -> u32 {
    (i >> POS_B) & mask1(SIZE_B)
}

pub fn getarg_c(i: u32) -> u32 {
    (i >> POS_C) & mask1(SIZE_C)
}

pub fn getarg_bx(i: u32) -> u32 {
    (i >> POS_C) & mask1(SIZE_B + SIZE_C)
}

pub fn getarg_sbx(i: u32) -> i32 {
    getarg_bx(i) as i32 - MAXARG_SBX
}

/// Ax occupies bits [6..31] (26 bits)
pub fn getarg_ax(i: u32) -> u32 {
    i >> POS_A
}

// ---------------------------------------------------------------------------
// Proto — owns all chunk data needed by the disassembler
// ---------------------------------------------------------------------------

/// Describes how one upvalue of a closure is captured.
#[derive(Clone, Debug)]
pub struct UpvalDesc {
    /// `true`  → captured from the enclosing function's register `idx`
    /// `false` → inherited from the enclosing function's upvalue `idx`
    pub on_stack: bool,
    pub idx: u8,
}

/// A local variable from the debug info: `name` lives in its register for
/// pcs `start_pc..end_pc`.
#[derive(Clone, Debug)]
pub struct LocVar {
    pub name: String,
    pub start_pc: usize,
    pub end_pc: usize,
    /// Its register, when the debug info records it (Luau).
    pub reg: Option<u16>,
}

#[derive(Clone)]
pub struct Proto {
    /// Lua version byte from the chunk header (0x51 .. 0x54).
    pub version: u8,
    pub linedefined: u64,
    pub numparams: u8,
    pub is_vararg: u8,
    /// Lua 5.5 prototype flags (PF_VAHID = 1, PF_VATAB = 2); 0 otherwise.
    pub flags: u8,
    pub maxstacksize: u8,
    pub sizecode: usize,
    pub code: Vec<u32>,
    pub sizep: usize,
    pub p: Vec<Proto>,
    pub constants: Vec<LuaConstant>,
    pub upvalue_names: Vec<String>,
    pub upvalue_infos: Vec<UpvalDesc>,
    pub num_upvalues: u8,
    /// Debug-info locals (empty for stripped chunks).
    pub locals: Vec<LocVar>,
    /// Luau bytecode (`version` is then 0x51: Luau numbers and globals
    /// behave like Lua 5.1's).
    pub luau: bool,
}

impl From<LuaChunk> for Proto {
    fn from(chunk: LuaChunk) -> Self {
        let sizecode = chunk.instructions.len();
        let sizep = chunk.prototypes.len();
        let num_upvalues = chunk.num_upvalues;
        let upvalue_names = chunk
            .upvalue_names
            .into_iter()
            .map(|v| String::from_utf8_lossy(&v).into_owned())
            .collect();
        let upvalue_infos = chunk
            .upvalue_infos
            .into_iter()
            .map(|u: UpVal| UpvalDesc { on_stack: u.on_stack, idx: u.id })
            .collect();
        let p = chunk.prototypes.into_iter().map(Proto::from).collect();
        let luau = lua_version() == LUAU_VERSION;
        let version = if luau { 0x51 } else { lua_version() };
        // Some Lua 5.2 variants set number_integral to a non-zero value but still
        // store numbers as IEEE 754 doubles (the raw 8 bytes are a double bit pattern
        // reinterpreted as an integer).  Re-interpret any Integer constant whose bit
        // pattern produces a normal (non-subnormal, non-NaN) f64 as a Float constant.
        // Lua 5.3 has real integer constants, so leave those alone.
        let constants = chunk.constants.into_iter().map(|c| {
            if let LuaConstant::Number(LuaNumber::Integer(v)) = c {
                let f = f64::from_bits(v as u64);
                if version < 0x53 && !luau && f.is_finite() && !f.is_subnormal() {
                    return LuaConstant::Number(LuaNumber::Float(f));
                }
                return LuaConstant::Number(LuaNumber::Integer(v));
            }
            c
        }).collect();
        let locals = chunk.locals.into_iter().map(|l| LocVar {
            name: l.name,
            start_pc: l.start_pc as usize,
            end_pc: l.end_pc as usize,
            reg: if luau { Some(l.reg as u16) } else { None },
        }).collect();
        Proto {
            version,
            locals,
            linedefined: chunk.line_defined,
            numparams: chunk.num_params,
            is_vararg: chunk.is_vararg.is_some() as u8,
            flags: if version >= 0x55 || luau { chunk.flags } else { 0 },
            maxstacksize: chunk.max_stack,
            sizecode,
            code: chunk.instructions,
            sizep,
            p,
            constants,
            upvalue_names,
            upvalue_infos,
            num_upvalues,
            luau,
        }
    }
}

// ---------------------------------------------------------------------------
// Helper functions used inside luadec_disassemble
// ---------------------------------------------------------------------------

pub fn nups(f: &Proto) -> u8 {
    f.num_upvalues
}

/// Escape a raw byte string into a valid Lua string literal body.
/// Printable ASCII (0x20–0x7E) passes through as-is, except `"` and `\`
/// which are backslash-escaped. Everything else becomes `\xHH`.
fn escape_lua_string(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len());
    for &b in bytes {
        match b {
            b'"'  => out.push_str("\\\""),
            b'\\'  => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7E => out.push(b as char),
            _ => { let _ = std::fmt::Write::write_fmt(&mut out, format_args!("\\x{:02X}", b)); }
        }
    }
    out
}

fn constant_to_string(c: &LuaConstant) -> String {
    match c {
        LuaConstant::Null => "nil".to_string(),
        LuaConstant::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        LuaConstant::Number(n) => match n {
            LuaNumber::Integer(i) => i.to_string(),
            LuaNumber::Float(f) => {
                // In Lua 5.1/5.2 every number is a float, so whole-number floats
                // like 1.0 / 2.0 are extremely common and look better as integers.
                // For Lua 5.3+ the integer type is separate (LuaNumber::Integer),
                // so a LuaNumber::Float that happens to be whole was written as
                // e.g. `1.0` in source — keep it as a float literal in that case.
                if f.fract() == 0.0 && f.abs() < 1e15 {
                    format!("{}", *f as i64)
                } else {
                    let s = format!("{}", f);
                    if s.contains('.') || s.contains('e') { s } else { format!("{:.1}", f) }
                }
            }
        },
        LuaConstant::String(s) => format!("\"{}\"", escape_lua_string(s)),
        LuaConstant::Proto(p) => format!("<proto {}>", p),
        LuaConstant::Table(_) => "<table>".to_string(),
        LuaConstant::Vector([x, y, z, _]) => format!("vector.create({}, {}, {})", x, y, z),
    }
}

pub fn decompile_constant(f: &Proto, idx: usize) -> String {
    f.constants
        .get(idx)
        .map(constant_to_string)
        .unwrap_or_else(|| format!("K{}", idx))
}

/// In lua51 globals are stored as string constants.
pub fn global_(f: &Proto, idx: usize) -> String {
    decompile_constant(f, idx)
}

/// "K" if the RK field refers to a constant, "" if a register.
pub fn cc(v: usize) -> &'static str {
    if v & BITRK != 0 { "K" } else { "" }
}

/// The index part of an RK field (strips the BITRK bit).
pub fn cv(v: usize) -> usize {
    v & !BITRK
}

/// Render an RK operand as a constant value or register name.
pub fn rk(f: &Proto, c: usize) -> String {
    if c & BITRK != 0 {
        decompile_constant(f, c & !BITRK)
    } else {
        format!("R{}", c)
    }
}

pub fn operators(o: OpCode) -> &'static str {
    match o {
        OpCode::Add  => "+",
        OpCode::Sub  => "-",
        OpCode::Mul  => "*",
        OpCode::Div  => "/",
        OpCode::Pow  => "^",
        OpCode::Mod  => "%",
        OpCode::IDiv => "//",
        OpCode::Band => "&",
        OpCode::Bor  => "|",
        OpCode::BXor => "~",
        OpCode::Shl  => "<<",
        OpCode::Shr  => ">>",
        OpCode::Unm  => "-",
        OpCode::Not  => "not ",
        OpCode::Len  => "#",
        OpCode::BNot => "~",
        _            => "?",
    }
}

pub fn opstr(o: OpCode) -> &'static str {
    match o {
        OpCode::Eq => "==",
        OpCode::Lt => "<",
        OpCode::Le => "<=",
        _          => "?",
    }
}

pub fn invopstr(o: OpCode) -> &'static str {
    match o {
        OpCode::Eq => "~=",
        OpCode::Lt => ">=",
        OpCode::Le => ">",
        _          => "?",
    }
}

pub fn lua_p_opnames(o: OpCode) -> &'static str {
    match o {
        OpCode::Move           => "MOVE",
        OpCode::LoadK          => "LOADK",
        OpCode::LoadKx         => "LOADKX",
        OpCode::LoadBool       => "LOADBOOL",
        OpCode::LoadNil        => "LOADNIL",
        OpCode::GetUpVal       => "GETUPVAL",
        OpCode::GetGlobal      => "GETGLOBAL",
        OpCode::GetTabUp       => "GETTABUP",
        OpCode::GetTable       => "GETTABLE",
        OpCode::SetGlobal      => "SETGLOBAL",
        OpCode::SetTabUp       => "SETTABUP",
        OpCode::SetUpVal       => "SETUPVAL",
        OpCode::SetTable       => "SETTABLE",
        OpCode::NewTable       => "NEWTABLE",
        OpCode::Self_          => "SELF",
        OpCode::Add            => "ADD",
        OpCode::Sub            => "SUB",
        OpCode::Mul            => "MUL",
        OpCode::Div            => "DIV",
        OpCode::Pow            => "POW",
        OpCode::Mod            => "MOD",
        OpCode::IDiv           => "IDIV",
        OpCode::Band           => "BAND",
        OpCode::Bor            => "BOR",
        OpCode::BXor           => "BXOR",
        OpCode::Shl            => "SHL",
        OpCode::Shr            => "SHR",
        OpCode::Unm            => "UNM",
        OpCode::Not            => "NOT",
        OpCode::Len            => "LEN",
        OpCode::BNot           => "BNOT",
        OpCode::Concat         => "CONCAT",
        OpCode::Jmp            => "JMP",
        OpCode::Eq             => "EQ",
        OpCode::Lt             => "LT",
        OpCode::Le             => "LE",
        OpCode::Test           => "TEST",
        OpCode::TestSet        => "TESTSET",
        OpCode::Call           => "CALL",
        OpCode::TailCall       => "TAILCALL",
        OpCode::Return         => "RETURN",
        OpCode::ForLoop        => "FORLOOP",
        OpCode::ForPrep        => "FORPREP",
        OpCode::LuaDecTForLoop => "TFORCALL",
        OpCode::TForLoop       => "TFORLOOP",
        OpCode::SetList        => "SETLIST",
        OpCode::Close          => "CLOSE",
        OpCode::Closure        => "CLOSURE",
        OpCode::VarArg         => "VARARG",
        OpCode::ExtraArg       => "EXTRAARG",
        OpCode::Unknown        => "UNKNOWN",
    }
}

/// Whether to recurse into nested function prototypes.
pub fn process_sub() -> bool {
    true
}

// ---------------------------------------------------------------------------
// Disassembler
// ---------------------------------------------------------------------------

/// Disassemble `fwork` to stdout.
pub fn luadec_disassemble(fwork: &Proto, dflag: i32, name: Option<&str>) {
    luadec_disassemble_to(fwork, dflag, name, &mut std::io::stdout());
}

/// Disassemble `fwork` into a `String`.
pub fn luadec_disassemble_str(fwork: &Proto, dflag: i32, name: Option<&str>) -> String {
    let mut buf = Vec::new();
    luadec_disassemble_to(fwork, dflag, name, &mut buf);
    String::from_utf8_lossy(&buf).into_owned()
}

pub fn luadec_disassemble_to(fwork: &Proto, dflag: i32, name: Option<&str>, out: &mut dyn std::io::Write) {
    if fwork.luau {
        return luau::disassemble_to(fwork, name, out);
    }
    if fwork.version >= 0x54 {
        return lua54::disassemble_to(fwork, name, out);
    }
    let f = fwork;
    let mut ignore_next = 0usize;

    let _ = writeln!(out, "; Function:        {}", name.unwrap_or(""));
    let _ = writeln!(out, "; Defined at line: {}", f.linedefined);
    let _ = writeln!(out, "; #Upvalues:       {}", nups(f));
    let _ = writeln!(out, "; #Parameters:     {}", f.numparams);
    let _ = writeln!(out, "; Is_vararg:       {}", f.is_vararg);
    let _ = writeln!(out, "; Max Stack Size:  {}", f.maxstacksize);
    let _ = writeln!(out, "; #Constants:      {}", f.constants.len());
    for (ki, kv) in f.constants.iter().enumerate() {
        let _ = writeln!(out, ";   K{} = {}", ki, constant_to_string(kv));
    }
    let _ = writeln!(out);

    let mut pc = 0usize;
    while pc < f.sizecode {
        let i = f.code[pc];
        let o = get_opcode(i);
        let a = getarg_a(i) as usize;
        let b = getarg_b(i) as usize;
        let c = getarg_c(i) as usize;
        let bc = getarg_bx(i) as usize;
        let sbc = getarg_sbx(i);

        let mut line = String::new();
        let mut lend = String::new();

        if ignore_next > 0 {
            ignore_next -= 1;
            let _ = writeln!(out, "{:5} [-]: {}", pc, i);
            pc += 1;
            continue;
        }

        match o {
            OpCode::Move => {
                line = format!("R{} R{}", a, b);
                lend = format!("R{} := R{}", a, b);
            }

            OpCode::LoadK => {
                line = format!("R{} K{}", a, bc);
                let tmpconstant1 = decompile_constant(f, bc);
                lend = format!("R{} := {}", a, tmpconstant1);
            }

            OpCode::LoadKx => {
                let ax = getarg_ax(f.code.get(pc + 1).copied().unwrap_or(0)) as usize;
                line = format!("R{}", a);
                let tmpconstant1 = decompile_constant(f, ax);
                lend = format!("R{} := K{} , {}", a, ax, tmpconstant1);
            }

            OpCode::ExtraArg => {
                let ax = getarg_ax(i);
                line = format!("{}", ax);
            }

            OpCode::LoadBool => {
                line = format!("R{} {} {}", a, b, c);
                if c != 0 {
                    lend = format!(
                        "R{} := {}; goto {}",
                        a,
                        if b != 0 { "true" } else { "false" },
                        pc + 2
                    );
                } else {
                    lend = format!("R{} := {}", a, if b != 0 { "true" } else { "false" });
                }
            }

            OpCode::LoadNil => {
                let rb = if lua_version() == 0x51 { b } else { a + b };
                if lua_version() == 0x51 {
                    line = format!("R{} R{}", a, b);
                } else {
                    line = format!("R{} {}", a, b);
                }

                if rb > a {
                    lend = format!("R{} to R{} := nil", a, rb);
                } else {
                    lend = format!("R{} := nil", rb);
                }
            }

            OpCode::VarArg => {
                line = format!("R{} {}", a, b);
                if b > 2 {
                    lend = format!("R{} to R{} := ...", a, a + b - 2);
                } else if b == 2 {
                    lend = format!("R{} := ...", a);
                } else if b == 0 {
                    lend = format!("R{} to top := ...", a);
                }
            }

            OpCode::GetUpVal => {
                line = format!("R{} U{}", a, b);
                lend = format!("R{} := U{}", a, b);
            }

            OpCode::GetGlobal => {
                line = format!("R{} K{}", a, bc);
                lend = format!("R{} := {}", a, global_(f, bc));
            }

            OpCode::GetTabUp => {
                line = format!("R{} U{} {}{}", a, b, cc(c), cv(c));
                let tmpconstant1 = rk(f, c);
                lend = format!("R{} := U{}[{}]", a, b, tmpconstant1);
            }

            OpCode::GetTable => {
                line = format!("R{} R{} {}{}", a, b, cc(c), cv(c));
                let tmpconstant1 = rk(f, c);
                lend = format!("R{} := R{}[{}]", a, b, tmpconstant1);
            }

            OpCode::SetGlobal => {
                line = format!("R{} K{}", a, bc);
                lend = format!("{} := R{}", global_(f, bc), a);
            }

            OpCode::SetTabUp => {
                line = format!("U{} {}{} {}{}", a, cc(b), cv(b), cc(c), cv(c));
                let tmpconstant1 = rk(f, b);
                let tmpconstant2 = rk(f, c);
                lend = format!("U{}[{}] := {}", a, tmpconstant1, tmpconstant2);
            }

            OpCode::SetUpVal => {
                line = format!("R{} U{}", a, b);
                lend = format!("U{} := R{}", b, a);
            }

            OpCode::SetTable => {
                line = format!("R{} {}{} {}{}", a, cc(b), cv(b), cc(c), cv(c));
                let tmpconstant1 = rk(f, b);
                let tmpconstant2 = rk(f, c);
                lend = format!("R{}[{}] := {}", a, tmpconstant1, tmpconstant2);
            }

            OpCode::NewTable => {
                line = format!("R{} {} {}", a, b, c);
                lend = format!("R{} := {{}} (size = {},{})", a, b, c);
            }

            OpCode::Self_ => {
                line = format!("R{} R{} {}{}", a, b, cc(c), cv(c));
                let tmpconstant1 = rk(f, c);
                lend = format!("R{} := R{}; R{} := R{}[{}]", a + 1, b, a, b, tmpconstant1);
            }

            OpCode::Add
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
            | OpCode::Shr => {
                line = format!("R{} {}{} {}{}", a, cc(b), cv(b), cc(c), cv(c));
                let tmpconstant1 = rk(f, b);
                let tmpconstant2 = rk(f, c);
                lend = format!("R{} := {} {} {}", a, tmpconstant1, operators(o), tmpconstant2);
            }

            OpCode::Unm | OpCode::Not | OpCode::Len | OpCode::BNot => {
                line = format!("R{} R{}", a, b);
                lend = format!("R{} := {}R{}", a, operators(o), b);
            }

            OpCode::Concat => {
                line = format!("R{} R{} R{}", a, b, c);
                lend = format!("R{} := concat(R{} to R{})", a, b, c);
            }

            OpCode::Jmp => {
                let dest = (pc as isize + sbc as isize + 1) as isize;
                line = format!("{}", sbc);
                lend = format!("PC += {} (goto {})", sbc, dest);

                if lua_version() != 0x51 {
                    line = format!("R{} {}", a, sbc);
                    if a > 0 {
                        lend.push_str(&format!("; close all upvalues in R{} to top", a - 1));
                    }
                }
            }

            OpCode::Eq | OpCode::Lt | OpCode::Le => {
                let dest = getarg_sbx(f.code.get(pc + 1).copied().unwrap_or(0)) + pc as i32 + 2;
                line = format!("{} {}{} {}{}", a, cc(b), cv(b), cc(c), cv(c));
                let tmpconstant1 = rk(f, b);
                let tmpconstant2 = rk(f, c);
                lend = format!(
                    "if {} {} {} then goto {} else goto {}",
                    tmpconstant1,
                    if a != 0 { invopstr(o) } else { opstr(o) },
                    tmpconstant2,
                    pc + 2,
                    dest
                );
            }

            OpCode::Test => {
                let dest = getarg_sbx(f.code.get(pc + 1).copied().unwrap_or(0)) + pc as i32 + 2;
                line = format!("R{} {}", a, c);
                lend = format!(
                    "if {}R{} then goto {} else goto {}",
                    if c != 0 { "not " } else { "" },
                    a,
                    pc + 2,
                    dest
                );
            }

            OpCode::TestSet => {
                let dest = getarg_sbx(f.code.get(pc + 1).copied().unwrap_or(0)) + pc as i32 + 2;
                line = format!("R{} R{} {}", a, b, c);
                lend = format!(
                    "if {}R{} then R{} := R{} ; goto {} else goto {}",
                    if c == 0 { "not " } else { "" },
                    b,
                    a,
                    b,
                    dest,
                    pc + 2
                );
            }

            OpCode::Call | OpCode::TailCall => {
                line = format!("R{} {} {}", a, b, c);

                let tmp = if b > 2 {
                    format!("R{} to R{}", a + 1, a + b - 1)
                } else if b == 2 {
                    format!("R{}", a + 1)
                } else if b == 1 {
                    String::new()
                } else {
                    format!("R{} to top", a + 1)
                };

                let tmp2 = if c > 2 {
                    format!("R{} to R{}", a, a + c - 2)
                } else if c == 2 {
                    format!("R{}", a)
                } else if c == 1 {
                    String::new()
                } else {
                    format!("R{} to top", a)
                };

                lend = format!("{} := R{}({})", tmp2, a, tmp);
            }

            OpCode::Return => {
                line = format!("R{} {}", a, b);

                let tmp = if b > 2 {
                    format!("R{} to R{}", a, a + b - 2)
                } else if b == 2 {
                    format!("R{}", a)
                } else if b == 1 {
                    String::new()
                } else {
                    format!("R{} to top", a)
                };

                lend = format!("return {}", tmp);
            }

            OpCode::ForLoop => {
                let dest = (pc as isize + sbc as isize + 1) as isize;
                line = format!("R{} {}", a, sbc);
                lend = format!(
                    "R{} += R{}; if R{} <= R{} then R{} := R{}; PC += {} , goto {} end",
                    a,
                    a + 2,
                    a,
                    a + 1,
                    a + 3,
                    a,
                    sbc,
                    dest
                );
            }

            OpCode::ForPrep => {
                line = format!("R{} {}", a, sbc);
                lend = format!(
                    "R{} -= R{}; pc += {} (goto {})",
                    a,
                    a + 2,
                    sbc,
                    pc as i32 + sbc + 1
                );
            }

            OpCode::LuaDecTForLoop => {
                line = format!("R{} {}", a, c);

                let tmp2 = if c == 1 {
                    format!("R{}", a + 3)
                } else if c > 1 {
                    format!("R{} to R{}", a + 3, a + c + 2)
                } else {
                    "ERROR c=0".to_string()
                };

                lend = format!("{} := R{}(R{},R{})", tmp2, a, a + 1, a + 2);

                if lua_version() == 0x51 {
                    lend.push_str(&format!(
                        "; if R{} ~= nil then R{} := R{} else goto {}",
                        a + 3,
                        a + 2,
                        a + 3,
                        pc + 2
                    ));
                }
            }

            OpCode::TForLoop => {
                let dest = (pc as isize + sbc as isize + 1) as isize;
                line = format!("R{} {}", a, sbc);
                lend = format!(
                    "if R{} ~= nil then {{ R{} := R{} ; pc += {} (goto {}) }}",
                    a + 1,
                    a,
                    a + 1,
                    sbc,
                    dest
                );
            }

            OpCode::SetList => {
                let mut next_is_extraarg = true;
                let mut realc = c as u32;

                if c == 0 {
                    let i_next_arg = f.code.get(pc + 1).copied().unwrap_or(0);

                    if lua_version() == 0x51 {
                        realc = i_next_arg;
                        ignore_next = 1;
                    } else {
                        if get_opcode(i_next_arg) == OpCode::ExtraArg {
                            realc = getarg_ax(i_next_arg);
                        } else {
                            next_is_extraarg = false;
                        }
                    }
                }

                let startindex = (realc.saturating_sub(1)) * LFIELDS_PER_FLUSH as u32;
                line = format!("R{} {} {}", a, b, c);

                if b == 0 {
                    lend = format!(
                        "R{}[{}] to R{}[top] := R{} to top",
                        a, startindex, a, a + 1
                    );
                } else if b == 1 {
                    lend = format!("R{}[{}] := R{}", a, startindex, a + 1);
                } else {
                    lend = format!(
                        "R{}[{}] to R{}[{}] := R{} to R{}",
                        a,
                        startindex,
                        a,
                        startindex + b as u32 - 1,
                        a + 1,
                        a + b
                    );
                }

                if c != 0 {
                    lend.push_str(&format!(
                        " ; R(a)[(c-1)*FPF+i] := R(a+i), 1 <= i <= b, a={}, b={}, c={}, FPF={}",
                        a, b, c, LFIELDS_PER_FLUSH
                    ));
                } else {
                    lend.push_str(&format!(
                        " ; R(a)[(realc-1)*FPF+i] := R(a+i), 1 <= i <= b, a={}, b={}, c={}, realc={}, FPF={}",
                        a, b, c, realc, LFIELDS_PER_FLUSH
                    ));

                    if lua_version() != 0x51 && !next_is_extraarg {
                        lend.push_str(
                            " ; Error: SETLIST with c==0, but not followed by EXTRAARG.",
                        );
                    }

                    if realc == 0 {
                        lend.push_str(" ; Error: SETLIST with c==0, but realc==0.");
                    }
                }

            }

            OpCode::Close => {
                line = format!("R{}", a);
                lend = format!("close all upvalues in R{} to top", a);
            }

            OpCode::Closure => {
                line = format!("R{} {}", a, bc);
                if let Some(name) = name {
                    lend = format!("R{} := closure(Function #{}_{})", a, name, bc);
                } else {
                    lend = format!("R{} := closure(Function #{})", a, bc);
                }
            }

            _ => {}
        }

        let _ = writeln!(
            out,
            "{:5} [-]: {:<9} {:<13}; {}",
            pc,
            lua_p_opnames(o),
            line,
            lend
        );

        pc += 1;
    }

    let _ = writeln!(out);

    if process_sub() && f.sizep != 0 {
        for sub_pc in 0..f.sizep {
            let subname = if let Some(name) = name {
                format!("{}_{}", name, sub_pc)
            } else {
                format!("{}", sub_pc)
            };
            luadec_disassemble_to(&f.p[sub_pc], dflag, Some(&subname), out);
        }
    }
}
