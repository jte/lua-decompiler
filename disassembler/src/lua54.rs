//! Lua 5.4 and 5.5 bytecode listing.  5.4 changed the instruction layout
//! (7-bit opcode, `k` flag, 25-bit jumps) and most opcodes, so it has its own
//! table; 5.5 is listed with 5.4's numbering (see `op55_as_54`).

use std::io::Write;

use crate::{constant_to_string, nups, process_sub, Proto};

const NAMES: [&str; 83] = [
    "MOVE", "LOADI", "LOADF", "LOADK", "LOADKX", "LOADFALSE", "LFALSESKIP", "LOADTRUE", "LOADNIL",
    "GETUPVAL", "SETUPVAL", "GETTABUP", "GETTABLE", "GETI", "GETFIELD", "SETTABUP", "SETTABLE",
    "SETI", "SETFIELD", "NEWTABLE", "SELF", "ADDI", "ADDK", "SUBK", "MULK", "MODK", "POWK", "DIVK",
    "IDIVK", "BANDK", "BORK", "BXORK", "SHRI", "SHLI", "ADD", "SUB", "MUL", "MOD", "POW", "DIV",
    "IDIV", "BAND", "BOR", "BXOR", "SHL", "SHR", "MMBIN", "MMBINI", "MMBINK", "UNM", "BNOT", "NOT",
    "LEN", "CONCAT", "CLOSE", "TBC", "JMP", "EQ", "LT", "LE", "EQK", "EQI", "LTI", "LEI", "GTI",
    "GEI", "TEST", "TESTSET", "CALL", "TAILCALL", "RETURN", "RETURN0", "RETURN1", "FORLOOP",
    "FORPREP", "TFORPREP", "TFORCALL", "TFORLOOP", "SETLIST", "CLOSURE", "VARARG", "VARARGPREP",
    "EXTRAARG",
];

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

/// Source symbol of the arithmetic ops ADD..SHR (and their K/I forms).
fn arith_sym(op: u32) -> &'static str {
    match op {
        21 | 22 | 34 => "+", 23 | 35 => "-", 24 | 36 => "*", 25 | 37 => "%", 26 | 38 => "^",
        27 | 39 => "/", 28 | 40 => "//", 29 | 41 => "&", 30 | 42 => "|", 31 | 43 => "~",
        33 | 44 => "<<", 32 | 45 => ">>", _ => "?",
    }
}

pub fn disassemble_to(f: &Proto, name: Option<&str>, out: &mut dyn Write) {
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

    let v55 = f.version >= 0x55;
    let k = |i: usize| f.constants.get(i).map(constant_to_string).unwrap_or_else(|| format!("K{}", i));
    for (pc, &i) in f.code.iter().enumerate() {
        let op = if v55 { op55_as_54(i & 0x7F) } else { i & 0x7F };
        let a = (i >> 7) & 0xFF;
        let kf = (i >> 15) & 1;
        let b = (i >> 16) & 0xFF;
        let c = (i >> 24) & 0xFF;
        let bx = i >> 15;
        let sbx = bx as i64 - 65535;
        let sb = b as i64 - 127;
        let sc = c as i64 - 127;
        let sj = (i >> 7) as i64 - 16_777_215;
        let ax = i >> 7;
        let rkc = if kf != 0 { k(c as usize) } else { format!("R{}", c) };
        let jmp = |off: i64| pc as i64 + 1 + off;
        let (args, note) = match op {
            0 => (format!("{} {}", a, b), format!("R{} := R{}", a, b)),
            1 | 2 => (format!("{} {}", a, sbx), format!("R{} := {}{}", a, sbx, if op == 2 { ".0" } else { "" })),
            3 => (format!("{} {}", a, bx), format!("R{} := {}", a, k(bx as usize))),
            4 => (format!("{}", a), format!("R{} := K[next EXTRAARG]", a)),
            5 => (format!("{}", a), format!("R{} := false", a)),
            6 => (format!("{}", a), format!("R{} := false; goto {}", a, pc + 2)),
            7 => (format!("{}", a), format!("R{} := true", a)),
            8 => (format!("{} {}", a, b), format!("R{} to R{} := nil", a, a + b)),
            9 => (format!("{} {}", a, b), format!("R{} := U{}", a, b)),
            10 => (format!("{} {}", a, b), format!("U{} := R{}", b, a)),
            11 => (format!("{} {} {}", a, b, c), format!("R{} := U{}[{}]", a, b, k(c as usize))),
            12 => (format!("{} {} {}", a, b, c), format!("R{} := R{}[R{}]", a, b, c)),
            13 => (format!("{} {} {}", a, b, c), format!("R{} := R{}[{}]", a, b, c)),
            14 => (format!("{} {} {}", a, b, c), format!("R{} := R{}[{}]", a, b, k(c as usize))),
            15 => (format!("{} {} {}{}", a, b, c, if kf != 0 { "k" } else { "" }), format!("U{}[{}] := {}", a, k(b as usize), rkc)),
            16 => (format!("{} {} {}{}", a, b, c, if kf != 0 { "k" } else { "" }), format!("R{}[R{}] := {}", a, b, rkc)),
            17 => (format!("{} {} {}{}", a, b, c, if kf != 0 { "k" } else { "" }), format!("R{}[{}] := {}", a, b, rkc)),
            18 => (format!("{} {} {}{}", a, b, c, if kf != 0 { "k" } else { "" }), format!("R{}[{}] := {}", a, k(b as usize), rkc)),
            19 => (format!("{} {} {}", a, b, c), format!("R{} := {{}}", a)),
            20 => {
                let key = if v55 { k(c as usize) } else { rkc.clone() };
                (format!("{} {} {}{}", a, b, c, if kf != 0 { "k" } else { "" }), format!("R{} := R{}; R{} := R{}[{}]", a + 1, b, a, b, key))
            }
            21 | 32 => (format!("{} {} {}", a, b, sc), format!("R{} := R{} {} {}", a, b, arith_sym(op), sc)),
            33 => (format!("{} {} {}", a, b, sc), format!("R{} := {} << R{}", a, sc, b)),
            22..=31 => (format!("{} {} {}", a, b, c), format!("R{} := R{} {} {}", a, b, arith_sym(op), k(c as usize))),
            34..=45 => (format!("{} {} {}", a, b, c), format!("R{} := R{} {} R{}", a, b, arith_sym(op), c)),
            46 => (format!("{} {} {}", a, b, c), format!("metamethod {} of R{}, R{}", c, a, b)),
            47 => (format!("{} {} {}", a, sb, c), format!("metamethod {} of R{}, {}", c, a, sb)),
            48 => (format!("{} {} {}", a, b, c), format!("metamethod {} of R{}, {}", c, a, k(b as usize))),
            49 => (format!("{} {}", a, b), format!("R{} := -R{}", a, b)),
            50 => (format!("{} {}", a, b), format!("R{} := ~R{}", a, b)),
            51 => (format!("{} {}", a, b), format!("R{} := not R{}", a, b)),
            52 => (format!("{} {}", a, b), format!("R{} := #R{}", a, b)),
            53 => (format!("{} {}", a, b), format!("R{} := R{} .. ... .. R{}", a, a, (a + b).saturating_sub(1))),
            54 => (format!("{}", a), format!("close upvalues and to-be-closed variables >= R{}", a)),
            55 => (format!("{}", a), format!("R{} is to be closed", a)),
            56 => (format!("{}", sj), format!("goto {}", jmp(sj))),
            57..=65 => {
                let rhs = match op {
                    57 | 58 | 59 => format!("R{}", b),
                    60 => k(b as usize),
                    _ => format!("{}{}", sb, if c != 0 { ".0" } else { "" }),
                };
                let sym = ["==", "<", "<=", "==", "==", "<", "<=", ">", ">="][(op - 57) as usize];
                (format!("{} {} {}", a, b, kf), format!("if (R{} {} {}) ~= {} then goto {}", a, sym, rhs, kf != 0, pc + 2))
            }
            66 => (format!("{} {}", a, kf), format!("if not R{} == {} then goto {}", a, kf != 0, pc + 2)),
            67 => (format!("{} {} {}", a, b, kf), format!("if not R{} == {} then goto {} else R{} := R{}", b, kf != 0, pc + 2, a, b)),
            68 | 69 => (format!("{} {} {}", a, b, c), format!("{}R{}({} args, {} results)", if op == 69 { "return " } else { "" }, a,
                if b == 0 { "...".to_string() } else { (b - 1).to_string() }, if c == 0 { "all".to_string() } else { (c as i64 - 1).to_string() })),
            70 => (format!("{} {} {}", a, b, c), format!("return R{} ({} values)", a, if b == 0 { "...".to_string() } else { (b - 1).to_string() })),
            71 => (String::new(), "return".to_string()),
            72 => (format!("{}", a), format!("return R{}", a)),
            73 if v55 => (format!("{} {}", a, bx), format!("update counters; if loop continues then R{} += step; goto {}", a + 2, jmp(-(bx as i64)))),
            73 => (format!("{} {}", a, bx), format!("R{} += R{}; if loop continues then R{} := R{}; goto {}", a, a + 2, a + 3, a, jmp(-(bx as i64)))),
            74 => (format!("{} {}", a, bx), format!("prepare R{}..R{}; if no iterations then goto {}", a, a + 3, jmp(bx as i64 + 1))),
            75 => (format!("{} {}", a, bx), format!("goto {}", jmp(bx as i64))),
            76 if v55 => (format!("{} {}", a, c), format!("R{} to R{} := R{}(R{}, R{})", a + 3, a + 2 + c, a, a + 1, a + 3)),
            76 => (format!("{} {}", a, c), format!("R{} to R{} := R{}(R{}, R{})", a + 4, a + 3 + c, a, a + 1, a + 2)),
            77 if v55 => (format!("{} {}", a, bx), format!("if R{} ~= nil then goto {}", a + 3, jmp(-(bx as i64)))),
            77 => (format!("{} {}", a, bx), format!("if R{} ~= nil then R{} := R{}; goto {}", a + 4, a + 2, a + 4, jmp(-(bx as i64)))),
            78 => {
                let (n, start) = if v55 { ((i >> 16) & 0x3F, (i >> 22) & 0x3FF) } else { (b, c) };
                (format!("{} {} {}", a, n, start), format!("R{}[{} + i] := R{} + i, 1 <= i <= {}", a, start, a, if n == 0 { "top".to_string() } else { n.to_string() }))
            }
            200 => (format!("{} {} {}", a, b, c), format!("R{} := vararg R{}[R{}]", a, b, c)),
            201 => (format!("{} {}", a, bx), format!("if R{} ~= nil then error \"global {} already defined\"", a,
                if bx > 0 { k(bx as usize - 1) } else { "?".to_string() })),
            79 => (format!("{} {}", a, bx), match name {
                Some(n) => format!("R{} := closure(Function #{}_{})", a, n, bx),
                None => format!("R{} := closure(Function #{})", a, bx),
            }),
            80 => (format!("{} {}", a, c), format!("R{} to R{} := ...", a, (a + c).saturating_sub(2))),
            81 => (format!("{}", a), "adjust varargs".to_string()),
            82 => (format!("{}", ax), String::new()),
            _ => (format!("{:#010x}", i), "unknown opcode".to_string()),
        };
        let opname = match op {
            200 => "GETVARG",
            201 => "ERRNNIL",
            _ => NAMES.get(op as usize).copied().unwrap_or("?"),
        };
        let _ = writeln!(out, "{:5} [-]: {:<10} {:<13}; {}", pc, opname, args, note);
    }
    let _ = writeln!(out);

    if process_sub() {
        for (sub_pc, sub) in f.p.iter().enumerate() {
            let subname = match name {
                Some(n) => format!("{}_{}", n, sub_pc),
                None => format!("{}", sub_pc),
            };
            disassemble_to(sub, Some(&subname), out);
        }
    }
}
