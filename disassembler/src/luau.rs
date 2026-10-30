//! Luau bytecode listing (Common/include/Luau/Bytecode.h).

use std::io::Write;

use crate::{constant_to_string, nups, process_sub, Proto};

const NAMES: [&str; 95] = [
    "NOP", "BREAK", "LOADNIL", "LOADB", "LOADN", "LOADK", "MOVE", "GETGLOBAL", "SETGLOBAL", "GETUPVAL",
    "SETUPVAL", "CLOSEUPVALS", "GETIMPORT", "GETTABLE", "SETTABLE", "GETTABLEKS", "SETTABLEKS", "GETTABLEN",
    "SETTABLEN", "NEWCLOSURE", "NAMECALL", "CALL", "RETURN", "JUMP", "JUMPBACK", "JUMPIF", "JUMPIFNOT",
    "JUMPIFEQ", "JUMPIFLE", "JUMPIFLT", "JUMPIFNOTEQ", "JUMPIFNOTLE", "JUMPIFNOTLT", "ADD", "SUB", "MUL", "DIV",
    "MOD", "POW", "ADDK", "SUBK", "MULK", "DIVK", "MODK", "POWK", "AND", "OR", "ANDK", "ORK", "CONCAT", "NOT",
    "MINUS", "LENGTH", "NEWTABLE", "DUPTABLE", "SETLIST", "FORNPREP", "FORNLOOP", "FORGLOOP", "FORGPREP_INEXT",
    "FASTCALL3", "FORGPREP_NEXT", "NATIVECALL", "GETVARARGS", "DUPCLOSURE", "PREPVARARGS", "LOADKX", "JUMPX",
    "FASTCALL", "COVERAGE", "CAPTURE", "SUBRK", "DIVRK", "FASTCALL1", "FASTCALL2", "FASTCALL2K", "FORGPREP",
    "JUMPXEQKNIL", "JUMPXEQKB", "JUMPXEQKN", "JUMPXEQKS", "IDIV", "IDIVK", "GETUDATAKS", "SETUDATAKS",
    "NAMECALLUDATA", "NEWCLASSMEMBER", "CALLFB", "CMPPROTO", "FASTPCALL", "NEWCLASS", "CONSTRUCT",
    "FINCONSTRUCT", "GETPRIVATEFIELD", "SETPRIVATEFIELD",
];

/// Instructions followed by an AUX word (Luau/BytecodeUtils.h).
pub(crate) fn has_aux(op: u32) -> bool {
    matches!(op, 7 | 8 | 12 | 15 | 16 | 20 | 27..=32 | 53 | 55 | 58 | 66 | 74 | 75 | 60 | 77..=80 | 83..=88 | 90 | 91 | 93 | 94)
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

    let k = |i: u32| f.constants.get(i as usize).map(constant_to_string).unwrap_or_else(|| format!("K{}", i));
    let mut pc = 0;
    while pc < f.code.len() {
        let i = f.code[pc];
        let op = i & 0xFF;
        let (a, b, c) = ((i >> 8) & 0xFF, (i >> 16) & 0xFF, (i >> 24) & 0xFF);
        let d = (i as i32) >> 16;
        let aux = if has_aux(op) { f.code.get(pc + 1).copied() } else { None };
        let target = pc as i64 + 1 + d as i64;
        let note = match op {
            2 => format!("R{} := nil", a),
            3 => format!("R{} := {}{}", a, b != 0, if c != 0 { format!("; goto {}", pc as u32 + 1 + c) } else { String::new() }),
            4 => format!("R{} := {}", a, d),
            5 => format!("R{} := {}", a, k(d as u16 as u32)),
            6 => format!("R{} := R{}", a, b),
            7 => format!("R{} := _G[{}]", a, k(aux.unwrap_or(0))),
            8 => format!("_G[{}] := R{}", k(aux.unwrap_or(0)), a),
            9 => format!("R{} := U{}", a, b),
            10 => format!("U{} := R{}", b, a),
            12 => {
                let x = aux.unwrap_or(0);
                let path: Vec<String> = [(x >> 20) & 1023, (x >> 10) & 1023, x & 1023][..((x >> 30).min(3)) as usize]
                    .iter().map(|&id| k(id)).collect();
                format!("R{} := {}", a, path.join("."))
            }
            13 => format!("R{} := R{}[R{}]", a, b, c),
            14 => format!("R{}[R{}] := R{}", b, c, a),
            15 => format!("R{} := R{}[{}]", a, b, k(aux.unwrap_or(0))),
            16 => format!("R{}[{}] := R{}", b, k(aux.unwrap_or(0)), a),
            17 => format!("R{} := R{}[{}]", a, b, c + 1),
            18 => format!("R{}[{}] := R{}", b, c + 1, a),
            19 => format!("R{} := closure(child {})", a, d),
            20 => format!("R{} := R{}; R{} := R{}[{}]", a + 1, b, a, b, k(aux.unwrap_or(0))),
            21 => format!("R{}({} args, {} results)", a, if b == 0 { "...".into() } else { (b - 1).to_string() }, if c == 0 { "all".into() } else { (c as i32 - 1).to_string() }),
            22 => format!("return R{} ({} values)", a, if b == 0 { "...".into() } else { (b - 1).to_string() }),
            23 | 24 => format!("goto {}", target),
            25 | 26 => format!("if {}R{} then goto {}", if op == 26 { "not " } else { "" }, a, target),
            27..=32 => {
                let sym = ["==", "<=", "<", "~=", ">", ">="][(op - 27) as usize];
                format!("if R{} {} R{} then goto {}", a, sym, aux.unwrap_or(0), target)
            }
            33..=38 | 81 => format!("R{} := R{} {} R{}", a, b, sym(op), c),
            39..=44 | 82 => format!("R{} := R{} {} {}", a, b, sym(op), k(c)),
            45 | 46 => format!("R{} := R{} {} R{}", a, b, if op == 45 { "and" } else { "or" }, c),
            47 | 48 => format!("R{} := R{} {} {}", a, b, if op == 47 { "and" } else { "or" }, k(c)),
            49 => format!("R{} := R{} .. ... .. R{}", a, b, c),
            50 => format!("R{} := not R{}", a, b),
            51 => format!("R{} := -R{}", a, b),
            52 => format!("R{} := #R{}", a, b),
            53 => format!("R{} := {{}}", a),
            54 => format!("R{} := copy of {}", a, k(d as u16 as u32)),
            55 => format!("R{}[{} + i] := R{} + i, 0 <= i < {}", a, aux.unwrap_or(0), b, if c == 0 { "top".into() } else { (c - 1).to_string() }),
            56 => format!("prepare R{}..R{}; if no iterations then goto {}", a, a + 2, target),
            57 => format!("R{} += R{}; if loop continues then goto {}", a + 2, a + 1, target),
            58 => format!("R{}.. := R{}(R{}, R{}); if R{} ~= nil then goto {}", a + 3, a, a + 1, a + 2, a + 3, target),
            59 | 61 | 76 => format!("goto {}", target),
            63 => format!("R{} .. := ...", a),
            64 => format!("R{} := closure({})", a, k(d as u16 as u32)),
            67 => format!("goto {}", pc as i64 + 1 + ((i as i32) >> 8) as i64),
            70 => format!("capture {} {}", ["value", "reference", "upvalue"].get(a as usize).copied().unwrap_or("?"), b),
            71 | 72 => format!("R{} := {} {} R{}", a, k(b), if op == 71 { "-" } else { "/" }, c),
            77 => format!("if R{} {} nil then goto {}", a, ne(aux), target),
            78 => format!("if R{} {} {} then goto {}", a, ne(aux), aux.unwrap_or(0) & 1 != 0, target),
            79 | 80 => format!("if R{} {} {} then goto {}", a, ne(aux), k(aux.unwrap_or(0) & 0xFF_FFFF), target),
            _ => String::new(),
        };
        let args = match aux {
            Some(x) => format!("{} {} {} [{}]", a, b, c, x),
            None => format!("{} {} {}", a, b, c),
        };
        let opname = NAMES.get(op as usize).copied().unwrap_or("?");
        let _ = writeln!(out, "{:5} [-]: {:<14} {:<16}; {}", pc, opname, args, note);
        pc += if aux.is_some() { 2 } else { 1 };
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

fn sym(op: u32) -> &'static str {
    match op {
        33 | 39 => "+", 34 | 40 => "-", 35 | 41 => "*", 36 | 42 => "/", 37 | 43 => "%", 38 | 44 => "^", 81 | 82 => "//",
        _ => "?",
    }
}

/// JUMPXEQK*: the AUX high bit flips the comparison.
fn ne(aux: Option<u32>) -> &'static str {
    if aux.unwrap_or(0) >> 31 != 0 { "~=" } else { "==" }
}
