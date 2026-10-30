//! LuaJIT bytecode (src/lj_bc.h): opcode numbering and listing.
//!
//! An instruction is `B:8 C:8 A:8 OP:8` (most significant first), or
//! `D:16 A:8 OP:8`.  Jump targets are `pc + 1 + D - 0x8000`.  LuaJIT 2.1
//! inserted ISTYPE/ISNUM, TGETR and TSETR into 2.0's numbering (and later
//! appended the bit operators); [`canon_op`] maps both onto 2.1's.

use std::io::Write;

use crate::{constant_to_string, nups, process_sub, Proto};

pub const ISLT: u32 = 0; pub const ISGE: u32 = 1; pub const ISLE: u32 = 2; pub const ISGT: u32 = 3;
pub const ISEQV: u32 = 4; pub const ISNEV: u32 = 5; pub const ISEQS: u32 = 6; pub const ISNES: u32 = 7;
pub const ISEQN: u32 = 8; pub const ISNEN: u32 = 9; pub const ISEQP: u32 = 10; pub const ISNEP: u32 = 11;
pub const ISTC: u32 = 12; pub const ISFC: u32 = 13; pub const IST: u32 = 14; pub const ISF: u32 = 15;
pub const ISTYPE: u32 = 16; pub const ISNUM: u32 = 17;
pub const MOV: u32 = 18; pub const NOT: u32 = 19; pub const UNM: u32 = 20; pub const LEN: u32 = 21;
pub const ADDVN: u32 = 22; pub const MODVN: u32 = 26; pub const ADDNV: u32 = 27; pub const MODNV: u32 = 31;
pub const ADDVV: u32 = 32; pub const MODVV: u32 = 36; pub const POW: u32 = 37; pub const CAT: u32 = 38;
pub const KSTR: u32 = 39; pub const KCDATA: u32 = 40; pub const KSHORT: u32 = 41; pub const KNUM: u32 = 42;
pub const KPRI: u32 = 43; pub const KNIL: u32 = 44;
pub const UGET: u32 = 45; pub const USETV: u32 = 46; pub const USETS: u32 = 47; pub const USETN: u32 = 48;
pub const USETP: u32 = 49; pub const UCLO: u32 = 50; pub const FNEW: u32 = 51;
pub const TNEW: u32 = 52; pub const TDUP: u32 = 53; pub const GGET: u32 = 54; pub const GSET: u32 = 55;
pub const TGETV: u32 = 56; pub const TGETS: u32 = 57; pub const TGETB: u32 = 58; pub const TGETR: u32 = 59;
pub const TSETV: u32 = 60; pub const TSETS: u32 = 61; pub const TSETB: u32 = 62; pub const TSETM: u32 = 63;
pub const TSETR: u32 = 64;
pub const CALLM: u32 = 65; pub const CALL: u32 = 66; pub const CALLMT: u32 = 67; pub const CALLT: u32 = 68;
pub const ITERC: u32 = 69; pub const ITERN: u32 = 70; pub const VARG: u32 = 71; pub const ISNEXT: u32 = 72;
pub const RETM: u32 = 73; pub const RET: u32 = 74; pub const RET0: u32 = 75; pub const RET1: u32 = 76;
pub const FORI: u32 = 77; pub const JFORI: u32 = 78; pub const FORL: u32 = 79; pub const IFORL: u32 = 80;
pub const JFORL: u32 = 81; pub const ITERL: u32 = 82; pub const IITERL: u32 = 83; pub const JITERL: u32 = 84;
pub const LOOP: u32 = 85; pub const ILOOP: u32 = 86; pub const JLOOP: u32 = 87; pub const JMP: u32 = 88;
pub const BNOT: u32 = 89; pub const BAND: u32 = 90; pub const BOR: u32 = 91; pub const BXOR: u32 = 92;
pub const BSHL: u32 = 93; pub const BSHR: u32 = 94; pub const BSAR: u32 = 95;
/// Not a LuaJIT opcode: anything `canon_op` does not know.
pub const UNKNOWN: u32 = 0xFF;

const NAMES: [&str; 96] = [
    "ISLT", "ISGE", "ISLE", "ISGT", "ISEQV", "ISNEV", "ISEQS", "ISNES", "ISEQN", "ISNEN", "ISEQP", "ISNEP",
    "ISTC", "ISFC", "IST", "ISF", "ISTYPE", "ISNUM", "MOV", "NOT", "UNM", "LEN",
    "ADDVN", "SUBVN", "MULVN", "DIVVN", "MODVN", "ADDNV", "SUBNV", "MULNV", "DIVNV", "MODNV",
    "ADDVV", "SUBVV", "MULVV", "DIVVV", "MODVV", "POW", "CAT",
    "KSTR", "KCDATA", "KSHORT", "KNUM", "KPRI", "KNIL",
    "UGET", "USETV", "USETS", "USETN", "USETP", "UCLO", "FNEW",
    "TNEW", "TDUP", "GGET", "GSET", "TGETV", "TGETS", "TGETB", "TGETR", "TSETV", "TSETS", "TSETB", "TSETM", "TSETR",
    "CALLM", "CALL", "CALLMT", "CALLT", "ITERC", "ITERN", "VARG", "ISNEXT",
    "RETM", "RET", "RET0", "RET1",
    "FORI", "JFORI", "FORL", "IFORL", "JFORL", "ITERL", "IITERL", "JITERL", "LOOP", "ILOOP", "JLOOP", "JMP",
    "BNOT", "BAND", "BOR", "BXOR", "BSHL", "BSHR", "BSAR",
];

/// The 2.1 number of opcode `op` of a dump in format `jit` (1 = LuaJIT
/// 2.0, 2 = 2.1).  Header-only and unknown opcodes give [`UNKNOWN`].
pub fn canon_op(jit: u8, op: u32) -> u32 {
    if jit == 1 {
        return match op {
            0..=15 => op,
            16..=56 => op + 2,  // MOV .. TGETB
            57..=60 => op + 3,  // TSETV .. TSETM
            61..=84 => op + 4,  // CALLM .. JMP
            _ => UNKNOWN,
        };
    }
    if op <= BSAR { op } else { UNKNOWN }
}

pub fn op_name(op: u32) -> &'static str {
    NAMES.get(op as usize).copied().unwrap_or("?")
}

pub fn disassemble_to(f: &Proto, name: Option<&str>, out: &mut dyn Write) {
    let _ = writeln!(out, "; Function:        {}", name.unwrap_or(""));
    let _ = writeln!(out, "; Defined at line: {}", f.linedefined);
    let _ = writeln!(out, "; #Upvalues:       {}", nups(f));
    let _ = writeln!(out, "; #Parameters:     {}", f.numparams);
    let _ = writeln!(out, "; Is_vararg:       {}", f.is_vararg);
    let _ = writeln!(out, "; Frame Size:      {}", f.maxstacksize);
    let _ = writeln!(out, "; #Constants:      {} (numbers from K{})", f.constants.len(), f.nkgc);
    for (ki, kv) in f.constants.iter().enumerate() {
        let _ = writeln!(out, ";   K{} = {}", ki, constant_to_string(kv));
    }
    let _ = writeln!(out);

    let k = |i: usize| f.constants.get(i).map(constant_to_string).unwrap_or_else(|| format!("K{}", i));
    let kn = |d: u32| k(f.nkgc + d as usize);
    let ks = |d: u32| k(d as usize);
    let pri = |d: u32| ["nil", "false", "true"].get(d as usize).copied().unwrap_or("?");
    let arg0 = f.jit_arg_offset() as u32;
    for (pc, &i) in f.code.iter().enumerate() {
        let op = canon_op(f.jit, i & 0xFF);
        let a = (i >> 8) & 0xFF;
        let c = (i >> 16) & 0xFF;
        let b = i >> 24;
        let d = i >> 16;
        let target = pc as i64 + 1 + d as i64 - 0x8000;
        let note = match op {
            ISLT..=ISGT => {
                let (sym, neg) = [("<", ""), ("<", "not "), ("<=", ""), ("<=", "not ")][op as usize];
                format!("if {}R{} {} R{} then goto next", neg, a, sym, d)
            }
            ISEQV | ISNEV => format!("if R{} {} R{} then goto next", a, eq(op), d),
            ISEQS | ISNES => format!("if R{} {} {} then goto next", a, eq(op), ks(d)),
            ISEQN | ISNEN => format!("if R{} {} {} then goto next", a, eq(op), kn(d)),
            ISEQP | ISNEP => format!("if R{} {} {} then goto next", a, eq(op), pri(d)),
            ISTC | ISFC => format!("if {}R{} then R{} := R{}; goto next", if op == ISFC { "not " } else { "" }, d, a, d),
            IST | ISF => format!("if {}R{} then goto next", if op == ISF { "not " } else { "" }, d),
            MOV => format!("R{} := R{}", a, d),
            NOT => format!("R{} := not R{}", a, d),
            UNM => format!("R{} := -R{}", a, d),
            LEN => format!("R{} := #R{}", a, d),
            ADDVN..=MODVN => format!("R{} := R{} {} {}", a, b, arith(op - ADDVN), kn(c)),
            ADDNV..=MODNV => format!("R{} := {} {} R{}", a, kn(c), arith(op - ADDNV), b),
            ADDVV..=MODVV => format!("R{} := R{} {} R{}", a, b, arith(op - ADDVV), c),
            POW => format!("R{} := R{} ^ R{}", a, b, c),
            CAT => format!("R{} := R{} .. ... .. R{}", a, b, c),
            KSTR | KCDATA => format!("R{} := {}", a, ks(d)),
            KSHORT => format!("R{} := {}", a, d as u16 as i16),
            KNUM => format!("R{} := {}", a, kn(d)),
            KPRI => format!("R{} := {}", a, pri(d)),
            KNIL => format!("R{}..R{} := nil", a, d),
            UGET => format!("R{} := U{}", a, d),
            USETV => format!("U{} := R{}", a, d),
            USETS => format!("U{} := {}", a, ks(d)),
            USETN => format!("U{} := {}", a, kn(d)),
            USETP => format!("U{} := {}", a, pri(d)),
            UCLO => format!("close upvalues >= R{}; goto {}", a, target),
            FNEW => format!("R{} := closure({})", a, ks(d)),
            TNEW => format!("R{} := {{}}", a),
            TDUP => format!("R{} := copy of {}", a, ks(d)),
            GGET => format!("R{} := _G[{}]", a, ks(d)),
            GSET => format!("_G[{}] := R{}", ks(d), a),
            TGETV | TGETR => format!("R{} := R{}[R{}]", a, b, c),
            TGETS => format!("R{} := R{}[{}]", a, b, ks(c)),
            TGETB => format!("R{} := R{}[{}]", a, b, c),
            TSETV | TSETR => format!("R{}[R{}] := R{}", b, c, a),
            TSETS => format!("R{}[{}] := R{}", b, ks(c), a),
            TSETB => format!("R{}[{}] := R{}", b, c, a),
            TSETM => format!("R{}[{} + i] := R{} + i, up to top", a.wrapping_sub(1), tsetm_first(f, d), a),
            CALLM | CALL => {
                let results = match b {
                    0 => format!("R{}..top := ", a),
                    1 => String::new(),
                    _ => format!("R{}..R{} := ", a, a + b - 2),
                };
                let args = match (op, c) {
                    (CALLM, _) => format!("R{}..top", a + arg0),
                    (_, 0 | 1) => String::new(),
                    _ => format!("R{}..R{}", a + arg0, a + arg0 + c - 2),
                };
                format!("{}R{}({})", results, a, args)
            }
            CALLMT => format!("return R{}(R{}..top)", a, a + arg0),
            CALLT if d <= 1 => format!("return R{}()", a),
            CALLT => format!("return R{}(R{}..R{})", a, a + arg0, a + arg0 + d - 2),
            ITERC | ITERN => format!("R{}.. := R{}(R{}, R{})", a, a.wrapping_sub(3), a.wrapping_sub(2), a.wrapping_sub(1)),
            VARG => format!("R{}.. := ...", a),
            ISNEXT | JMP => format!("goto {}", target),
            RETM => format!("return R{}..top", a),
            RET | RET0 | RET1 if d <= 1 => "return".into(),
            RET | RET0 | RET1 => format!("return R{}..R{}", a, a + d - 2),
            FORI | JFORI => format!("prepare R{}..R{}; if no iterations then goto {}", a, a + 2, target),
            FORL | IFORL | JFORL => format!("R{} += R{}; if loop continues then R{} := R{}; goto {}", a, a + 2, a + 3, a, target),
            ITERL | IITERL | JITERL => format!("if R{} ~= nil then R{} := R{}; goto {}", a, a.wrapping_sub(1), a, target),
            LOOP | ILOOP | JLOOP => "loop hint".into(),
            BNOT => format!("R{} := ~R{}", a, d),
            BAND..=BSAR => format!("R{} := R{} {} R{}", a, b, ["&", "|", "~", "<<", ">>", ">>>"][(op - BAND) as usize], c),
            _ => String::new(),
        };
        let args = if has_d(op) { format!("{} {}", a, d) } else { format!("{} {} {}", a, b, c) };
        let _ = writeln!(out, "{:5} [-]: {:<8} {:<14}; {}", pc, op_name(op), args, note);
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

/// TSETM's first index: the low word of its number constant (stored as
/// `2^52 + index`).
pub fn tsetm_first(f: &Proto, d: u32) -> u64 {
    match f.constants.get(f.nkgc + d as usize) {
        Some(crate::LuaConstant::Number(crate::LuaNumber::Float(x))) => x.to_bits() & 0xFFFF_FFFF,
        Some(crate::LuaConstant::Number(crate::LuaNumber::Integer(x))) => *x as u64 & 0xFFFF_FFFF,
        _ => 1,
    }
}

/// True for instructions with a 16-bit D operand (else B and C).
fn has_d(op: u32) -> bool {
    !matches!(op, ADDVN..=CAT | TGETV..=TGETR | TSETV..=TSETB | TSETR | CALLM | CALL | ITERC | ITERN | VARG | BAND..=BSAR)
}

fn eq(op: u32) -> &'static str {
    if op & 1 == 0 { "==" } else { "~=" }
}

fn arith(k: u32) -> &'static str {
    ["+", "-", "*", "/", "%"][k as usize]
}
