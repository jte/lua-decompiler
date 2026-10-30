//! Shared front end for the CLI and the web build: parse a compiled Lua chunk
//! and run it through the disassembler, decompiler and deobfuscator.

use disassembler::{Proto, luadec_disassemble_str};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Disassemble,
    Decompile,
    Deobfuscate,
    /// Graphviz DOT of the top-level function's control-flow graph.
    Cfg,
}

/// Parse `data` as a compiled Lua chunk.
///
/// If parsing fails and this looks like Lua 5.2, retry after stripping the
/// garbage debug-info fields that some obfuscators inject.
pub fn parse(data: &[u8]) -> Result<Proto, String> {
    let parsed_result = luac_parser::parse(data);
    let parsed_result = if parsed_result.is_err()
        && data.len() > 5 && data[4] == 0x52
    {
        let clean = sanitize_lua52(data);
        luac_parser::parse(&clean).map_err(|_| parsed_result.unwrap_err())
    } else {
        parsed_result
    };

    let parsed = parsed_result?;
    disassembler::set_header(&parsed.header);
    let mut proto = Proto::from(parsed.main_chunk);
    if proto.luau && luau_opcodes_encoded(&proto) {
        decode_luau_opcodes(&mut proto);
    }
    Ok(proto)
}

/// Luau opcodes as stored by Roblox clients: each opcode byte multiplied by
/// 227 (mod 256).  A main function always starts with PREPVARARGS (65),
/// which that turns into 163.
fn luau_opcodes_encoded(main: &Proto) -> bool {
    main.code.first().map_or(false, |&i| i & 0xFF == 163)
}

/// Undo the Roblox opcode encoding (203 is the inverse of 227 mod 256).
/// Only instruction words are touched; AUX words are data.
fn decode_luau_opcodes(p: &mut Proto) {
    let mut pc = 0;
    while pc < p.code.len() {
        let op = (p.code[pc] & 0xFF).wrapping_mul(203) & 0xFF;
        p.code[pc] = (p.code[pc] & !0xFF) | op;
        pc += disassembler::luau_op_length(op);
    }
    for c in p.p.iter_mut() {
        decode_luau_opcodes(c);
    }
}

/// Parse `data` and produce the output for `mode`.
///
/// `flatten` applies the CFG linearization pass before decompiling, for
/// control-flow-flattened (JMP-spaghetti) binaries. It only affects
/// `Decompile` and `Deobfuscate`.
pub fn process(data: &[u8], mode: Mode, flatten: bool) -> Result<String, String> {
    let proto = parse(data)?;
    Ok(run(&proto, mode, flatten))
}

pub fn run(proto: &Proto, mode: Mode, flatten: bool) -> String {
    match mode {
        Mode::Disassemble => luadec_disassemble_str(proto, 0, Some("0")),
        Mode::Cfg if proto.version >= 0x54 || proto.luau || proto.jit > 0 => decompiler::flow_dot(proto),
        Mode::Cfg => decompiler::cfg::Cfg::build(proto).to_dot(),
        Mode::Decompile if flatten => decompiler::decompile_cff(proto),
        Mode::Decompile => decompiler::decompile(proto),
        Mode::Deobfuscate => {
            // One name per variable for the deobfuscator; it applies the
            // locals limit itself at the end.
            let opts = decompiler::Options { reuse_locals: false };
            let mut block = if flatten {
                decompiler::decompile_cff_to_block_with(proto, opts)
            } else {
                decompiler::decompile_to_block_with(proto, opts)
            };
            deobfuscator::deobfuscate(&mut block);
            lua_ast::print_block(&block, 0)
        }
    }
}

/// Sanitize Lua 5.2 bytecode that has garbage in debug-info fields.
///
/// Walks the chunk tree preserving all structural fields (instructions,
/// constants, sub-protos, upvalue descriptors) but discarding/zeroing the
/// debug fields (source name, source lines, local names, upvalue names).
/// Any count field in the debug section that exceeds BOGUS_LIMIT is treated
/// as 0 so that the parser does not try to read billions of bytes.
pub fn sanitize_lua52(input: &[u8]) -> Vec<u8> {
    struct San<'a> {
        src: &'a [u8],
        pos: usize,
        out: Vec<u8>,
    }

    impl<'a> San<'a> {
        // 64 K — any count/size larger than this in a debug field is garbage.
        const BOGUS: u32 = 0x1_0000;

        fn r8(&mut self) -> u8 {
            if self.pos >= self.src.len() { return 0; }
            let v = self.src[self.pos];
            self.pos += 1;
            v
        }

        fn r32(&mut self) -> u32 {
            if self.pos + 4 > self.src.len() {
                self.pos = self.src.len();
                return 0;
            }
            let v = u32::from_le_bytes(self.src[self.pos..self.pos+4].try_into().unwrap());
            self.pos += 4;
            v
        }

        fn skip(&mut self, n: usize) {
            self.pos = (self.pos + n).min(self.src.len());
        }

        fn copy(&mut self, n: usize) {
            let end = (self.pos + n).min(self.src.len());
            self.out.extend_from_slice(&self.src[self.pos..end]);
            if end < self.pos + n {
                self.out.extend(std::iter::repeat(0).take(self.pos + n - end));
            }
            self.pos = end;
        }

        fn w32(&mut self, v: u32) {
            self.out.extend_from_slice(&v.to_le_bytes());
        }

        /// Write a Lua string literal (size_t-prefixed, null-terminated).
        fn wstr(&mut self, s: &str) {
            let len = (s.len() + 1) as u32; // +1 for null terminator
            self.w32(len);
            self.out.extend_from_slice(s.as_bytes());
            self.out.push(0); // null terminator
        }

        fn chunk(&mut self) {
            // Consume junk line_defined / last_line_defined; preserve structural metadata.
            self.r32(); self.r32();
            let num_params = self.r8();
            let is_vararg  = self.r8();
            let max_stack  = self.r8();
            // Write zeroed line fields, then the real structural bytes.
            self.out.extend_from_slice(&[0,0,0,0, 0,0,0,0]);
            self.out.push(num_params);
            self.out.push(is_vararg);
            self.out.push(max_stack);

            // instructions
            let ni = self.r32();
            let ni_ok = ni.min(Self::BOGUS - 1);
            self.w32(ni_ok);
            self.copy((ni_ok as usize) * 4);
            if ni >= Self::BOGUS { self.pos = self.src.len(); }

            // constants
            let nc = self.r32();
            let nc_ok = nc.min(Self::BOGUS - 1);
            self.w32(nc_ok);
            for _ in 0..nc_ok {
                let t = self.r8();
                self.out.push(t);
                match t {
                    0 => {}
                    1 => { let b = self.r8(); self.out.push(b); }
                    3 => self.copy(8),
                    4 => {
                        let sl = self.r32();
                        let sl_ok = sl.min(Self::BOGUS - 1);
                        self.w32(sl_ok);
                        self.copy(sl_ok as usize);
                        if sl >= Self::BOGUS { self.pos = self.src.len(); }
                    }
                    _ => { *self.out.last_mut().unwrap() = 0; break; }
                }
            }

            // sub-protos
            let np = self.r32();
            let np_ok = np.min(Self::BOGUS - 1);
            self.w32(np_ok);
            for _ in 0..np_ok {
                self.chunk();
            }

            // upvalue descriptors (structural — keep)
            let nu = self.r32();
            let nu_ok = nu.min(Self::BOGUS - 1);
            self.w32(nu_ok);
            self.copy((nu_ok as usize) * 2);

            // --- debug section: read & discard, write zero counts ---

            // source name (size_t-prefixed string)
            let sl = self.r32();
            if sl < Self::BOGUS { self.skip(sl as usize); } else { self.pos = self.src.len(); }
            self.w32(0);

            // source lines (one int per instruction)
            let nsl = self.r32();
            if nsl < Self::BOGUS { self.skip((nsl as usize) * 4); } else { self.pos = self.src.len(); }
            self.w32(0);

            // locals (string name + 2 ints each)
            let nloc = self.r32();
            self.w32(0);
            if nloc < Self::BOGUS {
                for _ in 0..nloc {
                    let nl = self.r32();
                    if nl < Self::BOGUS { self.skip(nl as usize + 8); } else { self.pos = self.src.len(); break; }
                }
            }

            // upvalue names: discard originals, emit synthetic "_upvN" names
            // so the decompiler can track upvalue references.
            let nun = self.r32();
            if nun < Self::BOGUS {
                for _ in 0..nun {
                    let sl2 = self.r32();
                    if sl2 < Self::BOGUS { self.skip(sl2 as usize); } else { self.pos = self.src.len(); break; }
                }
            }
            // Write nu_ok synthetic names (may differ from nun if nun was bogus).
            self.w32(nu_ok);
            for i in 0..nu_ok {
                let name = format!("_upv{i}");
                self.wstr(&name);
            }
        }
    }

    let mut s = San { src: input, pos: 0, out: Vec::with_capacity(input.len() / 4) };
    // copy header (18 bytes)
    s.copy(18);
    s.chunk();
    s.out
}


#[cfg(test)]
mod tests {
    use super::*;

    /// `luau-compile -O1 -g1` of:
    /// local t = {}
    /// for i = 1, 3 do t[i] = function() return i * 2 end end
    /// local s = 0
    /// for _, f in ipairs(t) do if f() > 2 then s += f() end end
    /// print(s, #t, game and 1 or 2)
    const LUAU: &[u8] = &[
        0x09, 0x03, 0x03, 0x06, 0x69, 0x70, 0x61, 0x69, 0x72, 0x73, 0x05, 0x70, 0x72, 0x69, 0x6e, 0x74,
        0x04, 0x67, 0x61, 0x6d, 0x65, 0x00, 0x02, 0x02, 0x00, 0x01, 0x00, 0x00, 0x00, 0x03, 0x09, 0x01,
        0x00, 0x00, 0x29, 0x00, 0x01, 0x00, 0x16, 0x00, 0x02, 0x00, 0x01, 0x02, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x40, 0x00, 0x02, 0x00, 0x01, 0x18, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00,
        0x00, 0x09, 0x00, 0x00, 0x01, 0x00, 0x00, 0x27, 0x41, 0x00, 0x00, 0x00, 0x35, 0x00, 0x00, 0x00,
        0x03, 0x00, 0x00, 0x00, 0x04, 0x03, 0x01, 0x00, 0x04, 0x01, 0x03, 0x00, 0x04, 0x02, 0x01, 0x00,
        0x38, 0x01, 0x04, 0x00, 0x13, 0x04, 0x00, 0x00, 0x46, 0x00, 0x03, 0x00, 0x0e, 0x04, 0x00, 0x03,
        0x39, 0x01, 0xfc, 0xff, 0x04, 0x01, 0x00, 0x00, 0x0c, 0x02, 0x01, 0x00, 0x00, 0x00, 0x00, 0x40,
        0x06, 0x03, 0x00, 0x00, 0x15, 0x02, 0x02, 0x04, 0x3b, 0x02, 0x08, 0x00, 0x06, 0x07, 0x06, 0x00,
        0x15, 0x07, 0x01, 0x02, 0x04, 0x08, 0x02, 0x00, 0x20, 0x08, 0x04, 0x00, 0x07, 0x00, 0x00, 0x00,
        0x06, 0x07, 0x06, 0x00, 0x15, 0x07, 0x01, 0x02, 0x21, 0x01, 0x01, 0x07, 0x3a, 0x02, 0xf7, 0xff,
        0x02, 0x00, 0x00, 0x80, 0x0c, 0x02, 0x03, 0x00, 0x00, 0x00, 0x20, 0x40, 0x06, 0x03, 0x01, 0x00,
        0x34, 0x04, 0x00, 0x00, 0x0c, 0x06, 0x05, 0x00, 0x00, 0x00, 0x40, 0x40, 0x1a, 0x06, 0x02, 0x00,
        0x04, 0x05, 0x01, 0x00, 0x17, 0x00, 0x01, 0x00, 0x04, 0x05, 0x02, 0x00, 0x15, 0x02, 0x04, 0x01,
        0x16, 0x00, 0x01, 0x00, 0x06, 0x03, 0x01, 0x04, 0x00, 0x00, 0x00, 0x40, 0x03, 0x02, 0x04, 0x00,
        0x00, 0x20, 0x40, 0x03, 0x03, 0x04, 0x00, 0x00, 0x40, 0x40, 0x01, 0x00, 0x01, 0x00, 0x01, 0x18,
        0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01,
    ];

    /// Store opcodes the way Roblox clients do (times 227).
    fn encode(p: &mut Proto) {
        let mut pc = 0;
        while pc < p.code.len() {
            let op = p.code[pc] & 0xFF;
            p.code[pc] = (p.code[pc] & !0xFF) | (op.wrapping_mul(227) & 0xFF);
            pc += disassembler::luau_op_length(op);
        }
        for c in p.p.iter_mut() { encode(c); }
    }

    fn codes(p: &Proto, out: &mut Vec<Vec<u32>>) {
        out.push(p.code.clone());
        for c in &p.p { codes(c, out); }
    }

    /// LuaJIT 2.1 (32-bit, so without FR2), `string.dump(f, true)` of:
    /// local t = { 1, 2, k = "v" }
    /// local o = { n = 0 }
    /// function o:add(x) self.n = self.n + x return self end
    /// for i = 1, 3 do
    ///   if i == 2 then goto skip end
    ///   o:add(i)
    ///   ::skip::
    /// end
    /// print(o.n, #t, t.k, 5LL)
    const LUAJIT: &[u8] = &[
        0x1b, 0x4c, 0x4a, 0x02, 0x06, 0x19, 0x00, 0x02, 0x03, 0x00, 0x01, 0x00, 0x04, 0x39, 0x02, 0x00,
        0x00, 0x20, 0x02, 0x01, 0x02, 0x3d, 0x02, 0x00, 0x00, 0x4c, 0x00, 0x02, 0x00, 0x06, 0x6e, 0x89,
        0x01, 0x07, 0x00, 0x09, 0x00, 0x08, 0x01, 0x17, 0x35, 0x00, 0x00, 0x00, 0x35, 0x01, 0x01, 0x00,
        0x33, 0x02, 0x03, 0x00, 0x3d, 0x02, 0x02, 0x01, 0x29, 0x02, 0x01, 0x00, 0x29, 0x03, 0x03, 0x00,
        0x29, 0x04, 0x01, 0x00, 0x4d, 0x02, 0x08, 0x80, 0x09, 0x05, 0x00, 0x00, 0x58, 0x06, 0x01, 0x80,
        0x58, 0x06, 0x04, 0x80, 0x12, 0x07, 0x01, 0x00, 0x39, 0x06, 0x02, 0x01, 0x12, 0x08, 0x05, 0x00,
        0x42, 0x06, 0x03, 0x01, 0x4f, 0x02, 0xf8, 0x7f, 0x36, 0x02, 0x04, 0x00, 0x39, 0x03, 0x05, 0x01,
        0x15, 0x04, 0x00, 0x00, 0x39, 0x05, 0x06, 0x00, 0x28, 0x06, 0x07, 0x00, 0x42, 0x02, 0x05, 0x01,
        0x4b, 0x00, 0x01, 0x00, 0x02, 0x05, 0x00, 0x06, 0x6b, 0x06, 0x6e, 0x0a, 0x70, 0x72, 0x69, 0x6e,
        0x74, 0x00, 0x08, 0x61, 0x64, 0x64, 0x01, 0x00, 0x01, 0x06, 0x6e, 0x03, 0x00, 0x01, 0x03, 0x01,
        0x00, 0x03, 0x01, 0x03, 0x02, 0x06, 0x6b, 0x06, 0x76, 0x04, 0x00,
    ];

    /// The same code in LuaJIT 2.0's opcode numbering (the dump format is
    /// otherwise identical).
    fn to_luajit20(p: &mut Proto) {
        use disassembler::luajit as lj;
        for w in p.code.iter_mut() {
            let op = *w & 0xFF;
            let old = match op {
                0..=15 => op,
                lj::MOV..=lj::TGETB => op - 2,
                lj::TSETV..=lj::TSETM => op - 3,
                lj::CALLM..=lj::JMP => op - 4,
                _ => panic!("{} is not in LuaJIT 2.0", lj::op_name(op)),
            };
            assert_eq!(lj::canon_op(1, old), op);
            *w = (*w & !0xFF) | old;
        }
        p.jit = 1;
        for c in p.p.iter_mut() { to_luajit20(c); }
    }

    #[test]
    fn luajit_bytecode() {
        let p = parse(LUAJIT).unwrap();
        assert_eq!((p.jit, p.jit_arg_offset()), (2, 1));
        let text = run(&p, Mode::Decompile, false);
        // Stripped, so locals get generated names.
        for want in [":add(", "5LL", "k = \"v\"", "print(", "for "] {
            assert!(text.contains(want), "{want} missing:\n{text}");
        }
        let mut p20 = p.clone();
        to_luajit20(&mut p20);
        assert_eq!(run(&p20, Mode::Decompile, false), text);
        assert!(run(&p, Mode::Disassemble, false).contains("FORI"));

        // Newer LuaJIT 2.1 bit operator instructions (same operands as
        // ADDVV): `self.n + x` becomes `self.n >>> x` (parameters are
        // unnamed in the stripped dump).
        use disassembler::luajit as lj;
        let mut pb = p.clone();
        let add = pb.p[0].code.iter_mut().find(|w| **w & 0xFF == lj::ADDVV).unwrap();
        *add = (*add & !0xFF) | lj::BSAR;
        let text = run(&pb, Mode::Decompile, false);
        assert!(text.contains("_p0.n = bit.arshift(_p0.n, _p1)"), "{text}");
    }

    #[test]
    fn roblox_encoded_luau_opcodes() {
        let plain = parse(LUAU).unwrap();
        assert!(plain.luau && !luau_opcodes_encoded(&plain));
        let mut enc = plain.clone();
        encode(&mut enc);
        assert!(luau_opcodes_encoded(&enc));
        decode_luau_opcodes(&mut enc);
        let (mut a, mut b) = (Vec::new(), Vec::new());
        codes(&plain, &mut a);
        codes(&enc, &mut b);
        assert_eq!(a, b);
        let text = run(&plain, Mode::Decompile, false);
        assert!(text.contains("ipairs") && text.contains("print"), "{text}");
    }
}
