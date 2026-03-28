/// Lua standard library stubs for the symbolic VM.
///
/// `build_globals()` returns a `LuaTable` that mirrors the `_G` seen by a
/// real Lua 5.3 runtime.  Functions that can be implemented concretely (math,
/// string, table) return real values; functions that touch the outside world
/// (io, os) or that require a full Lua VM (load, pcall) return `Unknown`.

use std::rc::Rc;

use crate::vm::{get_string_metatable, set_string_metatable, LuaTable, LuaValue, NativeFn};

// ---------------------------------------------------------------------------
// Convenience macros
// ---------------------------------------------------------------------------

/// Wrap a closure as a `LuaValue::Function`.
macro_rules! native {
    ($f:expr) => {
        LuaValue::Function(NativeFn(Rc::new($f)))
    };
}

/// Return a single Unknown value (used for functions we can't symbolically execute).
fn unknown(hint: &'static str) -> LuaValue {
    LuaValue::Unknown(hint.to_string())
}

fn ret_unknown(hint: &'static str) -> Vec<LuaValue> {
    vec![unknown(hint)]
}

// ---------------------------------------------------------------------------
// Helpers shared by multiple stdlib functions
// ---------------------------------------------------------------------------

fn lua_tostring(v: &LuaValue) -> String {
    match v {
        LuaValue::Nil => "nil".to_string(),
        LuaValue::Bool(b) => b.to_string(),
        LuaValue::Int(i) => i.to_string(),
        LuaValue::Float(f) => {
            // Lua 5.3 uses "%.14g" format
            let s = format!("{:.14}", f);
            // Trim trailing zeros but keep at least one decimal place
            if s.contains('.') {
                let trimmed = s.trim_end_matches('0');
                if trimmed.ends_with('.') {
                    format!("{}0", trimmed)
                } else {
                    trimmed.to_string()
                }
            } else {
                s
            }
        }
        LuaValue::Str(s) => String::from_utf8_lossy(s).into_owned(),
        LuaValue::Table(t) => format!("table: {:p}", Rc::as_ptr(&t.0)),
        // In GG's modified Lua runtime, native C functions do not expose memory
        // addresses via tostring — they report "nil". This is required for the
        // anti-tamper check that compares tostring(native_fn) with
        // tostring(debug.getmetatable(x)[nil]) to produce "nil" == "nil".
        LuaValue::Function(_) => "nil".to_string(),
        LuaValue::Closure(c) => format!("function: 0x{:x}", c.proto.linedefined),
        LuaValue::Unknown(h) => format!("?[{}]", h),
    }
}

// ---------------------------------------------------------------------------
// Basic / global functions
// ---------------------------------------------------------------------------

fn make_basic() -> Vec<(&'static str, LuaValue)> {
    vec![
        ("type", native!(|args| {
            let name = match args.first().unwrap_or(&LuaValue::Nil) {
                LuaValue::Nil        => "nil",
                LuaValue::Bool(_)    => "boolean",
                LuaValue::Int(_) | LuaValue::Float(_) => "number",
                LuaValue::Str(_)     => "string",
                LuaValue::Table(_)            => "table",
                LuaValue::Function(_) | LuaValue::Closure(_) => "function",
                LuaValue::Unknown(_) => return ret_unknown("type(?)"),
            };
            vec![LuaValue::Str(name.as_bytes().to_vec())]
        })),

        ("tostring", native!(|args| {
            let s = lua_tostring(args.first().unwrap_or(&LuaValue::Nil));
            vec![LuaValue::Str(s.into_bytes())]
        })),

        ("tonumber", native!(|args| {
            let base = args.get(1).and_then(|v| {
                if let LuaValue::Int(b) = v { Some(*b as u32) } else { None }
            });
            match args.first().unwrap_or(&LuaValue::Nil) {
                LuaValue::Int(i) => vec![LuaValue::Int(*i)],
                LuaValue::Float(f) => vec![LuaValue::Float(*f)],
                LuaValue::Str(s) => {
                    let text = String::from_utf8_lossy(s);
                    let text = text.trim();
                    if let Some(b) = base {
                        if let Ok(i) = i64::from_str_radix(text, b) {
                            return vec![LuaValue::Int(i)];
                        }
                        return vec![LuaValue::Nil];
                    }
                    if let Ok(i) = text.parse::<i64>() { return vec![LuaValue::Int(i)]; }
                    if let Ok(f) = text.parse::<f64>() { return vec![LuaValue::Float(f)]; }
                    if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
                        if let Ok(i) = i64::from_str_radix(hex, 16) { return vec![LuaValue::Int(i)]; }
                    }
                    vec![LuaValue::Nil]
                }
                _ => vec![LuaValue::Nil],
            }
        })),

        ("print", native!(|args| {
            let parts: Vec<String> = args.iter().map(lua_tostring).collect();
            println!("{}", parts.join("\t"));
            vec![]
        })),

        ("assert", native!(|args| {
            match args.first().unwrap_or(&LuaValue::Nil) {
                LuaValue::Nil | LuaValue::Bool(false) => {
                    let msg = args.get(1).map(lua_tostring)
                        .unwrap_or_else(|| "assertion failed!".to_string());
                    eprintln!("assert: {}", msg);
                    vec![unknown("assert-failed")]
                }
                LuaValue::Unknown(_) => ret_unknown("assert(?)"),
                _ => args.to_vec(),
            }
        })),

        ("error",     native!(|_args| ret_unknown("error()"))),
        ("pcall",     native!(|_args| ret_unknown("pcall()"))),
        ("xpcall",    native!(|_args| ret_unknown("xpcall()"))),

        ("select", native!(|args| {
            match args.first() {
                Some(LuaValue::Str(s)) if s == b"#" => {
                    vec![LuaValue::Int((args.len() - 1) as i64)]
                }
                Some(LuaValue::Int(n)) => {
                    let idx = *n as usize;
                    if idx < args.len() {
                        args[idx..].to_vec()
                    } else {
                        vec![]
                    }
                }
                _ => ret_unknown("select(?)"),
            }
        })),

        ("rawget", native!(|args| {
            match (args.first(), args.get(1)) {
                (Some(LuaValue::Table(t)), Some(k)) => vec![t.get(k)],
                _ => vec![LuaValue::Nil],
            }
        })),

        ("rawset", native!(|args| {
            if let (Some(LuaValue::Table(t)), Some(k), Some(v)) =
                (args.first(), args.get(1), args.get(2))
            {
                t.rawset(k.clone(), v.clone());
                vec![LuaValue::Table(t.clone())]
            } else {
                vec![LuaValue::Nil]
            }
        })),

        ("rawlen", native!(|args| {
            match args.first() {
                Some(LuaValue::Table(t)) => vec![LuaValue::Int(t.length())],
                Some(LuaValue::Str(s))   => vec![LuaValue::Int(s.len() as i64)],
                _ => vec![LuaValue::Int(0)],
            }
        })),

        ("rawequal", native!(|args| {
            let a = args.first().unwrap_or(&LuaValue::Nil);
            let b = args.get(1).unwrap_or(&LuaValue::Nil);
            vec![LuaValue::Bool(a == b)]
        })),

        ("pairs", native!(|args| {
            // Return (next, t, nil) — caller will use next() to iterate
            if let Some(t @ LuaValue::Table(_)) = args.first() {
                let next_fn = native!(|nargs| {
                    match (nargs.first(), nargs.get(1)) {
                        (Some(LuaValue::Table(t)), Some(key)) => {
                            match t.next_pair(key) {
                                Some((k, v)) => vec![k, v],
                                None => vec![LuaValue::Nil],
                            }
                        }
                        _ => vec![LuaValue::Nil],
                    }
                });
                vec![next_fn, t.clone(), LuaValue::Nil]
            } else {
                ret_unknown("pairs(?)")
            }
        })),

        ("ipairs", native!(|args| {
            if let Some(t @ LuaValue::Table(_)) = args.first() {
                let iter_fn = native!(|iargs| {
                    if let (Some(LuaValue::Table(t)), Some(LuaValue::Int(i))) =
                        (iargs.first(), iargs.get(1))
                    {
                        let next_i = i + 1;
                        let v = t.get(&LuaValue::Int(next_i));
                        if matches!(v, LuaValue::Nil) {
                            vec![LuaValue::Nil]
                        } else {
                            vec![LuaValue::Int(next_i), v]
                        }
                    } else {
                        vec![LuaValue::Nil]
                    }
                });
                vec![iter_fn, t.clone(), LuaValue::Int(0)]
            } else {
                ret_unknown("ipairs(?)")
            }
        })),

        ("next", native!(|args| {
            match (args.first(), args.get(1)) {
                (Some(LuaValue::Table(t)), key) => {
                    let k = key.unwrap_or(&LuaValue::Nil);
                    match t.next_pair(k) {
                        Some((k, v)) => vec![k, v],
                        None => vec![LuaValue::Nil],
                    }
                }
                _ => vec![LuaValue::Nil],
            }
        })),

        ("setmetatable", native!(|args| {
            match args.first() {
                Some(LuaValue::Table(t)) => {
                    match args.get(1) {
                        Some(LuaValue::Table(mt)) => {
                            // Respect __metatable protection
                            let existing_mm = t.get_metamethod("__metatable");
                            if !matches!(existing_mm, LuaValue::Nil) {
                                return ret_unknown("setmetatable: protected");
                            }
                            t.set_metatable(Some(mt.clone()));
                            vec![LuaValue::Table(t.clone())]
                        }
                        Some(LuaValue::Nil) => {
                            t.set_metatable(None);
                            vec![LuaValue::Table(t.clone())]
                        }
                        _ => ret_unknown("setmetatable(?,?)"),
                    }
                }
                _ => ret_unknown("setmetatable(?)"),
            }
        })),

        ("getmetatable", native!(|args| {
            match args.first() {
                Some(LuaValue::Table(t)) => {
                    match t.get_metatable() {
                        None => vec![LuaValue::Nil],
                        Some(mt) => {
                            // If __metatable is set, return that instead
                            let guard = mt.get_str("__metatable");
                            if !matches!(guard, LuaValue::Nil) {
                                vec![guard]
                            } else {
                                vec![LuaValue::Table(mt)]
                            }
                        }
                    }
                }
                Some(LuaValue::Str(_)) => {
                    // Strings share the string metatable
                    match get_string_metatable() {
                        Some(mt) => vec![LuaValue::Table(mt)],
                        None => vec![LuaValue::Nil],
                    }
                }
                _ => vec![LuaValue::Nil],
            }
        })),

        ("load",     native!(|_args| ret_unknown("load()"))),
        ("loadfile", native!(|_args| ret_unknown("loadfile()"))),
        ("dofile",   native!(|_args| ret_unknown("dofile()"))),
        ("require",  native!(|_args| ret_unknown("require()"))),

        ("unpack", native!(|args| {
            // table.unpack alias (Lua 5.1 compat)
            match args.first() {
                Some(LuaValue::Table(t)) => {
                    let i = args.get(1).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(1);
                    let j = args.get(2).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or_else(|| t.length());
                    (i..=j).map(|idx| t.get(&LuaValue::Int(idx))).collect()
                }
                _ => ret_unknown("unpack(?)"),
            }
        })),

        ("_VERSION", LuaValue::Str(b"Lua 5.3".to_vec())),
    ]
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// Lua 5.3 pattern matching engine
// ---------------------------------------------------------------------------

/// Match byte `c` against Lua character class `cls` (the byte after `%`).
fn lua_class_match(c: u8, cls: u8) -> bool {
    let base = cls.to_ascii_lowercase();
    let res = match base {
        b'a' => c.is_ascii_alphabetic(),
        b'c' => c.is_ascii_control(),
        b'd' => c.is_ascii_digit(),
        b'g' => c.is_ascii_graphic(),
        b'l' => c.is_ascii_lowercase(),
        b'p' => c.is_ascii_punctuation(),
        b's' => c.is_ascii_whitespace(),
        b'u' => c.is_ascii_uppercase(),
        b'w' => c.is_ascii_alphanumeric(),
        b'x' => c.is_ascii_hexdigit(),
        _ => return c == cls,  // %% → %, etc.
    };
    if cls != base { !res } else { res }  // uppercase = complement
}

/// Return the number of pattern bytes consumed by the item at `pat[pi]`
/// (not counting a following quantifier).
fn pat_item_size(pat: &[u8], pi: usize) -> usize {
    match pat.get(pi) {
        None => 0,
        Some(b'%') => 2,
        Some(b'[') => {
            let mut i = pi + 1;
            if pat.get(i) == Some(&b'^') { i += 1; }
            if pat.get(i) == Some(&b']') { i += 1; }   // ] at start is literal
            while i < pat.len() && pat[i] != b']' {
                if pat[i] == b'%' { i += 1; }
                i += 1;
            }
            i.saturating_sub(pi) + 1    // include closing ]
        }
        _ => 1,
    }
}

/// Return true if byte `c` matches the pattern item at `pat[pi..pi+item_size]`.
fn single_match(c: u8, pat: &[u8], pi: usize, item_size: usize) -> bool {
    match pat.get(pi) {
        Some(b'.') => true,
        Some(b'%') => pat.get(pi + 1).map_or(false, |&cls| lua_class_match(c, cls)),
        Some(b'[') => {
            let (negate, mut i) = if pat.get(pi + 1) == Some(&b'^') {
                (true, pi + 2)
            } else {
                (false, pi + 1)
            };
            let set_end = pi + item_size - 1;  // position of closing ]
            if pat.get(i) == Some(&b']') { i += 1; }  // ] at start is literal
            let mut matched = false;
            while i < set_end {
                if pat[i] == b'%' && i + 1 < set_end {
                    if lua_class_match(c, pat[i + 1]) { matched = true; }
                    i += 2;
                } else if i + 2 < set_end && pat[i + 1] == b'-' {
                    if c >= pat[i] && c <= pat[i + 2] { matched = true; }
                    i += 3;
                } else {
                    if c == pat[i] { matched = true; }
                    i += 1;
                }
            }
            matched != negate
        }
        Some(&b) => c == b,
        None => false,
    }
}

/// Core recursive pattern matcher.
/// `s`: subject; `pat`: pattern (anchored `^` already stripped);
/// `si`: position in s; `pi`: position in pat;
/// `caps`: list of (start, len) — len==usize::MAX means capture is still open.
/// Returns `Some(end_si)` on success.
fn lua_pat_match(s: &[u8], pat: &[u8], si: usize, pi: usize,
                 caps: &mut Vec<(usize, usize)>) -> Option<usize> {
    if pi >= pat.len() { return Some(si); }

    match pat[pi] {
        b'(' => {
            caps.push((si, usize::MAX));
            match lua_pat_match(s, pat, si, pi + 1, caps) {
                Some(e) => Some(e),
                None => { caps.pop(); None }
            }
        }
        b')' => {
            let ci = caps.iter().rposition(|&(_, e)| e == usize::MAX)?;
            caps[ci].1 = si - caps[ci].0;
            match lua_pat_match(s, pat, si, pi + 1, caps) {
                Some(e) => Some(e),
                None => { caps[ci].1 = usize::MAX; None }
            }
        }
        b'$' if pi + 1 == pat.len() => {
            if si == s.len() { Some(si) } else { None }
        }
        _ => {
            let isz = pat_item_size(pat, pi);
            let next = pi + isz;
            match pat.get(next) {
                Some(b'*') => {
                    // greedy 0+
                    let mut n = 0;
                    while si + n < s.len() && single_match(s[si + n], pat, pi, isz) { n += 1; }
                    loop {
                        if let r @ Some(_) = lua_pat_match(s, pat, si + n, next + 1, caps) { return r; }
                        if n == 0 { break; }
                        n -= 1;
                    }
                    None
                }
                Some(b'+') => {
                    // greedy 1+
                    let mut n = 0;
                    while si + n < s.len() && single_match(s[si + n], pat, pi, isz) { n += 1; }
                    while n >= 1 {
                        if let r @ Some(_) = lua_pat_match(s, pat, si + n, next + 1, caps) { return r; }
                        n -= 1;
                    }
                    None
                }
                Some(b'?') => {
                    if si < s.len() && single_match(s[si], pat, pi, isz) {
                        if let r @ Some(_) = lua_pat_match(s, pat, si + 1, next + 1, caps) { return r; }
                    }
                    lua_pat_match(s, pat, si, next + 1, caps)
                }
                Some(b'-') => {
                    // lazy 0+
                    let mut pos = si;
                    loop {
                        if let r @ Some(_) = lua_pat_match(s, pat, pos, next + 1, caps) { return r; }
                        if pos >= s.len() || !single_match(s[pos], pat, pi, isz) { return None; }
                        pos += 1;
                    }
                }
                _ => {
                    if si < s.len() && single_match(s[si], pat, pi, isz) {
                        lua_pat_match(s, pat, si + 1, next, caps)
                    } else {
                        None
                    }
                }
            }
        }
    }
}

/// Run `string.find` semantics: find first match of `raw_pat` in `s` starting
/// at `init` (1-indexed, may be negative). Returns `(start1, end1, captures)`.
fn lua_find(s: &[u8], raw_pat: &[u8], init: i64) -> Option<(usize, usize, Vec<Vec<u8>>)> {
    let anchored = raw_pat.first() == Some(&b'^');
    let pat = if anchored { &raw_pat[1..] } else { raw_pat };
    let has_caps = pat.contains(&b'(');
    let from = (if init < 0 { (s.len() as i64 + init).max(0) } else { (init - 1).max(0) }) as usize;
    let limit = if anchored { from + 1 } else { s.len() + 1 };
    for si in from..limit {
        let mut caps: Vec<(usize, usize)> = Vec::new();
        if let Some(end) = lua_pat_match(s, pat, si, 0, &mut caps) {
            let captures = if has_caps {
                caps.iter().map(|&(cs, len)| {
                    let ce = if len == usize::MAX { cs } else { cs + len };
                    s[cs..ce].to_vec()
                }).collect()
            } else {
                Vec::new()
            };
            return Some((si + 1, end, captures));
        }
    }
    None
}

/// Collect all non-overlapping gmatch matches of `raw_pat` in `s`.
/// Each entry is `Vec<Vec<u8>>`: the captures, or `[whole_match]` if no captures.
fn lua_gmatch_all(s: &[u8], raw_pat: &[u8]) -> Vec<Vec<Vec<u8>>> {
    let anchored = raw_pat.first() == Some(&b'^');
    let pat = if anchored { &raw_pat[1..] } else { raw_pat };
    let has_caps = pat.contains(&b'(');
    let mut results = Vec::new();
    let mut si = 0usize;
    loop {
        let mut caps: Vec<(usize, usize)> = Vec::new();
        if let Some(end) = lua_pat_match(s, pat, si, 0, &mut caps) {
            let m: Vec<Vec<u8>> = if has_caps {
                caps.iter().map(|&(cs, len)| {
                    let ce = if len == usize::MAX { cs } else { cs + len };
                    s[cs..ce].to_vec()
                }).collect()
            } else {
                vec![s[si..end].to_vec()]
            };
            results.push(m);
            si = if end == si { si + 1 } else { end };
        } else {
            si += 1;
        }
        if anchored || si > s.len() { break; }
    }
    results
}

// string.*
// ---------------------------------------------------------------------------

fn make_string_lib() -> LuaTable {
    let t = LuaTable::new();

    t.set_str("byte", native!(|args| {
        match args.first() {
            Some(LuaValue::Str(s)) => {
                let i = args.get(1).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(1);
                let j = args.get(2).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(i);
                let len = s.len() as i64;
                let from = (if i < 0 { (len + i).max(0) } else { (i - 1).max(0) }) as usize;
                let to   = (if j < 0 { (len + j + 1).max(0) } else { j.min(len) }) as usize;
                (from..to).map(|idx| LuaValue::Int(s[idx] as i64)).collect()
            }
            _ => ret_unknown("string.byte(?)"),
        }
    }));

    t.set_str("char", native!(|args| {
        let mut bytes = Vec::new();
        for a in args {
            if let LuaValue::Int(i) = a {
                bytes.push((*i & 0xFF) as u8);
            } else if let LuaValue::Float(f) = a {
                bytes.push((*f as i64 & 0xFF) as u8);
            } else {
                return ret_unknown("string.char(?)");
            }
        }
        vec![LuaValue::Str(bytes)]
    }));

    t.set_str("dump", native!(|_args| ret_unknown("string.dump()")));

    t.set_str("find", native!(|args| {
        match (args.first(), args.get(1)) {
            (Some(LuaValue::Str(s)), Some(LuaValue::Str(pat))) => {
                let plain = matches!(args.get(3), Some(LuaValue::Bool(true)));
                let init = match args.get(2) {
                    Some(LuaValue::Int(n)) => *n,
                    Some(LuaValue::Float(f)) => *f as i64,
                    _ => 1,
                };
                if plain {
                    let from = (if init < 0 { (s.len() as i64 + init).max(0) } else { (init - 1).max(0) }) as usize;
                    if let Some(pos) = s[from..].windows(pat.len()).position(|w| w == pat.as_slice()) {
                        let start = (from + pos + 1) as i64;
                        let end   = start + pat.len() as i64 - 1;
                        return vec![LuaValue::Int(start), LuaValue::Int(end)];
                    }
                    vec![LuaValue::Nil]
                } else {
                    match lua_find(s, pat, init) {
                        None => vec![LuaValue::Nil],
                        Some((start, end, caps)) => {
                            let mut r = vec![LuaValue::Int(start as i64), LuaValue::Int(end as i64)];
                            for c in caps { r.push(LuaValue::Str(c)); }
                            r
                        }
                    }
                }
            }
            _ => ret_unknown("string.find(?)"),
        }
    }));

    t.set_str("format", native!(|args| {
        // Minimal implementation — handles %d %i %u %f %s %q %%
        match args.first() {
            Some(LuaValue::Str(fmt)) => {
                let fmt_str = String::from_utf8_lossy(fmt).into_owned();
                let mut out = String::new();
                let mut chars = fmt_str.chars().peekable();
                let mut arg_idx = 1usize;
                while let Some(c) = chars.next() {
                    if c != '%' { out.push(c); continue; }
                    match chars.next() {
                        None => break,
                        Some('%') => { out.push('%'); }
                        Some(spec) => {
                            let arg = args.get(arg_idx).unwrap_or(&LuaValue::Nil);
                            arg_idx += 1;
                            match spec {
                                'd' | 'i' => match arg {
                                    LuaValue::Int(n) => out.push_str(&n.to_string()),
                                    LuaValue::Float(f) => out.push_str(&(*f as i64).to_string()),
                                    _ => { return ret_unknown("string.format(?)"); }
                                },
                                'u' => match arg {
                                    LuaValue::Int(n) => out.push_str(&(*n as u64).to_string()),
                                    _ => { return ret_unknown("string.format(?)"); }
                                },
                                'f' => match arg {
                                    LuaValue::Int(n) => out.push_str(&format!("{:.6}", *n as f64)),
                                    LuaValue::Float(f) => out.push_str(&format!("{:.6}", f)),
                                    _ => { return ret_unknown("string.format(?)"); }
                                },
                                's' => out.push_str(&lua_tostring(arg)),
                                'q' => {
                                    let s = lua_tostring(arg);
                                    out.push('"');
                                    for ch in s.chars() {
                                        match ch {
                                            '"' => out.push_str("\\\""),
                                            '\\' => out.push_str("\\\\"),
                                            '\n' => out.push_str("\\n"),
                                            _ => out.push(ch),
                                        }
                                    }
                                    out.push('"');
                                }
                                'x' => match arg {
                                    LuaValue::Int(n) => out.push_str(&format!("{:x}", n)),
                                    _ => { return ret_unknown("string.format(?)"); }
                                },
                                'X' => match arg {
                                    LuaValue::Int(n) => out.push_str(&format!("{:X}", n)),
                                    _ => { return ret_unknown("string.format(?)"); }
                                },
                                'o' => match arg {
                                    LuaValue::Int(n) => out.push_str(&format!("{:o}", n)),
                                    _ => { return ret_unknown("string.format(?)"); }
                                },
                                _ => { return ret_unknown("string.format(unsupported spec)"); }
                            }
                        }
                    }
                }
                vec![LuaValue::Str(out.into_bytes())]
            }
            _ => {
                ret_unknown("string.format(?)")
            }
        }
    }));

    t.set_str("gmatch", native!(|args| {
        let s = match args.first() {
            Some(LuaValue::Str(s)) => s.clone(),
            _ => return ret_unknown("string.gmatch()"),
        };
        let pat = match args.get(1) {
            Some(LuaValue::Str(p)) => p.clone(),
            _ => return ret_unknown("string.gmatch()"),
        };
        let matches = Rc::new(lua_gmatch_all(&s, &pat));
        let idx = Rc::new(std::cell::RefCell::new(0usize));
        let iter = NativeFn(Rc::new(move |_: &[LuaValue]| {
            let mut i = idx.borrow_mut();
            if *i >= matches.len() { return vec![LuaValue::Nil]; }
            let caps = matches[*i].iter().map(|c| LuaValue::Str(c.clone())).collect();
            *i += 1;
            caps
        }));
        vec![LuaValue::Function(iter)]
    }));
    t.set_str("gsub",   native!(|_args| ret_unknown("string.gsub()")));

    t.set_str("len", native!(|args| {
        match args.first() {
            Some(LuaValue::Str(s)) => vec![LuaValue::Int(s.len() as i64)],
            _ => ret_unknown("string.len(?)"),
        }
    }));

    t.set_str("lower", native!(|args| {
        match args.first() {
            Some(LuaValue::Str(s)) => vec![LuaValue::Str(s.to_ascii_lowercase())],
            _ => ret_unknown("string.lower(?)"),
        }
    }));

    t.set_str("match", native!(|args| {
        match (args.first(), args.get(1)) {
            (Some(LuaValue::Str(s)), Some(LuaValue::Str(pat))) => {
                let init = match args.get(2) {
                    Some(LuaValue::Int(n)) => *n,
                    Some(LuaValue::Float(f)) => *f as i64,
                    _ => 1,
                };
                match lua_find(s, pat, init) {
                    None => vec![LuaValue::Nil],
                    Some((start, end, caps)) => {
                        if caps.is_empty() {
                            vec![LuaValue::Str(s[(start-1)..end].to_vec())]
                        } else {
                            caps.into_iter().map(LuaValue::Str).collect()
                        }
                    }
                }
            }
            _ => ret_unknown("string.match(?)"),
        }
    }));

    t.set_str("pack",     native!(|_args| ret_unknown("string.pack()")));
    t.set_str("packsize", native!(|_args| ret_unknown("string.packsize()")));

    t.set_str("rep", native!(|args| {
        match (args.first(), args.get(1)) {
            (Some(LuaValue::Str(s)), Some(LuaValue::Int(n))) => {
                let sep = if let Some(LuaValue::Str(sep)) = args.get(2) { sep.clone() } else { vec![] };
                if *n <= 0 { return vec![LuaValue::Str(vec![])]; }
                let mut out = Vec::new();
                for i in 0..*n {
                    if i > 0 { out.extend_from_slice(&sep); }
                    out.extend_from_slice(s);
                }
                vec![LuaValue::Str(out)]
            }
            _ => ret_unknown("string.rep(?)"),
        }
    }));

    t.set_str("reverse", native!(|args| {
        match args.first() {
            Some(LuaValue::Str(s)) => {
                let mut r = s.clone();
                r.reverse();
                vec![LuaValue::Str(r)]
            }
            _ => ret_unknown("string.reverse(?)"),
        }
    }));

    t.set_str("sub", native!(|args| {
        match args.first() {
            Some(LuaValue::Str(s)) => {
                let len = s.len() as i64;
                let i = args.get(1).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(1);
                let j = args.get(2).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(-1);
                let from = (if i < 0 { (len + i).max(0) } else { (i - 1).max(0) }) as usize;
                let to   = (if j < 0 { (len + j + 1).max(0) } else { j.min(len) }) as usize;
                if from >= to { return vec![LuaValue::Str(vec![])]; }
                vec![LuaValue::Str(s[from..to].to_vec())]
            }
            _ => ret_unknown("string.sub(?)"),
        }
    }));

    t.set_str("unpack", native!(|_args| ret_unknown("string.unpack()")));

    t.set_str("upper", native!(|args| {
        match args.first() {
            Some(LuaValue::Str(s)) => vec![LuaValue::Str(s.to_ascii_uppercase())],
            _ => ret_unknown("string.upper(?)"),
        }
    }));

    t
}

// ---------------------------------------------------------------------------
// table.*
// ---------------------------------------------------------------------------

fn make_table_lib() -> LuaTable {
    let t = LuaTable::new();

    // Insertion order matches Lua 5.3 hash iteration order:
    // concat, insert, move, pack, remove, sort, unpack

    t.set_str("concat", native!(|args| {
        match args.first() {
            Some(LuaValue::Table(tbl)) => {
                let sep = args.get(1).and_then(|v| if let LuaValue::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
                let i = args.get(2).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(1);
                let j = args.get(3).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or_else(|| tbl.length());
                let mut parts = Vec::new();
                for idx in i..=j {
                    match tbl.get(&LuaValue::Int(idx)) {
                        LuaValue::Str(s) => parts.push(s),
                        LuaValue::Int(n) => parts.push(n.to_string().into_bytes()),
                        LuaValue::Float(f) => parts.push(f.to_string().into_bytes()),
                        _ => { return ret_unknown("table.concat(non-string)"); }
                    }
                }
                let result = parts.join(sep.as_slice());
                vec![LuaValue::Str(result)]
            }
            _ => ret_unknown("table.concat(?)"),
        }
    }));

    t.set_str("insert", native!(|args| {
        match args.first() {
            Some(LuaValue::Table(tbl)) => {
                match args.len() {
                    2 => {
                        let v = args[1].clone();
                        let pos = tbl.length() + 1;
                        tbl.rawset(LuaValue::Int(pos), v);
                    }
                    3 => {
                        if let LuaValue::Int(pos) = &args[1] {
                            let len = tbl.length();
                            let insert_at = *pos;
                            let mut i = len;
                            while i >= insert_at {
                                let v = tbl.get(&LuaValue::Int(i));
                                tbl.rawset(LuaValue::Int(i + 1), v);
                                i -= 1;
                            }
                            tbl.rawset(LuaValue::Int(insert_at), args[2].clone());
                        }
                    }
                    _ => {}
                }
                vec![]
            }
            _ => vec![],
        }
    }));

    t.set_str("move", native!(|args| {
        match (args.first(), args.get(1), args.get(2), args.get(3)) {
            (Some(LuaValue::Table(a1)), Some(LuaValue::Int(f)), Some(LuaValue::Int(e)), Some(LuaValue::Int(t_pos))) => {
                let a2 = if let Some(LuaValue::Table(tbl)) = args.get(4) { tbl.clone() } else { a1.clone() };
                let f = *f; let e = *e; let t_pos = *t_pos;
                if f <= e {
                    let vals: Vec<LuaValue> = (f..=e).map(|i| a1.get(&LuaValue::Int(i))).collect();
                    for (i, v) in vals.into_iter().enumerate() {
                        a2.rawset(LuaValue::Int(t_pos + i as i64), v);
                    }
                }
                vec![LuaValue::Table(a2)]
            }
            _ => ret_unknown("table.move(?)"),
        }
    }));

    t.set_str("pack", native!(|args| {
        let tbl = LuaTable::new();
        for (i, v) in args.iter().enumerate() {
            tbl.rawset(LuaValue::Int(i as i64 + 1), v.clone());
        }
        tbl.set_str("n", LuaValue::Int(args.len() as i64));
        vec![LuaValue::Table(tbl)]
    }));

    t.set_str("remove", native!(|args| {
        match args.first() {
            Some(LuaValue::Table(tbl)) => {
                let len = tbl.length();
                let pos = args.get(1)
                    .and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None })
                    .unwrap_or(len);
                let removed = tbl.get(&LuaValue::Int(pos));
                let mut i = pos;
                while i < len {
                    let v = tbl.get(&LuaValue::Int(i + 1));
                    tbl.rawset(LuaValue::Int(i), v);
                    i += 1;
                }
                tbl.rawset(LuaValue::Int(len), LuaValue::Nil);
                vec![removed]
            }
            _ => vec![LuaValue::Nil],
        }
    }));

    t.set_str("sort", native!(|_args| ret_unknown("table.sort()")));

    t.set_str("unpack", native!(|args| {
        match args.first() {
            Some(LuaValue::Table(tbl)) => {
                let i = args.get(1).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(1);
                let j = args.get(2).and_then(|v| if let LuaValue::Int(n) = v { Some(*n) } else { None }).unwrap_or_else(|| tbl.length());
                (i..=j).map(|idx| tbl.get(&LuaValue::Int(idx))).collect()
            }
            _ => ret_unknown("table.unpack(?)"),
        }
    }));

    t
}

// ---------------------------------------------------------------------------
// math.*
// ---------------------------------------------------------------------------

fn make_math_lib() -> LuaTable {
    let t = LuaTable::new();

    macro_rules! float1 {
        ($name:expr, $f:expr) => {
            t.set_str($name, native!(|args| {
                match args.first() {
                    Some(LuaValue::Float(x)) => vec![LuaValue::Float($f(*x))],
                    Some(LuaValue::Int(x))   => vec![LuaValue::Float($f(*x as f64))],
                    _ => ret_unknown(concat!("math.", $name, "(?)")),
                }
            }));
        };
    }

    float1!("sin",   f64::sin);
    float1!("cos",   f64::cos);
    float1!("tan",   f64::tan);
    float1!("asin",  f64::asin);
    float1!("acos",  f64::acos);
    float1!("exp",   f64::exp);
    float1!("sqrt",  f64::sqrt);

    t.set_str("atan", native!(|args| {
        match args.first() {
            Some(LuaValue::Float(y)) => {
                let x = match args.get(1) {
                    Some(LuaValue::Float(x)) => *x,
                    Some(LuaValue::Int(x))   => *x as f64,
                    _ => 1.0,
                };
                vec![LuaValue::Float(y.atan2(x))]
            }
            Some(LuaValue::Int(y)) => {
                let yf = *y as f64;
                let x = match args.get(1) {
                    Some(LuaValue::Float(x)) => *x,
                    Some(LuaValue::Int(x))   => *x as f64,
                    _ => 1.0,
                };
                vec![LuaValue::Float(yf.atan2(x))]
            }
            _ => ret_unknown("math.atan(?)"),
        }
    }));

    t.set_str("log", native!(|args| {
        match args.first() {
            Some(LuaValue::Float(x)) => {
                let base = match args.get(1) {
                    Some(LuaValue::Float(b)) => Some(*b),
                    Some(LuaValue::Int(b))   => Some(*b as f64),
                    _ => None,
                };
                let result = match base {
                    None | Some(f64::INFINITY) => x.ln(),
                    Some(b) if b == 10.0 => x.log10(),
                    Some(b) if b == 2.0  => x.log2(),
                    Some(b) => x.log(b),
                };
                vec![LuaValue::Float(result)]
            }
            Some(LuaValue::Int(x)) => {
                vec![LuaValue::Float((*x as f64).ln())]
            }
            _ => ret_unknown("math.log(?)"),
        }
    }));

    t.set_str("floor", native!(|args| {
        match args.first() {
            Some(LuaValue::Int(i))   => vec![LuaValue::Int(*i)],
            Some(LuaValue::Float(f)) => vec![LuaValue::Int(f.floor() as i64)],
            _ => ret_unknown("math.floor(?)"),
        }
    }));

    t.set_str("ceil", native!(|args| {
        match args.first() {
            Some(LuaValue::Int(i))   => vec![LuaValue::Int(*i)],
            Some(LuaValue::Float(f)) => vec![LuaValue::Int(f.ceil() as i64)],
            _ => ret_unknown("math.ceil(?)"),
        }
    }));

    t.set_str("abs", native!(|args| {
        match args.first() {
            Some(LuaValue::Int(i))   => vec![LuaValue::Int(i.wrapping_abs())],
            Some(LuaValue::Float(f)) => vec![LuaValue::Float(f.abs())],
            _ => ret_unknown("math.abs(?)"),
        }
    }));

    t.set_str("max", native!(|args| {
        if args.is_empty() { return ret_unknown("math.max()"); }
        let mut best = args[0].clone();
        for v in &args[1..] {
            let greater = match (&best, v) {
                (LuaValue::Int(a), LuaValue::Int(b))     => *b > *a,
                (LuaValue::Float(a), LuaValue::Float(b)) => *b > *a,
                (LuaValue::Int(a), LuaValue::Float(b))   => *b > *a as f64,
                (LuaValue::Float(a), LuaValue::Int(b))   => *b as f64 > *a,
                _ => { return ret_unknown("math.max(?)"); }
            };
            if greater { best = v.clone(); }
        }
        vec![best]
    }));

    t.set_str("min", native!(|args| {
        if args.is_empty() { return ret_unknown("math.min()"); }
        let mut best = args[0].clone();
        for v in &args[1..] {
            let less = match (&best, v) {
                (LuaValue::Int(a), LuaValue::Int(b))     => *b < *a,
                (LuaValue::Float(a), LuaValue::Float(b)) => *b < *a,
                (LuaValue::Int(a), LuaValue::Float(b))   => *b < *a as f64,
                (LuaValue::Float(a), LuaValue::Int(b))   => (*b as f64) < *a,
                _ => { return ret_unknown("math.min(?)"); }
            };
            if less { best = v.clone(); }
        }
        vec![best]
    }));

    t.set_str("fmod", native!(|args| {
        match (args.first(), args.get(1)) {
            (Some(LuaValue::Float(a)), Some(LuaValue::Float(b))) => vec![LuaValue::Float(a % b)],
            (Some(LuaValue::Int(a)),   Some(LuaValue::Int(b)))   => vec![LuaValue::Int(a % b)],
            _ => ret_unknown("math.fmod(?)"),
        }
    }));

    t.set_str("modf", native!(|args| {
        match args.first() {
            Some(LuaValue::Float(f)) => {
                let trunc = f.trunc();
                let frac  = f - trunc;
                vec![LuaValue::Float(trunc), LuaValue::Float(frac)]
            }
            Some(LuaValue::Int(i)) => vec![LuaValue::Float(*i as f64), LuaValue::Float(0.0)],
            _ => ret_unknown("math.modf(?)"),
        }
    }));

    t.set_str("tointeger", native!(|args| {
        match args.first() {
            Some(LuaValue::Int(i)) => vec![LuaValue::Int(*i)],
            Some(LuaValue::Float(f)) if f.fract() == 0.0 => vec![LuaValue::Int(*f as i64)],
            _ => vec![LuaValue::Nil],
        }
    }));

    t.set_str("type", native!(|args| {
        match args.first() {
            Some(LuaValue::Int(_))   => vec![LuaValue::Str(b"integer".to_vec())],
            Some(LuaValue::Float(_)) => vec![LuaValue::Str(b"float".to_vec())],
            _ => vec![LuaValue::Bool(false)],
        }
    }));

    t.set_str("random", native!(|_args| ret_unknown("math.random()")));
    t.set_str("randomseed", native!(|_args| vec![]));

    // Constants
    t.set_str("pi",         LuaValue::Float(std::f64::consts::PI));
    t.set_str("huge",       LuaValue::Float(f64::INFINITY));
    t.set_str("maxinteger", LuaValue::Int(i64::MAX));
    t.set_str("mininteger", LuaValue::Int(i64::MIN));

    t
}

// ---------------------------------------------------------------------------
// io.*
// ---------------------------------------------------------------------------

fn make_io_lib() -> LuaTable {
    let t = LuaTable::new();
    t.set_str("close",  native!(|_args| vec![]));
    t.set_str("flush",  native!(|_args| vec![]));
    t.set_str("input",  native!(|_args| ret_unknown("io.input()")));
    t.set_str("lines",  native!(|_args| ret_unknown("io.lines()")));
    t.set_str("open",   native!(|_args| ret_unknown("io.open()")));
    t.set_str("output", native!(|_args| ret_unknown("io.output()")));
    t.set_str("popen",  native!(|_args| ret_unknown("io.popen()")));
    t.set_str("read",   native!(|_args| ret_unknown("io.read()")));
    t.set_str("tmpfile", native!(|_args| ret_unknown("io.tmpfile()")));
    // Standard Lua 5.3: returns "file", "closed file", or "not a file".
    // Non-file args (e.g. integer 12) return "not a file".
    t.set_str("type",   native!(|args| {
        match args.first().unwrap_or(&LuaValue::Nil) {
            LuaValue::Table(_) => ret_unknown("io.type(table)"),
            _ => vec![LuaValue::Str(b"not a file".to_vec())],
        }
    }));
    t.set_str("write",  native!(|args| {
        for a in args { print!("{}", lua_tostring(a)); }
        vec![]
    }));
    t.set_str("stdin",  LuaValue::Unknown("io.stdin".to_string()));
    t.set_str("stdout", LuaValue::Unknown("io.stdout".to_string()));
    t.set_str("stderr", LuaValue::Unknown("io.stderr".to_string()));
    t
}

// ---------------------------------------------------------------------------
// os.*
// ---------------------------------------------------------------------------

fn make_os_lib() -> LuaTable {
    let t = LuaTable::new();
    t.set_str("clock",  native!(|_args| ret_unknown("os.clock()")));
    t.set_str("date",   native!(|_args| ret_unknown("os.date()")));
    t.set_str("difftime", native!(|args| {
        match (args.first(), args.get(1)) {
            (Some(LuaValue::Int(a)), Some(LuaValue::Int(b))) => vec![LuaValue::Int(a - b)],
            _ => ret_unknown("os.difftime(?)"),
        }
    }));
    t.set_str("execute",  native!(|_args| ret_unknown("os.execute()")));
    t.set_str("exit",   native!(|args| {
        let code = match args.first() {
            Some(LuaValue::Int(n)) => *n as i32,
            Some(LuaValue::Bool(false)) => 1,
            _ => 0,
        };
        eprintln!("[os.exit({})]", code);
        vec![]
    }));
    t.set_str("getenv",   native!(|_args| ret_unknown("os.getenv()")));
    t.set_str("remove",   native!(|_args| ret_unknown("os.remove()")));
    t.set_str("rename",   native!(|_args| ret_unknown("os.rename()")));
    t.set_str("setlocale", native!(|_args| ret_unknown("os.setlocale()")));
    t.set_str("time",   native!(|_args| ret_unknown("os.time()")));
    t.set_str("tmpname", native!(|_args| ret_unknown("os.tmpname()")));
    t
}

// ---------------------------------------------------------------------------
// debug.*
// ---------------------------------------------------------------------------

fn make_debug_lib() -> LuaTable {
    let t = LuaTable::new();

    // Insertion order matches GG's Lua 5.3 debug library iteration order:
    // debug, gethook, getinfo, getlocal, getmetatable, getregistry, getupvalue,
    // sethook, setlocal, setmetatable, setupvalue, traceback, upvalueid, upvaluejoin
    // The obfuscator extracts positions {5, 9, 14} → getmetatable, setlocal, upvaluejoin.

    t.set_str("debug",    native!(|_args| ret_unknown("debug.debug()")));
    t.set_str("gethook",  native!(|_args| ret_unknown("debug.gethook()")));
    t.set_str("getinfo",  native!(|_args| {
        let info = LuaTable::new();
        info.set_str("what",           LuaValue::Str(b"Lua".to_vec()));
        info.set_str("source",         LuaValue::Str(b"?".to_vec()));
        info.set_str("short_src",      LuaValue::Str(b"[C]".to_vec()));
        info.set_str("linedefined",    LuaValue::Int(-1));
        info.set_str("lastlinedefined",LuaValue::Int(-1));
        info.set_str("currentline",    LuaValue::Int(-1));
        info.set_str("nups",           LuaValue::Int(0));
        info.set_str("nparams",        LuaValue::Int(0));
        info.set_str("isvararg",       LuaValue::Bool(false));
        info.set_str("istailcall",     LuaValue::Bool(false));
        vec![LuaValue::Table(info)]
    }));
    t.set_str("getlocal", native!(|_args| ret_unknown("debug.getlocal()")));

    // debug.getmetatable — position 5; bypasses __metatable protection
    t.set_str("getmetatable", native!(|args| {
        match args.first() {
            Some(LuaValue::Table(tbl)) => {
                match tbl.get_metatable() {
                    Some(mt) => vec![LuaValue::Table(mt)],
                    None => vec![LuaValue::Nil],
                }
            }
            Some(LuaValue::Str(_)) => {
                match get_string_metatable() {
                    Some(mt) => vec![LuaValue::Table(mt)],
                    None => vec![LuaValue::Nil],
                }
            }
            _ => vec![LuaValue::Nil],
        }
    }));

    t.set_str("getregistry", native!(|_args| ret_unknown("debug.getregistry()")));
    t.set_str("getupvalue",  native!(|_args| ret_unknown("debug.getupvalue()")));
    t.set_str("sethook",     native!(|_args| vec![]));

    // debug.setlocal — position 9; returns the name of the local variable set
    t.set_str("setlocal",    native!(|_args| vec![LuaValue::Str(b"local".to_vec())]));

    // debug.setmetatable — bypasses __metatable protection
    t.set_str("setmetatable", native!(|args| {
        match args.first() {
            Some(LuaValue::Table(tbl)) => {
                match args.get(1) {
                    Some(LuaValue::Table(mt)) => {
                        tbl.set_metatable(Some(mt.clone()));
                        vec![LuaValue::Table(tbl.clone())]
                    }
                    Some(LuaValue::Nil) => {
                        tbl.set_metatable(None);
                        vec![LuaValue::Table(tbl.clone())]
                    }
                    _ => ret_unknown("debug.setmetatable(?,?)"),
                }
            }
            _ => ret_unknown("debug.setmetatable(?)"),
        }
    }));

    t.set_str("setupvalue", native!(|_args| vec![]));
    t.set_str("traceback",  native!(|_args| ret_unknown("debug.traceback()")));
    t.set_str("upvalueid",  native!(|_args| ret_unknown("debug.upvalueid()")));

    // debug.upvaluejoin — position 14
    t.set_str("upvaluejoin", native!(|_args| vec![]));

    t
}

// ---------------------------------------------------------------------------
// gg.* — GameGuardian API mock
// ---------------------------------------------------------------------------

fn make_gg_lib() -> LuaTable {
    let t = LuaTable::new();

    // Macros — entries must be inserted in the exact hash-iteration order that
    // GameGuardian's LuaJ runtime produces, so `next()` returns them in the
    // same sequence as the real app.
    macro_rules! icon {
        ($name:expr, $val:expr) => { t.set_str($name, LuaValue::Int($val)); };
    }
    macro_rules! scon {
        ($name:expr, $val:expr) => { t.set_str($name, LuaValue::Str($val.to_vec())); };
    }
    macro_rules! noop {
        ($name:expr) => { t.set_str($name, native!(|_args| vec![])); };
    }
    macro_rules! unk {
        ($name:expr) => { t.set_str($name, native!(|_args| ret_unknown(stringify!($name)))); };
    }
    macro_rules! nil_ret {
        ($name:expr) => { t.set_str($name, native!(|_args| vec![LuaValue::Nil])); };
    }

    // ── Exact hash-iteration order (142 entries) ────────────────────────────
    //  1
    unk!("getResultsCount");
    //  2
    icon!("SIGN_INEQUAL",  268435456);
    //  3
    unk!("multiChoice");
    //  4
    noop!("setSpeed");
    //  5
    unk!("getSpeed");
    //  6
    icon!("REGION_C_HEAP", 1);
    //  7
    unk!("bytes");
    //  8  ← getFile: returns the running script's filename
    t.set_str("getFile", native!(|_args| {
        vec![LuaValue::Str(
            b"/storage/emulated/0/gg_scripts/[SELGG]#Encrypt Tool ThanhDieuLua [ Byte V3 ].lua"
                .to_vec(),
        )]
    }));
    //  9
    unk!("require");
    // 10
    icon!("SIGN_LESS_OR_EQUAL", 134217728);
    // 11
    icon!("TYPE_QWORD", 32);
    // 12
    unk!("getValues");
    // 13
    noop!("setValues");
    // 14
    noop!("editAll");
    // 15
    icon!("SIGN_NOT_EQUAL", 268435456);
    // 16
    unk!("getListItems");
    // 17
    noop!("loadResults");
    // 18
    icon!("TYPE_XOR", 8);
    // 19
    unk!("getSelectedResults");
    // 20
    unk!("getTargetPackage");
    // 21
    unk!("internal3");
    // 22
    icon!("PROT_NONE", 0);
    // 23
    noop!("startFuzzy");
    // 24
    noop!("processKill");
    // 25  alert returns nil so comparisons yield a concrete falsy value
    nil_ret!("alert");
    // 26
    icon!("REGION_STACK", 64);
    // 27
    scon!("CACHE_DIR", b"/data/data/com.cba.gg/cache");
    // 28
    noop!("setRanges");
    // 29
    unk!("getRanges");
    // 30
    icon!("REGION_CODE_SYS", 32768);
    // 31
    unk!("getLine");
    // 32
    noop!("unrandomizer");
    // 33
    unk!("getActiveTab");
    // 34
    noop!("searchPointer");
    // 35
    icon!("ASM_THUMB", 5);
    // 36
    icon!("PROT_WRITE", 1);
    // 37
    noop!("skipRestoreState");
    // 38
    icon!("TYPE_BYTE", 1);
    // 39
    icon!("REGION_C_DATA", 8);
    // 40
    icon!("SIGN_GREATER_OR_EQUAL", 67108864);
    // 41
    scon!("FILES_DIR", b"/data/data/com.cba.gg/files");
    // 42
    icon!("FREEZE_IN_RANGE", 3);
    // 43
    unk!("allocatePage");
    // 44
    unk!("getValuesRange");
    // 45
    icon!("PROT_READ", 2);
    // 46
    icon!("REGION_OTHER", -2080896);
    // 47
    icon!("REGION_VIDEO", 1048576);
    // 48
    icon!("LOAD_VALUES", 2);
    // 49
    unk!("internal1");
    // 50
    scon!("EXT_FILES_DIR", b"/sdcard/Android/data/com.cba.gg/files");
    // 51
    icon!("REGION_BAD", 131072);
    // 52
    icon!("ANDROID_SDK_INT", 30);
    // 53
    noop!("removeListItems");
    // 54
    unk!("getTargetInfo");
    // 55
    noop!("toast");
    // 56
    noop!("processResume");
    // 57
    unk!("makeRequest");
    // 58
    icon!("LOAD_VALUES_FREEZE", 3);
    // 59
    unk!("getLocale");
    // 60
    unk!("getSelectedListItems");
    // 61
    noop!("timeJump");
    // 62
    noop!("processToggle");
    // 63
    unk!("disasm");
    // 64  deprecated alias
    unk!("getResultCount");
    // 65
    icon!("FREEZE_MAY_DECREASE", 2);
    // 66
    icon!("SIGN_FUZZY_EQUAL", 536870912);
    // 67
    noop!("processPause");
    // 68
    icon!("FREEZE_MAY_INCREASE", 1);
    // 69
    unk!("isProcessPaused");
    // 70
    unk!("getRangesList");
    // 71
    unk!("getResults");
    // 72
    icon!("TAB_SEARCH", 1);
    // 73
    noop!("copyText");
    // 74
    icon!("REGION_CODE_APP", 16384);
    // 75
    icon!("POINTER_NO", 4);
    // 76
    icon!("TAB_SAVED_LIST", 2);
    // 77
    noop!("searchFuzzy");
    // 78  BUILD = (int)((16396.7 - 254.7) + 0.5) = 16142
    icon!("BUILD", 16142);
    // 79
    unk!("internal2");
    // 80
    icon!("REGION_ASHMEM", 524288);
    // 81
    icon!("TYPE_AUTO", 127);
    // 82
    icon!("REGION_ANONYMOUS", 32);
    // 83
    noop!("clearResults");
    // 84
    icon!("SAVE_AS_TEXT", 1);
    // 85
    noop!("removeResults");
    // 86
    noop!("refineAddress");
    // 87
    noop!("refineNumber");
    // 88
    icon!("SIGN_LARGER", 67108864);
    // 89
    icon!("TYPE_FLOAT", 16);
    // 90
    unk!("choice");
    // 91
    icon!("ASM_ARM", 4);
    // 92
    icon!("SIGN_FUZZY_GREATER", 67108864);
    // 93
    icon!("SIGN_EQUAL", 536870912);
    // 94
    icon!("FREEZE_NORMAL", 0);
    // 95
    icon!("LOAD_APPEND", 8);
    // 96
    icon!("TYPE_WORD", 2);
    // 97
    unk!("numberFromLocale");
    // 98
    icon!("POINTER_READ_ONLY", 8);
    // 99
    icon!("POINTER_WRITABLE", 16);
    // 100
    icon!("REGION_JAVA_HEAP", 2);
    // 101
    unk!("getSelectedElements");
    // 102
    noop!("showUiButton");
    // 103
    unk!("isVisible");
    // 104
    noop!("gotoAddress");
    // 105
    icon!("SIGN_FUZZY_LESS", 134217728);
    // 106  deprecated alias for getTargetPackage
    unk!("getSelectedPackage");
    // 107
    icon!("TAB_MEMORY_EDITOR", 3);
    // 108
    icon!("REGION_C_BSS", 16);
    // 109
    noop!("saveList");
    // 110
    noop!("addListItems");
    // 111
    icon!("POINTER_EXECUTABLE", 2);
    // 112
    unk!("prompt");
    // 113
    icon!("DUMP_SKIP_SYSTEM_LIBS", 1);
    // 114
    noop!("setVisible");
    // 115
    icon!("REGION_PPSSPP", 262144);
    // 116
    icon!("REGION_JAVA", 65536);
    // 117
    noop!("searchNumber");
    // 118
    icon!("POINTER_EXECUTABLE_WRITABLE", 1);
    // 119
    icon!("TYPE_DOUBLE", 64);
    // 120
    icon!("PROT_EXEC", 4);
    // 121
    noop!("saveVariable");
    // 122
    icon!("TAB_SETTINGS", 0);
    // 123
    unk!("isPackageInstalled");
    // 124
    unk!("numberToLocale");
    // 125
    noop!("clearList");
    // 126
    noop!("copyMemory");
    // 127
    scon!("EXT_STORAGE", b"/sdcard");
    // 128
    icon!("SIGN_SMALLER", 134217728);
    // 129
    icon!("REGION_C_ALLOC", 4);
    // 130
    noop!("hideUiButton");
    // 131
    icon!("VERSION_INT", 101100);
    // 132
    icon!("ASM_ARM64", 6);
    // 133
    noop!("sleep");
    // 134
    noop!("loadList");
    // 135
    icon!("SIGN_FUZZY_NOT_EQUAL", 268435456);
    // 136
    icon!("TYPE_DWORD", 4);
    // 137  VERSION = 108.0 * 1 - 6.9 ≈ "101.1"
    scon!("VERSION", b"101.1");
    // 138
    unk!("isClickedUiButton");
    // 139
    noop!("dumpMemory");
    // 140
    scon!("PACKAGE", b"com.cba.gg");
    // 141
    scon!("EXT_CACHE_DIR", b"/sdcard/Android/data/com.cba.gg/cache");
    // 142
    noop!("searchAddress");

    t
}

// ---------------------------------------------------------------------------
// build_globals — the main entry point
// ---------------------------------------------------------------------------

pub fn build_globals() -> LuaTable {
    let g = LuaTable::new();

    // Basic functions
    for (name, val) in make_basic() {
        g.set_str(name, val);
    }

    // Sub-libraries
    let string_lib = make_string_lib();
    let table_lib  = make_table_lib();
    let math_lib   = make_math_lib();
    let io_lib     = make_io_lib();
    let os_lib     = make_os_lib();
    let debug_lib  = make_debug_lib();
    let gg_lib     = make_gg_lib();

    g.set_str("string", LuaValue::Table(string_lib.clone()));
    g.set_str("table",  LuaValue::Table(table_lib));
    g.set_str("math",   LuaValue::Table(math_lib));
    g.set_str("io",     LuaValue::Table(io_lib));
    g.set_str("os",     LuaValue::Table(os_lib));
    g.set_str("debug",  LuaValue::Table(debug_lib));
    g.set_str("gg",     LuaValue::Table(gg_lib));

    // Install the shared string metatable: { __index = string }
    // This makes ("hello"):upper() etc. work via __index lookup.
    let str_mt = LuaTable::new();
    str_mt.set_str("__index", LuaValue::Table(string_lib));
    set_string_metatable(str_mt);

    // _G self-reference
    g.set_str("_G", LuaValue::Table(g.clone()));

    g
}
