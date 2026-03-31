/// Pass – Stream-XOR string decryption.
///
/// Detects the stream-cipher pattern emitted after upvalue resolution:
///
/// ```lua
/// local <key_var> = "..."                     ← long key string
/// local <pos_var> = <expr>                    ← initial position (= 1)
/// local <fn> = function(<p0>)
///     local <t> = {}
///     local <bytes> = {string.byte(<p0>, 1, #<p0>)}
///     for <k> in pairs(<bytes>) do
///         <t>[<k>] = <val> ~ <acc>[<char>] ~ string.byte(<key_var>, <pos_var>)
///     end
///     <pos_var> = <pos_var> + <expr>          ← advance key position by 1
///     return <t>
/// end
/// ```
///
/// The identifying signature is the single line containing both:
///   `~ <ident>["<char>"] ~` (XOR with a one-byte table lookup)
///   `string.byte(<K>, <P>)`  (key-byte read)
///
/// Decryption formula (per call, NOT per character):
///   key_byte  = key_string[call_index]         (1-indexed; advances once per call)
///   xor_const = byte value of <char> in the table expression
///   plain[i]  = cipher[i] ^ xor_const ^ key_byte
///
/// All `<fn>("<ciphertext>")` call-sites are replaced with the plain-text
/// string literal in source order (so the running key position stays correct).
/// The now-dead key and position definition lines are also removed.

use regex::Regex;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn run(src: &str) -> String {
    let instances = detect_cipher_instances(src);
    if instances.is_empty() {
        return src.to_string();
    }

    // Collect all (start, end, replacement) edits.
    let mut replacements: Vec<(usize, usize, String)> = Vec::new();
    for inst in &instances {
        collect_replacements(src, inst, &mut replacements);
    }

    if replacements.is_empty() {
        return src.to_string();
    }

    // Apply right-to-left so earlier byte offsets remain valid.
    replacements.sort_by(|a, b| b.0.cmp(&a.0));
    let mut result = src.to_string();
    for (start, end, rep) in replacements {
        if start <= end && end <= result.len() {
            result.replace_range(start..end, &rep);
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Detection
// ---------------------------------------------------------------------------

struct CipherInstance {
    /// Name of the cipher function (e.g. `_f3`).
    fn_name: String,
    /// Raw key bytes.
    key: Vec<u8>,
    /// The constant XOR'd with every byte (derived from `_acc["\t"]` etc.).
    xor_const: u8,
    /// Byte offset in `src` of the cipher function's `local` declaration line.
    fn_def_start: usize,
    /// Byte offset just past the end of the search window (next same-name decl,
    /// or end-of-source).  Only calls within [fn_def_start, search_end) count.
    search_end: usize,
    /// Ranges to delete: the key-string line and the position-variable line.
    remove_ranges: Vec<(usize, usize)>,
}

/// Build a `Vec<(byte_offset, line_text)>` for the whole source.
fn lines_with_offsets(src: &str) -> Vec<(usize, &str)> {
    let mut v = Vec::new();
    let mut off = 0usize;
    for line in src.split('\n') {
        v.push((off, line.trim_end_matches('\r')));
        off += line.len() + 1; // +1 for the '\n'
    }
    v
}

fn leading_spaces(s: &str) -> usize {
    s.len() - s.trim_start().len()
}

/// Given the subscript expression of a one-character table lookup like
/// `_acc4["\t"]`, return the byte value of the character.
fn extract_xor_const(acc_expr: &str) -> Option<u8> {
    // acc_expr looks like: _acc4["\t"]  or  _acc4["\x09"]
    let bracket = acc_expr.find('[')?;
    let subscript = acc_expr[bracket + 1..].strip_suffix(']')?.trim();
    let bytes = parse_lua_string_literal(subscript)?;
    if bytes.len() == 1 { Some(bytes[0]) } else { None }
}

fn detect_cipher_instances(src: &str) -> Vec<CipherInstance> {
    let mut result = Vec::new();
    let lines = lines_with_offsets(src);

    // The identifying line contains:
    //   ~ <ident>["<escape_seq>"] ~ string.byte(<K>, <P>)
    // We capture: (1) the acc-table expression, (2) key_var, (3) pos_var.
    let re_xor = Regex::new(
        r#"~\s*(\w+\["(?:[^"\\]|\\.)*"\])\s*~\s*string\.byte\(\s*(\w+)\s*,\s*(\w+)\s*\)"#,
    )
    .unwrap();

    // Regex to extract the function name from `local <name> = function(`.
    let re_fn_decl = Regex::new(r"local\s+(\w+)\s*=\s*function\s*\(").unwrap();

    for (li, &(_line_off, line)) in lines.iter().enumerate() {
        let caps = match re_xor.captures(line) {
            Some(c) => c,
            None => continue,
        };

        let xor_expr = caps[1].to_string();
        let key_var  = caps[2].to_string();
        let pos_var  = caps[3].to_string();

        let xor_const = match extract_xor_const(&xor_expr) {
            Some(v) => v,
            None => continue,
        };

        // Verify: the same function body increments the position variable.
        //   <pos_var> = <pos_var> + ...
        let inc_needle = format!("{} = {} +", pos_var, pos_var);
        let has_inc = lines[li..]
            .iter()
            .take(20)
            .any(|(_, l)| l.contains(&inc_needle));
        if !has_inc {
            continue;
        }

        // The XOR line is inside a for-loop which is inside the cipher function.
        // Scan backward for the enclosing `local <fn> = function(` by looking for
        // a line with STRICTLY LESS indentation than our XOR line.
        let xor_indent = leading_spaces(line);

        // Patterns for key and pos definitions.
        let key_needle = format!("local {} = \"", key_var);
        let pos_needle = format!("local {} =", pos_var);
        // Regex to capture the string literal value from the key definition.
        let re_key_val = Regex::new(&format!(
            r#"local\s+{}\s*=\s*("(?:[^"\\]|\\.)*")"#,
            regex::escape(&key_var),
        ))
        .unwrap();

        let mut fn_name:       Option<String>        = None;
        let mut fn_def_start:  Option<usize>          = None;
        let mut key_bytes:     Option<Vec<u8>>        = None;
        let mut key_line_range: Option<(usize, usize)> = None;
        let mut pos_line_range: Option<(usize, usize)> = None;

        // Scan backward up to 200 lines.
        for &(boff, bline) in lines[..li].iter().rev().take(200) {
            // Function definition: must have lower indentation than the XOR line.
            if fn_name.is_none()
                && leading_spaces(bline) < xor_indent
                && bline.contains("= function(")
            {
                if let Some(fc) = re_fn_decl.captures(bline) {
                    fn_name      = Some(fc[1].to_string());
                    fn_def_start = Some(boff);
                }
            }

            // Key string definition.
            if key_bytes.is_none() && bline.contains(&key_needle) {
                if let Some(kc) = re_key_val.captures(bline) {
                    if let Some(bytes) = parse_lua_string_literal(&kc[1]) {
                        let lend = (boff + bline.len() + 1).min(src.len());
                        key_bytes      = Some(bytes);
                        key_line_range = Some((boff, lend));
                    }
                }
            }

            // Position variable definition (but not itself a function assignment).
            if pos_line_range.is_none()
                && bline.contains(&pos_needle)
                && !bline.contains("= function(")
            {
                let lend = (boff + bline.len() + 1).min(src.len());
                pos_line_range = Some((boff, lend));
            }

            // Stop once all three pieces are found.
            if fn_name.is_some() && key_bytes.is_some() && pos_line_range.is_some() {
                break;
            }
        }

        let (fn_n, key, fn_start) = match (fn_name, key_bytes, fn_def_start) {
            (Some(a), Some(b), Some(c)) => (a, b, c),
            _ => continue,
        };

        if key.is_empty() {
            continue;
        }

        // The search window for calls ends just before the next occurrence of a
        // declaration of the same function name (in a different closure scope),
        // or at end-of-source.
        // Skip past the entire current definition line before searching.
        let fn_redecl = format!("local {} = function(", fn_n);
        let after_fn_line = src[fn_start..]
            .find('\n')
            .map(|p| fn_start + p + 1)
            .unwrap_or(src.len());
        let search_end = src[after_fn_line..]
            .find(&fn_redecl)
            .map(|p| after_fn_line + p)
            .unwrap_or(src.len());

        let mut remove_ranges = Vec::new();
        if let Some(r) = key_line_range  { remove_ranges.push(r); }
        if let Some(r) = pos_line_range  { remove_ranges.push(r); }

        result.push(CipherInstance {
            fn_name: fn_n,
            key,
            xor_const,
            fn_def_start: fn_start,
            search_end,
            remove_ranges,
        });
    }

    result
}

// ---------------------------------------------------------------------------
// Decryption + replacement collection
// ---------------------------------------------------------------------------

fn collect_replacements(
    src: &str,
    inst: &CipherInstance,
    replacements: &mut Vec<(usize, usize, String)>,
) {
    let window = &src[inst.fn_def_start..inst.search_end];

    // Match every call-site: <fn_name>("<lua_string_literal>")
    // The string literal may contain any Lua escape sequences.
    let call_re = Regex::new(&format!(
        r#"{}\s*\(\s*("(?:[^"\\]|\\.)*")\s*\)"#,
        regex::escape(&inst.fn_name),
    ))
    .unwrap();

    // Collect all call sites in forward (source) order so that the running
    // key position advances correctly.
    let call_sites: Vec<(usize, usize, &str)> = call_re
        .captures_iter(window)
        .map(|caps| {
            let full  = caps.get(0).unwrap();
            let arg   = caps.get(1).unwrap().as_str();
            let abs_s = inst.fn_def_start + full.start();
            let abs_e = inst.fn_def_start + full.end();
            (abs_s, abs_e, arg)
        })
        .collect();

    if call_sites.is_empty() {
        return;
    }

    let key_len = inst.key.len();

    for (call_idx, (start, end, arg)) in call_sites.into_iter().enumerate() {
        let ciphertext = match parse_lua_string_literal(arg) {
            Some(b) => b,
            None => continue,
        };

        // key position is 1-indexed in Lua; call 0 uses key[0] in Rust.
        // Wrap with modulo as a safety net (should never trigger in practice).
        let key_byte = inst.key[call_idx % key_len];

        let plain: Vec<u8> = ciphertext
            .iter()
            .map(|&b| b ^ inst.xor_const ^ key_byte)
            .collect();

        replacements.push((start, end, lua_string_literal(&plain)));
    }

    // Queue removal of the key-string and position-variable definition lines.
    for &(s, e) in &inst.remove_ranges {
        replacements.push((s, e, String::new()));
    }
}

// ---------------------------------------------------------------------------
// Lua string literal parser
// ---------------------------------------------------------------------------

/// Parse a Lua double-quoted string literal (the outer quotes included) into
/// raw bytes.  Handles: `\\`, `\"`, `\n`, `\r`, `\t`, `\xHH`, `\DDD`.
fn parse_lua_string_literal(quoted: &str) -> Option<Vec<u8>> {
    let inner = quoted
        .strip_prefix('"')?
        .strip_suffix('"')?;

    let mut result = Vec::with_capacity(inner.len());
    let bytes = inner.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if bytes[i] != b'\\' {
            result.push(bytes[i]);
            i += 1;
            continue;
        }
        // Escape sequence
        i += 1;
        if i >= bytes.len() {
            return None;
        }
        match bytes[i] {
            b'\\' => { result.push(b'\\'); i += 1; }
            b'"'  => { result.push(b'"');  i += 1; }
            b'\'' => { result.push(b'\''); i += 1; }
            b'n'  => { result.push(b'\n'); i += 1; }
            b'r'  => { result.push(b'\r'); i += 1; }
            b't'  => { result.push(b'\t'); i += 1; }
            b'a'  => { result.push(0x07);  i += 1; }
            b'b'  => { result.push(0x08);  i += 1; }
            b'f'  => { result.push(0x0C);  i += 1; }
            b'v'  => { result.push(0x0B);  i += 1; }
            b'0'..=b'9' => {
                // Decimal escape: up to 3 digits.
                let start = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() && i - start < 3 {
                    i += 1;
                }
                let num: u16 = std::str::from_utf8(&bytes[start..i])
                    .ok()?
                    .parse()
                    .ok()?;
                if num > 255 {
                    return None;
                }
                result.push(num as u8);
            }
            b'x' => {
                // Hex escape: exactly 2 hex digits.
                i += 1;
                if i + 2 > bytes.len() {
                    return None;
                }
                let hi = from_hex(bytes[i])?;
                let lo = from_hex(bytes[i + 1])?;
                result.push((hi << 4) | lo);
                i += 2;
            }
            _ => return None,
        }
    }

    Some(result)
}

#[inline]
fn from_hex(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Lua string literal renderer
// ---------------------------------------------------------------------------

/// Encode a byte slice as a Lua double-quoted string literal.
fn lua_string_literal(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() + 2);
    out.push('"');
    for &b in bytes {
        match b {
            b'"'  => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7E => out.push(b as char),
            _ => out.push_str(&format!("\\x{:02X}", b)),
        }
    }
    out.push('"');
    out
}
