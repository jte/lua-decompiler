/// Pass – Encrypted-string decryption.
///
/// Detects the encrypted-string table pattern produced by the obfuscator:
///
/// ```lua
/// local _tN = {enc1, enc2, ..., encK, key, _acc14[#_acc14]}
/// ```
///
/// followed by one or more calls of the form:
///
/// ```lua
/// _acc14[#_acc14](_tN)
/// ```
///
/// Decryption formula (per the obfuscator's `_f0` closure, Python pseudocode):
///
/// ```python
/// for i in range(len(enc)):           # 0-based
///     idx = ((enc[i] ^ (i+1)) + key + GLOBAL_BASE) % MODULO
///     char = acc14[idx]               # 1-based lookup in the 256-char table
/// ```
///
/// Constants derived from the sample:
///   GLOBAL_BASE = 141696   (= 142070 − 374, where 374 is the per-table key)
///   MODULO      = 953
///
/// The `key` is the **second-to-last** element of the table (the last element is
/// the function-reference sentinel `_acc14[#_acc14]`, which is ignored).
///
/// Character mapping: the formula index is mapped to a byte via
///   `((index − 1) % 256) as u8`
/// so that it wraps over the 256-element identity char table.

use std::{collections::HashMap, ops::Rem};
use regex::Regex;

/// Global additive base baked into the decryption closure.
const GLOBAL_BASE: i64 = 142070;
/// Modulo used by the decryption closure.
const MODULO: i64 = 953;

/// Decrypt a slice of encrypted integers with the given per-table key.
fn decrypt(enc: &[i64], _key: i64) -> String {
    enc.iter()
        .enumerate()
        .map(|(i, &b)| {
            let code: u8 = ((b ^ (i as i64 + 1)) + GLOBAL_BASE).rem(MODULO) as u8;
            code as char
        })
        .collect()
}

/// Escape a raw string into a Lua double-quoted literal.
fn lua_string_literal(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        let b = c as u8;
        match b {
            b'"'  => out.push_str("\\\""),
            b'\\'  => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7e => out.push(c),
            _ => out.push_str(&format!("\\x{:02X}", b)),
        }
    }
    out.push('"');
    out
}

pub fn run(src: &str) -> String {
    let tables = collect_enc_tables(src);
    if tables.is_empty() {
        return src.to_string();
    }
    substitute(src, &tables)
}

// ---------------------------------------------------------------------------
// Internal type
// ---------------------------------------------------------------------------

struct TableDecl {
    decl_start:     usize,
    decl_end:       usize,
    /// Byte ranges of sentinel-assignment lines (`_tN[k] = _acc14[#_acc14]`)
    /// that belong to this declaration and should be removed alongside it.
    sentinel_lines: Vec<(usize, usize)>,
    name:           String,
    decrypted:      String,
}

// ---------------------------------------------------------------------------
// Step 1 – collect encrypted tables
// ---------------------------------------------------------------------------

fn collect_enc_tables(src: &str) -> Vec<TableDecl> {
    let mut result: Vec<TableDecl> = Vec::new();

    for item in parse_table_bodies(src) {
        if let Some((enc, key)) = parse_enc_table(&item.body) {
            let decrypted = decrypt(&enc, key);
            result.push(TableDecl {
                decl_start:     item.decl_start,
                decl_end:       item.decl_end,
                sentinel_lines: item.sentinel_lines,
                name:           item.name,
                decrypted:      lua_string_literal(&decrypted),
            });
        }
    }

    result
}

// ---------------------------------------------------------------------------
// Step 1a – parse table bodies
// ---------------------------------------------------------------------------

struct RawTableDecl {
    decl_start:     usize,
    decl_end:       usize,
    sentinel_lines: Vec<(usize, usize)>,
    name:           String,
    body:           String,
}

/// Parse all `local _tN = { ... }` blocks from the source in source order.
/// Duplicates are preserved (same name in different closures).
///
/// Also handles the split-assignment pattern produced by `pass_table_ctor`:
/// ```lua
/// local _tN = {int, int, ..., key}   -- reconstructed integers only
/// ...
/// _tN[k] = _acc14[#_acc14]           -- sentinel appended separately
/// ```
/// When such a sentinel line is found, `, _acc14[#_acc14]` is appended to the
/// body of the most-recent preceding declaration of that name, enabling
/// `parse_enc_table` to recognise it as an encrypted string table.
fn parse_table_bodies(src: &str) -> Vec<RawTableDecl> {
    let mut result: Vec<RawTableDecl> = Vec::new();

    // Build a table of (line_start_byte, line_text) so we can compute offsets.
    let mut lines: Vec<(usize, &str)> = Vec::new();
    let mut offset = 0usize;
    for line in src.split('\n') {
        lines.push((offset, line));
        offset += line.len() + 1; // +1 for the '\n'
    }

    let re_single   = Regex::new(r"^\s*local\s+(_t\d+)\s*=\s*\{([^}]*)\}\s*$").unwrap();
    let re_open     = Regex::new(r"^\s*local\s+(_t\d+)\s*=\s*\{\s*$").unwrap();
    // Sentinel-assignment line left by pass_table_ctor:  _tN[k] = _acc14[#_acc14]
    let re_sentinel = Regex::new(r"^\s*(_t\d+)\[\d+\]\s*=\s*_acc14\[#_acc14\]\s*$").unwrap();

    let mut i = 0;
    while i < lines.len() {
        let (line_start, line) = lines[i];
        // Strip trailing \r for Windows line endings
        let line = line.trim_end_matches('\r');
        // Inclusive end of this line in the source (including the '\n').
        let line_end = (line_start + line.len() + 1).min(src.len());

        if let Some(caps) = re_single.captures(line) {
            result.push(RawTableDecl {
                decl_start:     line_start,
                decl_end:       line_end,
                sentinel_lines: Vec::new(),
                name:           caps[1].to_string(),
                body:           caps[2].to_string(),
            });
            i += 1;
            continue;
        }

        if let Some(caps) = re_open.captures(line) {
            let name = caps[1].to_string();
            let decl_start = line_start;
            let mut body = String::new();
            i += 1;
            while i < lines.len() {
                let (close_start, l) = lines[i];
                let l = l.trim_end_matches('\r');
                if l.trim() == "}" {
                    let decl_end = (close_start + l.len() + 1).min(src.len());
                    result.push(RawTableDecl {
                        decl_start,
                        decl_end,
                        sentinel_lines: Vec::new(),
                        name,
                        body,
                    });
                    i += 1;
                    break;
                }
                if !body.is_empty() {
                    body.push(' ');
                }
                body.push_str(l.trim());
                i += 1;
            }
            continue;
        }

        // Sentinel-assignment line: _tN[k] = _acc14[#_acc14]
        // Append the sentinel to the most-recent preceding declaration of _tN
        // whose body is all-integer (i.e., has no sentinel yet).
        if let Some(caps) = re_sentinel.captures(line) {
            let name = &caps[1];
            let sentinel_pos = line_start;
            // Walk result in reverse to find the latest decl of this name
            // whose decl_end <= sentinel_pos and body lacks a sentinel.
            for entry in result.iter_mut().rev() {
                if entry.name == name && entry.decl_end <= sentinel_pos
                    && !entry.body.contains("[#")
                {
                    entry.body.push_str(", _acc14[#_acc14]");
                    entry.sentinel_lines.push((line_start, line_end));
                    break;
                }
            }
        }

        i += 1;
    }

    result
}

/// Parse a table body string like `"248, 254, ..., 374, _acc14[#_acc14],"`.
///
/// Returns `Some((enc_bytes, key))` when:
///   - the last element is non-numeric (the function-reference sentinel),
///   - the second-to-last element is a positive integer (the per-table key),
///   - all preceding elements are integers (the encrypted bytes).
fn parse_enc_table(body: &str) -> Option<(Vec<i64>, i64)> {
    let parts: Vec<&str> = body
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();

    if parts.len() < 3 {
        return None;
    }

    let sentinel = parts.last()?;
    if sentinel.chars().all(|c| c.is_ascii_digit() || c == '-') {
        return None;
    }
    if !sentinel.contains("[#") {
        return None;
    }

    let key: i64 = parts[parts.len() - 2].parse().ok()?;
    if key <= 0 {
        return None;
    }

    let enc: Option<Vec<i64>> = parts[..parts.len() - 2]
        .iter()
        .map(|s| s.parse::<i64>().ok())
        .collect();
    let enc = enc?;

    if enc.is_empty() {
        return None;
    }

    Some((enc, key))
}

// ---------------------------------------------------------------------------
// Step 2 – substitute calls and remove declarations
// ---------------------------------------------------------------------------

fn substitute(src: &str, tables: &[TableDecl]) -> String {
    // For each declaration entry, search for its call site ONLY within the
    // window [decl_end, next_same_name_decl_end).  This prevents a declaration
    // with no call site from "stealing" the call site of a later same-named
    // declaration in a different closure.
    //
    // After collecting all (match_start, match_end, replacement) pairs,
    // apply them right-to-left so earlier replacements don't shift offsets
    // for later ones.

    // Build per-name sorted list of decl_end positions for window calculation.
    let mut windows_by_name: HashMap<&str, Vec<usize>> = HashMap::new();
    for t in tables {
        windows_by_name.entry(t.name.as_str()).or_default().push(t.decl_end);
    }

    // Index into each name's window list (advances as we process entries).
    let mut name_idx: HashMap<&str, usize> = HashMap::new();

    // (start, end, replacement)  — "" means "delete this range"
    let mut replacements: Vec<(usize, usize, String)> = Vec::new();

    for t in tables {
        let idx = name_idx.entry(t.name.as_str()).or_insert(0);
        let windows = &windows_by_name[t.name.as_str()];

        let search_start = t.decl_end.min(src.len());
        let search_end = if *idx + 1 < windows.len() {
            windows[*idx + 1].min(src.len())
        } else {
            src.len()
        };
        *idx += 1;

        if search_start >= search_end {
            continue;
        }

        let pat = format!(
            r"_acc14\[#_acc14\]\s*\(\s*{}\s*\)",
            regex::escape(&t.name)
        );
        let re = match Regex::new(&pat) {
            Ok(r) => r,
            Err(_) => continue,
        };

        let mut matched = false;
        for m in re.find_iter(&src[search_start..search_end]) {
            let abs_start = search_start + m.start();
            let abs_end   = search_start + m.end();
            replacements.push((abs_start, abs_end, t.decrypted.clone()));
            matched = true;
        }

        // If at least one call site was substituted, also queue removal of
        // the table declaration and any associated sentinel assignment lines.
        if matched {
            replacements.push((t.decl_start, t.decl_end, String::new()));
            for &(sl_start, sl_end) in &t.sentinel_lines {
                replacements.push((sl_start, sl_end, String::new()));
            }
        }
    }

    // Apply right-to-left so byte offsets stay valid.
    replacements.sort_by(|a, b| b.0.cmp(&a.0));

    let mut result = src.to_string();
    for (start, end, replacement) in replacements {
        result.replace_range(start..end, &replacement);
    }

    result
}
