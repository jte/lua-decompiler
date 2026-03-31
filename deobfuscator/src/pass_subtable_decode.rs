/// Pass – Static sub-table decoding + _acc15 substitution.
///
/// Phase 1 – Sub-table decoding (two-loop pattern):
///   ```lua
///   local _r4, _r5, _r6 = pairs(<tbl>)     ← removed
///   local <acc3> = <tbl>                    ← kept (used later)
///   local <acc2> = {<integers>}             ← removed
///   for k, sub in ...                       ← removed
///     for i, v in pairs(sub)
///       <acc3>[k][i] = <acc2>[v - OFFSET] - BASE
///   for k, sub in pairs(<acc3>)             ← removed
///     <acc3>[k] = string.char(table.unpack(sub))
///   ```
///   Each `<tbl>[k] = {encoded}` assignment is replaced with the decoded string.
///
/// Phase 2 – _acc3[k] substitution:
///   Since `<acc3> = <tbl>` and we just decoded every `<tbl>[k]`, replace all
///   `<acc3>[NUMBER]` occurrences with the corresponding decoded string literal.
///
/// Phase 3 – _acc15 substitution:
///   Detects the follow-on pattern:
///   ```lua
///   local <eval_indices> = {8, 9, ..., 231}
///   local _rX = pairs(<eval_indices>)
///   local <acc15> = { string, math, ..., "<decoded>", ... }
///   for _vN, _vM in _rX ... do
///     <acc15>[_vM] = load(<acc15>[K] .. <acc15>[_vM])()
///   end
///   ```
///   After Phase 2 the `<acc15>` table body is fully known.  Build a map
///   index→value:
///     • indices 1–7:   the module-ref expression (e.g. `string`, `math`)
///     • eval'd range:  strip the outer quotes from the string literal, so
///                      `"string.byte"` → `string.byte`, `"100"` → `100`
///     • rest:          keep the quoted string literal
///   Then replace all `<acc15>[INTEGER]` occurrences with the resolved value,
///   iterating until fixed-point (handles `<acc15>[<acc15>[k]]` chains).
///   The entire _acc15 infrastructure block is removed.

use std::collections::HashMap;
use regex::Regex;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn run(src: &str) -> String {
    detect_and_apply(src).unwrap_or_else(|| src.to_string())
}

// ---------------------------------------------------------------------------
// Detection – phase 1 pattern
// ---------------------------------------------------------------------------

#[allow(dead_code)]
struct DecodePattern {
    acc3_name:   String,
    acc2_name:   String,
    tbl_name:    String,
    lookup:      Vec<i64>,
    offset:      i64,
    base:        i64,
    /// Byte range of the `local _rN = pairs(<tbl>)` setup line.  Removed
    /// separately so that the `local <acc3> = <tbl>` alias on the next line
    /// is preserved.
    pairs_line:  (usize, usize),
    /// Byte offset of the start of the `local <acc2> = {` line.
    block_start: usize,
    /// Byte offset just past the closing `end` of the second for-loop.
    block_end:   usize,
}

fn detect_and_apply(src: &str) -> Option<String> {
    let lines = lines_with_offsets(src);

    // Inner-assignment signature: X[A][B] = LOOKUP[V - OFFSET] - BASE
    let re_inner = Regex::new(
        r"(\w+)\[\w+\]\[\w+\]\s*=\s*(\w+)\[\w+\s*-\s*(\d+)\]\s*-\s*(\d+)",
    ).unwrap();

    for (li, &(_, line)) in lines.iter().enumerate() {
        let caps = match re_inner.captures(line) {
            Some(c) => c,
            None => continue,
        };
        let acc3_name = caps[1].to_string();
        let acc2_name = caps[2].to_string();
        let offset: i64 = caps[3].parse().ok()?;
        let base:   i64 = caps[4].parse().ok()?;

        // Scan backward for `local <acc3> = <tbl>`.
        let alias_needle = format!("local {} = ", acc3_name);
        let mut tbl_name: Option<String> = None;
        let mut alias_li: Option<usize> = None;
        for bi in (0..li).rev().take(50) {
            let (_, bl) = lines[bi];
            if let Some(pos) = bl.find(&alias_needle) {
                let rest = bl[pos + alias_needle.len()..].trim();
                if rest.chars().all(|c| c.is_alphanumeric() || c == '_') && !rest.is_empty() {
                    tbl_name  = Some(rest.to_string());
                    alias_li  = Some(bi);
                    break;
                }
            }
        }
        let tbl_name = tbl_name?;
        let alias_li = alias_li?;

        // Scan backward for `local _rN = pairs(<tbl>)` just before the alias.
        let pairs_needle = format!("pairs({})", tbl_name);
        let mut pairs_li = alias_li; // fallback: no separate pairs line
        for bi in (0..=alias_li).rev().take(5) {
            if lines[bi].1.contains(&pairs_needle) {
                pairs_li = bi;
                break;
            }
        }
        let (pairs_start, pairs_line_txt) = lines[pairs_li];
        let pairs_end = (pairs_start + pairs_line_txt.len() + 1).min(src.len());

        // Scan backward for `local <acc2> = {`.
        let acc2_needle = format!("local {} = {{", acc2_name);
        let mut acc2_li: Option<usize> = None;
        for bi in (0..li).rev().take(100) {
            if lines[bi].1.contains(&acc2_needle) {
                acc2_li = Some(bi);
                break;
            }
        }
        let acc2_li = acc2_li?;
        let lookup = parse_lookup_table(src, &lines, acc2_li)?;
        let (block_start, _) = lines[acc2_li];

        // Outer for-loop: scan backward from `li` for the `for` at lower indent.
        let inner_indent = leading_spaces(lines[li].1);
        let mut outer_for_li: Option<usize> = None;
        for bi in (0..li).rev().take(30) {
            let bl = lines[bi].1;
            if leading_spaces(bl) < inner_indent && bl.trim().starts_with("for ") {
                outer_for_li = Some(bi);
                break;
            }
        }
        let outer_for_li = outer_for_li?;
        let first_for_end = find_for_end(&lines, outer_for_li)?;

        // `local _rN = pairs(<acc3>)` just after first_for_end.
        let re_pairs2 = Regex::new(&format!(
            r"local\s+\w+\s*,\s*\w+\s*,\s*\w+\s*=\s*pairs\(\s*{}\s*\)",
            regex::escape(&acc3_name),
        )).unwrap();
        let mut pairs2_li: Option<usize> = None;
        for fi in first_for_end + 1..lines.len().min(first_for_end + 5) {
            if re_pairs2.is_match(lines[fi].1) { pairs2_li = Some(fi); break; }
        }
        let pairs2_li = pairs2_li?;

        // Find the `for` line after pairs2_li.
        let mut second_for_li: Option<usize> = None;
        for fi in pairs2_li + 1..lines.len().min(pairs2_li + 3) {
            if lines[fi].1.trim().starts_with("for ") {
                second_for_li = Some(fi); break;
            }
        }
        let second_for_li = second_for_li?;
        let second_for_end = find_for_end(&lines, second_for_li)?;

        let (end_line_off, end_line) = lines[second_for_end];
        let block_end = (end_line_off + end_line.len() + 1).min(src.len());

        let pattern = DecodePattern {
            acc3_name, acc2_name, tbl_name, lookup,
            offset, base,
            pairs_line: (pairs_start, pairs_end),
            block_start,
            block_end,
        };
        return Some(apply_all(src, &lines, &pattern));
    }
    None
}

// ---------------------------------------------------------------------------
// Apply everything
// ---------------------------------------------------------------------------

fn apply_all(src: &str, _lines: &[(usize, &str)], p: &DecodePattern) -> String {
    // Phase 1: decode sub-tables + remove _t350 decode infrastructure.
    let (result, decoded_map) = apply_subtable_decode(src, p);

    // Phase 2: replace _acc3[k] → decoded string.
    let result = replace_acc3_refs(&result, &p.acc3_name, &decoded_map);

    // Phase 3: detect and apply _acc15 substitution.
    apply_acc15_pass(&result, &decoded_map)
}

// ---------------------------------------------------------------------------
// Phase 1: sub-table decode
// ---------------------------------------------------------------------------

/// Returns (transformed_source, decoded_map).
/// decoded_map: tbl_index → raw decoded bytes.
fn apply_subtable_decode(
    src: &str,
    p: &DecodePattern,
) -> (String, HashMap<u64, Vec<u8>>) {
    let decode = |v: i64| -> Option<u8> {
        let idx = (v - p.offset - 1) as usize;
        if idx < p.lookup.len() {
            let code = p.lookup[idx] - p.base;
            if (0..=255).contains(&code) { Some(code as u8) } else { None }
        } else {
            None
        }
    };

    let re_assign = Regex::new(&format!(
        r"{}\[(\d+)\] = \{{",
        regex::escape(&p.tbl_name),
    )).unwrap();

    let mut replacements: Vec<(usize, usize, String)> = Vec::new();
    let mut decoded_map: HashMap<u64, Vec<u8>> = HashMap::new();

    for cap in re_assign.captures_iter(src) {
        let key: u64 = cap[1].parse().ok().unwrap_or(0);
        let match_start = cap.get(0).unwrap().start();
        let brace_start = cap.get(0).unwrap().end();

        let body_end = match find_closing_brace(src, brace_start - 1) {
            Some(e) => e,
            None => continue,
        };
        let assign_end = body_end + 1;

        let body = &src[brace_start..body_end];
        let encoded: Vec<i64> = body
            .split(|c: char| c == ',' || c == '\n' || c == '\r' || c == ' ')
            .filter_map(|s| s.trim().parse().ok())
            .collect();
        if encoded.is_empty() { continue; }

        let decoded: Option<Vec<u8>> = encoded.iter().map(|&v| decode(v)).collect();
        let decoded = match decoded {
            Some(b) => b,
            None => continue,
        };

        decoded_map.insert(key, decoded.clone());
        let new_val = lua_string_literal(&decoded);
        replacements.push((match_start, assign_end,
            format!("{}[{}] = {}", p.tbl_name, key, new_val)));
    }

    // Remove the `local _rN = pairs(<tbl>)` setup line (but NOT alias_li).
    replacements.push((p.pairs_line.0, p.pairs_line.1, String::new()));
    // Remove block from `local <acc2> = {` through second for-end.
    replacements.push((p.block_start, p.block_end, String::new()));

    replacements.sort_by(|a, b| b.0.cmp(&a.0));
    let mut result = src.to_string();
    for (s, e, r) in replacements {
        if s <= e && e <= result.len() {
            result.replace_range(s..e, &r);
        }
    }
    (result, decoded_map)
}

// ---------------------------------------------------------------------------
// Phase 2: _acc3[k] → decoded string
// ---------------------------------------------------------------------------

fn replace_acc3_refs(src: &str, acc3: &str, decoded: &HashMap<u64, Vec<u8>>) -> String {
    let re = Regex::new(&format!(
        r"{}\[(\d+)\]",
        regex::escape(acc3),
    )).unwrap();

    let mut result = src.to_string();
    // Apply right-to-left.
    let mut subs: Vec<(usize, usize, String)> = Vec::new();
    for cap in re.captures_iter(src) {
        let k: u64 = cap[1].parse().ok().unwrap_or(0);
        if let Some(bytes) = decoded.get(&k) {
            let m = cap.get(0).unwrap();
            subs.push((m.start(), m.end(), lua_string_literal(bytes)));
        }
    }
    subs.sort_by(|a, b| b.0.cmp(&a.0));
    for (s, e, r) in subs {
        if s <= e && e <= result.len() {
            result.replace_range(s..e, &r);
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Phase 3: _acc15 substitution
// ---------------------------------------------------------------------------

/// Detect `ACC15[VAR] = load(ACC15[NUM] .. ACC15[VAR])()` to find acc15_name.
fn detect_acc15_name(src: &str) -> Option<String> {
    let re = Regex::new(
        r"(\w+)\[(\w+)\]\s*=\s*load\s*\(\s*(\w+)\[\d+\]\s*\.\."
    ).unwrap();
    let caps = re.captures(src)?;
    if caps[1] == caps[3] {
        Some(caps[1].to_string())
    } else {
        None
    }
}

/// Parse the integer list from a `local NAME = { N, N, ... }` table.
fn parse_int_table(src: &str, name: &str) -> Option<Vec<usize>> {
    let re = Regex::new(&format!(
        r"local\s+{}\s*=\s*\{{([\s\S]*?)\n\}}",
        regex::escape(name),
    )).unwrap();
    let caps = re.captures(src)?;
    let nums: Vec<usize> = caps[1]
        .split(|c: char| c == ',' || c.is_whitespace())
        .filter_map(|s| s.trim().parse().ok())
        .collect();
    if nums.is_empty() { None } else { Some(nums) }
}

/// Parse the entries of `local ACC15 = { ... }` where the body may span
/// many lines.  Returns a Vec<String> of trimmed entry expressions (1-indexed).
fn parse_acc15_entries(src: &str, acc15: &str) -> Option<Vec<String>> {
    let needle = format!("local {} = {{", acc15);
    let decl_pos = src.find(&needle)?;
    let brace_start = src[decl_pos..].find('{')? + decl_pos;
    let brace_end = find_closing_brace(src, brace_start)?;
    let body = &src[brace_start + 1..brace_end];
    Some(split_table_entries(body))
}

/// Split a Lua table body string by commas, respecting strings and brackets.
fn split_table_entries(body: &str) -> Vec<String> {
    let mut entries: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut depth = 0usize;
    let mut in_str = false;
    let bytes = body.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if in_str {
            cur.push(b as char);
            if b == b'\\' {
                i += 1;
                if i < bytes.len() { cur.push(bytes[i] as char); }
            } else if b == b'"' {
                in_str = false;
            }
        } else {
            match b {
                b'"' => { in_str = true; cur.push(b as char); }
                b'[' | b'(' | b'{' => { depth += 1; cur.push(b as char); }
                b']' | b')' | b'}' => {
                    if depth > 0 { depth -= 1; }
                    cur.push(b as char);
                }
                b',' if depth == 0 => {
                    let e = cur.trim().to_string();
                    if !e.is_empty() { entries.push(e); }
                    cur.clear();
                }
                b'\n' | b'\r' => { cur.push(' '); }
                _ => { cur.push(b as char); }
            }
        }
        i += 1;
    }
    let e = cur.trim().to_string();
    if !e.is_empty() { entries.push(e); }
    entries
}

/// Remove outer double-quotes from a Lua string literal.
/// `"hello"` → `hello`.  Returns None if not a simple double-quoted string.
fn unquote(s: &str) -> Option<String> {
    let s = s.trim();
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        // Only unquote if the content has no escape sequences — these are
        // pure-ASCII printable strings (identifiers, numbers).
        let inner = &s[1..s.len() - 1];
        if !inner.contains('\\') && inner.is_ascii() {
            return Some(inner.to_string());
        }
    }
    None
}

fn apply_acc15_pass(src: &str, _decoded_map: &HashMap<u64, Vec<u8>>) -> String {
    // Detect the acc15 variable name from the load-loop signature.
    let acc15 = match detect_acc15_name(src) {
        Some(n) => n,
        None => return src.to_string(),
    };

    // Detect the eval-index table name (`local NAME = { 8, 9, ... }`).
    // It's used in `pairs(NAME)` just before the `local acc15 = ...` line.
    let pairs_idx_re = Regex::new(&format!(
        r"local\s+(\w+)\s*=\s*pairs\s*\(\s*(\w+)\s*\)\s*\n[\s\S]{{0,200}}local\s+{}\s*=",
        regex::escape(&acc15),
    )).unwrap();
    let eval_indices: std::collections::HashSet<usize> = if let Some(caps) = pairs_idx_re.captures(src) {
        let idx_tbl_name = caps[2].to_string();
        parse_int_table(src, &idx_tbl_name)
            .unwrap_or_default()
            .into_iter()
            .collect()
    } else {
        // Fallback: use 8..231 (the known range).
        (8..=231).collect()
    };

    // Parse acc15 table entries.
    let entries = match parse_acc15_entries(src, &acc15) {
        Some(e) => e,
        None => return src.to_string(),
    };

    // Build value map (1-indexed).
    let mut acc15_map: HashMap<usize, String> = HashMap::new();
    for (i, entry) in entries.iter().enumerate() {
        let k = i + 1; // 1-based
        let val = if eval_indices.contains(&k) {
            // Entry was processed by `load("return " .. s)()`.
            // Strip outer quotes to get the raw Lua expression.
            unquote(entry).unwrap_or_else(|| entry.clone())
        } else {
            entry.clone()
        };
        acc15_map.insert(k, val);
    }

    // Replace `acc15[INTEGER]` iteratively until fixed point.
    let mut result = src.to_string();
    let re_acc15 = Regex::new(&format!(
        r"{}\[(\d+)\]",
        regex::escape(&acc15),
    )).unwrap();

    for _ in 0..10 {
        let mut subs: Vec<(usize, usize, String)> = Vec::new();
        for cap in re_acc15.captures_iter(&result) {
            let k: usize = cap[1].parse().ok().unwrap_or(0);
            if let Some(val) = acc15_map.get(&k) {
                let m = cap.get(0).unwrap();
                // Don't substitute if it's the LHS of a plain assignment.
                let after = result[m.end()..].trim_start();
                if !after.starts_with('=') || after.starts_with("==") {
                    subs.push((m.start(), m.end(), val.clone()));
                }
            }
        }
        if subs.is_empty() { break; }
        subs.sort_by(|a, b| b.0.cmp(&a.0));
        for (s, e, r) in subs {
            if s <= e && e <= result.len() {
                result.replace_range(s..e, &r);
            }
        }
    }

    // Remove _acc15 infrastructure.
    result = remove_acc15_infra(&result, &acc15);
    result
}

/// Remove the _acc15 infrastructure block:
///   - `local <eval_tbl> = { ... }` (the index list like {8,9,...,231})
///   - `local _rN, _rM, _rK = pairs(<eval_tbl>)` iterator line
///   - `local <acc15> = { ... }` declaration
///   - `for ... do <acc15>[_v] = load(...) end` loop
fn remove_acc15_infra(src: &str, acc15: &str) -> String {
    let lines = lines_with_offsets(src);

    // Find the load-loop line to locate the for-loop.
    let re_load = Regex::new(&format!(
        r"{}\[\w+\]\s*=\s*load\s*\(",
        regex::escape(acc15),
    )).unwrap();
    let load_li = match lines.iter().position(|(_, l)| re_load.is_match(l)) {
        Some(i) => i,
        None => return src.to_string(),
    };

    // Find the outer `for` that contains the load line.
    let load_indent = leading_spaces(lines[load_li].1);
    let mut for_li: Option<usize> = None;
    for bi in (0..load_li).rev().take(10) {
        let bl = lines[bi].1;
        if leading_spaces(bl) < load_indent && bl.trim().starts_with("for ") {
            for_li = Some(bi);
            break;
        }
    }
    let for_li = match for_li { Some(i) => i, None => return src.to_string() };
    let for_end = match find_for_end(&lines, for_li) {
        Some(i) => i,
        None => return src.to_string(),
    };

    // Find `local acc15 = {` declaration end.
    let re_acc15_decl = Regex::new(&format!(
        r"local\s+{}\s*=\s*\{{",
        regex::escape(acc15),
    )).unwrap();
    let acc15_decl_li = match lines.iter().position(|(_, l)| re_acc15_decl.is_match(l)) {
        Some(i) => i,
        None => return src.to_string(),
    };
    // Find closing `}` of the acc15 table.
    let acc15_close_li = match (acc15_decl_li + 1..lines.len())
        .find(|&i| lines[i].1.trim() == "}")
    {
        Some(i) => i,
        None => return src.to_string(),
    };

    // Find `local _rN = pairs(EVALTBL)` line just before acc15_decl.
    let pairs_li = (0..acc15_decl_li).rev().take(5)
        .find(|&i| lines[i].1.contains("pairs("))
        .unwrap_or(acc15_decl_li.saturating_sub(1));

    // Find `local EVALTBL = {` — the eval-index table declaration.
    // It's the `local _tNNNN = {` declaration whose use is the `pairs(...)` line.
    let pairs_line = lines[pairs_li].1;
    let re_evaltbl_name = Regex::new(r"pairs\s*\(\s*(\w+)\s*\)").unwrap();
    let evaltbl_name = re_evaltbl_name.captures(pairs_line)
        .map(|c| c[1].to_string());

    let evaltbl_decl_li = evaltbl_name.as_deref().and_then(|name| {
        let needle = format!("local {} = {{", name);
        (0..pairs_li).rev().take(200)
            .find(|&i| lines[i].1.contains(&needle))
    });
    let evaltbl_close_li = evaltbl_decl_li.and_then(|start| {
        (start + 1..acc15_decl_li)
            .find(|&i| lines[i].1.trim() == "}")
    });

    let mut removals: Vec<(usize, usize)> = Vec::new();

    // Remove eval-index table (if found).
    if let (Some(start_li), Some(end_li)) = (evaltbl_decl_li, evaltbl_close_li) {
        let (s, _) = lines[start_li];
        let (e, el) = lines[end_li];
        removals.push((s, (e + el.len() + 1).min(src.len())));
    }

    // Remove `local _rN = pairs(...)` line.
    {
        let (s, l) = lines[pairs_li];
        removals.push((s, (s + l.len() + 1).min(src.len())));
    }

    // Remove `local acc15 = { ... }` declaration.
    {
        let (s, _) = lines[acc15_decl_li];
        let (e, el) = lines[acc15_close_li];
        removals.push((s, (e + el.len() + 1).min(src.len())));
    }

    // Remove the load for-loop.
    {
        let (s, _) = lines[for_li];
        let (e, el) = lines[for_end];
        removals.push((s, (e + el.len() + 1).min(src.len())));
    }

    // Apply right-to-left.
    removals.sort_by(|a, b| b.0.cmp(&a.0));
    let mut result = src.to_string();
    for (s, e) in removals {
        if s <= e && e <= result.len() {
            result.replace_range(s..e, "");
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Shared utilities
// ---------------------------------------------------------------------------

fn find_for_end(lines: &[(usize, &str)], start_li: usize) -> Option<usize> {
    let mut depth = 0i32;
    for i in start_li..lines.len() {
        let l = lines[i].1.trim();
        for word in l.split_whitespace() {
            match word.trim_end_matches(|c: char| !c.is_alphabetic()) {
                "for" | "while" | "if" | "function" => depth += 1,
                "end" => {
                    depth -= 1;
                    if depth <= 0 { return Some(i); }
                }
                _ => {}
            }
        }
    }
    None
}

fn parse_lookup_table(
    src: &str,
    lines: &[(usize, &str)],
    decl_li: usize,
) -> Option<Vec<i64>> {
    let (decl_off, _) = lines[decl_li];
    let brace_pos = src[decl_off..].find('{')?;
    let body_start = decl_off + brace_pos + 1;
    let mut body_end = src.len();
    for i in decl_li + 1..lines.len() {
        if lines[i].1.trim() == "}" {
            body_end = lines[i].0;
            break;
        }
    }
    let nums: Vec<i64> = src[body_start..body_end]
        .split(|c: char| c == ',' || c.is_whitespace())
        .filter_map(|s| s.trim().parse().ok())
        .collect();
    if nums.is_empty() { None } else { Some(nums) }
}

fn find_closing_brace(src: &str, open_pos: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    if open_pos >= bytes.len() || bytes[open_pos] != b'{' { return None; }
    let mut depth = 1usize;
    let mut i = open_pos + 1;
    while i < bytes.len() {
        match bytes[i] {
            b'{' => depth += 1,
            b'}' => { depth -= 1; if depth == 0 { return Some(i); } }
            _ => {}
        }
        i += 1;
    }
    None
}

fn leading_spaces(s: &str) -> usize {
    s.len() - s.trim_start().len()
}

fn lines_with_offsets(src: &str) -> Vec<(usize, &str)> {
    let mut v = Vec::new();
    let mut off = 0usize;
    for line in src.split('\n') {
        v.push((off, line.trim_end_matches('\r')));
        off += line.len() + 1;
    }
    v
}

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
            // Escape { and } so they don't confuse brace-counting parsers.
            b'{' => out.push_str("\\x7B"),
            b'}' => out.push_str("\\x7D"),
            0x20..=0x7E => out.push(b as char),
            _ => out.push_str(&format!("\\x{:02X}", b)),
        }
    }
    out.push('"');
    out
}
