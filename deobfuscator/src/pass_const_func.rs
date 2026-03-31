/// Pass – Obfuscated function inlining and string-keyed table substitution.
///
/// # Phase 1 – const-return function inlining
///
/// ```lua
/// local _fN = function()
///     local _t0 = {}
///     if _t0["i"] ~= nil then _t0["i"] = _t0["i"](_t0) end
///     return "LITERAL"
/// end
/// TABLE[KEY] = _fN()   →   TABLE[KEY] = "LITERAL"
/// ```
///
/// # Phase 2 – identity function inlining
///
/// ```lua
/// local _fN = function(_p0)
///     local _t0 = {}
///     if _t0["i"] ~= nil then _t0["i"] = _t0["i"](_t0) end
///     return _p0
/// end
/// TABLE[KEY] = _fN(EXPR)   →   TABLE[KEY] = EXPR
/// ```
///
/// # Phase 3 – string-keyed table substitution
///
/// After phases 1 and 2 each entry is of the form `TABLE[KEY] = VALUE`.
/// Every READ of `TABLE[KEY]` is replaced with `VALUE`.
///
/// Keys are matched at **byte level** (decoding Lua escapes), so `"}"` and
/// `"\x7D"` compare as equal.

use regex::Regex;
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn run(src: &str) -> String {
    // Phase 1: inline constant-returning functions.
    let s = inline_const_funcs(src);
    // Phase 2: inline identity functions.
    // Loop to handle nested identity calls (e.g. _fA(_fB(expr))):
    // on each pass the inner call is resolved, exposing the outer for the next pass.
    let mut s = s;
    for _ in 0..10 {
        let identity_fns = detect_identity_functions(&s);
        if identity_fns.is_empty() { break; }
        let next = inline_identity_funcs(&s, &identity_fns);
        if next == s { break; }
        s = next;
    }
    let s = s;

    // Phase 3: substitute TABLE[KEY] reads to convergence (no write removal yet,
    // so chained values like _t15909[k] → expr(_t8845[k2]) can resolve across passes).
    // Track which (table, key_bytes) pairs actually had reads substituted.
    let mut s = s;
    let mut all_substituted: std::collections::BTreeSet<(String, Vec<u8>)> =
        std::collections::BTreeSet::new();
    for _ in 0..5 {
        let (next, changed, substituted) = subst_keyed_table_reads(&s);
        all_substituted.extend(substituted);
        if !changed {
            break;
        }
        s = next;
    }

    // Phase 4: remove write lines ONLY for keys that had at least one read substituted.
    remove_dead_write_lines(s, &all_substituted)
}

// ---------------------------------------------------------------------------
// Phase 1 – const-return function detection + inlining
// ---------------------------------------------------------------------------

struct ConstFunc {
    fn_name:    String,
    return_val: String,
    decl_start: usize,
    decl_end:   usize,
}

fn inline_const_funcs(src: &str) -> String {
    let funcs = detect_const_functions(src);
    if funcs.is_empty() {
        return src.to_string();
    }

    let mut edits: Vec<(usize, usize, String)> = Vec::new();
    for f in &funcs {
        let call_re = Regex::new(&format!(
            r"\b{}\s*\(\s*\)",
            regex::escape(&f.fn_name),
        ))
        .unwrap();
        for m in call_re.find_iter(src) {
            if m.start() >= f.decl_start && m.end() <= f.decl_end {
                continue;
            }
            edits.push((m.start(), m.end(), f.return_val.clone()));
        }
        edits.push((f.decl_start, f.decl_end, String::new()));
    }

    apply_edits(src, edits)
}

fn detect_const_functions(src: &str) -> Vec<ConstFunc> {
    let mut result = Vec::new();
    let lines = build_line_table(src);

    let re_fn_start  = Regex::new(r"^\s*local\s+(_f\d+)\s*=\s*function\s*\(\s*\)\s*$").unwrap();
    let re_local_t   = Regex::new(r"^local\s+_t\d+\s*=\s*\{\}\s*$").unwrap();
    let re_if_dead   = Regex::new(r#"^if\s+_t\d+\["i"\]\s*~=\s*nil\s+then\s*$"#).unwrap();
    let re_call_dead = Regex::new(
        r#"^(_t\d+)\["i"\]\s*=\s*(_t\d+)\["i"\]\s*\(\s*(_t\d+)\s*\)\s*$"#,
    )
    .unwrap();
    let re_return = Regex::new(
        r#"^return\s+("(?:[^"\\]|\\.)*"|-?\d+(?:\.\d+)?)\s*$"#,
    )
    .unwrap();

    let mut i = 0;
    while i < lines.len() {
        let (line_start, line) = lines[i];
        if let Some(caps) = re_fn_start.captures(line) {
            let fn_name = caps[1].to_string();
            let (valid, depth, return_val, close_idx) =
                scan_dead_body(&lines, i + 1, &re_local_t, &re_if_dead, &re_call_dead, |t| {
                    re_return.captures(t).map(|c| c[1].to_string())
                });
            if valid && depth == 0 {
                if let Some(ret) = return_val {
                    let (close_off, close_text) = lines[close_idx];
                    let decl_end = (close_off + close_text.len() + 1).min(src.len());
                    result.push(ConstFunc {
                        fn_name,
                        return_val: ret,
                        decl_start: line_start,
                        decl_end,
                    });
                    i = close_idx + 1;
                    continue;
                }
            }
        }
        i += 1;
    }
    result
}

// ---------------------------------------------------------------------------
// Phase 2 – identity function detection + inlining
// ---------------------------------------------------------------------------

struct IdentityFunc {
    fn_name:    String,
    decl_start: usize,
    decl_end:   usize,
}

fn detect_identity_functions(src: &str) -> Vec<IdentityFunc> {
    let mut result = detect_identity_functions_inner(src);
    // Also detect local aliases of identity functions: `local ALIAS = _fN`
    // where `_fN` is already in the result list.
    let identity_names: std::collections::BTreeSet<String> =
        result.iter().map(|f| f.fn_name.clone()).collect();
    let re_fn_alias = Regex::new(r"^\s*local\s+(\w+)\s*=\s*(_f\d+)\s*$").unwrap();
    let lines = build_line_table(src);
    for (line_start, line) in &lines {
        if let Some(caps) = re_fn_alias.captures(line) {
            let alias    = caps[1].to_string();
            let original = caps[2].to_string();
            if identity_names.contains(&original) && !alias.starts_with("_f") {
                // The alias line `local ALIAS = _fN` - we treat ALIAS as identity.
                // decl_start/end covers just this one line (we'll remove it later).
                let line_end = (line_start + line.len() + 1).min(src.len());
                result.push(IdentityFunc {
                    fn_name: alias,
                    decl_start: *line_start,
                    decl_end: line_end,
                });
            }
        }
    }
    result
}

fn detect_identity_functions_inner(src: &str) -> Vec<IdentityFunc> {
    let mut result = Vec::new();
    let lines = build_line_table(src);

    let re_fn_start  = Regex::new(r"^\s*local\s+(_f\d+)\s*=\s*function\s*\(\s*(\w+)\s*\)\s*$").unwrap();
    let re_local_t   = Regex::new(r"^local\s+_t\d+\s*=\s*\{\}\s*$").unwrap();
    let re_if_dead   = Regex::new(r#"^if\s+_t\d+\["i"\]\s*~=\s*nil\s+then\s*$"#).unwrap();
    let re_call_dead = Regex::new(
        r#"^(_t\d+)\["i"\]\s*=\s*(_t\d+)\["i"\]\s*\(\s*(_t\d+)\s*\)\s*$"#,
    )
    .unwrap();

    let mut i = 0;
    while i < lines.len() {
        let (line_start, line) = lines[i];
        if let Some(caps) = re_fn_start.captures(line) {
            let fn_name   = caps[1].to_string();
            let param     = caps[2].to_string();
            // Pattern 1: simple return PARAM (standard identity).
            let re_ret = Regex::new(&format!(
                r"^return\s+{}\s*$",
                regex::escape(&param),
            ))
            .unwrap();

            let (valid, depth, has_return, close_idx) =
                scan_dead_body(&lines, i + 1, &re_local_t, &re_if_dead, &re_call_dead, |t| {
                    if re_ret.is_match(t) { Some(true) } else { None }
                });
            if valid && depth == 0 && has_return.is_some() {
                let (close_off, close_text) = lines[close_idx];
                let decl_end = (close_off + close_text.len() + 1).min(src.len());
                result.push(IdentityFunc { fn_name, decl_start: line_start, decl_end });
                i = close_idx + 1;
                continue;
            }
            // Pattern 2: transparent permutation identity (the _f4 pattern).
            // Body: [dead blocks] pairs(PARAM) loop via _acc4[] → return acc
            // The permutation is always identity after pass_stream_dec.
            if let Some(close_idx) = try_detect_perm_identity(&lines, i + 1, &param, &re_local_t, &re_if_dead, &re_call_dead) {
                let (close_off, close_text) = lines[close_idx];
                let decl_end = (close_off + close_text.len() + 1).min(src.len());
                result.push(IdentityFunc { fn_name, decl_start: line_start, decl_end });
                i = close_idx + 1;
                continue;
            }
        }
        i += 1;
    }
    result
}

/// Try to match the `_f4`-style transparent permutation body.
/// Body structure (after optional dead blocks):
///   local _rA, _rB, _rC = pairs(PARAM)
///   local _accX = ""
///   for _vY, _vZ in _rA, _rB, _rC do
///     _accX = _accX .. PERM_TABLE[_vZ]
///   end
///   return _accX
/// Returns the line index of the closing `end` of the function.
fn try_detect_perm_identity(
    lines: &[(usize, &str)],
    start: usize,
    param: &str,
    re_local_t: &Regex,
    re_if_dead: &Regex,
    re_call_dead: &Regex,
) -> Option<usize> {
    let mut j = start;
    let mut fn_depth: usize = 1;
    // Skip dead blocks at the start of the function body.
    loop {
        if j >= lines.len() { return None; }
        let trimmed = lines[j].1.trim();
        if trimmed.is_empty() { j += 1; continue; }
        match fn_depth {
            1 => {
                if re_local_t.is_match(trimmed) { j += 1; continue; }
                if re_if_dead.is_match(trimmed) { fn_depth = 2; j += 1; continue; }
                break; // reached the non-dead part
            }
            2 => {
                if trimmed == "end" { fn_depth = 1; j += 1; continue; }
                if re_call_dead.is_match(trimmed) { j += 1; continue; }
                return None;
            }
            _ => return None,
        }
    }
    // Now expect:
    //   local _rA, _rB, _rC = pairs(PARAM)
    let re_pairs = Regex::new(&format!(
        r"^local\s+(\w+),\s*(\w+),\s*(\w+)\s*=\s*pairs\s*\(\s*{}\s*\)\s*$",
        regex::escape(param),
    )).ok()?;
    //   local _accX = ""
    let re_acc_init = Regex::new(r#"^local\s+(\w+)\s*=\s*""\s*$"#).ok()?;
    //   for _vY, _vZ in _rA, _rB, _rC do
    //   _accX = _accX .. ANYTHING[_vZ]
    //   end
    //   return _accX

    if j >= lines.len() { return None; }
    let pairs_line = lines[j].1.trim();
    let pairs_caps = re_pairs.captures(pairs_line)?;
    let r_a = pairs_caps[1].to_string();
    let r_b = pairs_caps[2].to_string();
    let r_c = pairs_caps[3].to_string();
    j += 1;

    if j >= lines.len() { return None; }
    let acc_line = lines[j].1.trim();
    let acc_caps = re_acc_init.captures(acc_line)?;
    let acc_var = acc_caps[1].to_string();
    j += 1;

    // for loop
    let re_for = Regex::new(&format!(
        r"^for\s+\w+,\s*(\w+)\s+in\s+{},\s*{},\s*{}\s+do\s*$",
        regex::escape(&r_a),
        regex::escape(&r_b),
        regex::escape(&r_c),
    )).ok()?;
    if j >= lines.len() { return None; }
    let for_line = lines[j].1.trim();
    let for_caps = re_for.captures(for_line)?;
    let v_z = for_caps[1].to_string();
    j += 1;

    // for body: _accX = _accX .. PERM_TABLE[_vZ]
    let re_body = Regex::new(&format!(
        r"^{acc}\s*=\s*{acc}\s*\.\.\s*\w+\[{vz}\]\s*$",
        acc = regex::escape(&acc_var),
        vz  = regex::escape(&v_z),
    )).ok()?;
    if j >= lines.len() { return None; }
    let body_line = lines[j].1.trim();
    if !re_body.is_match(body_line) { return None; }
    j += 1;

    // end (closes for)
    if j >= lines.len() { return None; }
    if lines[j].1.trim() != "end" { return None; }
    j += 1;

    // return _accX
    let re_ret = Regex::new(&format!(r"^return\s+{}\s*$", regex::escape(&acc_var))).ok()?;
    if j >= lines.len() { return None; }
    if !re_ret.is_match(lines[j].1.trim()) { return None; }
    j += 1;

    // end (closes function)
    if j >= lines.len() { return None; }
    if lines[j].1.trim() != "end" { return None; }
    Some(j)
}

fn inline_identity_funcs(src: &str, funcs: &[IdentityFunc]) -> String {
    if funcs.is_empty() {
        return src.to_string();
    }

    let src_bytes = src.as_bytes();

    // Collect call edits tagged with the function index.
    // (start, end, replacement, fn_index)
    let mut call_edits: Vec<(usize, usize, String, usize)> = Vec::new();

    for (fi, f) in funcs.iter().enumerate() {
        let call_re = Regex::new(&format!(
            r"\b{}\s*\(",
            regex::escape(&f.fn_name),
        ))
        .unwrap();

        for m in call_re.find_iter(src) {
            // Skip occurrences inside the definition.
            if m.start() >= f.decl_start && m.start() < f.decl_end {
                continue;
            }
            let open_paren = m.end() - 1;
            if let Some(close_paren) = find_matching_paren(src_bytes, open_paren) {
                let expr = src[open_paren + 1..close_paren].to_string();
                call_edits.push((m.start(), close_paren + 1, expr, fi));
            }
        }
    }

    // Simulate apply_edits right-to-left over call edits to detect which would be
    // skipped due to nesting (outer call range overlaps an already-applied inner range).
    let mut sorted_sim = call_edits.clone();
    sorted_sim.sort_by(|a, b| b.0.cmp(&a.0));
    let mut skipped_funcs: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    let mut last_start = usize::MAX;
    for (start, end, _, fi) in &sorted_sim {
        if *end <= last_start && *start <= *end {
            last_start = *start;
        } else {
            // This call edit would be skipped — keep the definition so we can
            // inline it in a subsequent pass (after nested calls are resolved).
            skipped_funcs.insert(*fi);
        }
    }

    // Build the final edit list.
    let mut edits: Vec<(usize, usize, String)> = Vec::new();
    for (start, end, rep, _) in call_edits {
        edits.push((start, end, rep));
    }
    for (fi, f) in funcs.iter().enumerate() {
        // Only remove definition when no call of this function was skipped.
        if !skipped_funcs.contains(&fi) {
            edits.push((f.decl_start, f.decl_end, String::new()));
        }
    }

    apply_edits(src, edits)
}

// ---------------------------------------------------------------------------
// Shared body scanner for dead-block functions
// ---------------------------------------------------------------------------

/// Scan the body lines of a function that may contain:
///   - zero or more dead-table blocks (depth 1 → 2 → 1)
///   - a single payload line recognised by `payload_fn`
///   - a closing `end` at depth 1
///
/// Returns `(valid, final_depth, payload_value, close_line_index)`.
/// `close_line_index` is the index of the closing `end` line in `lines`.
fn scan_dead_body<T, F>(
    lines: &[(usize, &str)],
    start: usize,
    re_local_t:   &Regex,
    re_if_dead:   &Regex,
    re_call_dead: &Regex,
    payload_fn: F,
) -> (bool, usize, Option<T>, usize)
where
    F: Fn(&str) -> Option<T>,
{
    let mut j = start;
    let mut depth: usize = 1;
    let mut payload: Option<T> = None;
    let mut valid = true;
    let mut close_idx = start;

    'body: while j < lines.len() {
        let (_, body_line) = lines[j];
        let trimmed = body_line.trim();
        let cur_j = j;
        j += 1;

        if trimmed.is_empty() {
            continue;
        }

        match depth {
            1 => {
                if trimmed == "end" {
                    depth = 0;
                    close_idx = cur_j;
                    break 'body;
                } else if re_local_t.is_match(trimmed) {
                    // dead table decl
                } else if re_if_dead.is_match(trimmed) {
                    depth = 2;
                } else if let Some(val) = payload_fn(trimmed) {
                    payload = Some(val);
                } else {
                    valid = false;
                    break 'body;
                }
            }
            2 => {
                if trimmed == "end" {
                    depth = 1;
                } else if let Some(c) = re_call_dead.captures(trimmed) {
                    if &c[1] != &c[2] || &c[2] != &c[3] {
                        valid = false;
                        break 'body;
                    }
                } else {
                    valid = false;
                    break 'body;
                }
            }
            _ => {
                valid = false;
                break 'body;
            }
        }
    }

    (valid, depth, payload, close_idx)
}

// ---------------------------------------------------------------------------
// Phase 3 – string-keyed table read substitution
// ---------------------------------------------------------------------------

/// Collect single-write, non-self-referential table entries and build a
/// substitution map.  Returns `(table_name, key_bytes) → (value, key_literal)`.
fn build_known(src: &str) -> BTreeMap<(String, Vec<u8>), (String, String)> {
    let re_assign = Regex::new(
        r#"(?m)^\s*(_t\d+)\[("(?:[^"\\]|\\.)*")\]\s*=\s*(.+?)\s*$"#,
    )
    .unwrap();

    // (table_name, key_bytes) → (value_text, key_literal, write_count)
    let mut raw: BTreeMap<(String, Vec<u8>), (String, String, usize)> = BTreeMap::new();
    for caps in re_assign.captures_iter(src) {
        let tname   = caps[1].to_string();
        let key_lit = caps[2].to_string();
        let val     = caps[3].trim().to_string();
        if let Some(key_bytes) = parse_lua_string_literal(&key_lit) {
            let e = raw.entry((tname, key_bytes)).or_insert((val, key_lit, 0));
            e.2 += 1;
        }
    }

    // Keep only single-write, non-self-referential entries.
    let mut known = BTreeMap::new();
    for ((tname, key_bytes), (val, key_lit, count)) in raw {
        if count != 1 {
            continue;
        }
        // Exclude self-referential: value contains TABLE[KEY] with the same key.
        let self_ref = format!("{}[{}]", tname, key_lit);
        if val.contains(&self_ref) {
            continue;
        }
        known.insert((tname, key_bytes), (val, key_lit));
    }
    known
}

/// Detect local aliases of the form `local ALIAS = _tN` for tables that
/// appear in `known`.  Returns a map `alias_name → canonical_table_name`.
fn detect_aliases<'a>(
    src: &str,
    known: &'a BTreeMap<(String, Vec<u8>), (String, String)>,
) -> BTreeMap<String, String> {
    // Collect the set of canonical table names that appear in `known`.
    let canon_tables: std::collections::BTreeSet<&str> =
        known.keys().map(|(t, _)| t.as_str()).collect();

    let re_alias = Regex::new(r"(?m)^\s*local\s+(\w+)\s*=\s*(_t\d+)\s*$").unwrap();
    let mut aliases: BTreeMap<String, String> = BTreeMap::new();
    for caps in re_alias.captures_iter(src) {
        let alias  = caps[1].to_string();
        let tname  = caps[2].to_string();
        if canon_tables.contains(tname.as_str()) {
            aliases.insert(alias, tname);
        }
    }
    aliases
}

/// Replace every `TABLE[KEY_LIT]` **read** (and `ALIAS[KEY_LIT]` for detected
/// aliases) with the stored value.
/// Returns `(new_source, changed, set_of_substituted_keys)`.
fn subst_keyed_table_reads(
    src: &str,
) -> (String, bool, std::collections::BTreeSet<(String, Vec<u8>)>) {
    let known = build_known(src);
    if known.is_empty() {
        return (src.to_string(), false, std::collections::BTreeSet::new());
    }

    let aliases = detect_aliases(src, &known);

    // Build a combined access regex that matches both canonical tables and aliases.
    // We match any identifier followed by `["..."]`.
    let re_use = Regex::new(r#"(\b[_a-zA-Z]\w*)\[("(?:[^"\\]|\\.)*")\]"#).unwrap();

    let mut result = String::with_capacity(src.len());
    let mut last_end = 0usize;
    let mut changed = false;
    let mut substituted_keys: std::collections::BTreeSet<(String, Vec<u8>)> =
        std::collections::BTreeSet::new();

    for caps in re_use.captures_iter(src) {
        let m       = caps.get(0).unwrap();
        let ident   = &caps[1];
        let key_lit = &caps[2];

        result.push_str(&src[last_end..m.start()]);

        // Resolve the identifier to a canonical table name.
        let tname: Option<&str> = if ident.starts_with("_t") && ident[2..].chars().all(|c| c.is_ascii_digit()) {
            Some(ident.as_ref())
        } else {
            aliases.get(ident.as_ref() as &str).map(|s| s.as_str())
        };

        // Skip write sites: TABLE[KEY] followed by `=` (but not `==`).
        let after = src[m.end()..].trim_start();
        let is_write = after.starts_with('=') && !after.starts_with("==");

        let mut did_substitute = false;
        if !is_write {
            if let Some(tname) = tname {
                if let Some(key_bytes) = parse_lua_string_literal(key_lit) {
                    if let Some((val, _)) = known.get(&(tname.to_string(), key_bytes.clone())) {
                        result.push_str(val);
                        did_substitute = true;
                        changed = true;
                        substituted_keys.insert((tname.to_string(), key_bytes));
                    }
                }
            }
        }

        if !did_substitute {
            result.push_str(m.as_str());
        }
        last_end = m.end();
    }
    result.push_str(&src[last_end..]);
    (result, changed, substituted_keys)
}

// ---------------------------------------------------------------------------
// Phase 4 – remove dead write lines
// ---------------------------------------------------------------------------

/// After reads are fully resolved, remove:
///   1. Write lines `_tN["KEY"] = VALUE` for every key that was actually substituted.
///   2. Alias lines `local ALIAS = _tN` and declaration lines `local _tN = {}`
///      only when ALL known keys for that table were substituted (table fully inlined).
///
/// `substituted` is the set of `(table_name, key_bytes)` pairs that had at least
/// one read successfully substituted.  Write lines for keys NOT in this set are kept.
fn remove_dead_write_lines(
    src: String,
    substituted: &std::collections::BTreeSet<(String, Vec<u8>)>,
) -> String {
    if substituted.is_empty() {
        return src;
    }

    let known = build_known(&src);

    // For each table, count how many of its known keys were substituted.
    // A table is "fully inlined" if every key in `known` was substituted.
    let fully_inlined_tables: std::collections::BTreeSet<String> = {
        let mut table_known: BTreeMap<String, usize> = BTreeMap::new();
        for (tname, _) in known.keys() {
            *table_known.entry(tname.clone()).or_insert(0) += 1;
        }
        table_known
            .into_iter()
            .filter(|(tname, total)| {
                let subst = substituted.iter().filter(|(t, _)| t == tname).count();
                subst >= *total
            })
            .map(|(tname, _)| tname)
            .collect()
    };

    let aliases = detect_aliases(&src, &known);

    // Remove write lines only for keys that were actually substituted.
    let re_write_line = Regex::new(
        r#"(?m)^[^\S\n]*_t\d+\["(?:[^"\\]|\\.)*"\]\s*=[^=][^\n]*\n?"#,
    )
    .unwrap();
    let re_lhs = Regex::new(r#"^\s*(_t\d+)\[("(?:[^"\\]|\\.)*")\]"#).unwrap();

    let result = re_write_line.replace_all(&src, |caps: &regex::Captures| {
        let full = caps.get(0).unwrap().as_str();
        if let Some(lhs) = re_lhs.captures(full) {
            let tname   = &lhs[1];
            let key_lit = &lhs[2];
            if let Some(key_bytes) = parse_lua_string_literal(key_lit) {
                if substituted.contains(&(tname.to_string(), key_bytes)) {
                    return String::new();
                }
            }
        }
        full.to_string()
    });
    let src = result.into_owned();

    // Remove alias lines and declaration lines only for fully-inlined tables.
    let lines: Vec<&str> = src.lines().collect();
    let re_alias_line = Regex::new(r"^\s*local\s+\w+\s*=\s*(_t\d+)\s*$").unwrap();
    let re_decl_line  = Regex::new(r"^\s*local\s+(_t\d+)\s*=\s*\{\}\s*$").unwrap();

    let mut out: Vec<&str> = Vec::with_capacity(lines.len());
    for line in &lines {
        let mut keep = true;
        if let Some(c) = re_alias_line.captures(line) {
            let t: &str = &c[1];
            if fully_inlined_tables.contains(t) || aliases.values().any(|v| v.as_str() == t && fully_inlined_tables.contains(t)) {
                keep = false;
            }
        }
        if let Some(c) = re_decl_line.captures(line) {
            let t: &str = &c[1];
            if fully_inlined_tables.contains(t) {
                keep = false;
            }
        }
        if keep {
            out.push(line);
        }
    }
    out.join("\n")
}

// ---------------------------------------------------------------------------
// Balanced-parenthesis finder
// ---------------------------------------------------------------------------

/// Find the position of the `)` that matches the `(` at `open_pos`.
/// Skips over Lua double-quoted and single-quoted string literals.
fn find_matching_paren(src: &[u8], open_pos: usize) -> Option<usize> {
    debug_assert_eq!(src[open_pos], b'(');
    let mut depth = 1usize;
    let mut i = open_pos + 1;
    while i < src.len() {
        match src[i] {
            b'(' => {
                depth += 1;
                i += 1;
            }
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
                i += 1;
            }
            b'"' => {
                i += 1;
                while i < src.len() {
                    if src[i] == b'\\' {
                        i += 2;
                    } else if src[i] == b'"' {
                        i += 1;
                        break;
                    } else {
                        i += 1;
                    }
                }
            }
            b'\'' => {
                i += 1;
                while i < src.len() {
                    if src[i] == b'\\' {
                        i += 2;
                    } else if src[i] == b'\'' {
                        i += 1;
                        break;
                    } else {
                        i += 1;
                    }
                }
            }
            _ => {
                i += 1;
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------

/// Build a `Vec<(byte_offset, &str)>` for every line in `src`.
fn build_line_table<'a>(src: &'a str) -> Vec<(usize, &'a str)> {
    let mut v = Vec::new();
    let mut off = 0usize;
    for line in src.split('\n') {
        v.push((off, line.trim_end_matches('\r')));
        off += line.len() + 1;
    }
    v
}

/// Apply a list of `(start, end, replacement)` edits right-to-left.
fn apply_edits(src: &str, mut edits: Vec<(usize, usize, String)>) -> String {
    if edits.is_empty() {
        return src.to_string();
    }
    edits.sort_by(|a, b| b.0.cmp(&a.0));
    let mut result = src.to_string();
    let mut last_start = usize::MAX;
    for (start, end, rep) in edits {
        if end <= last_start && start <= end && end <= result.len() {
            result.replace_range(start..end, &rep);
            last_start = start;
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Lua string literal parser
// ---------------------------------------------------------------------------

fn parse_lua_string_literal(quoted: &str) -> Option<Vec<u8>> {
    let inner = quoted.strip_prefix('"')?.strip_suffix('"')?;
    let mut result = Vec::with_capacity(inner.len());
    let bytes = inner.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'\\' {
            result.push(bytes[i]);
            i += 1;
            continue;
        }
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
                let start = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() && i - start < 3 {
                    i += 1;
                }
                let num: u16 = std::str::from_utf8(&bytes[start..i]).ok()?.parse().ok()?;
                if num > 255 { return None; }
                result.push(num as u8);
            }
            b'x' => {
                i += 1;
                if i + 2 > bytes.len() { return None; }
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
