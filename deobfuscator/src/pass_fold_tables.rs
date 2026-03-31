/// Pass – Fold `local _tN = {}` + string-keyed assignments into table constructors.
///
/// ## Pattern
///
/// ```lua
/// local _t21577 = {}
/// _t21577["HP"]  = 2570
/// _t21577["ATK"] = 110
/// _t21577["SPD"] = 250
/// _t20687["Yi Sun-shin"] = _t21577    -- inner use → single-line ctor
/// ```
///
/// becomes (first iteration):
///
/// ```lua
/// _t20687["Yi Sun-shin"] = {HP = 2570, ATK = 110, SPD = 250}
/// ```
///
/// then (second iteration), if `_t20687` is itself foldable with a final use:
///
/// ```lua
/// heroStats = {
///   ["Yi Sun-shin"] = {HP = 2570, ATK = 110, SPD = 250},
///   ["Yu Zhong"]    = {HP = 2520, ATK = 129, SPD = 245},
///   ["Zilong"]      = {HP = 2511, ATK = 123, SPD = 265},
/// }
/// ```
///
/// ## Rules
///
/// - Only folds when **all** assignments to `_tN` are string-keyed (`_tN["k"] = v`).
/// - Only folds when `_tN` appears as an RHS **exactly once** outside its own block.
/// - Iterates to a fixed point so nested tables are handled bottom-up.

use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn run(src: &str) -> String {
    let mut s = src.to_string();
    for _ in 0..30 {
        let next = run_once(&s);
        if next == s { break; }
        s = next;
    }
    s
}

// ---------------------------------------------------------------------------
// Single pass
// ---------------------------------------------------------------------------

fn run_once(src: &str) -> String {
    let lines: Vec<&str> = src.lines().collect();

    let re_decl  = Regex::new(r"^(\s*)local\s+(_t\d+)\s*=\s*\{\}\s*$").unwrap();
    // String-keyed entry: _tN["key"] = VALUE  (VALUE is everything to end of line)
    let re_entry = Regex::new(
        r#"^(\s*)(_t\d+)\[("(?:[^"\\]|\\.)*")\]\s*=\s*(.+)$"#,
    ).unwrap();
    // Any table index on LHS (used to detect non-string-key entries)
    let re_any_lhs = Regex::new(r"^\s*(_t\d+)\[").unwrap();

    struct TableState {
        decl_idx:    usize,
        indent:      String,
        entries:     Vec<(usize, String, String)>, // (line_idx, key_literal, value)
        bad:         bool,
    }

    let mut tables: BTreeMap<String, TableState> = BTreeMap::new();
    // Track which lines are already claimed as entry lines (to avoid double-counting).
    let mut entry_lines_set: BTreeSet<usize> = BTreeSet::new();

    // --- Phase 1: collect declarations and entries ---
    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim_end();

        if let Some(caps) = re_decl.captures(trimmed) {
            let indent = caps[1].to_string();
            let tname  = caps[2].to_string();
            tables.insert(tname, TableState {
                decl_idx: i,
                indent,
                entries: Vec::new(),
                bad: false,
            });
            continue;
        }

        if let Some(caps) = re_entry.captures(trimmed) {
            let tname = caps[2].to_string();
            let key   = caps[3].to_string();
            let val   = caps[4].trim().to_string();
            if let Some(st) = tables.get_mut(&tname) {
                st.entries.push((i, key, val));
                entry_lines_set.insert(i);
                continue;
            }
        }

        // Non-string-keyed table write → mark that table as unprocessable.
        if let Some(caps) = re_any_lhs.captures(trimmed) {
            if !re_entry.is_match(trimmed) {
                let tname = caps[1].to_string();
                if let Some(st) = tables.get_mut(&tname) {
                    st.bad = true;
                }
            }
        }
    }

    // --- Phase 2: find use sites and build fold actions ---

    struct FoldAction {
        tname:       String,
        decl_line:   usize,
        entry_lines: Vec<usize>,
        use_line:    usize,    // the line where _tN appears as RHS
        constructor: String,   // replacement string for _tN at the use site
    }

    let mut actions: Vec<FoldAction> = Vec::new();

    for (tname, st) in &tables {
        if st.bad || st.entries.is_empty() { continue; }

        let my_entry_set: BTreeSet<usize> = st.entries.iter().map(|(i,_,_)| *i).collect();

        // Find lines that contain `_tN` as a whole word but are neither the
        // declaration nor an entry line for this table.
        let mut use_lines: Vec<usize> = Vec::new();
        for (i, line) in lines.iter().enumerate() {
            if i == st.decl_idx || my_entry_set.contains(&i) { continue; }
            if contains_word(line, tname) {
                use_lines.push(i);
            }
        }

        if use_lines.len() != 1 { continue; }

        let use_idx  = use_lines[0];
        let use_line = lines[use_idx];

        // Determine whether this is an "inner" use (value in another table entry)
        // or a "final" use (standalone variable assignment or similar).
        let is_inner_use = is_table_entry_rhs(use_line, tname);

        let constructor = build_constructor(&st.entries, &st.indent, use_line, is_inner_use);

        actions.push(FoldAction {
            tname: tname.clone(),
            decl_line:   st.decl_idx,
            entry_lines: st.entries.iter().map(|(i,_,_)| *i).collect(),
            use_line:    use_idx,
            constructor,
        });
    }

    if actions.is_empty() {
        return src.to_string();
    }

    // Bottom-up safety: if action A's entry line is the use_line of action B,
    // then folding A now would delete B's use site before B's constructor is
    // substituted.  Drop A from this pass; it will fold in the next iteration
    // after B's constructor has been inlined.
    let use_lines_set: BTreeSet<usize> = actions.iter().map(|a| a.use_line).collect();
    let actions: Vec<FoldAction> = actions.into_iter().filter(|a| {
        !a.entry_lines.iter().any(|el| use_lines_set.contains(el))
    }).collect();

    if actions.is_empty() {
        return src.to_string();
    }

    // --- Phase 3: apply actions ---
    // Build removal set and per-line replacements.
    let mut remove: BTreeSet<usize> = BTreeSet::new();
    // line_idx → list of (word_to_replace, replacement)
    let mut replacements: BTreeMap<usize, Vec<(String, String)>> = BTreeMap::new();

    for action in &actions {
        remove.insert(action.decl_line);
        for &el in &action.entry_lines {
            remove.insert(el);
        }
        replacements
            .entry(action.use_line)
            .or_default()
            .push((action.tname.clone(), action.constructor.clone()));
    }

    let mut out: Vec<String> = Vec::with_capacity(lines.len());
    for (i, line) in lines.iter().enumerate() {
        if remove.contains(&i) {
            continue;
        }
        let mut s = line.to_string();
        if let Some(repls) = replacements.get(&i) {
            for (word, ctor) in repls {
                s = replace_word(&s, word, ctor);
            }
        }
        out.push(s);
    }

    out.join("\n")
}

// ---------------------------------------------------------------------------
// Constructor building
// ---------------------------------------------------------------------------

/// Build the table constructor string for `entries`.
///
/// `is_inner` is true when the table will be used as a value inside another
/// table entry — in that case we use a compact single-line form so the outer
/// table's entry line stays as a single parseable line for the next iteration.
/// Otherwise (final assignment target) we emit a pretty multi-line form.
fn build_constructor(
    entries:  &[(usize, String, String)],
    _decl_indent: &str,
    use_line: &str,
    is_inner: bool,
) -> String {
    if is_inner {
        // Compact: {key1 = val1, key2 = val2, ...}
        let parts: Vec<String> = entries.iter()
            .map(|(_, key, val)| format!("{} = {}", format_key(key), val))
            .collect();
        format!("{{{}}}", parts.join(", "))
    } else {
        // Multi-line, indented to use-line level.
        let use_indent_len = use_line.len() - use_line.trim_start().len();
        let use_indent = &use_line[..use_indent_len];
        let inner = format!("{}  ", use_indent);
        let mut s = String::from("{\n");
        for (_, key, val) in entries {
            s.push_str(&format!("{}{} = {},\n", inner, format_key(key), val));
        }
        s.push_str(&format!("{}}}", use_indent));
        s
    }
}

/// Format a Lua string key literal as a table-constructor key.
/// `"HP"` → `HP`   (bare identifier)
/// `"Yi Sun-shin"` → `["Yi Sun-shin"]`   (bracket form)
fn format_key(key_literal: &str) -> String {
    // Strip outer quotes and unescape just enough to check identifier validity.
    let inner = lua_string_content(key_literal);
    if is_lua_ident(&inner) {
        inner
    } else {
        format!("[{}]", key_literal)
    }
}

/// Return the content of a Lua double-quoted string literal (outer quotes stripped,
/// no full unescaping — just enough to recognise simple identifiers).
fn lua_string_content(quoted: &str) -> String {
    let s = quoted.strip_prefix('"').unwrap_or(quoted);
    let s = s.strip_suffix('"').unwrap_or(s);
    // For identifier checking we only need the unescaped bytes; if there are
    // any backslash escapes the string can't be a plain identifier anyway.
    s.to_string()
}

fn is_lua_ident(s: &str) -> bool {
    if s.is_empty() { return false; }
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    for c in chars {
        if !c.is_ascii_alphanumeric() && c != '_' { return false; }
    }
    // Reject Lua keywords.
    !matches!(s,
        "and"|"break"|"do"|"else"|"elseif"|"end"|"false"|"for"|"function"|
        "goto"|"if"|"in"|"local"|"nil"|"not"|"or"|"repeat"|"return"|"then"|
        "true"|"until"|"while"
    )
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// True if `line` is of the form `_tM["k"] = TNAME` (the table being folded
/// appears as the RHS of another table's string-keyed entry).
fn is_table_entry_rhs(line: &str, tname: &str) -> bool {
    let pat = format!(
        r#"^\s*_t\d+\["(?:[^"\\]|\\.)*"\]\s*=\s*{}\s*$"#,
        regex::escape(tname)
    );
    Regex::new(&pat).map_or(false, |re| re.is_match(line.trim_end()))
}

/// True iff `word` appears as a whole word (not preceded/followed by
/// identifier characters) somewhere in `text`.
fn contains_word(text: &str, word: &str) -> bool {
    let mut start = 0;
    while let Some(pos) = text[start..].find(word) {
        let abs = start + pos;
        if is_word_boundary(text, abs, word.len()) {
            return true;
        }
        start = abs + 1;
    }
    false
}

/// Replace the first (and typically only) whole-word occurrence of `word`
/// in `text` with `replacement`.
fn replace_word(text: &str, word: &str, replacement: &str) -> String {
    let mut result = String::with_capacity(text.len() + replacement.len());
    let mut start = 0;
    let mut replaced = false;
    while let Some(pos) = text[start..].find(word) {
        let abs = start + pos;
        if is_word_boundary(text, abs, word.len()) && !replaced {
            result.push_str(&text[start..abs]);
            result.push_str(replacement);
            start = abs + word.len();
            replaced = true;
        } else {
            result.push_str(&text[start..abs + 1]);
            start = abs + 1;
        }
    }
    result.push_str(&text[start..]);
    result
}

fn is_word_boundary(text: &str, start: usize, len: usize) -> bool {
    let end = start + len;
    let bytes = text.as_bytes();
    let before_ok = start == 0 || {
        let b = bytes[start - 1];
        !b.is_ascii_alphanumeric() && b != b'_'
    };
    let after_ok = end >= text.len() || {
        let b = bytes[end];
        !b.is_ascii_alphanumeric() && b != b'_'
    };
    before_ok && after_ok
}
