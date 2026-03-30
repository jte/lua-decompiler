/// Pass – Inline single-use local table declarations.
///
/// Finds patterns of the form:
///
/// ```lua
/// local _tNNNN = { ... }   ← declaration (single- or multi-line)
/// ...
/// somevar[k] = _tNNNN      ← exactly one use as RHS of assignment
/// ```
///
/// and replaces them with:
///
/// ```lua
/// somevar[k] = { ... }
/// ```
///
/// removing the `local _tNNNN = { ... }` declaration entirely.
///
/// Conditions for inlining:
///   - The variable name matches `_t\d+`.
///   - The name appears exactly twice in the source: once in the declaration
///     and once at the use site.
///   - The use site is a plain assignment RHS: preceded by `= ` and not part
///     of `==`, `~=`, `<=`, `>=`.
///   - The declaration is either a single-line `local _tN = { ... }` or a
///     multi-line block `local _tN = {\n...\n}`.

use regex::Regex;

pub fn run(src: &str) -> String {
    // Iterate to a fixed point: each pass may inline one or more variables.
    // In practice one pass should be sufficient, but iterating is safe.
    let mut s = src.to_string();
    loop {
        let next = run_once(&s);
        if next == s {
            break;
        }
        s = next;
    }
    s
}

fn run_once(src: &str) -> String {
    let decls = collect_decls(src);
    if decls.is_empty() {
        return src.to_string();
    }

    // Build list of (decl_start, decl_end, name, body_expr) where
    // the name appears exactly twice in source (decl + one use) and the use
    // is a plain assignment RHS.
    let mut replacements: Vec<(usize, usize, String, String)> = Vec::new();

    for d in &decls {
        if !is_single_use(src, &d.name) {
            continue;
        }
        if let Some(use_pos) = find_rhs_use(src, &d.name) {
            // Exclude the occurrence inside the declaration itself.
            if use_pos >= d.decl_start && use_pos < d.decl_end {
                continue;
            }
            replacements.push((d.decl_start, d.decl_end, d.name.clone(), d.body_expr.clone()));
        }
    }

    if replacements.is_empty() {
        return src.to_string();
    }

    // Apply replacements: first substitute uses (right-to-left by use position),
    // then delete declarations (right-to-left by declaration position).
    // We do this in two passes to avoid offset invalidation.

    // Collect use positions for substitution.
    let mut use_subs: Vec<(usize, usize, String)> = Vec::new();
    for (_, _, name, body_expr) in &replacements {
        if let Some(use_pos) = find_rhs_use(src, name) {
            // Use position is the start of the name in src.
            let use_end = use_pos + name.len();
            use_subs.push((use_pos, use_end, body_expr.clone()));
        }
    }

    // Collect declaration removals.
    let del_ranges: Vec<(usize, usize)> = replacements
        .iter()
        .map(|(s, e, _, _)| (*s, *e))
        .collect();

    // Combine and apply right-to-left.
    let mut all_edits: Vec<(usize, usize, String)> = Vec::new();
    for (s, e, rep) in use_subs {
        all_edits.push((s, e, rep));
    }
    for (s, e) in del_ranges {
        all_edits.push((s, e, String::new()));
    }

    // Sort right-to-left by start position, with deletions before substitutions
    // at the same position (so the substitution offset isn't shifted by the delete).
    all_edits.sort_by(|a, b| {
        b.0.cmp(&a.0).then_with(|| a.2.len().cmp(&b.2.len()))
    });

    let mut result = src.to_string();
    for (start, end, rep) in all_edits {
        if start <= end && end <= result.len() {
            result.replace_range(start..end, &rep);
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Declaration collection
// ---------------------------------------------------------------------------

struct Decl {
    /// Byte offset of the start of the `local _tN` line.
    decl_start: usize,
    /// Byte offset just past the closing `}` line (including its `\n`).
    decl_end: usize,
    /// Variable name, e.g. `_t8650`.
    name: String,
    /// The table constructor expression to inline, e.g. `{\n  300, 392,\n}`.
    body_expr: String,
}

fn collect_decls(src: &str) -> Vec<Decl> {
    let mut result = Vec::new();

    // Build line table.
    let mut lines: Vec<(usize, &str)> = Vec::new();
    let mut offset = 0usize;
    for line in src.split('\n') {
        lines.push((offset, line.trim_end_matches('\r')));
        offset += line.len() + 1;
    }

    // Single-line: `local _tNNNN = { ... }`
    let re_single = Regex::new(r"^\s*local\s+(_t\d+)\s*=\s*(\{[^}]*\})\s*$").unwrap();
    // Multi-line open: `local _tNNNN = {`
    let re_open = Regex::new(r"^\s*local\s+(_t\d+)\s*=\s*\{\s*$").unwrap();

    let mut i = 0;
    while i < lines.len() {
        let (line_start, line) = lines[i];

        // Single-line form.
        if let Some(caps) = re_single.captures(line) {
            let name = caps[1].to_string();
            let body_expr = caps[2].to_string();
            let line_end = (line_start + line.len() + 1).min(src.len());
            result.push(Decl {
                decl_start: line_start,
                decl_end: line_end,
                name,
                body_expr,
            });
            i += 1;
            continue;
        }

        // Multi-line form: collect until closing `}`.
        if let Some(caps) = re_open.captures(line) {
            let name = caps[1].to_string();
            let decl_start = line_start;

            // Determine indentation of the opening line (for the closing `}`).
            let open_indent = line.len() - line.trim_start().len();

            let mut body_lines: Vec<&str> = Vec::new();
            body_lines.push("{");
            i += 1;
            let mut found_close = false;
            while i < lines.len() {
                let (close_start, l) = lines[i];
                let l_trimmed = l.trim();
                // The closing `}` must be at the same indentation as the opening line,
                // possibly followed by a comma or nothing.
                let l_indent = l.len() - l.trim_start().len();
                if l_trimmed == "}" || l_trimmed == "}," {
                    if l_indent == open_indent || l_trimmed == "}" || l_trimmed == "}," {
                        let decl_end = (close_start + l.len() + 1).min(src.len());
                        body_lines.push(l_trimmed);
                        let body_expr = body_lines.join("\n");
                        result.push(Decl {
                            decl_start,
                            decl_end,
                            name,
                            body_expr,
                        });
                        found_close = true;
                        i += 1;
                        break;
                    }
                }
                body_lines.push(l_trimmed);
                i += 1;
            }
            if !found_close {
                // Malformed — skip.
            }
            continue;
        }

        i += 1;
    }

    result
}

// ---------------------------------------------------------------------------
// Use-site detection
// ---------------------------------------------------------------------------

/// Return true iff `name` appears exactly twice as a whole word in `src`
/// (once in the declaration and once at the use site).
fn is_single_use(src: &str, name: &str) -> bool {
    count_word_occurrences(src, name) == 2
}

fn count_word_occurrences(src: &str, name: &str) -> usize {
    let mut count = 0;
    let mut start = 0;
    while let Some(pos) = src[start..].find(name) {
        let abs = start + pos;
        if is_word_boundary(src, abs, name.len()) {
            count += 1;
        }
        start = abs + 1;
    }
    count
}

fn is_word_boundary(src: &str, start: usize, len: usize) -> bool {
    let end = start + len;
    let before_ok = start == 0 || {
        let b = src.as_bytes()[start - 1];
        !b.is_ascii_alphanumeric() && b != b'_'
    };
    let after_ok = end >= src.len() || {
        let b = src.as_bytes()[end];
        !b.is_ascii_alphanumeric() && b != b'_'
    };
    before_ok && after_ok
}

/// Find the byte position of the use of `name` as an assignment RHS.
/// The use must be preceded (ignoring whitespace) by a bare `=` (not `==`,
/// `~=`, `<=`, `>=`).
fn find_rhs_use(src: &str, name: &str) -> Option<usize> {
    let mut start = 0;
    while let Some(pos) = src[start..].find(name) {
        let abs = start + pos;
        if is_word_boundary(src, abs, name.len()) && is_rhs_position(src, abs) {
            return Some(abs);
        }
        start = abs + 1;
    }
    None
}

/// Return true iff the character immediately preceding `pos` (skipping
/// whitespace) is a bare `=` (not `==`, `~=`, `<=`, `>=`).
fn is_rhs_position(src: &str, pos: usize) -> bool {
    if pos == 0 {
        return false;
    }
    let before = &src[..pos];
    let trimmed = before.trim_end();
    if trimmed.is_empty() {
        return false;
    }
    let last_bytes = trimmed.as_bytes();
    let n = last_bytes.len();
    // Must end with `=`.
    if last_bytes[n - 1] != b'=' {
        return false;
    }
    // Must not be `==`, `~=`, `<=`, `>=`.
    if n >= 2 {
        let prev = last_bytes[n - 2];
        if prev == b'=' || prev == b'~' || prev == b'<' || prev == b'>' {
            return false;
        }
    }
    true
}
