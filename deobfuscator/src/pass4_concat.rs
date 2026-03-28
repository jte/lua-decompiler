/// Pass 4 – String-concatenation collapse.
///
/// Collapses sequences of the form:
///
///   local _NAME = ""
///   _NAME = _NAME .. "a"
///   _NAME = _NAME .. "b"
///   ...
///
/// into a single:
///
///   local _NAME = "ab..."
///
/// Works on string literals only (no variable operands in the concat).

pub fn run(src: &str) -> String {
    let lines: Vec<String> = src.lines().map(|l| l.to_string()).collect();
    let mut out: Vec<String> = Vec::with_capacity(lines.len());
    let mut i = 0;

    while i < lines.len() {
        // Look for `local _NAME = ""`  (empty string seed)
        if let Some((name, indent)) = is_empty_string_decl(&lines[i]) {
            // Greedily consume `_NAME = _NAME .. "LITERAL"` lines
            let mut accumulated = String::new();
            let mut j = i + 1;
            while j < lines.len() {
                if let Some(piece) = is_concat_step(&lines[j], &name) {
                    accumulated.push_str(&piece);
                    j += 1;
                } else {
                    break;
                }
            }
            if j > i + 1 {
                // Emit the collapsed declaration and skip consumed lines
                out.push(format!("{}local {} = \"{}\"", indent, name, accumulated));
                i = j;
                continue;
            }
        }
        out.push(lines[i].clone());
        i += 1;
    }

    out.join("\n")
}

/// Returns `(name, indent)` if the line is `local NAME = ""`
fn is_empty_string_decl(line: &str) -> Option<(String, String)> {
    let trimmed = line.trim_start();
    let indent = &line[..line.len() - trimmed.len()];
    let rest = trimmed.strip_prefix("local ")?;
    let eq = rest.find(" = \"\"")?;
    let name = rest[..eq].trim().to_string();
    if name.starts_with('_') {
        Some((name, indent.to_string()))
    } else {
        None
    }
}

/// Returns the string piece if the line is `NAME = NAME .. "PIECE"` (no escapes)
fn is_concat_step(line: &str, name: &str) -> Option<String> {
    let trimmed = line.trim();
    // Expected: `NAME = NAME .. "..."`
    let prefix = format!("{} = {} .. \"", name, name);
    let rest = trimmed.strip_prefix(prefix.as_str())?;
    let piece = rest.strip_suffix('"')?;
    // Reject if the piece contains backslash escapes we can't flatten safely
    if piece.contains('\\') {
        return None;
    }
    Some(piece.to_string())
}
