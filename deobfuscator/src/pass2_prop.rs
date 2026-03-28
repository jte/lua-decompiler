/// Pass 2 – Constant propagation.
///
/// Finds `local _NAME = LITERAL` single-assignment locals and replaces every
/// use of `_NAME` with the literal value.  Only propagates integer/float
/// literals and simple single-quoted or double-quoted string literals that
/// contain no embedded quotes.  Variables that are ever reassigned are skipped.
use regex::Regex;
use std::collections::HashMap;

pub fn run(src: &str) -> String {
    let consts = collect_consts(src);
    if consts.is_empty() {
        return src.to_string();
    }
    substitute(src, &consts)
}

/// Returns `name → literal_expr` for safe single-assignment locals.
fn collect_consts(src: &str) -> HashMap<String, String> {
    let re_decl = Regex::new(
        r#"(?m)^\s*local\s+(_[a-zA-Z]\w*)\s*=\s*(-?\d+(?:\.\d+)?|"[^"\\]*")\s*$"#,
    )
    .unwrap();
    // Plain assignment: line that contains `_NAME =` but does NOT start with `local`
    let re_assign = Regex::new(r"^\s*(_[a-zA-Z]\w*)\s*=").unwrap();

    // Collect declarations
    let mut decls: HashMap<String, String> = HashMap::new();
    for caps in re_decl.captures_iter(src) {
        decls.insert(caps[1].to_string(), caps[2].to_string());
    }

    // Find all names that are reassigned (line starts with `_NAME =`, not `local`)
    let mut reassigned: std::collections::HashSet<String> = std::collections::HashSet::new();
    for line in src.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("local ") {
            continue; // skip declarations
        }
        if let Some(caps) = re_assign.captures(trimmed) {
            reassigned.insert(caps[1].to_string());
        }
    }

    // Keep only names declared exactly once and never plain-reassigned
    decls.retain(|name, _| !reassigned.contains(name));
    decls
}

fn substitute(src: &str, consts: &HashMap<String, String>) -> String {
    let mut s = src.to_string();
    for (name, value) in consts {
        // Replace word-boundary occurrences of `name` that are not in a `local NAME =` declaration line
        let pat = format!(r"\b{}\b", regex::escape(name));
        let re = Regex::new(&pat).unwrap();
        // Skip lines that declare the variable itself
        let decl_prefix = format!("local {} =", name);
        let lines: Vec<String> = s
            .lines()
            .map(|line| {
                if line.trim_start().starts_with(decl_prefix.as_str()) {
                    line.to_string()
                } else {
                    re.replace_all(line, value.as_str()).to_string()
                }
            })
            .collect();
        s = lines.join("\n");
    }
    s
}
