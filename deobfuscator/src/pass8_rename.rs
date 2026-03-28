/// Pass 8 – Variable renaming.
///
/// Renames `_accN` and `_vN` variables that were assigned a known Lua
/// standard-library module to the module name itself (e.g. `_acc3` → `string`).
/// Only safe because the module name is a global and the _acc variable is
/// local – there can be no conflict after we've inlined it everywhere.
///
/// Also strips orphaned `local _accN = MODULE` declarations left over after
/// substitution.
use regex::Regex;
use std::collections::HashMap;

const LUA_GLOBALS: &[&str] = &[
    "string", "table", "io", "os", "math", "debug", "package", "coroutine",
    "utf8", "bit32",
];

pub fn run(src: &str) -> String {
    let renames = collect_module_renames(src);
    if renames.is_empty() {
        return src.to_string();
    }
    let s = apply_renames(src, &renames);
    remove_trivial_decls(&s, &renames)
}

/// Find `local _NAME = MODULE` where MODULE is a known Lua global AND the
/// variable is never subsequently reassigned.
fn collect_module_renames(src: &str) -> HashMap<String, String> {
    let globals_alt = LUA_GLOBALS.join("|");
    let pat = format!(
        r"(?m)^\s*local\s+(_(?:acc|v)\d+)\s*=\s*({})\s*$",
        globals_alt
    );
    let re = Regex::new(&pat).unwrap();
    let re_assign = Regex::new(r"^\s*(_[a-zA-Z]\w*)\s*=").unwrap();

    let mut map = HashMap::new();
    for caps in re.captures_iter(src) {
        map.insert(caps[1].to_string(), caps[2].to_string());
    }

    // Remove any name that is ever plain-reassigned (not via `local`)
    let mut reassigned = std::collections::HashSet::new();
    for line in src.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("local ") {
            continue;
        }
        if let Some(c) = re_assign.captures(trimmed) {
            reassigned.insert(c[1].to_string());
        }
    }
    map.retain(|name, _| !reassigned.contains(name));
    map
}

fn apply_renames(src: &str, renames: &HashMap<String, String>) -> String {
    let mut s = src.to_string();
    for (old, new) in renames {
        let re = Regex::new(&format!(r"\b{}\b", regex::escape(old))).unwrap();
        s = re.replace_all(&s, new.as_str()).to_string();
    }
    s
}

/// After renaming, lines like `local string = string` are trivially redundant.
fn remove_trivial_decls(src: &str, renames: &HashMap<String, String>) -> String {
    let lines: Vec<&str> = src.lines().collect();
    let trivial: std::collections::HashSet<String> = renames
        .values()
        .map(|m| format!("local {} = {}", m, m))
        .collect();
    lines
        .into_iter()
        .filter(|l| !trivial.contains(l.trim()))
        .collect::<Vec<_>>()
        .join("\n")
}
