/// Pass 5 – Permutation-table resolution.
///
/// After Pass 1 + Pass 2 have folded constants, some tables are fully known:
///
///   local _t323 = {}
///   _t323[1] = 27
///   _t323[2] = 43
///   ...
///
/// This pass collects such integer-only tables and substitutes `_tN[M]` with
/// the known value wherever M is a literal integer index.
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};

pub fn run(src: &str) -> String {
    let tables = collect_integer_tables(src);
    if tables.is_empty() {
        return src.to_string();
    }
    substitute(src, &tables)
}

/// Returns `table_name → { index → value }` for tables whose every entry is
/// an integer literal assigned via `_tN[M] = VALUE`.
fn collect_integer_tables(src: &str) -> BTreeMap<String, BTreeMap<usize, i64>> {
    let re_entry = Regex::new(r"^\s*(_t\d+)\[(\d+)\]\s*=\s*(-?\d+)\s*$").unwrap();
    let re_decl  = Regex::new(r"^\s*local\s+(_t\d+)\s*=\s*\{\}\s*$").unwrap();

    // Find all locally-declared empty tables
    let mut known: BTreeSet<String> = BTreeSet::new();
    for line in src.lines() {
        if let Some(c) = re_decl.captures(line) {
            known.insert(c[1].to_string());
        }
    }

    // Collect entries
    let mut tables: BTreeMap<String, BTreeMap<usize, i64>> = BTreeMap::new();
    for line in src.lines() {
        if let Some(c) = re_entry.captures(line) {
            let tname = c[1].to_string();
            if known.contains(&tname) {
                let idx: usize = c[2].parse().unwrap_or(0);
                let val: i64   = c[3].parse().unwrap_or(0);
                tables.entry(tname).or_default().insert(idx, val);
            }
        }
    }

    // Filter out tables that have any non-integer entry assignment.
    // re_entry only matched integer values, so any _tN[M] = NON_INT line taints the table.
    let re_any_entry = Regex::new(r"^\s*(_t\d+)\[(\d+)\]\s*=\s*(.+)$").unwrap();
    let re_int_val   = Regex::new(r"^-?\d+$").unwrap();
    let mut tainted: BTreeSet<String> = BTreeSet::new();
    for line in src.lines() {
        if let Some(c) = re_any_entry.captures(line) {
            let tname = c[1].to_string();
            let val   = c[3].trim();
            if !re_int_val.is_match(val) {
                tainted.insert(tname);
            }
        }
    }
    tables.retain(|name, _| !tainted.contains(name));
    tables
}

fn substitute(src: &str, tables: &BTreeMap<String, BTreeMap<usize, i64>>) -> String {
    let mut s = src.to_string();
    for (tname, entries) in tables {
        let pat = format!(r"(?:^|(?P<pre>[^a-zA-Z0-9_])){}(?:\[(\d+)\])", regex::escape(tname));
        let re = Regex::new(&pat).unwrap();
        s = re.replace_all(&s, |caps: &regex::Captures| {
            let pre = caps.name("pre").map_or("", |m| m.as_str());
            let idx: usize = caps[2].parse().unwrap_or(0);
            match entries.get(&idx) {
                Some(&v) => format!("{}{}", pre, v),
                None => caps[0].to_string(),
            }
        }).to_string();
    }
    s
}
