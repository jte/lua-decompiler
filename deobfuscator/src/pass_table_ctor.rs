/// Table-constructor collapsing pass.
///
/// Rewrites the common obfuscation pattern
///
/// ```lua
/// local _t359 = {}
/// _acc25 = 74          -- plain (non-local) integer assignments
/// _acc26 = 44
/// ...
/// _t359[1] = _acc25    -- sequential index population
/// _t359[2] = _acc26
/// _t359[9] = 81        -- may also be direct literals
/// ```
///
/// into the compact form
///
/// ```lua
/// local _t359 = {74, 44, ..., 81, ...}
/// ```
///
/// The plain integer-assignment lines (`_acc25 = 74`, etc.) are **kept** – they
/// may feed other tables or be used elsewhere.  Only the `_tN[M] = EXPR` entry
/// lines are removed.
///
/// A table is collapsed only when:
///   - every entry index forms a gap-free sequence starting at 1, and
///   - every right-hand-side value is resolvable to an integer literal
///     (either directly or via the most-recently-seen assignment to that name).
use regex::Regex;
use std::collections::HashMap;

pub fn run(src: &str) -> String {
    let lines: Vec<&str> = src.lines().collect();

    let re_decl   = Regex::new(r"^(\s*)local\s+(_t\d+)\s*=\s*\{\}\s*$").unwrap();
    // plain assignment: _NAME = INTEGER  (no `local`, no indexing)
    let re_int_assign = Regex::new(r"^\s*(_\w+)\s*=\s*(-?\d+)\s*$").unwrap();
    // table entry: _tN[M] = NAME_OR_INT
    let re_entry  = Regex::new(r"^\s*(_t\d+)\[(\d+)\]\s*=\s*(-?[\w]+)\s*$").unwrap();

    // Current known integer value for each named variable.
    let mut val_ctx: HashMap<String, i64> = HashMap::new();

    // Per-table build state.
    #[derive(Default)]
    struct Build {
        decl_line:   usize,
        indent:      String,
        entries:     HashMap<usize, i64>,   // index → resolved value
        entry_lines: Vec<usize>,            // line indices to be removed
        bad:         bool,                  // unresolvable entry encountered
    }
    let mut tables: HashMap<String, Build> = HashMap::new();

    for (i, line) in lines.iter().enumerate() {
        // Table declaration
        if let Some(caps) = re_decl.captures(line) {
            let tname = caps[2].to_string();
            tables.insert(tname, Build {
                decl_line: i,
                indent: caps[1].to_string(),
                ..Default::default()
            });
            continue;
        }

        // Plain integer assignment → update value context
        if let Some(caps) = re_int_assign.captures(line) {
            let name: String = caps[1].to_string();
            let val: i64     = caps[2].parse().unwrap_or(0);
            val_ctx.insert(name, val);
            // (do NOT continue – may also be an entry line below, but that
            //  pattern has `[`, so it won't match re_int_assign anyway)
        }

        // Table entry assignment
        if let Some(caps) = re_entry.captures(line) {
            let tname     = caps[1].to_string();
            let idx: usize = caps[2].parse().unwrap_or(0);
            let rhs        = &caps[3];

            if let Some(build) = tables.get_mut(&tname) {
                let value: Option<i64> = rhs.parse::<i64>().ok()
                    .or_else(|| val_ctx.get(rhs).copied());

                match value {
                    Some(v) => { build.entries.insert(idx, v); build.entry_lines.push(i); }
                    None    => { build.bad = true; }
                }
            }
        }
    }

    // Decide which tables to collapse
    let mut remove:  std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut replace: HashMap<usize, String>             = HashMap::new();

    for (tname, build) in &tables {
        if build.bad || build.entries.is_empty() { continue; }

        let max_idx = match build.entries.keys().copied().max() { Some(m) => m, None => continue };
        // Require gap-free 1..=max_idx
        let values: Option<Vec<i64>> = (1..=max_idx)
            .map(|k| build.entries.get(&k).copied())
            .collect();
        let values = match values { Some(v) => v, None => continue };

        let constructor = format!(
            "{}local {} = {{{}}}",
            build.indent,
            tname,
            values.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")
        );
        replace.insert(build.decl_line, constructor);
        for &el in &build.entry_lines {
            remove.insert(el);
        }
    }

    // Emit
    lines.iter().enumerate().filter_map(|(i, line)| {
        if remove.contains(&i) {
            None
        } else if let Some(replacement) = replace.get(&i) {
            Some(replacement.clone())
        } else {
            Some(line.to_string())
        }
    })
    .collect::<Vec<_>>()
    .join("\n")
}
