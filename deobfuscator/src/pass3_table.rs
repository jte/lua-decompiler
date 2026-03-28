/// Pass 3 – Lookup-table resolution.
///
/// Detects the 256-entry identity character table (e.g. `_t14`) that maps
/// index N (1-based) to the character with code point N-1.  Replaces all
/// `_tVAR[N]` references with the corresponding Lua string literal.
use regex::Regex;

pub fn run(src: &str) -> String {
    let table_var = match find_lookup_table_var(src) {
        Some(v) => v,
        None => return src.to_string(),
    };

    // Build char map: index 1..=256 → Lua string literal
    let char_map: Vec<String> = (0u8..=255u8).map(lua_char_literal).collect();

    // Replace _tVAR[N] (literal integer index) with the character.
    // Use a word-char prefix group to avoid matching inside longer identifiers.
    let pat = format!(r"(?:^|(?P<pre>[^a-zA-Z0-9_])){}(?:\[(\d+)\])", regex::escape(&table_var));
    let re = Regex::new(&pat).unwrap();
    re.replace_all(src, |caps: &regex::Captures| {
        let pre = caps.name("pre").map_or("", |m| m.as_str());
        let idx: usize = caps[2].parse().unwrap_or(0);
        if idx >= 1 && idx <= 256 {
            format!("{}{}", pre, char_map[idx - 1])
        } else {
            caps[0].to_string()
        }
    })
    .to_string()
}

/// Scan source for a local table that starts with `"\x00"` as its first
/// element – the hallmark of the 256-char identity table.
fn find_lookup_table_var(src: &str) -> Option<String> {
    let re_decl = Regex::new(r#"local (_t\d+) = \{"#).unwrap();
    let lines: Vec<&str> = src.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if let Some(caps) = re_decl.captures(line) {
            // The very next line should contain "\x00" as the first entry
            if let Some(next) = lines.get(i + 1) {
                if next.contains(r#""\x00""#) {
                    return Some(caps[1].to_string());
                }
            }
        }
    }
    None
}

fn lua_char_literal(c: u8) -> String {
    match c {
        b'\t' => "\"\\t\"".to_string(),
        b'\n' => "\"\\n\"".to_string(),
        b'\r' => "\"\\r\"".to_string(),
        b'\\' => "\"\\\\\"".to_string(),
        b'"' => "\"\\\"\"".to_string(),
        0x20..=0x7e => format!("\"{}\"", c as char),
        _ => format!("\"\\x{:02X}\"", c),
    }
}
