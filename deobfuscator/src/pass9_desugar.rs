/// Pass 9 – Global-environment desugaring.
///
/// Runs at the very end of the pipeline, after all table substitutions are done.
///
/// ## Transforms (iterated to a fixed point)
///
/// 1. `_upv0["X"]["Y"]` → `X.Y`   — two-level upvalue access (handles the
///    `_upv0["gg"]["makeRequest"]` pattern directly)
/// 2. `_upv0["X"]`      → `X`     — single-level upvalue access
/// 3. `X["Y"]`          → `X.Y`   — bracket-to-dot for any identifier (or
///    dotted-identifier) base; excludes internal `_tNNN` obfuscation tables
///
/// After iteration converges:
///
/// 4. `_upv0` → `_G`  — any bare upvalue reference that couldn't be desugared

use regex::Regex;

pub fn run(src: &str) -> String {
    // These regexes are cheap to compile and this function is called once.
    let re_two = Regex::new(
        r#"_upv0\["([a-zA-Z_]\w*)"\]\["([a-zA-Z_]\w*)"\]"#,
    ).unwrap();
    let re_one = Regex::new(
        r#"_upv0\["([a-zA-Z_]\w*)"\]"#,
    ).unwrap();
    // Base is a plain identifier OR a dotted chain like `_G.gg`, `foo.bar.baz`.
    // Key must be a valid Lua identifier (letters/digits/underscore).
    let re_field = Regex::new(
        r#"([a-zA-Z_]\w*(?:\.[a-zA-Z_]\w*)*)\["([a-zA-Z_]\w*)"\]"#,
    ).unwrap();
    let re_bare = Regex::new(r"\b_upv0\b").unwrap();

    let mut s = src.to_string();

    // Iterate steps 1–3 until the source stabilises.  Each round can expose new
    // opportunities: e.g. resolving `_upv0["gg"]` → `gg` lets step 3 convert
    // `gg["makeRequest"]` → `gg.makeRequest` in the next pass.
    for _ in 0..10 {
        let before = s.clone();

        // Step 1: _upv0["X"]["Y"] → X.Y
        s = re_two.replace_all(&s, "$1.$2").into_owned();

        // Step 2: _upv0["X"] → X
        s = re_one.replace_all(&s, "$1").into_owned();

        // Step 3: base["Y"] → base.Y  (skip internal _tNNN tables)
        s = re_field.replace_all(&s, |caps: &regex::Captures| {
            let base = &caps[1];
            if is_internal_table(base) {
                caps[0].to_string()
            } else {
                format!("{}.{}", base, &caps[2])
            }
        }).into_owned();

        if s == before {
            break;
        }
    }

    // Step 4: any remaining bare _upv0 → _G
    re_bare.replace_all(&s, "_G").into_owned()
}

/// Returns true when `base` (the first dotted component) looks like an internal
/// obfuscation table name (`_t` followed only by digits, e.g. `_t8845`).
/// These still use string keys that are NOT valid Lua identifiers, so we must
/// not convert their bracket accesses to dot notation.
fn is_internal_table(base: &str) -> bool {
    let first = base.split('.').next().unwrap_or(base);
    match first.strip_prefix("_t") {
        Some(rest) => !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()),
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_desugar() {
        let input = concat!(
            "_upv0[\"gg\"][\"makeRequest\"](\"test\")\n",
            "_upv0[\"gg\"][\"searchNumber\"](4, x)\n",
            "_upv0[\"ThanhDieuPlus\"] = _f0\n",
            "_upv0[\"c\"] = debug.traceback()\n",
            "if _upv0[\"_G\"][\"gg\"][\"getFile\"]() then end\n",
            "local x = _upv0\n",
            "_t8845[\"somekey\"] = val\n",
        );
        let out = run(input);
        assert!(out.contains("gg.makeRequest("), "two-level: {}", out);
        assert!(out.contains("gg.searchNumber("), "two-level 2: {}", out);
        assert!(out.contains("ThanhDieuPlus = _f0"), "single-level: {}", out);
        assert!(out.contains("c = debug.traceback()"), "single-level c: {}", out);
        assert!(out.contains("_G.gg.getFile()"), "three-level: {}", out);
        assert!(out.contains("local x = _G"), "bare _upv0: {}", out);
        assert!(out.contains("_t8845[\"somekey\"]"), "internal table preserved: {}", out);
    }
}
