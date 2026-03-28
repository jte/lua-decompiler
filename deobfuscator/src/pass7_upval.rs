/// Pass 7 – Upvalue / field-access resolution.
///
/// `_upvN["global"]`  →  `global`   (for known Lua standard-library names)
/// `module["field"]`  →  `module.field`  (after the above substitution)
use regex::Regex;

const LUA_GLOBALS: &[&str] = &[
    "string", "table", "io", "os", "math", "debug", "package", "coroutine",
    "utf8", "bit32", "type", "tostring", "tonumber", "print", "next",
    "ipairs", "pairs", "select", "error", "assert", "pcall", "xpcall",
    "rawget", "rawset", "rawequal", "rawlen", "require", "load", "loadfile",
    "dofile", "collectgarbage", "setmetatable", "getmetatable", "unpack",
];

pub fn run(src: &str) -> String {
    // Step 1: _upvN["name"] → name  (only for known globals)
    let re_upv = Regex::new(r#"_upv\d+\["([^"]+)"\]"#).unwrap();
    let s = re_upv.replace_all(src, |caps: &regex::Captures| {
        let name = &caps[1];
        if LUA_GLOBALS.contains(&name) {
            name.to_string()
        } else {
            caps[0].to_string()
        }
    });

    // Step 2: known_module["field"] → known_module.field
    // Only applies when the object is a recognised Lua standard-library name.
    let globals_alternation = LUA_GLOBALS.join("|");
    let pat = format!(r#"(?P<obj>{})(?:\["([a-zA-Z_]\w*)"\])"#, globals_alternation);
    let re_field = Regex::new(&pat).unwrap();
    let s = re_field.replace_all(&s, |caps: &regex::Captures| {
        format!("{}.{}", &caps["obj"], caps.get(2).map_or("", |m| m.as_str()))
    });

    s.to_string()
}
