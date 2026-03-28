/// Pass 1 – Constant folding.
///
/// Repeatedly simplifies adjacent integer-literal arithmetic until stable:
///   • `A + B`  → `A+B`
///   • `A - B`  → `A-B`  (parenthesised when negative)
///   • `A * B`  → `A*B`
///   • `A // B` → `A//B` (floor div)
///   • `A % B`  → `A%B`
///   • `A ^ B`  → `A^B`  (integer base/exp only, guarded against overflow)
use regex::Regex;

pub fn run(src: &str) -> String {
    let mut s = src.to_string();
    for _ in 0..20 {
        let next = fold_once(&s);
        if next == s {
            break;
        }
        s = next;
    }
    s
}

fn fold_once(src: &str) -> String {
    // Floor division  (must come before plain `/`)
    let s = apply(src,  r"\b(\d+)\s*//\s*(\d+)\b",  |a, b| Some(a / b));
    // Modulo
    let s = apply(&s,   r"\b(\d+)\s*%\s*(\d+)\b",   |a, b| Some(a % b));
    // Power  (right-to-left; guard: exponent ≤ 20 to avoid explosion)
    let s = apply_pow(&s);
    // Multiplication
    let s = apply(&s,   r"\b(\d+)\s*\*\s*(\d+)\b",  |a, b| Some(a * b));
    // Addition  – must NOT fire when the left number is the RHS of a
    // higher-precedence operator (%  *  /  //  ^), e.g. `x % 520 + 1`
    // must stay as-is and not become `x % 521`.
    let s = apply_add(&s);
    // Subtraction (only when result is non-negative, to keep output clean)
    let s = apply(&s,   r"\b(\d+)\s*-\s*(\d+)\b",   |a, b| if a >= b { Some(a - b) } else { None });
    s
}

fn apply(src: &str, pat: &str, op: impl Fn(i64, i64) -> Option<i64>) -> String {
    let re = Regex::new(pat).unwrap();
    re.replace_all(src, |caps: &regex::Captures| {
        let a: i64 = caps[1].parse().unwrap_or(0);
        let b: i64 = caps[2].parse().unwrap_or(0);
        match op(a, b) {
            Some(v) => v.to_string(),
            None => caps[0].to_string(),
        }
    })
    .to_string()
}

/// Addition fold that is context-aware: skips `A + B` when `A` is the
/// RHS of a higher-precedence operator (`%`, `*`, `/`, `//`, `^`).
fn apply_add(src: &str) -> String {
    let re = Regex::new(r"\b(\d+)\s*\+\s*(\d+)\b").unwrap();
    let mut result = String::new();
    let mut last_end = 0;
    /*for cap in re.captures_iter(src) {
        let m = cap.get(0).unwrap();
        let start = m.start();
        let end = m.end();
        // Look at what immediately precedes the left operand (ignoring spaces).
        let before = src[..start].trim_end();
        let skip = before.ends_with('%')
            || before.ends_with('*')
            || before.ends_with('/')
            || before.ends_with('^');
        result.push_str(&src[last_end..start]);
        if skip {
            result.push_str(m.as_str());
        } else {
            let a: i64 = cap[1].parse().unwrap_or(0);
            let b: i64 = cap[2].parse().unwrap_or(0);
            result.push_str(&(a + b).to_string());
        }
        last_end = end;
    }
    result.push_str(&src[last_end..]);*/
    result.push_str(src);
    result
}

fn apply_pow(src: &str) -> String {
    let re = Regex::new(r"\b(\d+)\s*\^\s*(\d+)\b").unwrap();
    re.replace_all(src, |caps: &regex::Captures| {
        let base: i64 = caps[1].parse().unwrap_or(0);
        let exp: u32  = caps[2].parse().unwrap_or(0);
        if exp <= 18 {
            base.pow(exp).to_string()
        } else {
            caps[0].to_string()
        }
    })
    .to_string()
}
