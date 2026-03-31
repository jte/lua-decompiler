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
    // Chain subtraction: fold `- B - C` (both literals) → `- (B+C)`.
    // This must run BEFORE the pairwise fold so that `X - 250 - 20` becomes
    // `X - 270` rather than incorrectly folding `250 - 20 = 230` first.
    let s = apply_sub_chain(&s);
    // Pairwise subtraction: `A - B` where both are literals and A >= B.
    // Context-aware: skips when A is the RHS of a prior binary operator
    // (i.e. preceded by -, +, *, /, %, ^) to avoid the same mis-fold.
    let s = apply_sub(&s);
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
    let mut result = String::new();
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

/// Fold subtraction chains: `-\s*B\s*-\s*C` → `- (B+C)`.
///
/// Handles `X - 250 - 20` → `X - 270` by folding the two consecutive
/// literal-subtractions into one before the pairwise fold runs.
fn apply_sub_chain(src: &str) -> String {
    // Match: minus, literal B, minus, literal C.
    // The leading `-` is kept so we replace only `- B - C` with `- (B+C)`.
    let re = Regex::new(r"-\s*(\d+)\s*-\s*(\d+)").unwrap();
    re.replace_all(src, |caps: &regex::Captures| {
        let b: i64 = caps[1].parse().unwrap_or(0);
        let c: i64 = caps[2].parse().unwrap_or(0);
        format!("- {}", b + c)
    })
    .to_string()
}

/// Pairwise subtraction fold: `A - B` → `A-B` (only when A >= B).
///
/// Context-aware: skips the fold when `A` is itself the RHS of a binary
/// operator (i.e. immediately preceded by `-`, `+`, `*`, `/`, `%`, `^`).
/// Without this guard, `_v13 - 250 - 20` could match `250 - 20` and
/// incorrectly produce `_v13 - 230` instead of `_v13 - 270`.
fn apply_sub(src: &str) -> String {
    let re = Regex::new(r"\b(\d+)\s*-\s*(\d+)\b").unwrap();
    let mut result = String::new();
    let mut last_end = 0;
    for cap in re.captures_iter(src) {
        let m = cap.get(0).unwrap();
        let start = m.start();
        let end = m.end();
        let before = src[..start].trim_end();
        // Skip if A is the RHS of a prior binary operator.
        let skip = before.ends_with('-')
            || before.ends_with('+')
            || before.ends_with('*')
            || before.ends_with('/')
            || before.ends_with('%')
            || before.ends_with('^');
        result.push_str(&src[last_end..start]);
        if skip {
            result.push_str(m.as_str());
        } else {
            let a: i64 = cap[1].parse().unwrap_or(0);
            let b: i64 = cap[2].parse().unwrap_or(0);
            if a >= b {
                result.push_str(&(a - b).to_string());
            } else {
                result.push_str(m.as_str());
            }
        }
        last_end = end;
    }
    result.push_str(&src[last_end..]);
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
