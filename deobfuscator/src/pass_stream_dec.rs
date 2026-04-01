/// Pass – Stream-XOR string decryption (AST matcher).
///
/// Detects the XOR cipher function pattern and decrypts its call sites.
///
/// The identifying structure in the AST:
///   - A function body containing a GenFor loop
///   - Inside the loop: an assignment with BinOp{BXor, BinOp{BXor, byte, acc_table_lookup}, string_byte_call}
///   - A position-variable increment after the loop
///   - A key-string local before the function
///
/// All `fn_name(ciphertext)` calls are replaced with the decrypted plain text.

use lua_ast::{Block, BinOp, Expr, FuncBody, Stat, TableField, UnOp};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    loop {
        let before = block.len();
        process_once(block);
        if block.len() == before { break; }
    }
}

fn process_once(block: &mut Block) {
    // Find a cipher function declaration.
    let (fn_idx, fn_name, key, xor_const, key_var_name, pos_var_name) = {
        let mut found = None;
        for (i, stat) in block.iter().enumerate() {
            if let Some(info) = detect_cipher_func(block, i, stat) {
                found = Some((i, info.0, info.1, info.2, info.3, info.4));
                break;
            }
        }
        match found { Some(f) => f, None => return }
    };

    if key.is_empty() { return; }

    // Collect all call sites `fn_name("ciphertext")` in source order.
    let mut call_sites: Vec<(usize, Vec<u8>)> = Vec::new();
    for (i, stat) in block.iter().enumerate() {
        if i == fn_idx { continue; }
        if let Some(cipher) = find_cipher_call(stat, &fn_name) {
            call_sites.push((i, cipher));
        }
    }

    if call_sites.is_empty() { return; }

    // Decrypt each call site in source order (key position advances per call).
    let key_len = key.len();
    for (call_idx, (stat_idx, ciphertext)) in call_sites.iter().enumerate() {
        let key_byte = key[call_idx % key_len];
        let plain: Vec<u8> = ciphertext.iter().map(|&b| b ^ xor_const ^ key_byte).collect();
        replace_cipher_call(&mut block[*stat_idx], &fn_name, Expr::Str(plain));
    }

    // Remove the cipher function declaration.
    block.remove(fn_idx);

    // Remove key-string and position-variable declarations.
    block.retain(|s| !is_key_or_pos_decl(s, &key_var_name, &pos_var_name));
}

struct CipherInfo(String, Vec<u8>, u8, String, String);
// (fn_name, key_bytes, xor_const, key_var_name, pos_var_name)

/// Check if `stat` at `idx` is a cipher function declaration.
fn detect_cipher_func(
    block: &Block,
    idx: usize,
    stat: &Stat,
) -> Option<(String, Vec<u8>, u8, String, String)> {
    let (fn_name, body) = match stat {
        Stat::Local { names, values } if names.len() == 1 => {
            if let Expr::Function(fb) = &values[0] {
                (names[0].clone(), &fb.body)
            } else {
                return None;
            }
        }
        _ => return None,
    };

    // The function body must contain a GenFor with an XOR assignment inside it.
    let (xor_const, key_var, pos_var) = detect_xor_body(body)?;

    // Scan backwards in the outer block for the key string declaration.
    let key_bytes = find_key_string(block, idx, &key_var)?;

    Some((fn_name, key_bytes, xor_const, key_var, pos_var))
}

/// Inspect a function body to detect the XOR-cipher structure.
/// Returns (xor_const, key_var_name, pos_var_name) or None.
fn detect_xor_body(body: &Block) -> Option<(u8, String, String)> {
    // Look for a GenFor loop containing an XOR assignment.
    for stat in body {
        if let Stat::GenFor { body: for_body, .. } = stat {
            for inner in for_body {
                if let Some(result) = detect_xor_assign(inner) {
                    // Also verify there's a pos_var increment somewhere in the function body.
                    // For now, just return the detected values.
                    return Some(result);
                }
            }
        }
    }
    None
}

/// Detect `t[k] = byte ~ acc[char] ~ string.byte(key_var, pos_var)`.
fn detect_xor_assign(stat: &Stat) -> Option<(u8, String, String)> {
    let rhs = match stat {
        Stat::Assign { rhs, .. } if rhs.len() == 1 => &rhs[0],
        _ => return None,
    };

    // Pattern: X ~ acc[char] ~ string.byte(key_var, pos_var)
    // which is BinOp{BXor, BinOp{BXor, X, acc_lookup}, string_byte}
    let (inner_lhs, inner_rhs) = match rhs {
        Expr::BinOp { op: BinOp::BXor, lhs, rhs } => (lhs.as_ref(), rhs.as_ref()),
        _ => return None,
    };

    // inner_rhs must be string.byte(key_var, pos_var)
    let (key_var, pos_var) = extract_string_byte(inner_rhs)?;

    // inner_lhs must be BinOp{BXor, byte, acc[char]}
    let (acc_lookup, _) = match inner_lhs {
        Expr::BinOp { op: BinOp::BXor, lhs, rhs } => (rhs.as_ref(), lhs.as_ref()),
        _ => return None,
    };

    // acc_lookup: acc_var[char_literal]
    let xor_const = extract_xor_const(acc_lookup)?;

    Some((xor_const, key_var, pos_var))
}

/// Extract the character byte from `acc["\t"]` style expression.
fn extract_xor_const(e: &Expr) -> Option<u8> {
    match e {
        Expr::Index { key, .. } => {
            match key.as_ref() {
                Expr::Str(b) if b.len() == 1 => Some(b[0]),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract (key_var, pos_var) from `string.byte(key_var, pos_var)`.
fn extract_string_byte(e: &Expr) -> Option<(String, String)> {
    match e {
        Expr::Call { func, args } if args.len() == 2 => {
            // func must be string.byte
            let is_strbyte = match func.as_ref() {
                Expr::Index { table, key } => {
                    matches!(table.as_ref(), Expr::Name(n) if n == "string")
                        && matches!(key.as_ref(), Expr::Str(b) if b == b"byte")
                }
                _ => false,
            };
            if !is_strbyte { return None; }
            let key_var = match &args[0] { Expr::Name(n) => n.clone(), _ => return None };
            let pos_var = match &args[1] { Expr::Name(n) => n.clone(), _ => return None };
            Some((key_var, pos_var))
        }
        _ => None,
    }
}

/// Scan backwards in `block` before `before_idx` for `local key_var = "..."`.
fn find_key_string(block: &Block, before_idx: usize, key_var: &str) -> Option<Vec<u8>> {
    for stat in block[..before_idx].iter().rev().take(200) {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && names[0] == key_var {
                if let Expr::Str(b) = &values[0] {
                    return Some(b.clone());
                }
            }
        }
    }
    None
}

/// If `stat` is `fn_name("ciphertext")`, return the raw ciphertext bytes.
fn find_cipher_call(stat: &Stat, fn_name: &str) -> Option<Vec<u8>> {
    let e = match stat {
        Stat::Call(e) => e,
        Stat::Assign { rhs, .. } if rhs.len() == 1 => &rhs[0],
        Stat::Local { values, .. } if values.len() == 1 => &values[0],
        _ => return None,
    };
    match e {
        Expr::Call { func, args } if args.len() == 1 => {
            if !matches!(func.as_ref(), Expr::Name(n) if n == fn_name) { return None; }
            match &args[0] {
                Expr::Str(b) => Some(b.clone()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Replace `fn_name("...")` with `replacement` in `stat`.
fn replace_cipher_call(stat: &mut Stat, fn_name: &str, replacement: Expr) {
    let replace = |e: &mut Expr| {
        lua_ast::transform_expr(e, &mut |node| {
            if let Expr::Call { func, args } = node {
                if matches!(func.as_ref(), Expr::Name(n) if n == fn_name) {
                    if args.len() == 1 && matches!(&args[0], Expr::Str(_)) {
                        *node = replacement.clone();
                    }
                }
            }
        });
    };
    match stat {
        Stat::Call(e) => replace(e),
        Stat::Assign { rhs, .. } => { for e in rhs { replace(e); } }
        Stat::Local { values, .. } => { for v in values { replace(v); } }
        _ => {}
    }
}

fn is_key_or_pos_decl(stat: &Stat, key_var: &str, pos_var: &str) -> bool {
    if let Stat::Local { names, .. } = stat {
        if names.len() == 1 {
            return names[0] == key_var || names[0] == pos_var;
        }
    }
    false
}
