/// Pass – XOR cipher decryption.
///
/// Detects the obfuscation pattern:
///   local KEY_STR = "LONG_BYTES"         -- cipher key (> 100 bytes)
///   local POS_VAR = #X / #X              -- initial position = 1
///   local F3_NAME = function(_p0) ... end -- XOR decrypt: each byte XOR (9 XOR key[pos])
///   local F4_NAME = function(_p0) ... end -- bytes-to-string (byte → char)
///   local TBL_NAME = {}
///   local _fN = function() ... return F3_NAME(CIPHERTEXT) end
///   TBL_NAME[ENC_KEY] = _fN()
///   ...
///
/// Decrypts each wrapper function's ciphertext using key_byte = KEY_STR[call_num - 1]
/// (0-indexed), xor_mask = 9 ^ key_byte.
///
/// Substitutes all `F4_NAME(TBL_NAME[EK])` patterns with the decrypted string.
/// Also resolves alias patterns `ALIAS_F4(ALIAS_TBL[EK])` where aliases are
/// declared as `local ALIAS_F4 = F4_NAME` and `local ALIAS_TBL = TBL_NAME`.
///
/// Removes the cipher infrastructure (wrapper functions, key/pos variables,
/// F4 function, TBL declaration) from the AST.

use std::collections::BTreeMap;
use lua_ast::{Block, Expr, Stat};
use crate::for_each_block;

/// The XOR constant is the byte value of ASCII tab ('\t' = 9), which appears
/// in the obfuscated code as _acc4["\t"].
const XOR_CONST: u8 = 9;

/// Minimum length for a string to be considered the cipher key.
const MIN_KEY_LEN: usize = 100;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    // Step 1: Find wrapper functions and their ciphertexts.
    let (f3_name, tbl_name, wrappers, wrapper_indices) = match find_wrappers(block) {
        Some(x) => x,
        None => return,
    };

    // Step 2: Find the cipher key string variable.
    let (key_var, key_bytes, key_idx) = match find_key_string(block, &f3_name) {
        Some(x) => x,
        None => return,
    };

    // Step 3: Find the position variable (evaluates to 1).
    let (pos_var, pos_idx) = find_pos_var(block, key_idx).unwrap_or_default();

    // Step 4: Find the F4 function (byte-to-string, comes right after F3).
    let (f4_name, f4_idx) = match find_f4_var(block, &f3_name) {
        Some(x) => x,
        None => return,
    };

    // Step 5: Find the TBL declaration (`local TBL_NAME = {}`).
    let tbl_decl_idx = find_empty_table_decl(block, &tbl_name);

    // Step 6: Decrypt each wrapper function in order.
    let mut decrypted: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();
    for (call_num, (enc_key, ciphertext)) in wrappers.iter().enumerate() {
        let key_byte = key_bytes[call_num % key_bytes.len()];
        let xor_mask = XOR_CONST ^ key_byte;
        let plain: Vec<u8> = ciphertext.iter().map(|&b| b ^ xor_mask).collect();
        decrypted.insert(enc_key.clone(), plain);
    }

    // Step 7: Find any aliases (local ALIAS_F4 = F4_NAME, local ALIAS_TBL = TBL_NAME).
    let (aliases_f4, aliases_tbl, alias_indices) = find_aliases(block, &f4_name, &tbl_name);

    // Step 8: Substitute F4(TBL[EK]) → Str(decrypted) everywhere.
    let f4_names: Vec<&str> = std::iter::once(f4_name.as_str())
        .chain(aliases_f4.iter().map(|s| s.as_str()))
        .collect();
    let tbl_names: Vec<&str> = std::iter::once(tbl_name.as_str())
        .chain(aliases_tbl.iter().map(|s| s.as_str()))
        .collect();

    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Call { func, args } = e {
            if args.len() == 1 {
                if let Expr::Name(fname) = func.as_ref() {
                    if f4_names.contains(&fname.as_str()) {
                        if let Expr::Index { table, key } = &args[0] {
                            if let (Expr::Name(tname), Expr::Str(ek)) = (table.as_ref(), key.as_ref()) {
                                if tbl_names.contains(&tname.as_str()) {
                                    if let Some(plain) = decrypted.get(ek) {
                                        *e = Expr::Str(plain.clone());
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    });

    // Also substitute bare TBL[EK] → decrypted (without F4 wrapper).
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Index { table, key } = e {
            if let (Expr::Name(tname), Expr::Str(ek)) = (table.as_ref(), key.as_ref()) {
                if tbl_names.contains(&tname.as_str()) {
                    if let Some(plain) = decrypted.get(ek) {
                        *e = Expr::Str(plain.clone());
                    }
                }
            }
        }
    });

    // Step 9: Remove cipher infrastructure.
    // Build the set of indices to remove.
    let mut remove: Vec<usize> = Vec::new();

    // Remove key variable (local KEY_VAR = "...").
    if !key_var.is_empty() { remove.push(key_idx); }

    // Remove pos variable (local POS_VAR = #X / #X).
    if !pos_var.is_empty() { remove.push(pos_idx); }

    // Remove F4 function.
    remove.push(f4_idx);

    // Remove TBL declaration.
    if let Some(idx) = tbl_decl_idx { remove.push(idx); }

    // Remove wrapper function decls and table assignment pairs.
    for &(decl_i, assign_i) in &wrapper_indices {
        remove.push(decl_i);
        remove.push(assign_i);
    }

    // Remove alias declarations.
    for idx in alias_indices { remove.push(idx); }

    // Deduplicate and sort descending for safe in-place removal.
    remove.sort_unstable_by(|a, b| b.cmp(a));
    remove.dedup();
    for i in remove {
        if i < block.len() { block.remove(i); }
    }
}

// ---------------------------------------------------------------------------
// Detection helpers
// ---------------------------------------------------------------------------

/// Find wrapper functions: pairs of
///   `local _fN = function() ... return F3(CT) ... end`
///   `TBL[EK] = _fN()`
///
/// Returns (f3_name, tbl_name, [(enc_key, ciphertext)], [(decl_idx, assign_idx)]).
fn find_wrappers(
    block: &Block,
) -> Option<(String, String, Vec<(Vec<u8>, Vec<u8>)>, Vec<(usize, usize)>)> {
    let mut f3_name: Option<String> = None;
    let mut tbl_name: Option<String> = None;
    let mut wrappers: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    let mut indices: Vec<(usize, usize)> = Vec::new();

    let mut i = 0;
    while i + 1 < block.len() {
        // Try to match: local _fN = function() ... return F3(CT) end
        if let Stat::Local { names, values } = &block[i] {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Function(fb) = &values[0] {
                    if fb.params.is_empty() && !fb.has_vararg {
                        if let Some((f3, ct)) = extract_f3_call(&fb.body) {
                            let fn_name = names[0].clone();

                            // Consistency check for F3 name.
                            if let Some(ref known_f3) = f3_name {
                                if *known_f3 != f3 {
                                    i += 1;
                                    continue;
                                }
                            }

                            // Try to match next: TBL[EK] = _fN()
                            if let Stat::Assign { lhs, rhs } = &block[i + 1] {
                                if lhs.len() == 1 && rhs.len() == 1 {
                                    if let Expr::Index { table, key } = &lhs[0] {
                                        if let Expr::Name(tname) = table.as_ref() {
                                            if let Expr::Str(ek) = key.as_ref() {
                                                if let Expr::Call { func, args } = &rhs[0] {
                                                    if args.is_empty() {
                                                        if let Expr::Name(fname) = func.as_ref() {
                                                            if *fname == fn_name {
                                                                // Consistency check for TBL name.
                                                                let ok_tbl = match &tbl_name {
                                                                    None => true,
                                                                    Some(n) => n == tname,
                                                                };
                                                                if ok_tbl {
                                                                    if f3_name.is_none() {
                                                                        f3_name = Some(f3);
                                                                    }
                                                                    if tbl_name.is_none() {
                                                                        tbl_name = Some(tname.clone());
                                                                    }
                                                                    wrappers.push((ek.clone(), ct));
                                                                    indices.push((i, i + 1));
                                                                    i += 2;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        i += 1;
    }

    if wrappers.is_empty() { return None; }
    Some((f3_name?, tbl_name?, wrappers, indices))
}

/// Extract the F3 function name and ciphertext from a wrapper function body.
/// The body has noise (local _t = {}, if _t["i"] ...) then `return F3(CT)`.
fn extract_f3_call(body: &Block) -> Option<(String, Vec<u8>)> {
    for stat in body {
        if let Stat::Return(vals) = stat {
            if vals.len() == 1 {
                if let Expr::Call { func, args } = &vals[0] {
                    if args.len() == 1 {
                        if let (Expr::Name(f3name), Expr::Str(ct)) = (func.as_ref(), &args[0]) {
                            return Some((f3name.clone(), ct.clone()));
                        }
                    }
                }
            }
        }
    }
    None
}

/// Find the cipher key: `local VAR = "LONG_STRING"` (> MIN_KEY_LEN bytes)
/// defined before the position where F3 is declared.
fn find_key_string(block: &Block, f3_name: &str) -> Option<(String, Vec<u8>, usize)> {
    // Find the index of the F3 declaration.
    let f3_decl_idx = block.iter().position(|s| {
        matches!(s, Stat::Local { names, values }
            if names.len() == 1 && names[0] == f3_name
                && matches!(values[0], Expr::Function(_)))
    })?;

    // Search backwards from F3 for a long string literal.
    for i in (0..f3_decl_idx).rev().take(20) {
        if let Stat::Local { names, values } = &block[i] {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Str(b) = &values[0] {
                    if b.len() >= MIN_KEY_LEN {
                        return Some((names[0].clone(), b.clone(), i));
                    }
                }
            }
        }
    }
    None
}

/// Find the position variable: `local VAR = #X / #X` (evaluates to 1).
fn find_pos_var(block: &Block, after: usize) -> Option<(String, usize)> {
    for i in after..block.len().min(after + 10) {
        if let Stat::Local { names, values } = &block[i] {
            if names.len() == 1 && values.len() == 1 {
                if is_len_div_len(&values[0]) {
                    return Some((names[0].clone(), i));
                }
            }
        }
    }
    None
}

fn is_len_div_len(e: &Expr) -> bool {
    matches!(e, Expr::BinOp { op: lua_ast::BinOp::Div, lhs, rhs }
        if matches!(lhs.as_ref(), Expr::UnOp { op: lua_ast::UnOp::Len, .. })
        && matches!(rhs.as_ref(), Expr::UnOp { op: lua_ast::UnOp::Len, .. }))
}

/// Find the F4 function: the function declared right after F3 in the block.
fn find_f4_var(block: &Block, f3_name: &str) -> Option<(String, usize)> {
    let f3_idx = block.iter().position(|s| {
        matches!(s, Stat::Local { names, .. } if names.len() == 1 && names[0] == f3_name)
    })?;

    // Look for the next function declaration after F3.
    for i in f3_idx + 1..block.len().min(f3_idx + 5) {
        if let Stat::Local { names, values } = &block[i] {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Function(fb) = &values[0] {
                    if fb.params.len() == 1 && !fb.has_vararg {
                        return Some((names[0].clone(), i));
                    }
                }
            }
        }
    }
    None
}

/// Find `local TBL_NAME = {}` declaration.
fn find_empty_table_decl(block: &Block, tbl_name: &str) -> Option<usize> {
    block.iter().position(|s| {
        matches!(s, Stat::Local { names, values }
            if names.len() == 1 && names[0] == tbl_name
                && values.len() == 1 && values[0] == Expr::Table(vec![]))
    })
}

/// Find aliases: `local ALIAS_F4 = F4_NAME` and `local ALIAS_TBL = TBL_NAME`.
/// Returns (alias_f4_names, alias_tbl_names, indices_to_remove).
fn find_aliases(
    block: &Block,
    f4_name: &str,
    tbl_name: &str,
) -> (Vec<String>, Vec<String>, Vec<usize>) {
    let mut aliases_f4: Vec<String> = Vec::new();
    let mut aliases_tbl: Vec<String> = Vec::new();
    let mut indices: Vec<usize> = Vec::new();

    for (i, stat) in block.iter().enumerate() {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Name(n) = &values[0] {
                    if n == f4_name {
                        aliases_f4.push(names[0].clone());
                        indices.push(i);
                    } else if n == tbl_name {
                        aliases_tbl.push(names[0].clone());
                        indices.push(i);
                    }
                }
            }
        }
    }

    // Also pick up aliases of aliases.
    let all_f4: Vec<String> = aliases_f4.clone();
    let all_tbl: Vec<String> = aliases_tbl.clone();
    for (i, stat) in block.iter().enumerate() {
        if indices.contains(&i) { continue; }
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Name(n) = &values[0] {
                    if all_f4.contains(n) {
                        aliases_f4.push(names[0].clone());
                        indices.push(i);
                    } else if all_tbl.contains(n) {
                        aliases_tbl.push(names[0].clone());
                        indices.push(i);
                    }
                }
            }
        }
    }

    (aliases_f4, aliases_tbl, indices)
}
