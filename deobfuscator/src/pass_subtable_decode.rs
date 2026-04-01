/// Pass – Static sub-table decoding (AST matcher).
///
/// Detects the two-loop decode pattern:
///   for k, sub in pairs(tbl) do
///     for i, v in pairs(sub) do
///       acc3[k][i] = acc2[v - OFFSET] - BASE
///     end
///   end
///   for k, sub in pairs(acc3) do
///     acc3[k] = string.char(table.unpack(sub))
///   end
///
/// Decodes each `tbl[k] = {encoded}` assignment and replaces with the string.
/// Then substitutes `acc3[k]` references with the decoded string.
///
/// This is a simplified AST matcher that detects the structural signature
/// and applies the decode transform.

use std::collections::HashMap;
use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    if let Some(result) = detect_and_apply(block) {
        *block = result;
    }
}

fn detect_and_apply(block: &Block) -> Option<Block> {
    // Find the inner-assignment signature: acc3[k][i] = acc2[v - OFFSET] - BASE
    let (acc3_name, acc2_name, offset, base, outer_for_idx) = detect_inner_pattern(block)?;

    // Find `local acc3 = tbl_name` alias (scanned backwards from outer_for_idx).
    let (tbl_name, _alias_idx) = find_alias(block, outer_for_idx, &acc3_name)?;

    // Find `local acc2 = {lookup_integers}` declaration.
    let (lookup, acc2_decl_idx) = find_lookup_decl(block, outer_for_idx, &acc2_name)?;

    // Find the second for-loop: `for k, sub in pairs(acc3) do acc3[k] = string.char(...)`
    let second_for_idx = find_second_for(block, outer_for_idx, &acc3_name)?;

    // Decode all `tbl_name[k] = {encoded_ints}` assignments in the block.
    let (decoded_map, mut new_block) = decode_tbl_entries(block, &tbl_name, &lookup, offset, base);

    // Remove the first outer for-loop, second for-loop, acc2 decl, pairs line.
    // (The acc3 alias `local acc3 = tbl_name` is kept.)
    let to_remove: Vec<usize> = {
        let mut r = Vec::new();
        r.push(outer_for_idx);
        r.push(second_for_idx);
        r.push(acc2_decl_idx);
        // Also find `local _rN = pairs(tbl_name)` line just before alias.
        if let Some(pairs_idx) = find_pairs_line(&new_block, outer_for_idx, &tbl_name) {
            r.push(pairs_idx);
        }
        r.sort_unstable();
        r.dedup();
        r
    };

    for &i in to_remove.iter().rev() {
        if i < new_block.len() { new_block.remove(i); }
    }

    // Substitute acc3[k] references with decoded strings.
    replace_acc3_refs(&mut new_block, &acc3_name, &decoded_map);

    Some(new_block)
}

// ---------------------------------------------------------------------------
// Detection helpers
// ---------------------------------------------------------------------------

fn detect_inner_pattern(block: &Block) -> Option<(String, String, i64, i64, usize)> {
    for (li, stat) in block.iter().enumerate() {
        if let Stat::GenFor { body: outer_body, .. } = stat {
            for inner_stat in outer_body {
                if let Stat::GenFor { body: inner_body, .. } = inner_stat {
                    for s in inner_body {
                        if let Some((acc3, acc2, off, base)) = detect_inner_assign(s) {
                            return Some((acc3, acc2, off, base, li));
                        }
                    }
                }
            }
        }
    }
    None
}

/// Detect `acc3[k_var][i_var] = acc2[v_var - OFFSET] - BASE`.
/// Extract an integer value from either `Expr::Integer(n)` or `Expr::Float(f)` where f is whole.
fn expr_as_int(e: &Expr) -> Option<i64> {
    match e {
        Expr::Integer(n) => Some(*n),
        Expr::Float(f) if f.fract() == 0.0 && f.is_finite() => Some(*f as i64),
        _ => None,
    }
}

/// Extract the integer offset from a key expression of the form:
///   `v - OFFSET`        → OFFSET
///   `v - a - b`         → a + b   (left-associative double subtraction)
/// OFFSET, a, b may be stored as Float or Integer.
fn extract_sub_offset(key: &Expr) -> Option<i64> {
    // Simple: v - OFFSET (where v is not a Sub BinOp)
    if let Expr::BinOp { op: lua_ast::BinOp::Sub, lhs, rhs } = key {
        if let Some(b) = expr_as_int(rhs.as_ref()) {
            // Check if lhs is also a (v - a) subtraction → double case
            if let Expr::BinOp { op: lua_ast::BinOp::Sub, lhs: _, rhs: inner_rhs } = lhs.as_ref() {
                if let Some(a) = expr_as_int(inner_rhs.as_ref()) {
                    return Some(a.wrapping_add(b)); // (v - a) - b → offset = a + b
                }
            }
            // Simple v - b
            return Some(b);
        }
    }
    None
}

fn detect_inner_assign(stat: &Stat) -> Option<(String, String, i64, i64)> {
    let (lhs, rhs) = match stat {
        Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => (&lhs[0], &rhs[0]),
        _ => return None,
    };

    // LHS: acc3[k][i]
    let acc3 = match lhs {
        Expr::Index { table, .. } => match table.as_ref() {
            Expr::Index { table, .. } => match table.as_ref() {
                Expr::Name(n) => n.clone(),
                _ => return None,
            },
            _ => return None,
        },
        _ => return None,
    };

    // RHS: acc2[v - OFFSET] - BASE
    let (inner, base) = match rhs {
        Expr::BinOp { op: lua_ast::BinOp::Sub, lhs, rhs } => {
            if let Some(base) = expr_as_int(rhs.as_ref()) {
                (lhs.as_ref(), base)
            } else { return None; }
        }
        _ => return None,
    };

    let (acc2, offset) = match inner {
        Expr::Index { table, key } => {
            let acc2 = match table.as_ref() {
                Expr::Name(n) => n.clone(),
                _ => return None,
            };
            let offset = extract_sub_offset(key.as_ref())?;
            (acc2, offset)
        }
        _ => return None,
    };

    Some((acc3, acc2, offset, base))
}

fn find_alias(block: &Block, before: usize, acc3: &str) -> Option<(String, usize)> {
    for i in (0..before).rev().take(50) {
        if let Stat::Local { names, values } = &block[i] {
            if names.len() == 1 && names[0] == acc3 {
                if let Expr::Name(tbl) = &values[0] {
                    return Some((tbl.clone(), i));
                }
            }
        }
    }
    None
}

fn find_lookup_decl(block: &Block, before: usize, acc2: &str) -> Option<(Vec<i64>, usize)> {
    for i in (0..before).rev().take(100) {
        if let Stat::Local { names, values } = &block[i] {
            if names.len() == 1 && names[0] == acc2 {
                if let Expr::Table(fields) = &values[0] {
                    let nums: Option<Vec<i64>> = fields.iter().map(|f| {
                        match f {
                            TableField::ValueField(e) => expr_as_int(e),
                            _ => None,
                        }
                    }).collect();
                    if let Some(v) = nums {
                        return Some((v, i));
                    }
                }
            }
        }
    }
    None
}

fn find_second_for(block: &Block, after: usize, acc3: &str) -> Option<usize> {
    // Collect variable names that are assigned from pairs(acc3) nearby.
    let mut pairs_vars: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for i in after + 1..block.len().min(after + 20) {
        if let Stat::Local { names, values } = &block[i] {
            // local r1, r2, r3 = pairs(acc3)
            if values.len() == 1 && is_pairs_of(&values[0], acc3) {
                for n in names { pairs_vars.insert(n.clone()); }
            }
        }
        if let Stat::GenFor { iters, body, .. } = &block[i] {
            // Check if iters contains pairs(acc3) directly OR variables from pairs(acc3)
            let has_pairs_acc3 = iters.iter().any(|e|
                is_pairs_of(e, acc3) ||
                matches!(e, Expr::Name(n) if pairs_vars.contains(n.as_str()))
            );
            // Check if body contains acc3[k] = string.char(...)
            let has_char = body.iter().any(|s| is_string_char_assign(s, acc3));
            if has_pairs_acc3 && has_char { return Some(i); }
        }
    }
    None
}

fn is_pairs_of(e: &Expr, name: &str) -> bool {
    match e {
        Expr::Call { func, args } => {
            matches!(func.as_ref(), Expr::Name(n) if n == "pairs")
                && args.len() == 1
                && matches!(&args[0], Expr::Name(n) if n == name)
        }
        _ => false,
    }
}

fn is_string_char_assign(stat: &Stat, acc3: &str) -> bool {
    if let Stat::Assign { lhs, rhs } = stat {
        if lhs.len() == 1 && rhs.len() == 1 {
            // LHS: acc3[k]
            let lhs_ok = matches!(&lhs[0], Expr::Index { table, .. }
                if matches!(table.as_ref(), Expr::Name(n) if n == acc3));
            // RHS: string.char(...) or table.unpack(...)
            let rhs_ok = matches!(&rhs[0], Expr::Call { func, .. }
                if matches!(func.as_ref(), Expr::Index { table, key }
                    if matches!(table.as_ref(), Expr::Name(n) if n == "string")
                        && matches!(key.as_ref(), Expr::Str(b) if b == b"char")));
            return lhs_ok && rhs_ok;
        }
    }
    false
}

fn find_pairs_line(block: &Block, before: usize, tbl: &str) -> Option<usize> {
    let needle = format!("pairs({})", tbl);
    for i in (0..before).rev().take(5) {
        let tmp: Block = vec![block[i].clone()];
        let s = lua_ast::print_block(&tmp, 0);
        if s.contains(&needle) { return Some(i); }
    }
    None
}

// ---------------------------------------------------------------------------
// Decoding
// ---------------------------------------------------------------------------

fn decode_tbl_entries(
    block: &Block,
    tbl_name: &str,
    lookup: &[i64],
    offset: i64,
    base: i64,
) -> (HashMap<u64, Vec<u8>>, Block) {
    let decode = |v: i64| -> Option<u8> {
        let idx = (v - offset - 1) as usize;
        if idx < lookup.len() {
            let code = lookup[idx] - base;
            if (0..=255).contains(&code) { Some(code as u8) } else { None }
        } else {
            None
        }
    };

    let mut decoded_map: HashMap<u64, Vec<u8>> = HashMap::new();
    let mut new_block: Block = Vec::new();

    for stat in block {
        // Check if this is tbl_name[k] = { encoded_ints }
        if let Stat::Assign { lhs, rhs } = stat {
            if lhs.len() == 1 && rhs.len() == 1 {
                if let Expr::Index { table, key } = &lhs[0] {
                    if matches!(table.as_ref(), Expr::Name(n) if n == tbl_name) {
                        if let Some(k) = expr_as_int(key.as_ref()) {
                        if let Expr::Table(fields) = &rhs[0] {
                            let encoded: Option<Vec<i64>> = fields.iter().map(|f| {
                                match f {
                                    TableField::ValueField(e) => expr_as_int(e),
                                    _ => None,
                                }
                            }).collect();
                            if let Some(enc) = encoded {
                                let decoded: Option<Vec<u8>> = enc.iter().map(|&v| decode(v)).collect();
                                if let Some(dec) = decoded {
                                    decoded_map.insert(k as u64, dec.clone());
                                    new_block.push(Stat::Assign {
                                        lhs: lhs.clone(),
                                        rhs: vec![Expr::Str(dec)],
                                    });
                                    continue;
                                }
                            }
                        } // Table
                        } // expr_as_int(key)
                    }
                }
            }
        }
        new_block.push(stat.clone());
    }

    (decoded_map, new_block)
}

fn replace_acc3_refs(block: &mut Block, acc3: &str, decoded: &HashMap<u64, Vec<u8>>) {
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Index { table, key } = e {
            if matches!(table.as_ref(), Expr::Name(n) if n == acc3) {
                if let Some(k) = expr_as_int(key.as_ref()) {
                    if let Some(bytes) = decoded.get(&(k as u64)) {
                        *e = Expr::Str(bytes.clone());
                    }
                }
            }
        }
    });
}
