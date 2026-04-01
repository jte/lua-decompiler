/// Pass – Encrypted-string decryption (AST matcher).
///
/// Detects `local _tN = {enc1, ..., encK, key, _acc14[#_acc14]}` and
/// replaces each `_acc14[#_acc14](_tN)` call site with the decrypted string.
///
/// Decryption formula:
///   plain[i] = ((enc[i] ^ (i+1)) + GLOBAL_BASE) % MODULO   (as u8)

use lua_ast::{Block, Expr, Stat, TableField, UnOp};
use crate::for_each_block;

const GLOBAL_BASE: i64 = 142070;
const MODULO: i64 = 953;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    // Iterate to fixed point (multiple encrypted tables in same block).
    loop {
        let before_len = block.len();
        process_once(block);
        if block.len() == before_len { break; }
    }
}

fn process_once(block: &mut Block) {
    // Find one encrypted-string table declaration.
    let decl_pos = match block.iter().position(is_enc_table_decl) {
        Some(p) => p,
        None => return,
    };

    let tname = match &block[decl_pos] {
        Stat::Local { names, .. } => names[0].clone(),
        _ => return,
    };

    let (enc, key) = match parse_enc_table(&block[decl_pos]) {
        Some(v) => v,
        None => return,
    };

    let decrypted = decrypt(&enc, key);

    // Find the call site: Stat::Call(Call { func: _acc14[#_acc14], args: [Name(tname)] })
    // or Stat::Assign { rhs: [Call { ... }] } — search forwards from decl_pos.
    let call_pos = match find_call_site(block, &tname, decl_pos) {
        Some(p) => p,
        None => return,
    };

    // Replace the call site with the decrypted string literal.
    replace_call_site(block, call_pos, &tname, Expr::Str(decrypted));

    // Remove the table declaration (adjust for any shifts from replacement).
    // The decl_pos may still be valid if call_pos > decl_pos.
    if decl_pos < block.len() {
        if let Stat::Local { names, .. } = &block[decl_pos] {
            if names.len() == 1 && names[0] == tname {
                block.remove(decl_pos);
            }
        }
    }
}

/// True if `stat` is `local _tN = {Integer*, Integer, _acc14[#_acc14]}`.
fn is_enc_table_decl(stat: &Stat) -> bool {
    parse_enc_table(stat).is_some()
}

/// Extract (enc_bytes, key) from a matching decl, or None.
fn parse_enc_table(stat: &Stat) -> Option<(Vec<i64>, i64)> {
    let values = match stat {
        Stat::Local { names, values } if names.len() == 1 && values.len() == 1 => values,
        _ => return None,
    };
    let fields = match &values[0] {
        Expr::Table(f) if f.len() >= 3 => f,
        _ => return None,
    };

    // Last field must be the sentinel: _acc14[#_acc14] (Index expression)
    let last = match fields.last()? {
        TableField::ValueField(e) => e,
        _ => return None,
    };
    if !is_acc14_len_index(last) { return None; }

    // Second-to-last: the key (positive integer)
    let key = match fields[fields.len() - 2] {
        TableField::ValueField(Expr::Integer(k)) if k > 0 => k,
        _ => return None,
    };

    // All preceding: encrypted bytes (integers)
    let enc: Option<Vec<i64>> = fields[..fields.len() - 2].iter().map(|f| {
        match f {
            TableField::ValueField(Expr::Integer(v)) => Some(*v),
            _ => None,
        }
    }).collect();
    let enc = enc?;
    if enc.is_empty() { return None; }

    Some((enc, key))
}

/// True if `e` is `_acc14[#_acc14]`.
fn is_acc14_len_index(e: &Expr) -> bool {
    match e {
        Expr::Index { table, key } => {
            matches!(table.as_ref(), Expr::Name(n) if n == "_acc14")
                && matches!(key.as_ref(), Expr::UnOp { op: UnOp::Len, operand }
                    if matches!(operand.as_ref(), Expr::Name(n) if n == "_acc14"))
        }
        _ => false,
    }
}

/// Find the call site `_acc14[#_acc14](_tN)` within `block` after `after_pos`.
fn find_call_site(block: &Block, tname: &str, after_pos: usize) -> Option<usize> {
    for (i, stat) in block.iter().enumerate().skip(after_pos) {
        if is_call_site(stat, tname) { return Some(i); }
    }
    None
}

fn is_call_site(stat: &Stat, tname: &str) -> bool {
    let call_expr = match stat {
        Stat::Call(e) => e,
        Stat::Assign { rhs, .. } if rhs.len() == 1 => &rhs[0],
        Stat::Local { values, .. } if values.len() == 1 => &values[0],
        _ => return false,
    };
    match call_expr {
        Expr::Call { func, args } => {
            is_acc14_len_index(func)
                && args.len() == 1
                && matches!(&args[0], Expr::Name(n) if n == tname)
        }
        _ => false,
    }
}

/// Replace the call site expression with `replacement`.
fn replace_call_site(block: &mut Block, pos: usize, tname: &str, replacement: Expr) {
    match &mut block[pos] {
        Stat::Call(_) => {
            // A bare call used as a statement — replace with nothing (the decrypted
            // string would just be thrown away). Remove the statement.
            block.remove(pos);
        }
        Stat::Assign { rhs, .. } => {
            if let Some(e) = rhs.get_mut(0) {
                if matches!(e, Expr::Call { .. }) { *e = replacement; }
            }
        }
        Stat::Local { values, .. } => {
            if let Some(e) = values.get_mut(0) {
                if matches!(e, Expr::Call { .. }) { *e = replacement; }
            }
        }
        _ => {}
    }
}

fn decrypt(enc: &[i64], _key: i64) -> Vec<u8> {
    enc.iter().enumerate().map(|(i, &b)| {
        ((b ^ (i as i64 + 1)) + GLOBAL_BASE).rem_euclid(MODULO) as u8
    }).collect()
}
