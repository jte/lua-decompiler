/// Pass – Const-return and identity function inlining.
///
/// Phase 1: inline constant-returning functions.
///   local _fN = function()
///       local _t0 = {}
///       if _t0["i"] ~= nil then ... end
///       return LITERAL
///   end
///   → replace every `_fN()` call with LITERAL.
///
/// Phase 2: inline identity functions.
///   local _fN = function(_p0) ... return _p0 end
///   → replace every `_fN(EXPR)` call with EXPR.
///
/// Phase 3: string-keyed table substitution.
///   tbl["key"] = VALUE  →  replace all reads of tbl["key"] with VALUE.

use std::collections::BTreeMap;
use lua_ast::{Block, Expr, Stat, TableField};
use crate::for_each_block;

pub fn run(block: &mut Block) {
    for_each_block(block, &mut process_block);
}

fn process_block(block: &mut Block) {
    // Phase 1 & 2: function inlining (iterate to fix-point).
    for _ in 0..20 {
        let before = block.len();
        inline_const_funcs(block);
        inline_identity_funcs(block);
        if block.len() == before { break; }
    }

    // Phase 3: string-keyed table substitution (iterate to fix-point).
    for _ in 0..20 {
        let before = lua_ast::print_block(block, 0);
        substitute_table_reads(block);
        if lua_ast::print_block(block, 0) == before { break; }
    }
}

// ---------------------------------------------------------------------------
// Phase 1: const-return function inlining
// ---------------------------------------------------------------------------

fn inline_const_funcs(block: &mut Block) {
    // Collect { fn_name → literal } for const-return functions.
    let mut const_fns: BTreeMap<String, Expr> = BTreeMap::new();
    for stat in block.iter() {
        if let Some((name, lit)) = detect_const_func(stat) {
            const_fns.insert(name, lit);
        }
    }
    if const_fns.is_empty() { return; }

    // Substitute all `fn_name()` calls.
    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Call { func, args } = e {
            if args.is_empty() {
                if let Expr::Name(n) = func.as_ref() {
                    if let Some(lit) = const_fns.get(n) {
                        *e = lit.clone();
                        return;
                    }
                }
            }
        }
    });

    // Remove the now-inlined function declarations.
    block.retain(|s| {
        if let Stat::Local { names, .. } = s {
            if names.len() == 1 { return !const_fns.contains_key(&names[0]); }
        }
        true
    });
}

fn detect_const_func(stat: &Stat) -> Option<(String, Expr)> {
    let (name, fb) = match stat {
        Stat::Local { names, values } if names.len() == 1 => {
            if let Expr::Function(fb) = &values[0] { (names[0].clone(), fb) } else { return None; }
        }
        _ => return None,
    };

    if !fb.params.is_empty() || fb.has_vararg { return None; }

    // Body: optional local _t = {} + optional if + return LITERAL
    let ret = extract_const_return(&fb.body)?;
    Some((name, ret))
}

fn extract_const_return(body: &Block) -> Option<Expr> {
    // Walk statements, skipping `local _t = {}` and `if _t["i"] ~= nil` patterns.
    let mut ret_expr: Option<Expr> = None;
    for stat in body {
        match stat {
            // local _t0 = {} — obfuscation noise, skip
            Stat::Local { values, .. } if values.len() == 1 && values[0] == Expr::Table(vec![]) => {}
            // if _t["i"] ~= nil then ... end — obfuscation noise, skip
            Stat::If { .. } => {}
            // return LITERAL
            Stat::Return(vals) if vals.len() == 1 && vals[0].is_literal() => {
                ret_expr = Some(vals[0].clone());
            }
            _ => return None, // Unexpected statement — not a const function
        }
    }
    ret_expr
}

// ---------------------------------------------------------------------------
// Phase 2: identity function inlining
// ---------------------------------------------------------------------------

fn inline_identity_funcs(block: &mut Block) {
    let mut id_fns: BTreeMap<String, usize> = BTreeMap::new(); // fn_name → param_count
    for stat in block.iter() {
        if let Some((name, nparams)) = detect_identity_func(stat) {
            id_fns.insert(name, nparams);
        }
    }
    if id_fns.is_empty() { return; }

    lua_ast::transform_block(block, &mut |e| {
        if let Expr::Call { func, args } = e {
            if let Expr::Name(n) = func.as_ref() {
                if let Some(&nparams) = id_fns.get(n) {
                    if nparams == 1 && args.len() == 1 {
                        *e = args[0].clone();
                        return;
                    } else if nparams == 0 && args.is_empty() {
                        *e = Expr::Nil;
                        return;
                    }
                }
            }
        }
    });

    block.retain(|s| {
        if let Stat::Local { names, .. } = s {
            if names.len() == 1 { return !id_fns.contains_key(&names[0]); }
        }
        true
    });
}

fn detect_identity_func(stat: &Stat) -> Option<(String, usize)> {
    let (name, fb) = match stat {
        Stat::Local { names, values } if names.len() == 1 => {
            if let Expr::Function(fb) = &values[0] { (names[0].clone(), fb) } else { return None; }
        }
        _ => return None,
    };

    let nparams = fb.params.len();
    // Body: optional local _t = {} + optional if + return _p0
    for stat in &fb.body {
        match stat {
            Stat::Local { values, .. } if values.len() == 1 && values[0] == Expr::Table(vec![]) => {}
            Stat::If { .. } => {}
            Stat::Return(vals) if vals.len() == 1 => {
                match &vals[0] {
                    Expr::Name(p) if nparams >= 1 && *p == fb.params[0] => {
                        return Some((name, nparams));
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Phase 3: string-keyed table substitution
// ---------------------------------------------------------------------------

/// True if `e` can be safely substituted as a table value (no side effects).
fn is_substitutable(e: &Expr) -> bool {
    e.is_literal()
        || matches!(e, Expr::Name(_))
        || matches!(e, Expr::Index { table, key }
            if matches!(table.as_ref(), Expr::Name(_))
            && matches!(key.as_ref(), Expr::Str(_)))
}

fn substitute_table_reads(block: &mut Block) {
    substitute_table_reads_inner(block, &BTreeMap::new());
}

fn substitute_table_reads_inner(block: &mut Block, inherited: &BTreeMap<(String, Vec<u8>), Expr>) {
    use std::collections::BTreeSet;

    // Step 0: collect Name aliases: local ALIAS = ORIG (only direct name aliases)
    let mut aliases: BTreeMap<String, String> = BTreeMap::new();
    for stat in block.iter() {
        if let Stat::Local { names, values } = stat {
            if names.len() == 1 && values.len() == 1 {
                if let Expr::Name(orig) = &values[0] {
                    aliases.insert(names[0].clone(), orig.clone());
                }
            }
        }
    }
    // Resolve transitive aliases (A → B → C becomes A → C)
    let mut changed = true;
    while changed {
        changed = false;
        let snapshot = aliases.clone();
        for orig in aliases.values_mut() {
            if let Some(resolved) = snapshot.get(orig.as_str()) {
                if resolved != orig {
                    *orig = resolved.clone();
                    changed = true;
                }
            }
        }
    }

    // Start with inherited table values from outer scopes.
    let mut table_vals: BTreeMap<(String, Vec<u8>), Expr> = inherited.clone();
    let mut multi: BTreeSet<(String, Vec<u8>)> = BTreeSet::new();

    // Add entries from this block's assignment statements AND inline constructors.
    // Only include keys assigned exactly once — multiple assignments make
    // substitution unsafe (we don't know which value is "current").
    for stat in block.iter() {
        match stat {
            Stat::Assign { lhs, rhs } if lhs.len() == 1 && rhs.len() == 1 => {
                if let Expr::Index { table, key } = &lhs[0] {
                    if let (Expr::Name(tname), Expr::Str(kb)) = (table.as_ref(), key.as_ref()) {
                        // Skip the global-env upvalue — its fields are mutable globals,
                        // not safe to substitute unconditionally.
                        if tname.starts_with("_upv") { continue; }
                        if is_substitutable(&rhs[0]) {
                            let k = (tname.clone(), kb.clone());
                            if table_vals.contains_key(&k) && !inherited.contains_key(&k) {
                                multi.insert(k);
                            } else if !table_vals.contains_key(&k) {
                                table_vals.insert(k, rhs[0].clone());
                            }
                        }
                    }
                }
            }
            // Also collect from `local TNAME = { [key] = val, ... }` constructors.
            Stat::Local { names, values }
                if names.len() == 1 && values.len() == 1 =>
            {
                if let Expr::Table(fields) = &values[0] {
                    let tname = &names[0];
                    if tname.starts_with("_upv") { continue; }
                    for field in fields {
                        if let TableField::IndexField(k_expr, v_expr) = field {
                            if let Expr::Str(kb) = k_expr {
                                if is_substitutable(v_expr) {
                                    let k = (tname.clone(), kb.clone());
                                    if !table_vals.contains_key(&k) {
                                        table_vals.insert(k, v_expr.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    for k in multi { table_vals.remove(&k); }

    // Add alias entries: if ALIAS → ORIG is an alias, add (ALIAS, key) entries
    // for every (ORIG, key) entry in table_vals.
    let orig_entries: Vec<((String, Vec<u8>), Expr)> = table_vals
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    for (alias, orig) in &aliases {
        for ((tname, key), val) in &orig_entries {
            if tname == orig {
                table_vals.entry((alias.clone(), key.clone())).or_insert_with(|| val.clone());
            }
        }
    }

    if table_vals.is_empty() { return; }

    // Substitute reads only — NOT the LHS of assignments.
    // Use manual iteration so we can skip LHS table-index positions.
    for stat in block.iter_mut() {
        match stat {
            Stat::Assign { lhs, rhs } => {
                // For LHS, only substitute inside index sub-expressions (not the
                // top-level Index node itself, which is the assignment target).
                for e in lhs.iter_mut() {
                    match e {
                        Expr::Index { table, key } => {
                            subst_reads(table, &table_vals);
                            subst_reads(key, &table_vals);
                        }
                        _ => {}
                    }
                }
                for e in rhs.iter_mut() { subst_reads(e, &table_vals); }
            }
            Stat::Local { values, .. } => {
                for v in values.iter_mut() { subst_reads(v, &table_vals); }
            }
            Stat::Return(vals) => {
                for v in vals.iter_mut() { subst_reads(v, &table_vals); }
            }
            Stat::Call(e) => subst_reads(e, &table_vals),
            Stat::If { branches, else_body } => {
                for (cond, body) in branches.iter_mut() {
                    subst_reads(cond, &table_vals);
                    substitute_table_reads_inner(body, &table_vals);
                }
                if let Some(b) = else_body { substitute_table_reads_inner(b, &table_vals); }
            }
            Stat::While { cond, body } => {
                subst_reads(cond, &table_vals);
                substitute_table_reads_inner(body, &table_vals);
            }
            Stat::Repeat { body, cond } => {
                substitute_table_reads_inner(body, &table_vals);
                subst_reads(cond, &table_vals);
            }
            Stat::NumFor { from, to, step, body, .. } => {
                subst_reads(from, &table_vals);
                subst_reads(to, &table_vals);
                if let Some(s) = step { subst_reads(s, &table_vals); }
                substitute_table_reads_inner(body, &table_vals);
            }
            Stat::GenFor { iters, body, .. } => {
                for e in iters.iter_mut() { subst_reads(e, &table_vals); }
                substitute_table_reads_inner(body, &table_vals);
            }
            Stat::Do(body) => substitute_table_reads_inner(body, &table_vals),
            _ => {}
        }
    }
}

fn subst_reads(e: &mut Expr, table_vals: &BTreeMap<(String, Vec<u8>), Expr>) {
    lua_ast::transform_expr(e, &mut |node| {
        if let Expr::Index { table, key } = node {
            if let (Expr::Name(tname), Expr::Str(kb)) = (table.as_ref(), key.as_ref()) {
                let k = (tname.clone(), kb.clone());
                if let Some(val) = table_vals.get(&k) {
                    *node = val.clone();
                }
            }
        }
    });
}
