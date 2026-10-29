/// Pass – standard library and globals.
///
///   • `local p = print` (never reassigned)   →  uses of `p` become `print`
///   • `local c = string.char`                →  uses of `c` become `string.char`
///   • `string.char(104, 105)`                →  `"hi"`
///
/// Assumes the host runs the script with the standard library, and only
/// rewrites when the script itself cannot change what these names mean: the
/// global is never declared as a local or assigned (for `string`, also never
/// written through or used other than as `string.<name>`), and nothing that
/// can reach globals or library tables (`_G`, `_ENV`, `setfenv`,
/// `getmetatable`, `rawset`, `require`, loaded code, ...) appears.

use std::collections::BTreeSet;
use lua_ast::{Block, Expr, Stat};
use crate::for_each_block;
use crate::util::{assigned_names, count_refs, visit_exprs, visit_stats};

const ESCAPES: &[&str] = &[
    "_G", "_ENV", "getfenv", "setfenv", "getmetatable", "rawset", "require", "package",
    "load", "loadstring", "loadfile", "dofile",
];

pub fn run(block: &mut Block) {
    if escapes(block) { return; }
    let assigned = assigned_names(block);
    let string_ok = lib_untouched(block, "string", &assigned);
    let stable = |e: &Expr| match e {
        Expr::Name(g) => global_untouched(block, g, &assigned),
        _ => string_ok && is_lib_field(e, "string", &[]),
    };
    let mut aliases = Vec::new();
    visit_stats(block, &mut |s| if let Stat::Local { names, values } = s {
        if names.len() == 1 && values.len() == 1 && !assigned.contains(&names[0]) && stable(&values[0]) {
            aliases.push(names[0].clone());
        }
    });
    if !aliases.is_empty() { substitute_aliases(block, &aliases.into_iter().collect()); }
    if string_ok {
        lua_ast::transform_block(block, &mut |e| {
            if let Some(s) = fold_char(e) { *e = Expr::Str(s); }
        });
    }
}

/// Replace uses of each alias after its declaration, then drop the declaration
/// (reading a global or library field has no effect).
fn substitute_aliases(block: &mut Block, aliases: &BTreeSet<String>) {
    for_each_block(block, &mut |b| {
        let mut i = 0;
        while i < b.len() {
            let found = match &b[i] {
                Stat::Local { names, values } if names.len() == 1 && aliases.contains(&names[0]) => {
                    Some((names[0].clone(), values[0].clone()))
                }
                _ => None,
            };
            let Some((n, v)) = found else { i += 1; continue };
            let mut rest = b.split_off(i + 1);
            lua_ast::transform_block(&mut rest, &mut |e| {
                if matches!(e, Expr::Name(m) if *m == n) { *e = v.clone(); }
            });
            b.pop();
            b.extend(rest);
        }
    });
}

/// Is anything present that can reach globals or library tables?
pub(crate) fn escapes(b: &Block) -> bool {
    let (mut esc, mut debug, mut debug_ok) = (false, 0, 0);
    visit_exprs(b, &mut |e| match e {
        Expr::Name(n) if n == "debug" => debug += 1,
        Expr::Name(n) if ESCAPES.contains(&n.as_str()) => esc = true,
        // These cannot reach other tables or environments.
        _ if is_lib_field(e, "debug", &["getinfo", "traceback", "gethook", "sethook"]) => debug_ok += 1,
        _ => {}
    });
    esc || debug != debug_ok || count_refs(b, "debug") != debug
}

/// The global `g` is never declared (so never shadowed) nor assigned.
fn global_untouched(b: &Block, g: &str, assigned: &BTreeSet<String>) -> bool {
    let mut names = 0;
    visit_exprs(b, &mut |e| if matches!(e, Expr::Name(n) if n == g) { names += 1; });
    !assigned.contains(g) && count_refs(b, g) == names
}

/// `lib.<name>`, for any name when `names` is empty.
fn is_lib_field(e: &Expr, lib: &str, names: &[&str]) -> bool {
    matches!(e, Expr::Index { table, key } if matches!(table.as_ref(), Expr::Name(n) if n == lib)
        && matches!(key.as_ref(), Expr::Str(k) if names.is_empty() || names.iter().any(|n| n.as_bytes() == k.as_slice())))
}

/// The library table `lib` is the untouched global and every mention is a
/// field read.
pub(crate) fn lib_untouched(b: &Block, lib: &str, assigned: &BTreeSet<String>) -> bool {
    let (mut names, mut fields) = (0, 0);
    visit_exprs(b, &mut |e| match e {
        Expr::Name(n) if n == lib => names += 1,
        _ if is_lib_field(e, lib, &[]) => fields += 1,
        _ => {}
    });
    let mut written = false;
    visit_stats(b, &mut |s| if let Stat::Assign { lhs, .. } = s {
        written |= lhs.iter().any(|l| is_lib_field(l, lib, &[]));
    });
    !written && names == fields && global_untouched(b, lib, assigned)
}

/// `string.char(<integers 0..=255>)`.
fn fold_char(e: &Expr) -> Option<Vec<u8>> {
    let Expr::Call { func, args } = e else { return None };
    if !is_lib_field(func, "string", &["char"]) { return None; }
    args.iter().map(|a| {
        let n = match a {
            Expr::Integer(n) => *n,
            Expr::Float(f) if f.fract() == 0.0 => *f as i64,
            _ => return None,
        };
        u8::try_from(n).ok()
    }).collect()
}
