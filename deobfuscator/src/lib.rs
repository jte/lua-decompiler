//! Lua source deobfuscator.
//!
//! Operates on the Lua **source text** produced by the decompiler and applies
//! a series of transformation passes to undo common obfuscation patterns.
//!
//! # Passes (in execution order)
//!
//! | # | Module             | What it does                                              |
//! |---|--------------------|-----------------------------------------------------------|
//! | 7 | [`pass7_upval`]    | `_upvN["global"]` → `global`; `mod["fn"]` → `mod.fn`     |
//! | 6 | [`pass6_dead`]     | Remove empty for/if blocks and `local x = nil`            |
//! | 2 | [`pass2_prop`]     | Propagate single-assignment integer/string constants      |
//! | 1 | [`pass1_fold`]     | Fold literal arithmetic (`A + B`, `A * B`, `A ^ B`, …)   |
//! | 3 | [`pass3_table`]    | Resolve 256-char identity lookup table (`_t14[N]` → char) |
//! | 5 | [`pass5_perm`]     | Resolve fully-known integer permutation tables            |
//! | 4 | [`pass4_concat`]   | Collapse `"" .. "a" .. "b"` string-concat sequences       |
//! | 6 | [`pass6_dead`]     | Second dead-code sweep after earlier passes               |
//! | 8 | [`pass8_rename`]   | Rename `_accN` vars that hold known Lua library modules   |

pub mod pass1_fold;
pub mod pass2_prop;
pub mod pass3_table;
pub mod pass4_concat;
pub mod pass5_perm;
pub mod pass6_dead;
pub mod pass7_upval;
pub mod pass8_rename;
pub mod pass_table_ctor;
pub mod pass_strdec;
pub mod pass_stream_dec;

/// Run all deobfuscation passes on a decompiled Lua source string and return
/// the cleaned-up source.
pub fn deobfuscate(src: &str) -> String {
    // --- Phase A: name/structure cleanup ---
    let s = pass7_upval::run(src);          // resolve _upvN global refs
    let s = pass6_dead::run(&s);            // remove empty blocks

    // --- Phase B: constant simplification (iterate to reach fixed point) ---
    let mut s = s;
    for _ in 0..5 {
        let next = pass2_prop::run(&s);     // substitute constants
        let next = pass1_fold::run(&next);  // fold arithmetic
        if next == s {
            break;
        }
        s = next;
    }

    // --- Phase C: table-based obfuscation ---
    let s = pass3_table::run(&s);           // _t14[N] → char literal
    let s = pass_table_ctor::run(&s);       // local _tN={} + _tN[M]=VAR → constructor
    let s = pass5_perm::run(&s);            // permutation table inlining (uses constructors)

    // Fold again after table substitution may have created new constant exprs
    let mut s = s;
    for _ in 0..5 {
        let next = pass1_fold::run(&s);
        if next == s {
            break;
        }
        s = next;
    }

    // --- Phase D: string reconstruction ---
    let s = pass_strdec::run(&s);           // decrypt _acc14[#_acc14](_tN) calls
    let s = pass_stream_dec::run(&s);       // decrypt stream-XOR cipher (_f3-style)
    let s = pass4_concat::run(&s);          // collapse "" .. "a" .. "b"

    // --- Phase E: final cleanup ---
    let s = pass6_dead::run(&s);            // second dead-code sweep
    pass8_rename::run(&s)                   // rename module-holding vars
}
