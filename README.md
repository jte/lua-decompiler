# Lua Decompiler

A decompiler, disassembler and deobfuscator for compiled Lua bytecode, written
in Rust.

**Try it online: [lua-decompiler.com](https://lua-decompiler.com)** — runs
entirely in your browser via WebAssembly; files are never uploaded.

## Features

- Decompiles Lua **5.1, 5.2, 5.3, 5.4 and 5.5** bytecode (`luac` output) back
  to source: loops, `if`/`elseif`, `and`/`or` expressions, method calls,
  table constructors, closures, `<close>` variables, 5.5 named varargs
  (`...t`) and `global` declarations; local names come from debug info when
  present
- Decompiles **Luau** (Roblox) bytecode, versions 3–14, into valid Luau:
  `continue`, generalized iteration (`for k, v in t`), imports, table
  templates; opcodes scrambled by the Roblox client are recognised and
  decoded.  Luau has no `goto`, so code that cannot be structured becomes a
  `while` loop over a state variable instead
- Output is meant to behave exactly like the bytecode; unstructurable
  (irreducible) control flow falls back to `goto`
- **Deobfuscation** passes that only rewrite what they can prove equivalent:
  noise removal, opaque predicates and junk loops, constant folding and
  propagation, lookup-table resolution, string decoding (XOR ciphers and a
  bounded evaluator for decoder functions), constant/identity function
  inlining, dead-code removal, naming of re-bound API functions
- **Control-flow unflattening** for JMP-spaghetti obfuscators (5.1–5.3)
- Recovers Lua 5.2 files whose debug info was corrupted by obfuscators
- Bytecode disassembler, control-flow-graph export (Graphviz DOT) and an
  interactive bytecode debugger (5.1–5.3)

Not supported yet: LuaJIT bytecode. Decompilation is not perfect —
if a file produces wrong output, please
[open an issue](https://github.com/jte/lua-decompiler/issues/new).

## Command line

Requires [Rust](https://rustup.rs).

```sh
cargo build --release -p cli

# decompile
target/release/cli input.luac output.lua --decompile
# decompile + deobfuscate
target/release/cli input.luac output.lua --deobfuscate
# control-flow-flattened input (combine with --deobfuscate if needed)
target/release/cli input.luac output.lua --flatten
# bytecode listing
target/release/cli input.luac output.txt --disassemble
# control-flow graph of the main function
target/release/cli input.luac output.dot --dump-cfg
```

Interactive debugger (step through bytecode, inspect registers):

```sh
cargo run --release -p debugger --bin ldebug -- input.luac
```

## Project layout

| Crate | Purpose |
|---|---|
| `disassembler` | Bytecode model and listing (wraps `luac-parser`) |
| `decompiler` | CFG construction, structuring, AST generation, CFF linearization |
| `lua_ast` | Lua AST and pretty-printer |
| `deobfuscator` | AST-level deobfuscation passes |
| `engine` | Shared parse → decompile → deobfuscate pipeline |
| `cli` | Command-line tool |
| `debugger` | Interactive bytecode debugger (`ldebug`) |
| `web` | WebAssembly bindings and the [lua-decompiler.com](https://lua-decompiler.com) site — see [web/README.md](web/README.md) |

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this work, as defined in the Apache-2.0 license, shall be dual
licensed as above, without any additional terms or conditions.
