use std::{fs, process};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: ldebug <file.luac> [proto_index]");
        eprintln!();
        eprintln!("Opens the Lua bytecode file and starts an interactive GDB-like session.");
        eprintln!("  proto_index  Optional: start on proto N instead of 0 (root function)");
        process::exit(1);
    }

    let path = &args[1];
    let start_proto: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);

    let data = match fs::read(path) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error reading '{}': {}", path, e);
            process::exit(1);
        }
    };

    let parsed = match luac_parser::parse(&data) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            process::exit(1);
        }
    };

    disassembler::set_lua_version(parsed.header.lua_version);

    let root = disassembler::Proto::from(parsed.main_chunk);

    let mut dbg = debugger::repl::Debugger::new(&root);

    // Optionally start on a non-root proto
    if start_proto != 0 {
        println!("Tip: use 'func {}' to switch to that proto.", start_proto);
    }

    dbg.run_repl();
}
