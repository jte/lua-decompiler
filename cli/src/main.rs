use std::{fs, path::PathBuf, process};
use clap::Parser;
use engine::Mode;

#[derive(Parser)]
#[command(name = "lua-decompiler", about = "Lua decompiler")]
struct Cli {
    /// Input file
    input_file: PathBuf,

    /// Output file
    output_file: PathBuf,

    #[arg(long)]
    disassemble: bool,

    #[arg(long)]
    decompile: bool,

    /// Dump the control-flow graph of the top-level function as a Graphviz DOT file.
    #[arg(long)]
    dump_cfg: bool,

    /// Decompile and then run all deobfuscation passes on the output.
    #[arg(long)]
    deobfuscate: bool,

    /// Decompile a control-flow-flattened (JMP-spaghetti) binary.
    /// Applies a CFG linearization pass before decompiling to remove relay JMPs
    /// and restore sequential execution order.
    /// Combine with --deobfuscate to also run deobfuscation passes.
    #[arg(long)]
    flatten: bool,
}

fn main() {
    // The decompiler uses deep recursion (emit_node + op_closure nesting).
    // Spawn on a thread with a 64 MiB stack to avoid stack overflow on large
    // or heavily-obfuscated binaries.
    let exit_code = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("worker thread panicked");
    std::process::exit(exit_code);
}

fn run() -> i32 {
    let args = Cli::parse();

    let data: Vec<u8> = match fs::read(&args.input_file) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error reading {:?}: {e}", args.input_file);
            process::exit(1);
        }
    };

    match process_file(&data, args.disassemble, args.decompile, args.dump_cfg, args.deobfuscate, args.flatten) {
        Ok(output) => {
            if let Err(e) = fs::write(&args.output_file, &output) {
                eprintln!("Error writing output: {e}");
                return 1;
            }
            println!("Done.");
        }
        Err(e) => {
            eprintln!("Error: {e}");
            return 1;
        }
    }
    0
}

fn dump_chunk(chunk: &luac_parser::LuaChunk, depth: usize) {
    let indent = "  ".repeat(depth);
    eprintln!("{}[proto] name={:?} params={} upvals={} consts={} protos={}",
        indent,
        String::from_utf8_lossy(&chunk.name),
        chunk.num_params,
        chunk.num_upvalues,
        chunk.constants.len(),
        chunk.prototypes.len(),
    );
    for (i, c) in chunk.constants.iter().enumerate() {
        eprintln!("{}  K{} = {:?}", indent, i, c);
    }
    for (i, sub) in chunk.prototypes.iter().enumerate() {
        eprintln!("{}  sub[{}]:", indent, i);
        dump_chunk(sub, depth + 2);
    }
}

fn process_file(
    data: &Vec<u8>,
    disassemble: bool,
    decompile: bool,
    dump_cfg: bool,
    deobfuscate: bool,
    flatten: bool,
) -> Result<Vec<u8>, String> {
    let proto = engine::parse(data)?;
    //dump_chunk(&parsed.main_chunk, 0);

    let mode = if disassemble {
        Mode::Disassemble
    } else if dump_cfg {
        Mode::Cfg
    } else if deobfuscate {
        Mode::Deobfuscate
    } else if decompile || flatten {
        Mode::Decompile
    } else {
        return Ok(data.clone());
    };

    Ok(engine::run(&proto, mode, flatten).into_bytes())
}
