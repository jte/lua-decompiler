//! WebAssembly bindings for the browser front end in `www/`.
//!
//! Panics abort on wasm32-unknown-unknown and leave the instance unusable, so
//! the panic hook forwards the message to JS and the page throws the worker
//! away afterwards.

use engine::Mode;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = globalThis, js_name = __luaDecompilerPanic)]
    fn report_panic(msg: &str);
}

#[wasm_bindgen(start)]
pub fn start() {
    std::panic::set_hook(Box::new(|info| report_panic(&info.to_string())));
}

/// Run `data` (a compiled Lua chunk) through the pipeline.
///
/// `mode` is one of `"decompile"`, `"deobfuscate"`, `"disassemble"`, `"cfg"`.
#[wasm_bindgen]
pub fn run(data: &[u8], mode: &str, flatten: bool) -> Result<String, JsError> {
    let mode = match mode {
        "decompile" => Mode::Decompile,
        "deobfuscate" => Mode::Deobfuscate,
        "disassemble" => Mode::Disassemble,
        "cfg" => Mode::Cfg,
        other => return Err(JsError::new(&format!("unknown mode {other:?}"))),
    };
    let proto = engine::parse(data).map_err(|e| {
        JsError::new(&format!("Could not parse this file as Lua 5.1–5.5, LuaJIT or Luau bytecode.\n\nParser details:\n{e}"))
    })?;
    Ok(engine::run(&proto, mode, flatten))
}
