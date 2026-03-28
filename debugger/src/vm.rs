/// Symbolic Lua VM — tracks concrete register values where possible.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

// ---------------------------------------------------------------------------
// Global string metatable (set by stdlib::build_globals)
// ---------------------------------------------------------------------------

thread_local! {
    static STRING_METATABLE: RefCell<Option<LuaTable>> = RefCell::new(None);
}

/// Called by `build_globals` to register the shared string metatable.
pub fn set_string_metatable(mt: LuaTable) {
    STRING_METATABLE.with(|s| *s.borrow_mut() = Some(mt));
}

/// Returns the shared string metatable (if one has been registered).
pub fn get_string_metatable() -> Option<LuaTable> {
    STRING_METATABLE.with(|s| s.borrow().clone())
}

use disassembler::{
    decompile_constant, get_opcode, getarg_a, getarg_b, getarg_c, getarg_bx, getarg_sbx, OpCode,
    Proto,
};

// ---------------------------------------------------------------------------
// NativeFn wrapper  (PartialEq = always false, which matches Lua semantics)
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct NativeFn(pub Rc<dyn Fn(&[LuaValue]) -> Vec<LuaValue>>);

impl PartialEq for NativeFn {
    fn eq(&self, _: &Self) -> bool { false }
}
impl std::fmt::Debug for NativeFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<function>")
    }
}

// ---------------------------------------------------------------------------
// LuaTable
// ---------------------------------------------------------------------------

/// Key that can live in the hash part of a table.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum HashableKey {
    Int(i64),
    Str(Vec<u8>),
    Bool(bool),
}

pub struct LuaTableInner {
    /// Array part: 1-indexed, stored at offset -1 (index 1 → array[0]).
    pub array: Vec<LuaValue>,
    /// Hash part: preserves insertion order so `next()` is deterministic.
    pub pairs: Vec<(HashableKey, LuaValue)>,
    /// Optional metatable.
    pub metatable: Option<LuaTable>,
}

impl LuaTableInner {
    fn hash_get(&self, k: &HashableKey) -> Option<&LuaValue> {
        self.pairs.iter().find(|(hk, _)| hk == k).map(|(_, v)| v)
    }
    fn hash_set(&mut self, k: HashableKey, v: LuaValue) {
        if let Some(slot) = self.pairs.iter_mut().find(|(hk, _)| hk == &k) {
            slot.1 = v;
        } else {
            self.pairs.push((k, v));
        }
    }
}

#[derive(Clone)]
pub struct LuaTable(pub Rc<RefCell<LuaTableInner>>);

impl PartialEq for LuaTable {
    fn eq(&self, other: &Self) -> bool { Rc::ptr_eq(&self.0, &other.0) }
}

impl std::fmt::Debug for LuaTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<table {:p}>", Rc::as_ptr(&self.0))
    }
}

impl LuaTable {
    pub fn new() -> Self {
        LuaTable(Rc::new(RefCell::new(LuaTableInner {
            array: Vec::new(),
            pairs: Vec::new(),
            metatable: None,
        })))
    }

    /// Returns the raw metatable (no `__metatable` protection).
    pub fn get_metatable(&self) -> Option<LuaTable> {
        self.0.borrow().metatable.clone()
    }

    /// Sets (or clears) the metatable.
    pub fn set_metatable(&self, mt: Option<LuaTable>) {
        self.0.borrow_mut().metatable = mt;
    }

    /// Looks up a metamethod by name in this table's metatable.
    /// Returns `Nil` if there is no metatable or the field is absent.
    pub fn get_metamethod(&self, name: &str) -> LuaValue {
        match &self.0.borrow().metatable {
            None => LuaValue::Nil,
            Some(mt) => mt.get_str(name),
        }
    }

    pub fn get(&self, key: &LuaValue) -> LuaValue {
        // Normalize: float-that-is-integer → integer (Lua semantics: t[1.0] == t[1])
        let normalized;
        let key = match key {
            LuaValue::Float(f) if f.fract() == 0.0 => {
                normalized = LuaValue::Int(*f as i64);
                &normalized
            }
            other => other,
        };
        let inner = self.0.borrow();
        match key {
            LuaValue::Int(i) if *i >= 1 => inner
                .array
                .get((*i - 1) as usize)
                .cloned()
                .unwrap_or(LuaValue::Nil),
            LuaValue::Unknown(hint) => {
                // Unknown key — result is indeterminate, preserve as Unknown
                LuaValue::Unknown(format!("?[{}]", hint))
            }
            _ => {
                match to_hash_key(key) {
                    Some(hk) => inner.hash_get(&hk).cloned().unwrap_or(LuaValue::Nil),
                    None => LuaValue::Nil,
                }
            }
        }
    }

    pub fn rawset(&self, key: LuaValue, val: LuaValue) {
        // Normalize: float-that-is-integer → integer (Lua semantics: t[1.0] == t[1])
        let key = match key {
            LuaValue::Float(f) if f.fract() == 0.0 => LuaValue::Int(f as i64),
            other => other,
        };
        let mut inner = self.0.borrow_mut();
        match &key {
            LuaValue::Int(i) if *i >= 1 => {
                let idx = (*i - 1) as usize;
                if idx < inner.array.len() {
                    inner.array[idx] = val;
                    // Truncate trailing Nils so #t reflects sequence length correctly.
                    while inner.array.last() == Some(&LuaValue::Nil) {
                        inner.array.pop();
                    }
                } else if idx == inner.array.len() {
                    inner.array.push(val);
                    // Migrate sequential hash entries into array
                    loop {
                        let next = (inner.array.len() + 1) as i64;
                        if let Some(pos) = inner.pairs.iter().position(|(k, _)| k == &HashableKey::Int(next)) {
                            let v = inner.pairs.remove(pos).1;
                            inner.array.push(v);
                        } else {
                            break;
                        }
                    }
                } else {
                    inner.hash_set(HashableKey::Int(*i), val);
                }
            }
            _ => {
                if let Some(hk) = to_hash_key(&key) {
                    inner.hash_set(hk, val);
                }
            }
        }
    }

    /// Lua-style table length (border of the array part).
    pub fn length(&self) -> i64 {
        self.0.borrow().array.len() as i64
    }

    /// Convenience: set by string key.
    pub fn set_str(&self, key: &str, val: LuaValue) {
        self.rawset(LuaValue::Str(key.as_bytes().to_vec()), val);
    }

    /// Convenience: get by string key.
    pub fn get_str(&self, key: &str) -> LuaValue {
        self.get(&LuaValue::Str(key.as_bytes().to_vec()))
    }

    /// Iterator support for `next(t, key)`.
    pub fn next_pair(&self, after: &LuaValue) -> Option<(LuaValue, LuaValue)> {
        // Normalize float key
        let normalized;
        let after = match after {
            LuaValue::Float(f) if f.fract() == 0.0 => {
                normalized = LuaValue::Int(*f as i64);
                &normalized
            }
            other => other,
        };
        let inner = self.0.borrow();
        // Build a flat ordered key list: array first, then hash
        let total_array = inner.array.len();
        let _total_hash = inner.pairs.len();

        // Determine position of `after`
        let start = match after {
            LuaValue::Nil => 0, // start from beginning
            LuaValue::Int(i) if *i >= 1 && (*i as usize) <= total_array => *i as usize,
            _ => {
                let hk = to_hash_key(after)?;
                let pos = inner.pairs.iter().position(|(k, _)| k == &hk)?;
                total_array + pos + 1
            }
        };

        // Return the entry at `start`
        if start < total_array {
            let v = inner.array.get(start).cloned()?;
            if matches!(v, LuaValue::Nil) {
                // sparse array — skip
                drop(inner);
                return self.next_pair(&LuaValue::Int(start as i64 + 1));
            }
            Some((LuaValue::Int(start as i64 + 1), v))
        } else {
            let hash_idx = start - total_array;
            let (k, v) = inner.pairs.get(hash_idx)?;
            Some((hash_key_to_value(k), v.clone()))
        }
    }

    pub fn display_short(&self) -> String {
        let inner = self.0.borrow();
        let n_arr = inner.array.len();
        let n_hash = inner.pairs.len();
        if n_arr == 0 && n_hash == 0 {
            return "{}".to_string();
        }
        let mut parts = Vec::new();
        for (i, v) in inner.array.iter().enumerate().take(4) {
            parts.push(format!("[{}]={}", i + 1, v.display_short()));
        }
        for (k, v) in inner.pairs.iter().take(4usize.saturating_sub(parts.len())) {
            parts.push(format!("{}={}", hash_key_display(k), v.display_short()));
        }
        let total = n_arr + n_hash;
        if total > 4 {
            format!("{{{}, ...({} total)}}", parts.join(", "), total)
        } else {
            format!("{{{}}}", parts.join(", "))
        }
    }
}

fn to_hash_key(v: &LuaValue) -> Option<HashableKey> {
    match v {
        LuaValue::Int(i) => Some(HashableKey::Int(*i)),
        LuaValue::Str(s) => Some(HashableKey::Str(s.clone())),
        LuaValue::Bool(b) => Some(HashableKey::Bool(*b)),
        LuaValue::Float(f) if f.fract() == 0.0 => Some(HashableKey::Int(*f as i64)),
        _ => None,
    }
}

fn hash_key_to_value(k: &HashableKey) -> LuaValue {
    match k {
        HashableKey::Int(i) => LuaValue::Int(*i),
        HashableKey::Str(s) => LuaValue::Str(s.clone()),
        HashableKey::Bool(b) => LuaValue::Bool(*b),
    }
}

fn hash_key_display(k: &HashableKey) -> String {
    match k {
        HashableKey::Int(i) => i.to_string(),
        HashableKey::Str(s) => format!("\"{}\"", String::from_utf8_lossy(s)),
        HashableKey::Bool(b) => b.to_string(),
    }
}

// ---------------------------------------------------------------------------
// LuaValue
// ---------------------------------------------------------------------------

/// A captured Lua closure: an executable proto + shared upvalue cells.
#[derive(Clone)]
pub struct LuaClosure {
    pub proto: Rc<Proto>,
    pub upvalues: Vec<Rc<RefCell<LuaValue>>>,
}

impl PartialEq for LuaClosure {
    fn eq(&self, _: &Self) -> bool { false } // closures never equal
}

impl std::fmt::Debug for LuaClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<closure line={}>", self.proto.linedefined)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum LuaValue {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(Vec<u8>),
    Table(LuaTable),
    Function(NativeFn),
    Closure(LuaClosure),
    /// Opaque value we couldn't compute.
    Unknown(String),
}

impl LuaValue {
    pub fn is_truthy(&self) -> Option<bool> {
        match self {
            LuaValue::Nil => Some(false),
            LuaValue::Bool(b) => Some(*b),
            LuaValue::Int(_) | LuaValue::Float(_) | LuaValue::Str(_)
            | LuaValue::Table(_) | LuaValue::Function(_) | LuaValue::Closure(_) => Some(true),
            // Unknown values come from unresolved function returns. In Lua only
            // nil and false are falsy; everything else is truthy. Treat Unknown
            // as truthy so the symbolic VM follows the success/continuation path
            // past guards like `if string.format(...) then ...`.
            LuaValue::Unknown(_) => Some(true),
        }
    }

    /// Lua `type()` name.
    pub fn lua_type(&self) -> &'static str {
        match self {
            LuaValue::Nil => "nil",
            LuaValue::Bool(_) => "boolean",
            LuaValue::Int(_) | LuaValue::Float(_) => "number",
            LuaValue::Str(_) => "string",
            LuaValue::Table(_) => "table",
            LuaValue::Function(_) | LuaValue::Closure(_) => "function",
            LuaValue::Unknown(_) => "unknown",
        }
    }

    /// More detailed name for `info reg` display.
    pub fn type_name(&self) -> &'static str {
        match self {
            LuaValue::Nil => "nil",
            LuaValue::Bool(_) => "boolean",
            LuaValue::Int(_) => "number<int>",
            LuaValue::Float(_) => "number<float>",
            LuaValue::Str(_) => "string",
            LuaValue::Table(_) => "table",
            LuaValue::Function(_) => "function",
            LuaValue::Closure(c) => {
                let _ = c;
                "function<closure>"
            }
            LuaValue::Unknown(_) => "unknown",
        }
    }

    pub fn display_value(&self) -> String {
        match self {
            LuaValue::Nil => "nil".to_string(),
            LuaValue::Bool(b) => b.to_string(),
            LuaValue::Int(i) => i.to_string(),
            LuaValue::Float(f) => {
                let s = format!("{}", f);
                if s.contains('.') || s.contains('e') { s } else { format!("{}.0", s) }
            }
            LuaValue::Str(s) => format!("\"{}\"", escape_bytes(s)),
            LuaValue::Table(t) => t.display_short(),
            LuaValue::Function(_) => "<function>".to_string(),
            LuaValue::Closure(c) => format!("<closure line={}>", c.proto.linedefined),
            LuaValue::Unknown(h) => format!("?[{}]", h),
        }
    }

    /// Compact display for nested use (inside tables).
    pub fn display_short(&self) -> String {
        match self {
            LuaValue::Table(_) => "<table>".to_string(),
            LuaValue::Function(_) => "<fn>".to_string(),
            LuaValue::Closure(c) => format!("<closure:{}>", c.proto.linedefined),
            other => other.display_value(),
        }
    }

    pub fn to_number(&self) -> Option<LuaValue> {
        match self {
            LuaValue::Int(i) => Some(LuaValue::Int(*i)),
            LuaValue::Float(f) => Some(LuaValue::Float(*f)),
            LuaValue::Str(s) => {
                let s = String::from_utf8_lossy(s);
                let s = s.trim();
                if let Ok(i) = s.parse::<i64>() { return Some(LuaValue::Int(i)); }
                if let Ok(f) = s.parse::<f64>() { return Some(LuaValue::Float(f)); }
                if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
                    if let Ok(i) = i64::from_str_radix(hex, 16) { return Some(LuaValue::Int(i)); }
                }
                None
            }
            _ => None,
        }
    }
}

impl std::fmt::Display for LuaValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_value())
    }
}

fn escape_bytes(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &b in bytes {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7E => out.push(b as char),
            _ => out.push_str(&format!("\\x{:02x}", b)),
        }
    }
    out
}

/// Parse a `LuaValue` from a user-typed expression string.
pub fn parse_value(s: &str) -> LuaValue {
    let s = s.trim();
    if s == "nil"   { return LuaValue::Nil; }
    if s == "true"  { return LuaValue::Bool(true); }
    if s == "false" { return LuaValue::Bool(false); }
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        if let Ok(i) = i64::from_str_radix(hex, 16) { return LuaValue::Int(i); }
    }
    if let Ok(i) = s.parse::<i64>()  { return LuaValue::Int(i); }
    if let Ok(f) = s.parse::<f64>()  { return LuaValue::Float(f); }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return LuaValue::Str(s[1..s.len() - 1].as_bytes().to_vec());
    }
    LuaValue::Unknown(s.to_string())
}

// ---------------------------------------------------------------------------
// VmState
// ---------------------------------------------------------------------------

pub struct VmState {
    pub pc: usize,
    pub regs: Vec<LuaValue>,
    /// Shared upvalue cells for the current function's captured upvalues.
    pub upvalues: Vec<Rc<RefCell<LuaValue>>>,
    /// Register slots that have been captured by inner closures — maps reg index → shared cell.
    /// When set_reg writes to a captured register, it also updates the cell so inner closures see the new value.
    pub open_upvalues: HashMap<usize, Rc<RefCell<LuaValue>>>,
    pub halted: bool,
}

impl VmState {
    pub fn new(proto: &Proto, globals: &LuaTable) -> Self {
        let nregs = (proto.maxstacksize as usize).max(1);
        let nups = proto.num_upvalues as usize;
        let upvalues = (0..nups)
            .map(|i| {
                // Seed the _ENV upvalue with the globals table
                let name = proto.upvalue_names.get(i).map(|s| s.as_str()).unwrap_or("");
                let v = if name == "_ENV" || (i == 0 && nups == 1 && name.is_empty()) {
                    LuaValue::Table(globals.clone())
                } else {
                    LuaValue::Unknown(format!("U{}", i))
                };
                Rc::new(RefCell::new(v))
            })
            .collect();
        VmState {
            pc: 0,
            regs: vec![LuaValue::Nil; nregs],
            upvalues,
            open_upvalues: HashMap::new(),
            halted: false,
        }
    }

    pub fn reset(&mut self, proto: &Proto, globals: &LuaTable) {
        *self = VmState::new(proto, globals);
    }

    pub fn reg(&self, r: usize) -> LuaValue {
        // If this register is backed by an open upvalue cell, read from the cell.
        // Child closures write to the cell via SETUPVAL; without this the parent
        // would see the stale value from when the closure was created.
        if let Some(cell) = self.open_upvalues.get(&r) {
            return cell.borrow().clone();
        }
        self.regs.get(r).cloned().unwrap_or(LuaValue::Nil)
    }

    pub fn set_reg(&mut self, r: usize, v: LuaValue) {
        if r < self.regs.len() {
            self.regs[r] = v.clone();
            // Propagate write to any open upvalue cell that was created for this register.
            if let Some(cell) = self.open_upvalues.get(&r) {
                *cell.borrow_mut() = v;
            }
        }
    }

    /// Read upvalue u, returning the value by clone.
    pub fn upv(&self, u: usize) -> LuaValue {
        self.upvalues.get(u)
            .map(|cell| cell.borrow().clone())
            .unwrap_or(LuaValue::Nil)
    }

    /// Write upvalue u through its shared cell.
    pub fn set_upv(&self, u: usize, v: LuaValue) {
        if let Some(cell) = self.upvalues.get(u) {
            *cell.borrow_mut() = v;
        }
    }

    /// Resolve an RK operand (register or constant).
    pub fn rk(&self, proto: &Proto, rk: usize) -> LuaValue {
        const BITRK: usize = 1 << 8;
        if rk & BITRK != 0 {
            constant_to_value(proto, rk & !BITRK)
        } else {
            self.reg(rk)
        }
    }
}

pub fn constant_to_value(proto: &Proto, idx: usize) -> LuaValue {
    use luac_parser::{LuaConstant, LuaNumber};
    match proto.constants.get(idx) {
        None => LuaValue::Nil,
        Some(c) => match c {
            LuaConstant::Null => LuaValue::Nil,
            LuaConstant::Bool(b) => LuaValue::Bool(*b),
            LuaConstant::Number(n) => match n {
                LuaNumber::Integer(i) => LuaValue::Int(*i),
                LuaNumber::Float(f) => LuaValue::Float(*f),
            },
            LuaConstant::String(s) => LuaValue::Str(s.to_vec()),
            _ => LuaValue::Unknown(decompile_constant(proto, idx)),
        },
    }
}

// ---------------------------------------------------------------------------
// StepResult
// ---------------------------------------------------------------------------

pub enum StepResult {
    Ok,
    Jumped { from: usize, to: usize },
    Returned(Vec<LuaValue>),
    Halted,
    UnknownBranch(String),
}

// ---------------------------------------------------------------------------
// step() — execute one instruction symbolically
// ---------------------------------------------------------------------------

pub fn step(state: &mut VmState, proto: &Proto) -> StepResult {
    if state.halted {
        return StepResult::Halted;
    }
    if state.pc >= proto.sizecode {
        state.halted = true;
        return StepResult::Halted;
    }

    let i = proto.code[state.pc];
    let op = get_opcode(i);
    let a = getarg_a(i) as usize;
    let b = getarg_b(i) as usize;
    let c = getarg_c(i) as usize;
    let bx = getarg_bx(i) as usize;
    let sbx = getarg_sbx(i);

    macro_rules! next {
        () => {{
            state.pc += 1;
            StepResult::Ok
        }};
    }

    use OpCode::*;
    match op {
        // ------------------------------------------------------------------
        // Loads
        // ------------------------------------------------------------------
        Move => {
            let v = state.reg(b).clone();
            state.set_reg(a, v);
            next!()
        }
        LoadK => {
            let v = constant_to_value(proto, bx);
            state.set_reg(a, v);
            next!()
        }
        LoadKx => {
            let extra_idx = if state.pc + 1 < proto.sizecode {
                (proto.code[state.pc + 1] >> 6) as usize
            } else { 0 };
            let v = constant_to_value(proto, extra_idx);
            state.set_reg(a, v);
            state.pc += 2;
            StepResult::Ok
        }
        LoadBool => {
            state.set_reg(a, LuaValue::Bool(b != 0));
            state.pc += if c != 0 { 2 } else { 1 };
            StepResult::Ok
        }
        LoadNil => {
            for r in a..=a + b {
                state.set_reg(r, LuaValue::Nil);
            }
            next!()
        }

        // ------------------------------------------------------------------
        // Upvalues
        // ------------------------------------------------------------------
        GetUpVal => {
            let v = state.upv(b);
            state.set_reg(a, v);
            next!()
        }
        SetUpVal => {
            let v = state.reg(a).clone();
            state.set_upv(b, v);
            next!()
        }

        // ------------------------------------------------------------------
        // Table access
        // ------------------------------------------------------------------
        GetTabUp | GetGlobal => {
            let tbl = state.upv(b);
            let key = if op == GetGlobal {
                constant_to_value(proto, bx)
            } else {
                state.rk(proto, c)
            };
            let result = table_get(&tbl, &key, || format!("U{}[{}]", b, key));
            if matches!(result, LuaValue::Nil) {
                if let LuaValue::Str(ref s) = key {
                    eprintln!("[miss] PC={} key \"{}\" not found in U{}", state.pc, String::from_utf8_lossy(s), b);
                }
            }
            state.set_reg(a, result);
            next!()
        }
        GetTable => {
            let tbl = state.reg(b).clone();
            let key = state.rk(proto, c);
            let result = table_get(&tbl, &key, || format!("R{}[{}]", b, key));
            if matches!(result, LuaValue::Nil) {
                if let LuaValue::Str(ref s) = key {
                    eprintln!("[miss] PC={} key \"{}\" not found in R{}", state.pc, String::from_utf8_lossy(s), b);
                }
            }
            state.set_reg(a, result);
            next!()
        }
        SetTabUp => {
            let key = state.rk(proto, b);
            let val = state.rk(proto, c);
            let tbl = state.upv(a);
            if let LuaValue::Table(t) = &tbl {
                t.rawset(key, val);
            }
            next!()
        }
        SetTable => {
            let key = state.rk(proto, b);
            let val = state.rk(proto, c);
            let tbl = state.reg(a).clone();
if let LuaValue::Table(t) = &tbl {
                t.rawset(key, val);
            }
            next!()
        }
        SetGlobal => {
            let key = constant_to_value(proto, bx);
            let val = state.reg(a).clone();
            let tbl = state.upv(0);
            if let LuaValue::Table(t) = &tbl {
                t.rawset(key, val);
            }
            next!()
        }
        NewTable => {
            state.set_reg(a, LuaValue::Table(LuaTable::new()));
            next!()
        }
        Self_ => {
            let obj = state.reg(b).clone();
            let key = state.rk(proto, c);
            let method = table_get(&obj, &key, || format!("method[{}]", key));
            state.set_reg(a + 1, obj);
            state.set_reg(a, method);
            next!()
        }
        SetList => {
            // R[a][(c-1)*FPF+1 .. (c-1)*FPF+b] = R[a+1..a+b]
            let tbl = state.reg(a).clone();
            if let LuaValue::Table(t) = &tbl {
                let base = if c == 0 { 0 } else { (c - 1) * 50 };
                let count = if b == 0 {
                    // b=0: use all non-empty registers from a+1
                    (a + 1..state.regs.len())
                        .rev()
                        .find(|&r| !matches!(state.reg(r), LuaValue::Nil))
                        .map(|r| r - a)
                        .unwrap_or(0)
                } else { b };
                for i in 1..=count {
                    let v = state.reg(a + i).clone();
                    t.rawset(LuaValue::Int((base + i) as i64), v);
                }
            }
            next!()
        }

        // ------------------------------------------------------------------
        // Arithmetic / bitwise / string
        // ------------------------------------------------------------------
        Add | Sub | Mul | Div | Mod | Pow | IDiv | Band | Bor | BXor | Shl | Shr => {
            let lhs = state.rk(proto, b);
            let rhs = state.rk(proto, c);
            // Try string coercion for arithmetic
            let lhs = coerce_to_number(lhs);
            let rhs = coerce_to_number(rhs);
            let result = arith(op, &lhs, &rhs);
            if proto.linedefined == 33 {
                eprintln!("[d33] PC={} {:?} R{}={} R/K{}={} => R{}={}", state.pc, op, b, lhs, c, rhs, a, result);
            }
            state.set_reg(a, result);
            next!()
        }
        Unm => {
            let v = coerce_to_number(state.reg(b).clone());
            let r = match &v {
                LuaValue::Int(i) => LuaValue::Int(i.wrapping_neg()),
                LuaValue::Float(f) => LuaValue::Float(-f),
                _ => LuaValue::Unknown(format!("-{}", v)),
            };
            state.set_reg(a, r);
            next!()
        }
        Not => {
            let r = match state.reg(b).is_truthy() {
                Some(t) => LuaValue::Bool(!t),
                None    => LuaValue::Unknown(format!("not {}", state.reg(b))),
            };
            state.set_reg(a, r);
            next!()
        }
        Len => {
            let r = match state.reg(b) {
                LuaValue::Str(s)  => LuaValue::Int(s.len() as i64),
                LuaValue::Table(t) => LuaValue::Int(t.length()),
                v => LuaValue::Unknown(format!("#{}", v)),
            };
            state.set_reg(a, r);
            next!()
        }
        BNot => {
            let r = match state.reg(b) {
                LuaValue::Int(i) => LuaValue::Int(!i),
                v => LuaValue::Unknown(format!("~{}", v)),
            };
            state.set_reg(a, r);
            next!()
        }
        Concat => {
            let mut bytes: Vec<u8> = Vec::new();
            let mut all_known = true;
            let mut parts: Vec<String> = Vec::new();
            for r in b..=c {
                match state.reg(r) {
                    LuaValue::Str(s)   => { bytes.extend_from_slice(&s); parts.push(String::from_utf8_lossy(&s).into_owned()); }
                    LuaValue::Int(i)   => { let s = i.to_string(); bytes.extend_from_slice(s.as_bytes()); parts.push(s); }
                    LuaValue::Float(f) => { let s = lua_float_tostring(f); bytes.extend_from_slice(s.as_bytes()); parts.push(s); }
                    other => { all_known = false; parts.push(format!("?{}", other)); }
                }
            }
            state.set_reg(a, if all_known { LuaValue::Str(bytes) } else { LuaValue::Unknown(parts.join("..")) });
            next!()
        }

        // ------------------------------------------------------------------
        // Control flow
        // ------------------------------------------------------------------
        Jmp => {
            let from = state.pc;
            let to = (state.pc as i32 + 1 + sbx) as usize;
            state.pc = to;
            StepResult::Jumped { from, to }
        }
        Eq | Lt | Le => {
            let lhs = state.rk(proto, b);
            let rhs = state.rk(proto, c);
            match compare(op, &lhs, &rhs) {
                Some(result) => {
                    if result != (a != 0) {
                        // skip JMP
                        state.pc += 2;
                        StepResult::Ok
                    } else {
                        let jmp_i = proto.code[state.pc + 1];
                        let jmp_sbx = getarg_sbx(jmp_i);
                        let from = state.pc;
                        let to = (state.pc as i32 + 2 + jmp_sbx) as usize;
                        state.pc = to;
                        StepResult::Jumped { from, to }
                    }
                }
                None => {
                    state.pc += 1;
                    StepResult::UnknownBranch(format!("{} {} {}  (A={})",
                        lhs, disassembler::opstr(op), rhs, a))
                }
            }
        }
        Test => {
            match state.reg(a).is_truthy() {
                Some(truthy) => {
                    if truthy != (c != 0) {
                        state.pc += 2; // skip JMP
                        StepResult::Ok
                    } else {
                        let jmp_i = proto.code[state.pc + 1];
                        let jmp_sbx = getarg_sbx(jmp_i);
                        let from = state.pc;
                        let to = (state.pc as i32 + 2 + jmp_sbx) as usize;
                        state.pc = to;
                        StepResult::Jumped { from, to }
                    }
                }
                None => {
                    state.pc += 1;
                    StepResult::UnknownBranch(format!("test R{}={}", a, state.reg(a)))
                }
            }
        }
        TestSet => {
            let val = state.reg(b).clone();
            match val.is_truthy() {
                Some(truthy) => {
                    if truthy == (c != 0) {
                        state.set_reg(a, val);
                        state.pc += 2; // skip JMP
                    } else {
                        let jmp_i = proto.code[state.pc + 1];
                        let jmp_sbx = getarg_sbx(jmp_i);
                        let from = state.pc;
                        let to = (state.pc as i32 + 2 + jmp_sbx) as usize;
                        state.pc = to;
                        return StepResult::Jumped { from, to };
                    }
                    StepResult::Ok
                }
                None => {
                    state.set_reg(a, LuaValue::Unknown(format!("testset R{}", b)));
                    state.pc += 1;
                    StepResult::UnknownBranch(format!("testset R{}={}", b, state.reg(b)))
                }
            }
        }

        // ------------------------------------------------------------------
        // Calls
        // ------------------------------------------------------------------
        Call => {
            let func = state.reg(a).clone();
            let nargs = if b == 0 {
                // variadic from previous call: collect all non-nil from a+1
                (a + 1..state.regs.len())
                    .take_while(|&r| !matches!(state.reg(r), LuaValue::Nil))
                    .count()
            } else { b - 1 };
            let args: Vec<LuaValue> = (a + 1..a + 1 + nargs)
                .map(|r| state.reg(r).clone())
                .collect();

            {
                let arg_strs: Vec<String> = args.iter().map(|v| v.display_short()).collect();
                eprintln!("[call] PC={} R{}={} ({})", state.pc, a, func.display_short(), arg_strs.join(", "));
            }

            let results = call_value(&func, &args);

            let ret_count = if c == 0 { results.len().max(1) } else { c.saturating_sub(1) };
            for idx in 0..ret_count {
                let v = results.get(idx).cloned().unwrap_or(LuaValue::Nil);
                state.set_reg(a + idx, v);
            }
            // Clear registers beyond what the function returned
            for idx in results.len()..ret_count {
                state.set_reg(a + idx, LuaValue::Nil);
            }
            next!()
        }
        TailCall => {
            let func = state.reg(a).clone();
            let nargs = if b == 0 { 0 } else { b - 1 };
            let args: Vec<LuaValue> = (a + 1..a + 1 + nargs)
                .map(|r| state.reg(r).clone())
                .collect();

            {
                let arg_strs: Vec<String> = args.iter().map(|v| v.display_short()).collect();
                eprintln!("[tail] PC={} R{}={} ({})", state.pc, a, func.display_short(), arg_strs.join(", "));
            }

            let results = call_value(&func, &args);
            state.halted = true;
            StepResult::Returned(results)
        }
        Return => {
            let mut vals = Vec::new();
            if b >= 2 {
                for r in a..a + b - 1 {
                    vals.push(state.reg(r).clone());
                }
            } else if b == 0 {
                for r in a..state.regs.len() {
                    match state.reg(r) {
                        LuaValue::Nil => break,
                        v => vals.push(v.clone()),
                    }
                }
            }
            state.halted = true;
            StepResult::Returned(vals)
        }

        // ------------------------------------------------------------------
        // Numeric for
        // ------------------------------------------------------------------
        ForPrep => {
            let init = coerce_to_number(state.reg(a).clone());
            let s    = coerce_to_number(state.reg(a + 2).clone());
            state.set_reg(a, arith(Sub, &init, &s));
            let from = state.pc;
            let to = (state.pc as i32 + 1 + sbx) as usize;
            state.pc = to;
            StepResult::Jumped { from, to }
        }
        ForLoop => {
            let v     = coerce_to_number(state.reg(a).clone());
            let limit = coerce_to_number(state.reg(a + 1).clone());
            let s     = coerce_to_number(state.reg(a + 2).clone());
            let new_v = arith(Add, &v, &s);
            state.set_reg(a, new_v.clone());
            state.set_reg(a + 3, new_v.clone());

            let in_range = match (&new_v, &s, &limit) {
                (LuaValue::Int(v), LuaValue::Int(step), LuaValue::Int(lim)) =>
                    Some(if *step >= 0 { v <= lim } else { v >= lim }),
                (LuaValue::Float(v), LuaValue::Float(step), LuaValue::Float(lim)) =>
                    Some(if *step >= 0.0 { v <= lim } else { v >= lim }),
                _ => None,
            };

            match in_range {
                Some(true) => {
                    let from = state.pc;
                    let to = (state.pc as i32 + 1 + sbx) as usize;
                    state.pc = to;
                    StepResult::Jumped { from, to }
                }
                Some(false) => next!(),
                None => {
                    state.pc += 1;
                    StepResult::UnknownBranch(format!("forloop R{}", a))
                }
            }
        }

        // ------------------------------------------------------------------
        // Generic for
        // ------------------------------------------------------------------
        LuaDecTForLoop => {
            // TFORCALL: calls R[a](R[a+1], R[a+2]) → R[a+3..a+2+c]
            let func = state.reg(a).clone();
            let args = vec![state.reg(a + 1).clone(), state.reg(a + 2).clone()];
            let results = call_value(&func, &args);
            for idx in 0..c {
                let v = results.get(idx).cloned().unwrap_or(LuaValue::Nil);
                state.set_reg(a + 3 + idx, v);
            }
            next!()
        }
        TForLoop => {
            // Lua 5.3: if R[a+1] ~= nil then { R[a] = R[a+1]; pc += sBx }
            // R[a+1] is the first result slot of the preceding TFORCALL (the key).
            let val = state.reg(a + 1).clone();
            match val.is_truthy() {
                Some(false) => next!(),
                Some(true) => {
                    state.set_reg(a, val);
                    let from = state.pc;
                    let to = (state.pc as i32 + 1 + sbx) as usize;
                    state.pc = to;
                    StepResult::Jumped { from, to }
                }
                None => {
                    state.pc += 1;
                    StepResult::UnknownBranch(format!("tforloop R{}", a + 1))
                }
            }
        }

        // ------------------------------------------------------------------
        // Other
        // ------------------------------------------------------------------
        Closure => {
            if let Some(child) = proto.p.get(bx) {
                // Capture upvalues using shared Rc<RefCell> cells.
                // on_stack=true  → share/create a cell tied to a parent register.
                // on_stack=false → clone the parent's own upvalue cell (already shared).
                let mut captured: Vec<Rc<RefCell<LuaValue>>> = Vec::new();
                let mut has_degraded = false;
                for (ui, info) in child.upvalue_infos.iter().enumerate() {
                    let cell: Rc<RefCell<LuaValue>> = if info.on_stack {
                        let reg = info.idx as usize;
                        // Reuse existing cell if this register was already captured.
                        let reg_val = state.regs.get(reg).cloned().unwrap_or(LuaValue::Nil);
                        if let Some(existing) = state.open_upvalues.get(&reg) {
                            existing.clone()
                        } else {
                            let new_cell = Rc::new(RefCell::new(reg_val));
                            state.open_upvalues.insert(reg, new_cell.clone());
                            new_cell
                        }
                    } else {
                        // Share parent's upvalue cell directly.
                        state.upvalues.get(info.idx as usize)
                            .cloned()
                            .unwrap_or_else(|| Rc::new(RefCell::new(
                                LuaValue::Unknown(format!("U{}", info.idx))
                            )))
                    };
                    let v = cell.borrow().clone();
                    if matches!(v, LuaValue::Unknown(_) | LuaValue::Nil) {
                        let src = if info.on_stack {
                            format!("R{}", info.idx)
                        } else {
                            format!("U{}", info.idx)
                        };
                        eprintln!("[clos] PC={} line={} U{}←{} = {}",
                            state.pc, child.linedefined, ui, src, v.display_short());
                        has_degraded = true;
                    }
                    captured.push(cell);
                }
                if has_degraded {
                    eprintln!("[clos] PC={} closure line={} created with degraded upvalues — decryption may fail",
                        state.pc, child.linedefined);
                }
                let closure = LuaClosure {
                    proto: Rc::new(child.clone()),
                    upvalues: captured,
                };
                state.set_reg(a, LuaValue::Closure(closure));
            } else {
                state.set_reg(a, LuaValue::Unknown(format!("closure(proto {})", bx)));
            }
            next!()
        }
        VarArg => {
            let count = if b <= 1 { 1 } else { b - 1 };
            for r in a..a + count {
                state.set_reg(r, LuaValue::Unknown("...".into()));
            }
            next!()
        }
        Close => {
            // Seal all open upvalues from register `a` onward.
            // After CLOSE, the register is out of scope — remove cells so future
            // set_reg writes to those slots don't propagate into the sealed upvalue.
            let sealed: Vec<usize> = state.open_upvalues.keys()
                .filter(|&&r| r >= a)
                .cloned()
                .collect();
            for r in sealed {
                state.open_upvalues.remove(&r);
            }
            next!()
        }
        ExtraArg | Unknown => next!(),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Table/string index with `__index` metamethod support (up to 10 levels deep).
pub fn table_get(tbl: &LuaValue, key: &LuaValue, fallback: impl Fn() -> String) -> LuaValue {
    table_get_inner(tbl, key, &fallback, 10)
}

fn table_get_inner(tbl: &LuaValue, key: &LuaValue, fallback: &dyn Fn() -> String, depth: u8) -> LuaValue {
    if depth == 0 {
        return LuaValue::Unknown(format!("__index loop"));
    }
    match tbl {
        LuaValue::Table(t) => {
            // Unknown key → result is indeterminate regardless of __index
            if matches!(key, LuaValue::Unknown(_)) {
                return LuaValue::Unknown(fallback());
            }
            let v = t.get(key);
            if !matches!(v, LuaValue::Nil) {
                return v;
            }
            // Raw get returned nil — check __index metamethod
            let index_mm = t.get_metamethod("__index");
            match index_mm {
                LuaValue::Nil => LuaValue::Nil,
                LuaValue::Table(_) => table_get_inner(&index_mm, key, fallback, depth - 1),
                LuaValue::Function(ref f) => {
                    f.0(&[tbl.clone(), key.clone()]).into_iter().next().unwrap_or(LuaValue::Nil)
                }
                _ => LuaValue::Unknown(fallback()),
            }
        }
        LuaValue::Nil => LuaValue::Nil,
        LuaValue::Str(_) => {
            // Strings delegate to the string metatable's __index (= string lib)
            match get_string_metatable() {
                Some(mt) => {
                    let index = mt.get_str("__index");
                    match index {
                        LuaValue::Table(string_lib) => string_lib.get(key),
                        LuaValue::Function(ref f) => {
                            f.0(&[tbl.clone(), key.clone()]).into_iter().next().unwrap_or(LuaValue::Nil)
                        }
                        _ => LuaValue::Unknown(fallback()),
                    }
                }
                None => LuaValue::Unknown(fallback()),
            }
        }
        _ => LuaValue::Unknown(fallback()),
    }
}

pub fn call_value(func: &LuaValue, args: &[LuaValue]) -> Vec<LuaValue> {
    match func {
        LuaValue::Function(f) => f.0(args),
        LuaValue::Closure(c) => run_closure(c, args),
        LuaValue::Table(t) => {
            // Check __call metamethod
            let call_mm = t.get_metamethod("__call");
            match call_mm {
                LuaValue::Function(f) => {
                    let mut full_args = vec![func.clone()];
                    full_args.extend_from_slice(args);
                    f.0(&full_args)
                }
                LuaValue::Closure(c) => {
                    let mut full_args = vec![func.clone()];
                    full_args.extend_from_slice(args);
                    run_closure(&c, &full_args)
                }
                LuaValue::Nil => vec![LuaValue::Unknown("call_table()".into())],
                _ => vec![LuaValue::Unknown("call_table()".into())],
            }
        }
        LuaValue::Unknown(s) => vec![LuaValue::Unknown(format!("{}()", s))],
        _ => vec![LuaValue::Unknown("call()".into())],
    }
}

/// Execute a Lua closure to completion, returning its return values.
/// Capped at 1 000 000 steps to prevent infinite loops.
fn run_closure(closure: &LuaClosure, args: &[LuaValue]) -> Vec<LuaValue> {
    let proto = &closure.proto;
    let nregs = (proto.maxstacksize as usize).max(1);

    // Build register file: params = args, rest = nil
    let mut regs = vec![LuaValue::Nil; nregs];
    for (i, v) in args.iter().enumerate().take(proto.numparams as usize) {
        if i < nregs { regs[i] = v.clone(); }
    }
    // vararg: store extra args above numparams (simplified — kept in regs)
    if proto.is_vararg != 0 {
        let base = proto.numparams as usize;
        for (i, v) in args.iter().enumerate().skip(base) {
            let r = base + i - base; // offset from base
            let slot = base + r;
            if slot < nregs { regs[slot] = v.clone(); }
        }
    }

    // Clone Rc pointers — the child shares upvalue cells with the parent closure.
    let upvalues = closure.upvalues.clone();
    {
        let upv_strs: Vec<String> = upvalues.iter().enumerate()
            .map(|(i, cell)| format!("U{}={}", i, cell.borrow().display_value()))
            .collect();
        eprintln!("[enter] line={} upvalues: [{}]", proto.linedefined, upv_strs.join(", "));
    }
    let mut state = VmState {
        pc: 0,
        regs,
        upvalues,
        open_upvalues: HashMap::new(),
        halted: false,
    };

    const MAX_STEPS: usize = 1_000_000;
    for _ in 0..MAX_STEPS {
        match step(&mut state, proto) {
            StepResult::Returned(vals) => {
                let short: Vec<String> = vals.iter().map(|v| v.display_short()).collect();
                eprintln!("[ret] line={} → [{}]", proto.linedefined, short.join(", "));
                return vals;
            }
            StepResult::Halted => {
                eprintln!("[ret] line={} → halted (no return)", proto.linedefined);
                return vec![];
            }
            StepResult::UnknownBranch(ref msg) => {
                eprintln!("[ret] line={} → unknown branch: {}", proto.linedefined, msg);
                return vec![LuaValue::Unknown("closure(unknown branch)".into())];
            }
            StepResult::Ok | StepResult::Jumped { .. } => {}
        }
    }
    eprintln!("[ret] line={} → step limit", proto.linedefined);
    vec![LuaValue::Unknown("closure(step limit)".into())]
}

fn coerce_to_number(v: LuaValue) -> LuaValue {
    match &v {
        LuaValue::Int(_) | LuaValue::Float(_) => v,
        LuaValue::Str(s) => {
            let t = String::from_utf8_lossy(s);
            let t = t.trim();
            if let Ok(i) = t.parse::<i64>()  { return LuaValue::Int(i); }
            if let Ok(f) = t.parse::<f64>()  { return LuaValue::Float(f); }
            v
        }
        _ => v,
    }
}

pub fn lua_float_tostring(f: f64) -> String {
    if f.is_nan() { return "-nan".to_string(); }
    if f.is_infinite() { return if f > 0.0 { "inf".to_string() } else { "-inf".to_string() }; }
    let s = format!("{:.14}", f);
    // Strip trailing zeros after decimal point, keep at least one digit
    if s.contains('.') {
        let trimmed = s.trim_end_matches('0');
        let trimmed = if trimmed.ends_with('.') { format!("{}0", trimmed) } else { trimmed.to_string() };
        trimmed
    } else {
        s
    }
}

pub fn arith(op: OpCode, lhs: &LuaValue, rhs: &LuaValue) -> LuaValue {
    match (lhs, rhs) {
        (LuaValue::Int(a),   LuaValue::Int(b))   => int_arith(op, *a, *b),
        (LuaValue::Float(a), LuaValue::Float(b)) => float_arith(op, *a, *b),
        // Custom runtime: first operand type determines result type.
        // Int lhs + Float rhs → truncate rhs to Int, use integer arithmetic.
        (LuaValue::Int(a),   LuaValue::Float(b)) => int_arith(op, *a, *b as i64),
        (LuaValue::Float(a), LuaValue::Int(b))   => float_arith(op, *a, *b as f64),
        _ => LuaValue::Unknown(format!("{} ? {}", lhs, rhs)),
    }
}

fn int_arith(op: OpCode, a: i64, b: i64) -> LuaValue {
    use OpCode::*;
    match op {
        Add  => LuaValue::Int(a.wrapping_add(b)),
        Sub  => LuaValue::Int(a.wrapping_sub(b)),
        Mul  => LuaValue::Int(a.wrapping_mul(b)),
        // Custom runtime: Int / Int → Int (floor division, same as IDiv).
        Div  => if b == 0 { LuaValue::Unknown("div/0".into()) }
                else { LuaValue::Int(lua_idiv(a, b)) },
        IDiv => if b == 0 { LuaValue::Unknown("idiv/0".into()) }
                else { LuaValue::Int(lua_idiv(a, b)) },
        Mod  => if b == 0 { LuaValue::Unknown("mod/0".into()) }
                else { LuaValue::Int(lua_imod(a, b)) },
        Pow  => LuaValue::Float((a as f64).powf(b as f64)),
        Band => LuaValue::Int(a & b),
        Bor  => LuaValue::Int(a | b),
        BXor => LuaValue::Int(a ^ b),
        Shl  => LuaValue::Int(lua_shl(a, b)),
        Shr  => LuaValue::Int(lua_shr(a, b)),
        _ => LuaValue::Unknown(format!("{} op {}", a, b)),
    }
}

/// Lua 5.3 floor division for integers — matches `math.floor(a/b)`.
pub fn lua_idiv(a: i64, b: i64) -> i64 {
    let d = a / b;
    let r = a % b;
    // Subtract 1 if remainder is non-zero and signs differ
    if (r != 0) && ((r < 0) != (b < 0)) { d - 1 } else { d }
}

/// Lua 5.3 modulo for integers — `a - floor(a/b)*b`.
pub fn lua_imod(a: i64, b: i64) -> i64 {
    let r = a % b;
    if (r != 0) && ((r < 0) != (b < 0)) { r + b } else { r }
}

fn lua_shl(a: i64, b: i64) -> i64 {
    if b == 0 { return a; }
    if b >= 64 || b <= -64 { return 0; }
    if b > 0 { (a as u64).wrapping_shl(b as u32) as i64 }
    else     { (a as u64).wrapping_shr((-b) as u32) as i64 }
}

fn lua_shr(a: i64, b: i64) -> i64 {
    lua_shl(a, -b)
}

fn float_arith(op: OpCode, a: f64, b: f64) -> LuaValue {
    use OpCode::*;
    // For bitwise ops, convert float operands to integer and delegate.
    match op {
        Band | Bor | BXor | Shl | Shr => {
            return int_arith(op, a as i64, b as i64);
        }
        _ => {}
    }
    LuaValue::Float(match op {
        Add  => a + b,
        Sub  => a - b,
        Mul  => a * b,
        Div  => a / b,
        Mod  => a - (a / b).floor() * b,
        Pow  => a.powf(b),
        IDiv => (a / b).floor(),
        _ => return LuaValue::Unknown(format!("{} op {}", a, b)),
    })
}

pub fn compare(op: OpCode, lhs: &LuaValue, rhs: &LuaValue) -> Option<bool> {
    use OpCode::*;
    match (lhs, rhs) {
        (LuaValue::Int(a),   LuaValue::Int(b)) => Some(match op {
            Eq => a == b, Lt => a < b, Le => a <= b, _ => return None }),
        (LuaValue::Float(a), LuaValue::Float(b)) => Some(match op {
            Eq => a == b, Lt => a < b, Le => a <= b, _ => return None }),
        (LuaValue::Int(a),   LuaValue::Float(b)) => { let a = *a as f64; Some(match op {
            Eq => a == *b, Lt => a < *b, Le => a <= *b, _ => return None }) }
        (LuaValue::Float(a), LuaValue::Int(b))   => { let b = *b as f64; Some(match op {
            Eq => *a == b, Lt => *a < b, Le => *a <= b, _ => return None }) }
        (LuaValue::Nil, LuaValue::Nil)  => Some(op == Eq),
        (LuaValue::Nil, _) | (_, LuaValue::Nil) => Some(matches!(op, Eq) && false),
        (LuaValue::Bool(a), LuaValue::Bool(b))   => Some(op == Eq && a == b),
        (LuaValue::Str(a),  LuaValue::Str(b))    => Some(match op {
            Eq => a == b, Lt => a < b, Le => a <= b, _ => return None }),
        (LuaValue::Table(a), LuaValue::Table(b)) => Some(op == Eq && a == b),
        _ => None,
    }
}
