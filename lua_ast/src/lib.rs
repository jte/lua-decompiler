//! Lua AST types and printer.
//!
//! # Types
//! - [`Expr`] — expressions
//! - [`Stat`] — statements
//! - [`Block`] = `Vec<Stat>` — a sequence of statements
//! - [`FuncBody`] — function parameter list + body block
//! - [`TableField`] — one field in a table constructor
//! - [`BinOp`] / [`UnOp`] — operator enums
//!
//! # Usage
//! Build a `Block` (from the decompiler or deobfuscator), then call
//! [`print_block`] to render it as Lua source text.

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A Lua expression.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Nil,
    True,
    False,
    /// Integer literal (Lua 5.3+ native int, or integer-valued float in 5.1/5.2).
    Integer(i64),
    /// Float literal.
    Float(f64),
    /// String literal — raw bytes; printer handles `\xNN` escaping.
    Str(Vec<u8>),
    /// Vararg `...`.
    Vararg,
    /// A name (variable, global, upvalue).
    Name(String),
    /// Table index: `table[key]`.
    Index {
        table: Box<Expr>,
        key:   Box<Expr>,
    },
    /// Binary operation.
    BinOp {
        op:  BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// Unary operation.
    UnOp {
        op:      UnOp,
        operand: Box<Expr>,
    },
    /// Function call: `func(arg1, arg2, ...)`.
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    /// Function definition `function(params) body end`.
    Function(Box<FuncBody>),
    /// Table constructor `{fields}`.
    Table(Vec<TableField>),
}

impl Expr {
    /// If this is a `Str`, return its bytes.
    pub fn as_str_bytes(&self) -> Option<&[u8]> {
        if let Expr::Str(b) = self { Some(b) } else { None }
    }

    /// If this is a `Str` and valid UTF-8, return the string slice.
    pub fn as_str_utf8(&self) -> Option<&str> {
        if let Expr::Str(b) = self { std::str::from_utf8(b).ok() } else { None }
    }

    /// If this is an `Integer`, return the value.
    pub fn as_integer(&self) -> Option<i64> {
        if let Expr::Integer(n) = self { Some(*n) } else { None }
    }

    /// If this is `Integer` or `Float`, return as f64.
    pub fn as_number(&self) -> Option<f64> {
        match self {
            Expr::Integer(n) => Some(*n as f64),
            Expr::Float(f)   => Some(*f),
            _ => None,
        }
    }

    /// True iff this is a simple literal (Nil/True/False/Integer/Float/Str).
    pub fn is_literal(&self) -> bool {
        matches!(self,
            Expr::Nil | Expr::True | Expr::False
            | Expr::Integer(_) | Expr::Float(_) | Expr::Str(_)
        )
    }
}

/// Binary operators in Lua precedence order (see [`BinOp::prec`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinOp {
    Or,
    And,
    Lt, Gt, Le, Ge, Ne, Eq,
    BOr,
    BXor,
    BAnd,
    Shl, Shr,
    Concat,
    Add, Sub,
    Mul, Div, IDiv, Mod,
    Pow,
}

impl BinOp {
    /// Lua operator precedence: higher = binds tighter.
    /// or=1, and=2, comparison=3, |=4, ~=5, &=6, <<>>=7, ..=8, +−=9, */%//=10, ^=12
    pub fn prec(&self) -> u8 {
        match self {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge | BinOp::Ne | BinOp::Eq => 3,
            BinOp::BOr => 4,
            BinOp::BXor => 5,
            BinOp::BAnd => 6,
            BinOp::Shl | BinOp::Shr => 7,
            BinOp::Concat => 8,
            BinOp::Add | BinOp::Sub => 9,
            BinOp::Mul | BinOp::Div | BinOp::IDiv | BinOp::Mod => 10,
            BinOp::Pow => 12,
        }
    }

    /// True for right-associative operators (`..` and `^`).
    pub fn is_right_assoc(&self) -> bool {
        matches!(self, BinOp::Pow | BinOp::Concat)
    }

    /// Lua source symbol for this operator.
    pub fn sym(&self) -> &'static str {
        match self {
            BinOp::Or    => "or",  BinOp::And  => "and",
            BinOp::Lt    => "<",   BinOp::Gt   => ">",
            BinOp::Le    => "<=",  BinOp::Ge   => ">=",
            BinOp::Ne    => "~=",  BinOp::Eq   => "==",
            BinOp::BOr   => "|",   BinOp::BXor => "~",
            BinOp::BAnd  => "&",   BinOp::Shl  => "<<",
            BinOp::Shr   => ">>",  BinOp::Concat => "..",
            BinOp::Add   => "+",   BinOp::Sub  => "-",
            BinOp::Mul   => "*",   BinOp::Div  => "/",
            BinOp::IDiv  => "//",  BinOp::Mod  => "%",
            BinOp::Pow   => "^",
        }
    }
}

/// Unary operators.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// Arithmetic negation `-`.
    Neg,
    /// Logical not.
    Not,
    /// Length operator `#`.
    Len,
    /// Bitwise not `~` (Lua 5.3+).
    BNot,
}

/// Function parameter list + body.
#[derive(Clone, Debug, PartialEq)]
pub struct FuncBody {
    pub params:     Vec<String>,
    pub has_vararg: bool,
    pub body:       Block,
}

/// One field in a table constructor.
#[derive(Clone, Debug, PartialEq)]
pub enum TableField {
    /// `[key] = value` — computed key.
    IndexField(Expr, Expr),
    /// `name = value` — identifier key (valid Lua identifier string key).
    NameField(String, Expr),
    /// `value` — positional / array entry.
    ValueField(Expr),
}

/// A Lua statement.
#[derive(Clone, Debug, PartialEq)]
pub enum Stat {
    /// `lhs1, lhs2 = rhs1, rhs2`
    Assign { lhs: Vec<Expr>, rhs: Vec<Expr> },
    /// `local name1, name2 = val1, val2`
    Local { names: Vec<String>, values: Vec<Expr> },
    /// `do ... end`
    Do(Block),
    /// `while cond do ... end`
    While { cond: Expr, body: Block },
    /// `repeat ... until cond`
    Repeat { body: Block, cond: Expr },
    /// `if ... then ... [elseif ... then ...]* [else ...]? end`
    If { branches: Vec<(Expr, Block)>, else_body: Option<Block> },
    /// `for var = from, to[, step] do ... end`
    NumFor { var: String, from: Expr, to: Expr, step: Option<Expr>, body: Block },
    /// `for vars in iters do ... end`
    GenFor { vars: Vec<String>, iters: Vec<Expr>, body: Block },
    /// `return [expr, ...]`
    Return(Vec<Expr>),
    /// `break`
    Break,
    /// `goto label`
    Goto(String),
    /// `::label::`
    Label(String),
    /// A call used as a statement.
    Call(Expr),
}

/// A block is a sequence of statements.
pub type Block = Vec<Stat>;

// ---------------------------------------------------------------------------
// Printer
// ---------------------------------------------------------------------------

/// Render `block` as indented Lua source text starting at `indent` level.
pub fn print_block(block: &Block, indent: usize) -> String {
    let mut p = Printer { buf: String::new(), indent };
    p.write_block(block);
    // Trim trailing newline
    let s = p.buf;
    s.trim_end_matches('\n').to_string()
}

struct Printer {
    buf:    String,
    indent: usize,
}

impl Printer {
    fn write_block(&mut self, block: &Block) {
        for stat in block {
            self.write_stat(stat);
        }
    }

    fn pad(&self) -> String {
        "  ".repeat(self.indent)
    }

    fn line(&mut self, s: impl AsRef<str>) {
        self.buf.push_str(&self.pad());
        self.buf.push_str(s.as_ref());
        self.buf.push('\n');
    }

    /// Write a multi-line table constructor for a statement context.
    /// Caller writes `prefix = {` on the line before calling this.
    fn write_table_body(&mut self, fields: &[TableField]) {
        let all_value = fields.iter().all(|f| matches!(f, TableField::ValueField(_)));
        if all_value {
            // Pack ValueField items in groups per line (up to 8 per line).
            const PER_LINE: usize = 8;
            let items: Vec<String> = fields.iter().map(|f| {
                if let TableField::ValueField(v) = f { expr_inner(v) } else { unreachable!() }
            }).collect();
            for chunk in items.chunks(PER_LINE) {
                self.line(format!("{},", chunk.join(", ")));
            }
        } else {
            for f in fields {
                let s = match f {
                    TableField::IndexField(k, v) =>
                        format!("[{}] = {}", expr_inner(k), expr_inner(v)),
                    TableField::NameField(k, v) =>
                        format!("{} = {}", k, expr_inner(v)),
                    TableField::ValueField(v) => expr_inner(v),
                };
                self.line(format!("{},", s));
            }
        }
    }

    /// Write a table value that may be multi-line, given a statement prefix
    /// (e.g. `"local foo = "` or `"bar = "`).
    fn write_value_with_table(&mut self, prefix: &str, expr: &Expr) {
        if let Expr::Table(fields) = expr {
            if !fields.is_empty() && table_needs_multiline(fields) {
                self.line(format!("{}{{", prefix));
                self.indent += 1;
                self.write_table_body(fields);
                self.indent -= 1;
                self.line("}");
                return;
            }
        }
        self.line(format!("{}{}", prefix, expr_str(expr)));
    }

    fn write_stat(&mut self, stat: &Stat) {
        match stat {
            Stat::Assign { lhs, rhs } => {
                let lhs_s = lhs.iter().map(|e| expr_str(e)).collect::<Vec<_>>().join(", ");
                if rhs.len() == 1 {
                    self.write_value_with_table(&format!("{} = ", lhs_s), &rhs[0]);
                } else {
                    let rhs_s = rhs.iter().map(|e| expr_str(e)).collect::<Vec<_>>().join(", ");
                    self.line(format!("{} = {}", lhs_s, rhs_s));
                }
            }
            Stat::Local { names, values } => {
                let names_s = names.join(", ");
                if values.is_empty() {
                    self.line(format!("local {}", names_s));
                    return;
                }
                // Special case: single function value → multi-line form
                if values.len() == 1 {
                    if let Expr::Function(body) = &values[0] {
                        let params = fmt_params(body);
                        self.line(format!("local {} = function({})", names_s, params));
                        self.indent += 1;
                        self.write_block(&body.body);
                        self.indent -= 1;
                        self.line("end");
                        return;
                    }
                }
                if values.len() == 1 {
                    self.write_value_with_table(&format!("local {} = ", names_s), &values[0]);
                } else {
                    let vals_s = values.iter().map(|e| expr_str(e)).collect::<Vec<_>>().join(", ");
                    self.line(format!("local {} = {}", names_s, vals_s));
                }
            }
            Stat::Do(body) => {
                self.line("do");
                self.indent += 1;
                self.write_block(body);
                self.indent -= 1;
                self.line("end");
            }
            Stat::While { cond, body } => {
                self.line(format!("while {} do", expr_str(cond)));
                self.indent += 1;
                self.write_block(body);
                self.indent -= 1;
                self.line("end");
            }
            Stat::Repeat { body, cond } => {
                self.line("repeat");
                self.indent += 1;
                self.write_block(body);
                self.indent -= 1;
                self.line(format!("until {}", expr_str(cond)));
            }
            Stat::If { branches, else_body } => {
                for (i, (cond, body)) in branches.iter().enumerate() {
                    let kw = if i == 0 { "if" } else { "elseif" };
                    self.line(format!("{} {} then", kw, expr_str(cond)));
                    self.indent += 1;
                    self.write_block(body);
                    self.indent -= 1;
                }
                if let Some(eb) = else_body {
                    self.line("else");
                    self.indent += 1;
                    self.write_block(eb);
                    self.indent -= 1;
                }
                self.line("end");
            }
            Stat::NumFor { var, from, to, step, body } => {
                let is_step_one = matches!(step, Some(Expr::Integer(1)))
                    || matches!(step, Some(Expr::Float(f)) if *f == 1.0);
                let step_s = if is_step_one { String::new() }
                    else { step.as_ref().map(|s| format!(", {}", expr_str(s))).unwrap_or_default() };
                self.line(format!("for {} = {}, {}{} do",
                    var, expr_str(from), expr_str(to), step_s));
                self.indent += 1;
                self.write_block(body);
                self.indent -= 1;
                self.line("end");
            }
            Stat::GenFor { vars, iters, body } => {
                let vars_s  = vars.join(", ");
                let iters_s = iters.iter().map(|e| expr_str(e)).collect::<Vec<_>>().join(", ");
                self.line(format!("for {} in {} do", vars_s, iters_s));
                self.indent += 1;
                self.write_block(body);
                self.indent -= 1;
                self.line("end");
            }
            Stat::Return(vals) => {
                if vals.is_empty() {
                    self.line("return");
                } else {
                    let s = vals.iter().map(|e| expr_str(e)).collect::<Vec<_>>().join(", ");
                    self.line(format!("return {}", s));
                }
            }
            Stat::Break => self.line("break"),
            Stat::Goto(lbl) => self.line(format!("goto {}", lbl)),
            Stat::Label(lbl) => self.line(format!("::{}::", lbl)),
            Stat::Call(e) => self.line(expr_str(e)),
        }
    }
}

/// Determine if a table should be written multi-line in statement context.
/// - Pure ValueField tables: multi-line if > 6 items or any item is long.
/// - Tables with NameField or IndexField: always multi-line.
fn table_needs_multiline(fields: &[TableField]) -> bool {
    if fields.is_empty() { return false; }
    let has_named = fields.iter().any(|f| matches!(f, TableField::NameField(..) | TableField::IndexField(..)));
    if has_named { return true; }
    // Pure ValueField: multi-line if > 6 items or any item is long.
    fields.len() > 6 || fields.iter().any(|f| {
        if let TableField::ValueField(v) = f { expr_inner(v).len() > 60 } else { false }
    })
}

/// Format function parameter list (no surrounding parens).
fn fmt_params(body: &FuncBody) -> String {
    let mut p = body.params.clone();
    if body.has_vararg { p.push("...".to_string()); }
    p.join(", ")
}

// ---------------------------------------------------------------------------
// Expression printer (no indentation — single-line)
// ---------------------------------------------------------------------------

/// Render an expression as a Lua source string (single line, no outer parens).
pub fn expr_str(expr: &Expr) -> String {
    expr_with_prec(expr, 0, false)
}

/// Render an expression, adding parentheses if its precedence is insufficient.
///
/// `min_prec`: the minimum precedence needed to be safe without parens.
/// `strict`:   if true, add parens even when `expr.prec == min_prec`.
fn expr_with_prec(expr: &Expr, min_prec: u8, strict: bool) -> String {
    let s = expr_inner(expr);
    let prec = expr_prec(expr);
    let needs = if strict { prec <= min_prec } else { prec < min_prec };
    if needs { format!("({})", s) } else { s }
}

fn expr_prec(expr: &Expr) -> u8 {
    match expr {
        Expr::BinOp { op, .. } => op.prec(),
        Expr::UnOp  { .. }     => 11,
        _ => 12,
    }
}

fn expr_inner(expr: &Expr) -> String {
    match expr {
        Expr::Nil        => "nil".to_string(),
        Expr::True       => "true".to_string(),
        Expr::False      => "false".to_string(),
        Expr::Integer(n) => n.to_string(),
        Expr::Float(f)   => format_float(*f),
        Expr::Str(b)     => lua_string_literal(b),
        Expr::Vararg     => "...".to_string(),
        Expr::Name(n)    => n.clone(),

        Expr::Index { table, key } => {
            let t = expr_with_prec(table, 12, false);
            // Use dot notation when key is a valid identifier and the table is a
            // "pure index chain" (only Names and ident-keyed Index nodes — no calls).
            // This gives A.B.C instead of A.B["C"], but keeps f()["k"] as bracket.
            if is_pure_index_chain(table) {
                if let Expr::Str(kb) = key.as_ref() {
                    if let Ok(ks) = std::str::from_utf8(kb) {
                        // Use dot notation only for idents with length >= 2.
                        // Single-char keys (like "i") are kept as string indices.
                        if ks.len() >= 2 && is_lua_ident(ks) {
                            return format!("{}.{}", t, ks);
                        }
                    }
                }
            }
            let k = expr_inner(key);
            format!("{}[{}]", t, k)
        }

        Expr::BinOp { op, lhs, rhs } => {
            let p  = op.prec();
            let ra = op.is_right_assoc();
            // Left child: for right-assoc ops, same-prec child needs parens.
            let lhs_s = expr_with_prec(lhs, p, ra);
            // Right child: for left-assoc ops, same-prec child needs parens.
            let rhs_s = expr_with_prec(rhs, p, !ra);
            format!("{} {} {}", lhs_s, op.sym(), rhs_s)
        }

        Expr::UnOp { op, operand } => {
            // Unary prec is 11; operand needs parens if its prec < 11.
            // Special case: -(-x) must not become --x.
            let child_prec = expr_prec(operand);
            let needs_parens = child_prec < 11
                || (matches!(op, UnOp::Neg) && matches!(operand.as_ref(), Expr::UnOp { op: UnOp::Neg, .. }));
            let s = if needs_parens {
                format!("({})", expr_inner(operand))
            } else {
                expr_inner(operand)
            };
            match op {
                UnOp::Neg  => format!("-{}", s),
                UnOp::Not  => format!("not {}", s),
                UnOp::Len  => format!("#{}", s),
                UnOp::BNot => format!("~{}", s),
            }
        }

        Expr::Call { func, args } => {
            // Wrap func if it's a compound expression (e.g. index result).
            let f = expr_with_prec(func, 12, false);
            let a = args.iter().map(|e| expr_inner(e)).collect::<Vec<_>>().join(", ");
            format!("{}({})", f, a)
        }

        Expr::Function(body) => {
            // Compact single-line form (used when function appears inline, e.g. in a table).
            let params = fmt_params(body);
            format!("function({}) ... end", params)
        }

        Expr::Table(fields) => {
            if fields.is_empty() {
                return "{}".to_string();
            }
            let items: Vec<String> = fields.iter().map(|f| match f {
                TableField::IndexField(k, v) =>
                    format!("[{}] = {}", expr_inner(k), expr_inner(v)),
                TableField::NameField(k, v) =>
                    format!("{} = {}", k, expr_inner(v)),
                TableField::ValueField(v) =>
                    expr_inner(v),
            }).collect();
            // Always inline in expression context — write_stat handles multi-line.
            format!("{{{}}}", items.join(", "))
        }
    }
}

// ---------------------------------------------------------------------------
// Formatting helpers
// ---------------------------------------------------------------------------

/// Format a float as a Lua literal. Whole-number floats are printed as integers
/// (Lua 5.1/5.2 style where there's no separate integer type).
fn format_float(f: f64) -> String {
    if f.fract() == 0.0 && f.abs() < 1e15 && f.is_finite() {
        format!("{}", f as i64)
    } else {
        // Use Rust's default float formatting, which is always parseable.
        let s = format!("{}", f);
        // Ensure it has a decimal point so Lua parses it as a float.
        if s.contains('.') || s.contains('e') || s.contains('E') || s.contains("inf") || s.contains("nan") {
            s
        } else {
            format!("{}.0", s)
        }
    }
}

/// Render raw bytes as a Lua double-quoted string literal.
pub fn lua_string_literal(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() + 2);
    out.push('"');
    for &b in bytes {
        match b {
            b'"'  => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            // Exclude '{' (0x7B) and '}' (0x7D) — escape them for clarity.
            0x20..=0x7a | 0x7c | 0x7e => out.push(b as char),
            _ => out.push_str(&format!("\\x{:02X}", b)),
        }
    }
    out.push('"');
    out
}

/// True iff `e` is a "pure index chain" — only Names and ident-keyed Index nodes,
/// no function calls, BinOps, etc.  Used to decide whether dot notation is safe.
fn is_pure_index_chain(e: &Expr) -> bool {
    match e {
        Expr::Name(_) => true,
        Expr::Index { table, key } => {
            if let Expr::Str(kb) = key.as_ref() {
                if let Ok(ks) = std::str::from_utf8(kb) {
                    if is_lua_ident(ks) {
                        return is_pure_index_chain(table);
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// True iff `s` is a valid Lua identifier (non-empty, starts with letter or `_`,
/// contains only alphanumeric / `_`, and is not a Lua reserved word).
pub fn is_lua_ident(s: &str) -> bool {
    if s.is_empty() { return false; }
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    if !chars.all(|c| c.is_ascii_alphanumeric() || c == '_') { return false; }
    !matches!(s,
        "and"|"break"|"do"|"else"|"elseif"|"end"|"false"|"for"|"function"|
        "goto"|"if"|"in"|"local"|"nil"|"not"|"or"|"repeat"|"return"|"then"|
        "true"|"until"|"while"
    )
}

/// True if `name` is a valid Lua lvalue (can appear on the left of `=`).
/// Accepts `Name`, `Name[...]`, `Name.field` forms.
pub fn is_valid_lvalue(name: &str) -> bool {
    if name.is_empty() { return false; }
    if !name.starts_with(|c: char| c == '_' || c.is_ascii_alphabetic()) { return false; }
    let end = name.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(name.len());
    let tok = &name[..end];
    if matches!(tok,
        "nil"|"true"|"false"|"not"|"and"|"or"|"if"|"then"|"else"|"elseif"|"end"
        |"do"|"while"|"repeat"|"until"|"for"|"in"|"local"|"function"|"return"|"break"|"goto"
    ) { return false; }
    matches!(name.as_bytes().get(end), None | Some(b'[') | Some(b'.'))
}

// ---------------------------------------------------------------------------
// AST traversal helpers
// ---------------------------------------------------------------------------

/// Recursively walk every [`Expr`] node in `expr`, bottom-up, calling `f` on each.
/// The closure may replace the expression by writing to `*expr`.
pub fn transform_expr(expr: &mut Expr, f: &mut impl FnMut(&mut Expr)) {
    // Recurse into children first (bottom-up).
    match expr {
        Expr::Index { table, key } => {
            transform_expr(table, f);
            transform_expr(key, f);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            transform_expr(lhs, f);
            transform_expr(rhs, f);
        }
        Expr::UnOp { operand, .. } => transform_expr(operand, f),
        Expr::Call { func, args } => {
            transform_expr(func, f);
            for a in args.iter_mut() { transform_expr(a, f); }
        }
        Expr::Function(body) => transform_block(&mut body.body, f),
        Expr::Table(fields) => {
            for field in fields.iter_mut() {
                match field {
                    TableField::IndexField(k, v) => { transform_expr(k, f); transform_expr(v, f); }
                    TableField::NameField(_, v)  => transform_expr(v, f),
                    TableField::ValueField(v)    => transform_expr(v, f),
                }
            }
        }
        _ => {} // Leaf nodes
    }
    f(expr);
}

/// Walk every `Expr` in every `Stat` in `block`, bottom-up.
pub fn transform_block(block: &mut Block, f: &mut impl FnMut(&mut Expr)) {
    for stat in block.iter_mut() {
        transform_stat(stat, f);
    }
}

/// Walk every `Expr` in `stat`, bottom-up.
pub fn transform_stat(stat: &mut Stat, f: &mut impl FnMut(&mut Expr)) {
    match stat {
        Stat::Assign { lhs, rhs } => {
            for e in lhs.iter_mut().chain(rhs.iter_mut()) { transform_expr(e, f); }
        }
        Stat::Local { values, .. } => {
            for e in values.iter_mut() { transform_expr(e, f); }
        }
        Stat::Do(body)               => transform_block(body, f),
        Stat::While { cond, body }   => { transform_expr(cond, f); transform_block(body, f); }
        Stat::Repeat { body, cond }  => { transform_block(body, f); transform_expr(cond, f); }
        Stat::If { branches, else_body } => {
            for (cond, body) in branches.iter_mut() {
                transform_expr(cond, f);
                transform_block(body, f);
            }
            if let Some(eb) = else_body { transform_block(eb, f); }
        }
        Stat::NumFor { from, to, step, body, .. } => {
            transform_expr(from, f);
            transform_expr(to, f);
            if let Some(s) = step { transform_expr(s, f); }
            transform_block(body, f);
        }
        Stat::GenFor { iters, body, .. } => {
            for e in iters.iter_mut() { transform_expr(e, f); }
            transform_block(body, f);
        }
        Stat::Return(vals) => {
            for e in vals.iter_mut() { transform_expr(e, f); }
        }
        Stat::Call(e) => transform_expr(e, f),
        Stat::Break | Stat::Goto(_) | Stat::Label(_) => {}
    }
}

/// Walk and optionally replace/remove/expand each [`Stat`] in `block`.
/// The closure receives each stat and returns `Vec<Stat>` — the replacement list
/// (empty = delete, one = replace, multiple = expand).
/// Recurses into nested blocks first (bottom-up).
pub fn transform_stats(block: &mut Block, f: &mut impl FnMut(Stat) -> Vec<Stat>) {
    // Recurse into nested blocks of each stat before applying f.
    let old = std::mem::take(block);
    for mut stat in old {
        recurse_nested_blocks(&mut stat, &mut |nested| transform_stats(nested, f));
        block.extend(f(stat));
    }
}

fn recurse_nested_blocks(stat: &mut Stat, f: &mut impl FnMut(&mut Block)) {
    match stat {
        Stat::Do(body)               => f(body),
        Stat::While { body, .. }     => f(body),
        Stat::Repeat { body, .. }    => f(body),
        Stat::If { branches, else_body } => {
            for (_, b) in branches.iter_mut() { f(b); }
            if let Some(eb) = else_body { f(eb); }
        }
        Stat::NumFor { body, .. }    => f(body),
        Stat::GenFor { body, .. }    => f(body),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Counting helpers (used by deobfuscator passes)
// ---------------------------------------------------------------------------

/// Count how many times `name` appears as an `Expr::Name` anywhere in `block`.
pub fn count_name_uses(block: &Block, name: &str) -> usize {
    let mut count = 0usize;
    count_in_block(block, name, &mut count);
    count
}

fn count_in_block(block: &Block, name: &str, count: &mut usize) {
    for stat in block { count_in_stat(stat, name, count); }
}

fn count_in_stat(stat: &Stat, name: &str, count: &mut usize) {
    match stat {
        Stat::Assign { lhs, rhs } => {
            for e in lhs.iter().chain(rhs.iter()) { count_in_expr(e, name, count); }
        }
        Stat::Local { values, .. } => {
            for e in values { count_in_expr(e, name, count); }
        }
        Stat::Do(b) => count_in_block(b, name, count),
        Stat::While { cond, body } => {
            count_in_expr(cond, name, count);
            count_in_block(body, name, count);
        }
        Stat::Repeat { body, cond } => {
            count_in_block(body, name, count);
            count_in_expr(cond, name, count);
        }
        Stat::If { branches, else_body } => {
            for (c, b) in branches {
                count_in_expr(c, name, count);
                count_in_block(b, name, count);
            }
            if let Some(eb) = else_body { count_in_block(eb, name, count); }
        }
        Stat::NumFor { from, to, step, body, .. } => {
            count_in_expr(from, name, count);
            count_in_expr(to, name, count);
            if let Some(s) = step { count_in_expr(s, name, count); }
            count_in_block(body, name, count);
        }
        Stat::GenFor { iters, body, .. } => {
            for e in iters { count_in_expr(e, name, count); }
            count_in_block(body, name, count);
        }
        Stat::Return(vals) => {
            for e in vals { count_in_expr(e, name, count); }
        }
        Stat::Call(e) => count_in_expr(e, name, count),
        _ => {}
    }
}

fn count_in_expr(expr: &Expr, name: &str, count: &mut usize) {
    match expr {
        Expr::Name(n) if n == name => *count += 1,
        Expr::Index { table, key } => {
            count_in_expr(table, name, count);
            count_in_expr(key, name, count);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            count_in_expr(lhs, name, count);
            count_in_expr(rhs, name, count);
        }
        Expr::UnOp { operand, .. } => count_in_expr(operand, name, count),
        Expr::Call { func, args } => {
            count_in_expr(func, name, count);
            for a in args { count_in_expr(a, name, count); }
        }
        Expr::Function(body) => count_in_block(&body.body, name, count),
        Expr::Table(fields) => {
            for field in fields {
                match field {
                    TableField::IndexField(k, v) => {
                        count_in_expr(k, name, count);
                        count_in_expr(v, name, count);
                    }
                    TableField::NameField(_, v) => count_in_expr(v, name, count),
                    TableField::ValueField(v)   => count_in_expr(v, name, count),
                }
            }
        }
        _ => {}
    }
}

/// True iff `name` is ever the target of a plain assignment (`name = ...`)
/// anywhere in `block`, excluding `local name = ...` declarations.
pub fn is_ever_assigned(block: &Block, name: &str) -> bool {
    block.iter().any(|s| stat_assigns(s, name))
}

fn stat_assigns(stat: &Stat, name: &str) -> bool {
    match stat {
        Stat::Assign { lhs, .. } => lhs.iter().any(|e| matches!(e, Expr::Name(n) if n == name)),
        Stat::Do(b) => b.iter().any(|s| stat_assigns(s, name)),
        Stat::While { body, .. } | Stat::Repeat { body, .. } | Stat::NumFor { body, .. } | Stat::GenFor { body, .. } =>
            body.iter().any(|s| stat_assigns(s, name)),
        Stat::If { branches, else_body } => {
            branches.iter().any(|(_, b)| b.iter().any(|s| stat_assigns(s, name)))
            || else_body.as_ref().map_or(false, |b| b.iter().any(|s| stat_assigns(s, name)))
        }
        _ => false,
    }
}
