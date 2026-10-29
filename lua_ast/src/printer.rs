//! Lua source printer.

use crate::{BinOp, Block, Expr, FuncBody, Stat, TableField, UnOp};

/// Render `block` as indented Lua source text starting at `indent` level.
pub fn print_block(block: &Block, indent: usize) -> String {
    let mut p = Printer { buf: String::new(), indent };
    p.write_block(block);
    let s = p.buf;
    s.trim_end_matches('\n').to_string()
}

/// Render an expression as a Lua source string.  Nested function bodies are
/// written as if the expression started at indentation level 0.
pub fn expr_str(expr: &Expr) -> String {
    expr_with_prec(expr, 0, false, 0)
}

struct Printer {
    buf: String,
    indent: usize,
}

impl Printer {
    fn write_block(&mut self, block: &Block) {
        let mut i = 0;
        while i < block.len() {
            // `local f` + `f = function ... end` → `local function f`
            if let (Stat::Local { names, values }, Some(Stat::Assign { lhs, rhs })) = (&block[i], block.get(i + 1)) {
                if names.len() == 1 && values.is_empty() && lhs.len() == 1 && rhs.len() == 1 {
                    if let (Expr::Name(n), Expr::Function(f)) = (&lhs[0], &rhs[0]) {
                        if *n == names[0] {
                            self.write_function_stat(&format!("local function {}", n), f, false);
                            i += 2;
                            continue;
                        }
                    }
                }
            }
            let s = &block[i];
            let last = i + 1 == block.len();
            // `f()` followed by `(x).y = 1` would parse as `f()(x).y = 1`.
            if i > 0 && starts_with_paren(s) {
                self.line(";");
            }
            if !last && matches!(s, Stat::Return(_) | Stat::Break) {
                // Lua only allows these at the end of a block.
                self.line("do");
                self.indent += 1;
                self.write_stat(s);
                self.indent -= 1;
                self.line("end");
            } else {
                self.write_stat(s);
            }
            i += 1;
        }
    }

    fn pad(&self) -> String {
        "  ".repeat(self.indent)
    }

    fn line(&mut self, s: impl AsRef<str>) {
        let pad = self.pad();
        self.buf.push_str(&pad);
        self.buf.push_str(s.as_ref());
        self.buf.push('\n');
    }

    fn expr(&self, e: &Expr) -> String {
        expr_with_prec(e, 0, false, self.indent)
    }

    fn exprs(&self, es: &[Expr]) -> String {
        es.iter().map(|e| self.expr(e)).collect::<Vec<_>>().join(", ")
    }

    fn write_function_stat(&mut self, head: &str, f: &FuncBody, method: bool) {
        let params = if method { fmt_params_from(f, 1) } else { fmt_params_from(f, 0) };
        self.line(format!("{}({})", head, params));
        self.indent += 1;
        self.write_block(&f.body);
        self.indent -= 1;
        self.line("end");
    }

    /// Write a multi-line table constructor for a statement context.
    fn write_table_body(&mut self, fields: &[TableField]) {
        let all_value = fields.iter().all(|f| matches!(f, TableField::ValueField(_)));
        if all_value && fields.iter().all(|f| !matches!(f, TableField::ValueField(Expr::Function(_)) | TableField::ValueField(Expr::Table(_)))) {
            const PER_LINE: usize = 8;
            let items: Vec<String> = fields.iter().map(|f| {
                if let TableField::ValueField(v) = f { self.expr(v) } else { unreachable!() }
            }).collect();
            for chunk in items.chunks(PER_LINE) {
                self.line(format!("{},", chunk.join(", ")));
            }
        } else {
            for f in fields {
                match f {
                    TableField::IndexField(k, v) => {
                        let prefix = format!("[{}] = ", self.expr(k));
                        self.write_value(&prefix, v, ",");
                    }
                    TableField::NameField(k, v) => self.write_value(&format!("{} = ", k), v, ","),
                    TableField::ValueField(v) => self.write_value("", v, ","),
                }
            }
        }
    }

    /// Write `prefix <value><suffix>`, spreading big tables over lines.
    fn write_value(&mut self, prefix: &str, expr: &Expr, suffix: &str) {
        if let Expr::Table(fields) = expr {
            if !fields.is_empty() && table_needs_multiline(fields, self.indent) {
                self.line(format!("{}{{", prefix));
                self.indent += 1;
                self.write_table_body(fields);
                self.indent -= 1;
                self.line(format!("}}{}", suffix));
                return;
            }
        }
        let e = self.expr(expr);
        self.line(format!("{}{}{}", prefix, e, suffix));
    }

    fn write_stat(&mut self, stat: &Stat) {
        match stat {
            Stat::Assign { lhs, rhs } => {
                if lhs.len() == 1 && rhs.len() == 1 {
                    if let Expr::Function(f) = &rhs[0] {
                        if let Some((path, method)) = function_name(&lhs[0], f) {
                            self.write_function_stat(&format!("function {}", path), f, method);
                            return;
                        }
                    }
                }
                let lhs_s = self.exprs(lhs);
                if rhs.len() == 1 {
                    self.write_value(&format!("{} = ", lhs_s), &rhs[0], "");
                } else {
                    let rhs_s = self.exprs(rhs);
                    self.line(format!("{} = {}", lhs_s, rhs_s));
                }
            }
            Stat::Local { names, values } => {
                let names_s = names.join(", ");
                if values.is_empty() {
                    self.line(format!("local {}", names_s));
                } else if values.len() == 1 {
                    if let (Expr::Function(f), 1) = (&values[0], names.len()) {
                        // Safe: the body cannot refer to this local (the
                        // decompiler declares self-recursive functions first).
                        self.write_function_stat(&format!("local function {}", names[0]), f, false);
                        return;
                    }
                    self.write_value(&format!("local {} = ", names_s), &values[0], "");
                } else {
                    let vals_s = self.exprs(values);
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
                let c = self.expr(cond);
                self.line(format!("while {} do", c));
                self.indent += 1;
                self.write_block(body);
                self.indent -= 1;
                self.line("end");
            }
            Stat::Repeat { body, cond } => {
                self.line("repeat");
                self.indent += 1;
                self.write_block(body);
                let c = self.expr(cond);
                self.indent -= 1;
                self.line(format!("until {}", c));
            }
            Stat::If { branches, else_body } => {
                for (i, (cond, body)) in branches.iter().enumerate() {
                    let kw = if i == 0 { "if" } else { "elseif" };
                    let c = self.expr(cond);
                    self.line(format!("{} {} then", kw, c));
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
                let step_s = if is_step_one || step.is_none() { String::new() }
                    else { format!(", {}", self.expr(step.as_ref().unwrap())) };
                let (f, t) = (self.expr(from), self.expr(to));
                self.line(format!("for {} = {}, {}{} do", var, f, t, step_s));
                self.indent += 1;
                self.write_block(body);
                self.indent -= 1;
                self.line("end");
            }
            Stat::GenFor { vars, iters, body } => {
                let vars_s = vars.join(", ");
                let iters_s = self.exprs(iters);
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
                    let s = self.exprs(vals);
                    self.line(format!("return {}", s));
                }
            }
            Stat::Break => self.line("break"),
            Stat::Goto(lbl) => self.line(format!("goto {}", lbl)),
            Stat::Label(lbl) => self.line(format!("::{}::", lbl)),
            Stat::Call(e) => {
                let s = self.expr(e);
                self.line(s);
            }
        }
    }
}

/// Would this statement's text begin with `(`?
fn starts_with_paren(s: &Stat) -> bool {
    fn leftmost_paren(e: &Expr) -> bool {
        match e {
            Expr::Index { table, .. } => !is_prefix_exp(table) || leftmost_paren(table),
            Expr::Call { func, .. } => !is_prefix_exp(func) || leftmost_paren(func),
            Expr::Method { obj, .. } => !is_prefix_exp(obj) || leftmost_paren(obj),
            Expr::Paren(_) => true,
            _ => false,
        }
    }
    match s {
        Stat::Assign { lhs, .. } => lhs.first().map_or(false, leftmost_paren),
        Stat::Call(e) => leftmost_paren(e),
        _ => false,
    }
}

/// `a.b.c = function` → `function a.b.c`, and `function a.b:c` when the
/// first parameter is `self`.
fn function_name(lhs: &Expr, f: &FuncBody) -> Option<(String, bool)> {
    fn path(e: &Expr) -> Option<String> {
        match e {
            Expr::Name(n) if is_lua_ident(n) => Some(n.clone()),
            Expr::Index { table, key } => {
                let k = key.as_str_utf8().filter(|k| is_lua_ident(k))?;
                Some(format!("{}.{}", path(table)?, k))
            }
            _ => None,
        }
    }
    let p = path(lhs)?;
    if let Expr::Index { table, key } = lhs {
        if f.params.first().map_or(false, |p| p == "self") {
            let k = key.as_str_utf8().unwrap();
            return Some((format!("{}:{}", path(table)?, k), true));
        }
    }
    Some((p, false))
}

/// Should a table be written over several lines in statement context?
fn table_needs_multiline(fields: &[TableField], indent: usize) -> bool {
    if fields.is_empty() { return false; }
    let has_named = fields.iter().any(|f| matches!(f, TableField::NameField(..) | TableField::IndexField(..)));
    if has_named { return true; }
    fields.len() > 6 || fields.iter().any(|f| {
        if let TableField::ValueField(v) = f {
            matches!(v, Expr::Function(_)) || expr_with_prec(v, 0, false, indent).len() > 60
        } else { false }
    })
}

fn fmt_params_from(body: &FuncBody, skip: usize) -> String {
    let mut p: Vec<String> = body.params.iter().skip(skip).cloned().collect();
    if body.has_vararg { p.push("...".to_string()); }
    p.join(", ")
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

fn expr_with_prec(expr: &Expr, min_prec: u8, strict: bool, indent: usize) -> String {
    let s = expr_inner(expr, indent);
    let prec = expr_prec(expr);
    let needs = if strict { prec <= min_prec } else { prec < min_prec };
    if needs { format!("({})", s) } else { s }
}

fn expr_prec(expr: &Expr) -> u8 {
    match expr {
        Expr::BinOp { op, .. } => op.prec(),
        Expr::UnOp { .. } => 11,
        Expr::Integer(i) if *i < 0 => 11,
        Expr::Float(f) if *f < 0.0 || f.is_nan() || f.is_infinite() => 11,
        Expr::Function(_) | Expr::Table(_) | Expr::Nil | Expr::True | Expr::False
        | Expr::Str(_) | Expr::Vararg | Expr::Integer(_) | Expr::Float(_) => 13,
        _ => 14,
    }
}

/// Can `e` be the prefix of a call or index without parentheses?
fn is_prefix_exp(e: &Expr) -> bool {
    matches!(e, Expr::Name(_) | Expr::Index { .. } | Expr::Call { .. } | Expr::Method { .. } | Expr::Paren(_))
}

fn prefix(e: &Expr, indent: usize) -> String {
    let s = expr_inner(e, indent);
    if is_prefix_exp(e) { s } else { format!("({})", s) }
}

fn expr_inner(expr: &Expr, indent: usize) -> String {
    match expr {
        Expr::Nil => "nil".to_string(),
        Expr::True => "true".to_string(),
        Expr::False => "false".to_string(),
        Expr::Integer(n) => {
            if *n == i64::MIN { "math.mininteger".to_string() } else { n.to_string() }
        }
        Expr::Float(f) => format_float(*f),
        Expr::Str(b) => lua_string_literal(b),
        Expr::Vararg => "...".to_string(),
        Expr::Name(n) => n.clone(),
        Expr::Paren(e) => format!("({})", expr_inner(e, indent)),

        Expr::Index { table, key } => {
            let t = prefix(table, indent);
            if let Expr::Str(kb) = key.as_ref() {
                if let Ok(ks) = std::str::from_utf8(kb) {
                    if is_lua_ident(ks) {
                        return format!("{}.{}", t, ks);
                    }
                }
            }
            format!("{}[{}]", t, expr_inner(key, indent))
        }

        Expr::BinOp { op, lhs, rhs } => {
            let p = op.prec();
            let ra = op.is_right_assoc();
            let lhs_s = expr_with_prec(lhs, p, ra, indent);
            let rhs_s = expr_with_prec(rhs, p, !ra, indent);
            format!("{} {} {}", lhs_s, op.sym(), rhs_s)
        }

        Expr::UnOp { op, operand } => {
            let child_prec = expr_prec(operand);
            let needs_parens = child_prec < 11
                || (matches!(op, UnOp::Neg) && starts_with_minus(operand, indent))
                || (matches!(op, UnOp::BNot) && matches!(operand.as_ref(), Expr::UnOp { op: UnOp::BNot, .. }));
            let s = if needs_parens {
                format!("({})", expr_inner(operand, indent))
            } else {
                expr_inner(operand, indent)
            };
            match op {
                UnOp::Neg => format!("-{}", s),
                UnOp::Not => format!("not {}", s),
                UnOp::Len => format!("#{}", s),
                UnOp::BNot => format!("~{}", s),
            }
        }

        Expr::Call { func, args } => {
            // obj.m(obj, ...) → obj:m(...)
            if let Expr::Index { table, key } = func.as_ref() {
                if let (Expr::Name(_), Some(k)) = (table.as_ref(), key.as_str_utf8()) {
                    if is_lua_ident(k) && args.first() == Some(table.as_ref()) {
                        let a = args[1..].iter().map(|e| expr_inner(e, indent)).collect::<Vec<_>>().join(", ");
                        return format!("{}:{}({})", expr_inner(table, indent), k, a);
                    }
                }
            }
            let f = prefix(func, indent);
            let a = args.iter().map(|e| expr_inner(e, indent)).collect::<Vec<_>>().join(", ");
            format!("{}({})", f, a)
        }

        Expr::Method { obj, method, args } => {
            let a = args.iter().map(|e| expr_inner(e, indent)).collect::<Vec<_>>().join(", ");
            format!("{}:{}({})", prefix(obj, indent), method, a)
        }

        Expr::Function(body) => {
            let params = fmt_params_from(body, 0);
            if body.body.is_empty() {
                return format!("function({}) end", params);
            }
            let inner = print_block(&body.body, indent + 1);
            format!("function({})\n{}\n{}end", params, inner, "  ".repeat(indent))
        }

        Expr::Table(fields) => {
            if fields.is_empty() {
                return "{}".to_string();
            }
            let items: Vec<String> = fields.iter().map(|f| match f {
                TableField::IndexField(k, v) =>
                    format!("[{}] = {}", expr_inner(k, indent), expr_inner(v, indent)),
                TableField::NameField(k, v) =>
                    format!("{} = {}", k, expr_inner(v, indent)),
                TableField::ValueField(v) =>
                    expr_inner(v, indent),
            }).collect();
            format!("{{{}}}", items.join(", "))
        }
    }
}

fn starts_with_minus(e: &Expr, indent: usize) -> bool {
    expr_inner(e, indent).starts_with('-')
}

/// Format a float so that Lua reads back exactly the same value and type.
fn format_float(f: f64) -> String {
    if f.is_nan() { return "(0/0)".to_string(); }
    if f.is_infinite() { return if f > 0.0 { "(1/0)".to_string() } else { "(-1/0)".to_string() }; }
    let s = format!("{:?}", f);
    if s.contains('.') || s.contains('e') || s.contains('E') { s } else { format!("{}.0", s) }
}

/// Render raw bytes as a Lua string literal using only escapes that every
/// Lua version understands.
pub fn lua_string_literal(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() + 2);
    out.push('"');
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x20..=0x7e => out.push(b as char),
            _ => {
                // Decimal escape; pad to 3 digits if a digit follows.
                let next_digit = bytes.get(i + 1).map_or(false, |c| c.is_ascii_digit());
                if next_digit { out.push_str(&format!("\\{:03}", b)); } else { out.push_str(&format!("\\{}", b)); }
            }
        }
    }
    out.push('"');
    out
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

#[allow(dead_code)]
fn _unused(_: BinOp) {}
