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
    /// `(expr)` — truncates a multi-value call or `...` to one value.
    Paren(Box<Expr>),
    /// Method call `obj:method(args)` (evaluates `obj` once).
    Method {
        obj:    Box<Expr>,
        method: String,
        args:   Vec<Expr>,
    },
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

/// The value of a to-be-closed marker `@tbc(x)`: Lua 5.4's
/// `local x <close> = ...` is a declaration plus this statement, which
/// marks `x` to be closed at the end of the enclosing block.  Passes that
/// move statements across block boundaries must treat it like a `local`.
pub fn tbc_arg(s: &Stat) -> Option<&Expr> {
    match s {
        Stat::Call(Expr::Call { func, args }) if args.len() == 1
            && matches!(func.as_ref(), Expr::Name(n) if n == "@tbc") => Some(&args[0]),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Printer
// ---------------------------------------------------------------------------

mod printer;
pub use printer::{expr_str, is_lua_ident, is_valid_lvalue, lua_string_literal, print_block};


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
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => transform_expr(operand, f),
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
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
        Expr::UnOp { operand, .. } | Expr::Paren(operand) => count_in_expr(operand, name, count),
        Expr::Call { func, args } | Expr::Method { obj: func, args, .. } => {
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
