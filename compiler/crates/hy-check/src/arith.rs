//! arith.rs — constant arithmetic that would make emitted Go unbuildable.
//!
//! Issue #149: `x / 0` and `x % 0` with a constant `0` divisor pass
//! `hyb check` (0 diagnostics) and then fail `go vet` /
//! `go build` with `invalid operation: division by zero`. The accepted-
//! should-emit-buildable-Go contract requires a checker diagnostic
//! (HYB-E6001) for that constant case. The divisor is constant-folded over
//! literal/unary/binary integer arithmetic (`x / (1 - 1)`, `x % (0 * 5)`).
//! Non-constant zero divisors stay out of scope — Go accepts them and
//! panics at run time.

use crate::model::{unwrap_parens, Checker};
use hy_diag::{Diagnostic, Span};
use hy_syntax::{
    AssignOp, BinOp, Expr, ForKind, InterpPart, LitKind, Place, PlaceKind, SelectArmKind,
    Stmt, UnOp,
};

impl<'a> Checker<'a> {
    /// Pass-B entry: walk the same expression surface as `walk::own_uses`.
    /// Nested block bodies are NOT recursed here — `walk::flatten` already
    /// lists those statements, and a second walk would duplicate diagnostics.
    pub(crate) fn check_stmt_const_zero_divisor(&mut self, stmt: &Stmt) {
        self.check_stmt_const_zero_divisor_inner(stmt, /*deep=*/ false);
    }

    fn check_stmt_const_zero_divisor_inner(&mut self, stmt: &Stmt, deep: bool) {
        match stmt {
            Stmt::Local(l) => {
                for v in &l.values {
                    self.check_expr_const_zero_divisor(v);
                }
            }
            Stmt::Assign {
                targets,
                op,
                values,
                span,
            } => {
                for t in targets {
                    self.check_place_const_zero_divisor(t);
                }
                for v in values {
                    self.check_expr_const_zero_divisor(v);
                }
                if matches!(op, AssignOp::DivAssign | AssignOp::ModAssign)
                    && values.len() == 1
                    && is_constant_zero(&values[0])
                {
                    self.emit_const_zero_divisor(*span, assign_op_txt(*op));
                }
            }
            Stmt::Expr { expr, .. } => self.check_expr_const_zero_divisor(expr),
            Stmt::Send { chan, value, .. } => {
                self.check_expr_const_zero_divisor(chan);
                self.check_expr_const_zero_divisor(value);
            }
            Stmt::If {
                init,
                cond,
                then,
                otherwise,
                ..
            } => {
                if deep {
                    if let Some(init) = init {
                        self.check_stmt_const_zero_divisor_inner(init, true);
                    }
                }
                self.check_expr_const_zero_divisor(cond);
                if deep {
                    for s in &then.stmts {
                        self.check_stmt_const_zero_divisor_inner(s, true);
                    }
                    if let Some(other) = otherwise {
                        self.check_stmt_const_zero_divisor_inner(other, true);
                    }
                }
            }
            Stmt::For { kind, body, .. } => {
                match kind {
                    ForKind::While { cond } => self.check_expr_const_zero_divisor(cond),
                    ForKind::Range { lo, hi, .. } => {
                        self.check_expr_const_zero_divisor(lo);
                        self.check_expr_const_zero_divisor(hi);
                    }
                    ForKind::Iterate { expr, .. } => self.check_expr_const_zero_divisor(expr),
                    ForKind::Infinite => {}
                }
                if deep {
                    for s in &body.stmts {
                        self.check_stmt_const_zero_divisor_inner(s, true);
                    }
                }
            }
            Stmt::Return { values, .. } => {
                for v in values {
                    self.check_expr_const_zero_divisor(v);
                }
            }
            Stmt::Task { callee, args, .. } => {
                self.check_expr_const_zero_divisor(callee);
                for a in args {
                    self.check_expr_const_zero_divisor(&a.value);
                }
            }
            Stmt::Managed { body, .. } => {
                if deep {
                    for s in &body.stmts {
                        self.check_stmt_const_zero_divisor_inner(s, true);
                    }
                }
            }
            Stmt::Match { subject, arms, .. } => {
                self.check_expr_const_zero_divisor(subject);
                for arm in arms {
                    if let Some(g) = &arm.guard {
                        self.check_expr_const_zero_divisor(g);
                    }
                    if deep {
                        for s in &arm.body.stmts {
                            self.check_stmt_const_zero_divisor_inner(s, true);
                        }
                    }
                }
            }
            Stmt::Defer { call, .. } => self.check_expr_const_zero_divisor(call),
            Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Block { block, .. } => {
                if deep {
                    for s in &block.stmts {
                        self.check_stmt_const_zero_divisor_inner(s, true);
                    }
                }
            }
            Stmt::Select { arms, .. } => {
                for arm in arms {
                    match &arm.kind {
                        SelectArmKind::Send { chan, value, .. } => {
                            self.check_expr_const_zero_divisor(chan);
                            self.check_expr_const_zero_divisor(value);
                        }
                        SelectArmKind::Recv { chan, .. } => {
                            self.check_expr_const_zero_divisor(chan)
                        }
                        SelectArmKind::Default => {}
                    }
                    if deep {
                        for s in &arm.body.stmts {
                            self.check_stmt_const_zero_divisor_inner(s, true);
                        }
                    }
                }
            }
        }
    }

    fn check_place_const_zero_divisor(&mut self, place: &Place) {
        match &place.kind {
            PlaceKind::Ident(_) => {}
            PlaceKind::Index { base, index } => {
                self.check_place_const_zero_divisor(base);
                self.check_expr_const_zero_divisor(index);
            }
            PlaceKind::Field { base, .. } | PlaceKind::AddrOf { base } => {
                self.check_place_const_zero_divisor(base)
            }
        }
    }

    pub(crate) fn check_expr_const_zero_divisor(&mut self, expr: &Expr) {
        match expr {
            Expr::Binary { op, lhs, rhs, span } => {
                self.check_expr_const_zero_divisor(lhs);
                self.check_expr_const_zero_divisor(rhs);
                if matches!(op, BinOp::Div | BinOp::Mod) && is_constant_zero(rhs) {
                    self.emit_const_zero_divisor(*span, bin_op_txt(*op));
                }
            }
            Expr::Unary { operand, .. }
            | Expr::AddrOf { operand, .. }
            | Expr::Move { operand, .. }
            | Expr::Try { operand, .. }
            | Expr::Paren { inner: operand, .. }
            | Expr::Field { base: operand, .. }
            | Expr::Receive { chan: operand, .. } => {
                self.check_expr_const_zero_divisor(operand)
            }
            Expr::Index { base, index, .. } => {
                self.check_expr_const_zero_divisor(base);
                self.check_expr_const_zero_divisor(index);
            }
            Expr::Slice { base, lo, hi, .. } => {
                self.check_expr_const_zero_divisor(base);
                if let Some(lo) = lo {
                    self.check_expr_const_zero_divisor(lo);
                }
                if let Some(hi) = hi {
                    self.check_expr_const_zero_divisor(hi);
                }
            }
            Expr::Call { callee, args, .. } => {
                self.check_expr_const_zero_divisor(callee);
                for a in args {
                    self.check_expr_const_zero_divisor(&a.value);
                }
            }
            Expr::StructLit { fields, .. } => {
                for f in fields {
                    self.check_expr_const_zero_divisor(&f.value);
                }
            }
            Expr::SliceLit { items, .. } => {
                for i in items {
                    self.check_expr_const_zero_divisor(i);
                }
            }
            Expr::MapLit { entries, .. } => {
                for (k, v) in entries {
                    self.check_expr_const_zero_divisor(k);
                    self.check_expr_const_zero_divisor(v);
                }
            }
            Expr::Interp { parts, .. } => {
                for p in parts {
                    if let InterpPart::Expr(e) = p {
                        self.check_expr_const_zero_divisor(e);
                    }
                }
            }
            Expr::FnLit { body, .. } => {
                // Closure bodies are not flattened into Pass B — deep-walk.
                for stmt in &body.stmts {
                    self.check_stmt_const_zero_divisor_inner(stmt, /*deep=*/ true);
                }
            }
            Expr::Ident { .. } | Expr::Lit { .. } => {}
        }
    }

    fn emit_const_zero_divisor(&mut self, span: Span, op_txt: &str) {
        let msg = format!(
            "division by constant zero (`{}`): Go rejects this at compile time, so the emitted module would not build",
            op_txt
        );
        self.diags.push(
            Diagnostic::error("HYB-E6001", self.path.clone(), span, msg).with_notes(vec![
                "why: a literal `0` divisor is a Go compile error (`invalid operation: division by zero`); Hybrid's accepted programs must emit buildable Go (issue #149)".to_string(),
                "fix: use a non-zero constant, or bind the divisor to a variable if a run-time panic is the intended behaviour".to_string(),
            ]),
        );
    }
}

fn bin_op_txt(op: BinOp) -> &'static str {
    match op {
        BinOp::Div => "/",
        BinOp::Mod => "%",
        _ => "?",
    }
}

fn assign_op_txt(op: AssignOp) -> &'static str {
    match op {
        AssignOp::DivAssign => "/=",
        AssignOp::ModAssign => "%=",
        _ => "?",
    }
}

/// True when `expr` is a compile-time integer constant that folds to zero.
/// This is the #149/#290 family: the checker must reject the divisor before
/// the emitter produces Go that the Go compiler refuses to fold itself.
fn is_constant_zero(expr: &Expr) -> bool {
    const_int_value(expr) == Some(0)
}

/// Constant-fold integer arithmetic (literals, parentheses, unary negation,
/// add/sub/mul/div/mod). `None` when the expression is not a compile-time
/// integer constant, or when the fold leaves `i128` — Go folds untyped
/// constants at arbitrary precision, so anything we cannot fold keeps the
/// documented run-time-panic path instead of a false positive.
fn const_int_value(expr: &Expr) -> Option<i128> {
    match unwrap_parens(expr) {
        Expr::Lit {
            kind: LitKind::Int(raw),
            ..
        } => int_lit_value(raw),
        Expr::Unary {
            op: UnOp::Neg,
            operand,
            ..
        } => const_int_value(operand).and_then(i128::checked_neg),
        Expr::Binary { op, lhs, rhs, .. } => {
            let l = const_int_value(lhs)?;
            let r = const_int_value(rhs)?;
            match op {
                BinOp::Add => l.checked_add(r),
                BinOp::Sub => l.checked_sub(r),
                BinOp::Mul => l.checked_mul(r),
                BinOp::Div => l.checked_div(r),
                BinOp::Mod => l.checked_rem(r),
                _ => None,
            }
        }
        _ => None,
    }
}

fn int_lit_value(raw: &str) -> Option<i128> {
    let s: String = raw.chars().filter(|c| *c != '_').collect();
    if s.is_empty() {
        return None;
    }
    let (radix, digits) = if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X"))
    {
        (16, rest)
    } else if let Some(rest) = s.strip_prefix("0o").or_else(|| s.strip_prefix("0O")) {
        (8, rest)
    } else if let Some(rest) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
        (2, rest)
    } else if s.len() > 1 && s.starts_with('0') {
        // Go's legacy octal form: a leading 0 followed by octal digits.
        // `010` is eight, not ten; digits 8/9 make it an invalid literal.
        (8, &s[1..])
    } else {
        (10, s.as_str())
    };
    if digits.is_empty() {
        return None;
    }
    i128::try_from(u128::from_str_radix(digits, radix).ok()?).ok()
}

#[cfg(test)]
mod lit_zero_tests {
    use super::{int_lit_value, is_constant_zero};
    use hy_diag::{Pos, Span};
    use hy_syntax::{BinOp, Expr, LitKind, UnOp};

    fn make_int(s: &str) -> Expr {
        Expr::Lit {
            kind: LitKind::Int(s.to_string()),
            span: Span::new(Pos::new(1, 1), Pos::new(1, 1)),
        }
    }

    fn make_neg(inner: Expr) -> Expr {
        Expr::Unary {
            op: UnOp::Neg,
            operand: Box::new(inner),
            span: Span::new(Pos::new(1, 1), Pos::new(1, 1)),
        }
    }

    fn make_bin(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            span: Span::new(Pos::new(1, 1), Pos::new(1, 1)),
        }
    }

    #[test]
    fn recognizes_zero_spellings() {
        for s in ["0", "00", "0_0", "0x0", "0X00", "0o0", "0b0", "0b000"] {
            assert_eq!(int_lit_value(s), Some(0), "{s}");
            assert!(is_constant_zero(&make_int(s)), "{s}");
            assert!(is_constant_zero(&make_neg(make_int(s))), "-{s}");
            assert!(is_constant_zero(&make_neg(make_neg(make_int(s)))), "--{s}");
        }
    }

    #[test]
    fn rejects_nonzero() {
        for s in ["1", "10", "0x1", "0b1", "0o7", "00_1"] {
            assert_ne!(int_lit_value(s), Some(0), "{s}");
            assert!(!is_constant_zero(&make_int(s)), "{s}");
            assert!(!is_constant_zero(&make_neg(make_int(s))), "-{s}");
        }
    }

    #[test]
    fn folds_constant_arithmetic_to_zero() {
        let zero = || make_int("0");
        let one = || make_int("1");
        let two = || make_int("2");
        for expr in [
            make_bin(BinOp::Sub, one(), one()),
            make_bin(BinOp::Add, zero(), zero()),
            make_bin(BinOp::Mul, zero(), make_int("5")),
            make_bin(BinOp::Sub, two(), two()),
            make_bin(BinOp::Div, zero(), make_int("7")),
            make_bin(BinOp::Mod, zero(), make_int("7")),
            make_neg(make_bin(BinOp::Sub, one(), one())),
        ] {
            assert!(is_constant_zero(&expr), "expected zero fold: {expr:?}");
        }
    }

    #[test]
    fn go_integer_literal_bases() {
        assert_eq!(int_lit_value("0"), Some(0));
        assert_eq!(int_lit_value("00"), Some(0));
        assert_eq!(int_lit_value("10"), Some(10));
        assert_eq!(int_lit_value("0_10"), Some(8));
        assert_eq!(int_lit_value("010"), Some(8));
        assert_eq!(int_lit_value("0o10"), Some(8));
        assert_eq!(int_lit_value("0O10"), Some(8));
        assert_eq!(int_lit_value("0x10"), Some(16));
        assert_eq!(int_lit_value("0X10"), Some(16));
        assert_eq!(int_lit_value("0b10"), Some(2));
        assert_eq!(int_lit_value("0B10"), Some(2));
        assert_eq!(int_lit_value("08"), None);
        assert_eq!(int_lit_value("0o8"), None);
        // Legacy octal folds: 010 - 8 is zero, 010 - 10 is -2.
        assert!(is_constant_zero(&make_bin(
            BinOp::Sub,
            make_int("010"),
            make_int("8")
        )));
        assert!(!is_constant_zero(&make_bin(
            BinOp::Sub,
            make_int("010"),
            make_int("10")
        )));
    }

    #[test]
    fn folded_nonzero_or_nonconstant_is_not_zero() {
        assert!(!is_constant_zero(&make_bin(
            BinOp::Sub,
            make_int("1"),
            make_int("0")
        )));
        assert!(!is_constant_zero(&make_bin(
            BinOp::Add,
            make_bin(BinOp::Mul, make_int("0"), make_int("5")),
            make_int("1")
        )));
        assert!(!is_constant_zero(&make_neg(make_bin(
            BinOp::Sub,
            make_int("2"),
            make_int("1")
        ))));
    }
}
