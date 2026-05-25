//! Structural walkers for the runtime IR tree.
//!
//! Each walker visits the immediate `Expr` children of a node and delegates
//! recursion back to the caller. This lets visitors handle node-local work
//! without re-implementing the `match` over every `ExprKind` variant.

use crate::{Expr, ExprKind, Pattern, RecordSpreadExpr, RecordSpreadPattern, Stmt};

/// Visit every immediate child `Expr` reachable from `expr`, including
/// `Expr`s embedded inside child `Stmt`s (block body) and `Pattern`s
/// (only `Stmt::Let` patterns — record field defaults).
///
/// Match/Handle arm patterns are intentionally not traversed: their record
/// defaults are not reachable in well-formed runtime IR. This matches the
/// behavior of every existing visitor in `yulang-runtime-finalize`.
pub fn walk_children<T, F: FnMut(&Expr<T>)>(expr: &Expr<T>, mut f: F) {
    walk_children_impl(expr, &mut f);
}

fn walk_children_impl<T, F: FnMut(&Expr<T>)>(expr: &Expr<T>, f: &mut F) {
    match &expr.kind {
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
        ExprKind::Lambda { body, .. } => f(body),
        ExprKind::Apply { callee, arg, .. } => {
            f(callee);
            f(arg);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            f(cond);
            f(then_branch);
            f(else_branch);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                f(item);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                f(&field.value);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(e) | RecordSpreadExpr::Tail(e) => f(e),
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                f(value);
            }
        }
        ExprKind::Select { base, .. } => f(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            f(scrutinee);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    f(guard);
                }
                f(&arm.body);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                walk_stmt_exprs_impl(stmt, f);
            }
            if let Some(tail) = tail {
                f(tail);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            f(body);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    f(guard);
                }
                f(&arm.body);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => f(expr),
        ExprKind::LocalPushId { body, .. } => f(body),
        ExprKind::AddId { thunk, .. } => f(thunk),
    }
}

/// Like `walk_children` but stops as soon as `f` returns `true` for any
/// child, and returns `true` itself in that case. Use for short-circuiting
/// predicates.
pub fn walk_children_any<T, F: FnMut(&Expr<T>) -> bool>(expr: &Expr<T>, mut f: F) -> bool {
    walk_children_any_impl(expr, &mut f)
}

fn walk_children_any_impl<T, F: FnMut(&Expr<T>) -> bool>(expr: &Expr<T>, f: &mut F) -> bool {
    match &expr.kind {
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
        ExprKind::Lambda { body, .. } => f(body),
        ExprKind::Apply { callee, arg, .. } => f(callee) || f(arg),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => f(cond) || f(then_branch) || f(else_branch),
        ExprKind::Tuple(items) => items.iter().any(|item| f(item)),
        ExprKind::Record { fields, spread } => {
            fields.iter().any(|field| f(&field.value))
                || spread.as_ref().is_some_and(|spread| match spread {
                    RecordSpreadExpr::Head(e) | RecordSpreadExpr::Tail(e) => f(e),
                })
        }
        ExprKind::Variant { value, .. } => value.as_ref().is_some_and(|v| f(v)),
        ExprKind::Select { base, .. } => f(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            f(scrutinee)
                || arms
                    .iter()
                    .any(|arm| arm.guard.as_ref().is_some_and(|guard| f(guard)) || f(&arm.body))
        }
        ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| walk_stmt_exprs_any_impl(stmt, f))
                || tail.as_ref().is_some_and(|tail| f(tail))
        }
        ExprKind::Handle { body, arms, .. } => {
            f(body)
                || arms
                    .iter()
                    .any(|arm| arm.guard.as_ref().is_some_and(|guard| f(guard)) || f(&arm.body))
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => f(expr),
        ExprKind::LocalPushId { body, .. } => f(body),
        ExprKind::AddId { thunk, .. } => f(thunk),
    }
}

fn walk_stmt_exprs_any_impl<T, F: FnMut(&Expr<T>) -> bool>(stmt: &Stmt<T>, f: &mut F) -> bool {
    match stmt {
        Stmt::Let { pattern, value } => walk_pattern_exprs_any_impl(pattern, f) || f(value),
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => f(expr),
    }
}

fn walk_pattern_exprs_any_impl<T, F: FnMut(&Expr<T>) -> bool>(
    pattern: &Pattern<T>,
    f: &mut F,
) -> bool {
    match pattern {
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => false,
        Pattern::Tuple { items, .. } => items
            .iter()
            .any(|item| walk_pattern_exprs_any_impl(item, f)),
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            prefix
                .iter()
                .chain(suffix.iter())
                .any(|item| walk_pattern_exprs_any_impl(item, f))
                || spread
                    .as_ref()
                    .is_some_and(|spread| walk_pattern_exprs_any_impl(spread, f))
        }
        Pattern::Record { fields, spread, .. } => {
            fields.iter().any(|field| {
                walk_pattern_exprs_any_impl(&field.pattern, f)
                    || field.default.as_ref().is_some_and(|default| f(default))
            }) || spread.as_ref().is_some_and(|spread| match spread {
                RecordSpreadPattern::Head(p) | RecordSpreadPattern::Tail(p) => {
                    walk_pattern_exprs_any_impl(p, f)
                }
            })
        }
        Pattern::Variant { value, .. } => value
            .as_ref()
            .is_some_and(|v| walk_pattern_exprs_any_impl(v, f)),
        Pattern::Or { left, right, .. } => {
            walk_pattern_exprs_any_impl(left, f) || walk_pattern_exprs_any_impl(right, f)
        }
        Pattern::As { pattern, .. } => walk_pattern_exprs_any_impl(pattern, f),
    }
}

/// Visit every immediate child `Expr` of `expr` for mutation, fallibly.
/// Stops and propagates on the first `Err`.
pub fn walk_children_try_mut<T, E, F: FnMut(&mut Expr<T>) -> Result<(), E>>(
    expr: &mut Expr<T>,
    mut f: F,
) -> Result<(), E> {
    walk_children_try_mut_impl(expr, &mut f)
}

fn walk_children_try_mut_impl<T, E, F: FnMut(&mut Expr<T>) -> Result<(), E>>(
    expr: &mut Expr<T>,
    f: &mut F,
) -> Result<(), E> {
    match &mut expr.kind {
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => Ok(()),
        ExprKind::Lambda { body, .. } => f(body),
        ExprKind::Apply { callee, arg, .. } => {
            f(callee)?;
            f(arg)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            f(cond)?;
            f(then_branch)?;
            f(else_branch)
        }
        ExprKind::Tuple(items) => {
            for item in items {
                f(item)?;
            }
            Ok(())
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                f(&mut field.value)?;
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(e) | RecordSpreadExpr::Tail(e) => f(e)?,
                }
            }
            Ok(())
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                f(value)?;
            }
            Ok(())
        }
        ExprKind::Select { base, .. } => f(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            f(scrutinee)?;
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    f(guard)?;
                }
                f(&mut arm.body)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                walk_stmt_exprs_try_mut_impl(stmt, f)?;
            }
            if let Some(tail) = tail {
                f(tail)?;
            }
            Ok(())
        }
        ExprKind::Handle { body, arms, .. } => {
            f(body)?;
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    f(guard)?;
                }
                f(&mut arm.body)?;
            }
            Ok(())
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => f(expr),
        ExprKind::LocalPushId { body, .. } => f(body),
        ExprKind::AddId { thunk, .. } => f(thunk),
    }
}

fn walk_stmt_exprs_try_mut_impl<T, E, F: FnMut(&mut Expr<T>) -> Result<(), E>>(
    stmt: &mut Stmt<T>,
    f: &mut F,
) -> Result<(), E> {
    match stmt {
        Stmt::Let { pattern, value } => {
            walk_pattern_exprs_try_mut_impl(pattern, f)?;
            f(value)
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => f(expr),
    }
}

fn walk_pattern_exprs_try_mut_impl<T, E, F: FnMut(&mut Expr<T>) -> Result<(), E>>(
    pattern: &mut Pattern<T>,
    f: &mut F,
) -> Result<(), E> {
    match pattern {
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => Ok(()),
        Pattern::Tuple { items, .. } => {
            for item in items {
                walk_pattern_exprs_try_mut_impl(item, f)?;
            }
            Ok(())
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter_mut().chain(suffix.iter_mut()) {
                walk_pattern_exprs_try_mut_impl(item, f)?;
            }
            if let Some(spread) = spread {
                walk_pattern_exprs_try_mut_impl(spread, f)?;
            }
            Ok(())
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                walk_pattern_exprs_try_mut_impl(&mut field.pattern, f)?;
                if let Some(default) = &mut field.default {
                    f(default)?;
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(p) | RecordSpreadPattern::Tail(p) => {
                        walk_pattern_exprs_try_mut_impl(p, f)?;
                    }
                }
            }
            Ok(())
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                walk_pattern_exprs_try_mut_impl(value, f)?;
            }
            Ok(())
        }
        Pattern::Or { left, right, .. } => {
            walk_pattern_exprs_try_mut_impl(left, f)?;
            walk_pattern_exprs_try_mut_impl(right, f)
        }
        Pattern::As { pattern, .. } => walk_pattern_exprs_try_mut_impl(pattern, f),
    }
}

/// Visit every immediate child `Expr` of `expr` for mutation.
pub fn walk_children_mut<T, F: FnMut(&mut Expr<T>)>(expr: &mut Expr<T>, mut f: F) {
    let _: Result<(), std::convert::Infallible> = walk_children_try_mut(expr, |child| {
        f(child);
        Ok(())
    });
}

/// Visit every `Expr` directly carried by a `Stmt`. For `Stmt::Let`, this
/// includes the value and any record-field default `Expr`s inside the pattern.
pub fn walk_stmt_exprs<T, F: FnMut(&Expr<T>)>(stmt: &Stmt<T>, mut f: F) {
    walk_stmt_exprs_impl(stmt, &mut f);
}

fn walk_stmt_exprs_impl<T, F: FnMut(&Expr<T>)>(stmt: &Stmt<T>, f: &mut F) {
    match stmt {
        Stmt::Let { pattern, value } => {
            walk_pattern_exprs_impl(pattern, f);
            f(value);
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => f(expr),
    }
}

/// Visit every `Expr` embedded in a `Pattern` (currently only record-field
/// default values).
pub fn walk_pattern_exprs<T, F: FnMut(&Expr<T>)>(pattern: &Pattern<T>, mut f: F) {
    walk_pattern_exprs_impl(pattern, &mut f);
}

fn walk_pattern_exprs_impl<T, F: FnMut(&Expr<T>)>(pattern: &Pattern<T>, f: &mut F) {
    match pattern {
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
        Pattern::Tuple { items, .. } => {
            for item in items {
                walk_pattern_exprs_impl(item, f);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter().chain(suffix.iter()) {
                walk_pattern_exprs_impl(item, f);
            }
            if let Some(spread) = spread {
                walk_pattern_exprs_impl(spread, f);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                walk_pattern_exprs_impl(&field.pattern, f);
                if let Some(default) = &field.default {
                    f(default);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(p) | RecordSpreadPattern::Tail(p) => {
                        walk_pattern_exprs_impl(p, f);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                walk_pattern_exprs_impl(value, f);
            }
        }
        Pattern::Or { left, right, .. } => {
            walk_pattern_exprs_impl(left, f);
            walk_pattern_exprs_impl(right, f);
        }
        Pattern::As { pattern, .. } => walk_pattern_exprs_impl(pattern, f),
    }
}
