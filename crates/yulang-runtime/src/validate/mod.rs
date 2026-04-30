use std::collections::{BTreeMap, BTreeSet, HashMap};

use yulang_core_ir as core_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult, TypeSource};
use crate::ir::{
    Binding, Expr, ExprKind, HandleArm, HandleEffect, MatchArm, Module, Pattern, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, Stmt, Type as RuntimeType, TypeInstantiation,
};
use crate::types::{
    BoundsChoice, choose_bounds_type, collect_type_vars, core_types_compatible,
    diagnostic_core_type, effect_compatible, is_qualified_runtime_path,
    project_runtime_hir_type_with_vars, strict_core_type as core_type,
};

mod expr;
mod helpers;
mod pattern;
mod types;

use expr::*;
use helpers::*;
use pattern::*;
use types::*;

#[derive(Debug, Clone)]
pub(super) struct BindingInfo {
    pub(super) ty: RuntimeType,
    pub(super) type_params: Vec<core_ir::TypeVar>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeArgKind {
    Value,
    Effect,
}

pub(super) type TypeArgKinds = HashMap<core_ir::Path, Vec<TypeArgKind>>;

pub fn validate_module(module: &Module) -> RuntimeResult<()> {
    let mut bindings = HashMap::new();
    for binding in &module.bindings {
        let info = BindingInfo {
            ty: binding.body.ty.clone(),
            type_params: binding.type_params.clone(),
        };
        match bindings.get_mut(&binding.name) {
            Some(current) if binding_info_generality(&info) > binding_info_generality(current) => {
                *current = info;
            }
            Some(_) => {}
            None => {
                bindings.insert(binding.name.clone(), info);
            }
        }
    }
    let type_arg_kinds = infer_type_arg_kinds(&module.bindings);
    for root in &module.roots {
        match root {
            Root::Binding(path) if !bindings.contains_key(path) => {
                return Err(RuntimeError::UnboundVariable { path: path.clone() });
            }
            Root::Expr(index) if *index >= module.root_exprs.len() => {
                return Err(RuntimeError::MissingRootType { index: *index });
            }
            Root::Binding(_) | Root::Expr(_) => {}
        }
    }
    for binding in &module.bindings {
        validate_binding(binding, &bindings, &type_arg_kinds)?;
    }
    for expr in &module.root_exprs {
        validate_expr(expr, &bindings, &type_arg_kinds, &mut HashMap::new())?;
    }
    Ok(())
}

fn validate_binding(
    binding: &Binding,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
    type_arg_kinds: &TypeArgKinds,
) -> RuntimeResult<()> {
    validate_hir_type_no_any(&binding.body.ty, TypeSource::Validation, type_arg_kinds)?;
    validate_expr(&binding.body, bindings, type_arg_kinds, &mut HashMap::new())?;
    let mut vars = BTreeSet::new();
    collect_type_vars(&binding.scheme.body, &mut vars);
    require_same_hir_type(
        &project_runtime_hir_type_with_vars(&binding.scheme.body, &vars),
        &binding.body.ty,
        TypeSource::BindingScheme,
    )
}

fn infer_type_arg_kinds(bindings: &[Binding]) -> TypeArgKinds {
    let mut out = TypeArgKinds::new();
    for binding in bindings {
        infer_type_arg_kinds_from_hir(&binding.body.ty, &mut out);
        infer_type_arg_kinds_from_core(&binding.scheme.body, &mut out);
        infer_type_arg_kinds_from_expr(&binding.body, &mut out);
    }
    for binding in bindings {
        infer_concrete_effect_args_from_expr(&binding.body, &mut out);
    }
    for binding in bindings {
        infer_concrete_effect_args_from_hir(&binding.body.ty, &mut out);
        infer_concrete_effect_args_from_core(&binding.scheme.body, &mut out);
    }
    out
}

fn infer_type_arg_kinds_from_hir(ty: &RuntimeType, out: &mut TypeArgKinds) {
    let mut vars = HashMap::<core_ir::TypeVar, TypeArgKind>::new();
    collect_hir_type_var_kinds(ty, TypeArgKind::Value, &mut vars);
    collect_hir_named_arg_kinds(ty, &vars, out);
}

fn infer_type_arg_kinds_from_core(ty: &core_ir::Type, out: &mut TypeArgKinds) {
    let mut vars = HashMap::<core_ir::TypeVar, TypeArgKind>::new();
    collect_core_type_var_kinds(ty, TypeArgKind::Value, &mut vars);
    collect_core_named_arg_kinds(ty, &vars, out);
}

fn infer_type_arg_kinds_from_expr(expr: &Expr, out: &mut TypeArgKinds) {
    infer_type_arg_kinds_from_hir(&expr.ty, out);
    match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::Pack { expr: body, .. } => infer_type_arg_kinds_from_expr(body, out),
        ExprKind::Apply { callee, arg, .. } => {
            infer_type_arg_kinds_from_expr(callee, out);
            infer_type_arg_kinds_from_expr(arg, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            infer_type_arg_kinds_from_expr(cond, out);
            infer_type_arg_kinds_from_expr(then_branch, out);
            infer_type_arg_kinds_from_expr(else_branch, out);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                infer_type_arg_kinds_from_expr(item, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                infer_type_arg_kinds_from_expr(&field.value, out);
            }
            infer_type_arg_kinds_from_record_spread(spread, out);
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                infer_type_arg_kinds_from_expr(value, out);
            }
        }
        ExprKind::Select { base, .. } => infer_type_arg_kinds_from_expr(base, out),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            infer_type_arg_kinds_from_expr(scrutinee, out);
            for arm in arms {
                infer_type_arg_kinds_from_pattern(&arm.pattern, out);
                if let Some(guard) = &arm.guard {
                    infer_type_arg_kinds_from_expr(guard, out);
                }
                infer_type_arg_kinds_from_expr(&arm.body, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                infer_type_arg_kinds_from_stmt(stmt, out);
            }
            if let Some(tail) = tail {
                infer_type_arg_kinds_from_expr(tail, out);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            infer_type_arg_kinds_from_expr(body, out);
            for arm in arms {
                infer_type_arg_kinds_from_pattern(&arm.payload, out);
                if let Some(resume) = &arm.resume {
                    infer_type_arg_kinds_from_hir(&resume.ty, out);
                }
                if let Some(guard) = &arm.guard {
                    infer_type_arg_kinds_from_expr(guard, out);
                }
                infer_type_arg_kinds_from_expr(&arm.body, out);
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            infer_type_arg_kinds_from_core(effect, out);
            infer_type_arg_kinds_from_hir(value, out);
            infer_type_arg_kinds_from_expr(expr, out);
        }
        ExprKind::AddId { allowed, thunk, .. } => {
            infer_type_arg_kinds_from_core(allowed, out);
            infer_type_arg_kinds_from_expr(thunk, out);
        }
        ExprKind::Coerce { from, to, expr } => {
            infer_type_arg_kinds_from_core(from, out);
            infer_type_arg_kinds_from_core(to, out);
            infer_type_arg_kinds_from_expr(expr, out);
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_hir_type_var_kinds(
    ty: &RuntimeType,
    slot: TypeArgKind,
    out: &mut HashMap<core_ir::TypeVar, TypeArgKind>,
) {
    match ty {
        RuntimeType::Core(ty) => collect_core_type_var_kinds(ty, slot, out),
        RuntimeType::Fun { param, ret } => {
            collect_hir_type_var_kinds(param, TypeArgKind::Value, out);
            collect_hir_type_var_kinds(ret, TypeArgKind::Value, out);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_core_type_var_kinds(effect, TypeArgKind::Effect, out);
            collect_hir_type_var_kinds(value, TypeArgKind::Value, out);
        }
    }
}

fn collect_core_type_var_kinds(
    ty: &core_ir::Type,
    slot: TypeArgKind,
    out: &mut HashMap<core_ir::TypeVar, TypeArgKind>,
) {
    match ty {
        core_ir::Type::Var(var) => merge_var_kind(out, var.clone(), slot),
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    core_ir::TypeArg::Type(ty) => {
                        collect_core_type_var_kinds(ty, TypeArgKind::Value, out)
                    }
                    core_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_core_type_var_kinds(lower, TypeArgKind::Value, out);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_core_type_var_kinds(upper, TypeArgKind::Value, out);
                        }
                    }
                }
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_core_type_var_kinds(param, TypeArgKind::Value, out);
            collect_core_type_var_kinds(param_effect, TypeArgKind::Effect, out);
            collect_core_type_var_kinds(ret_effect, TypeArgKind::Effect, out);
            collect_core_type_var_kinds(ret, TypeArgKind::Value, out);
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_core_type_var_kinds(item, slot, out);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_type_var_kinds(&field.value, TypeArgKind::Value, out);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_core_type_var_kinds(ty, TypeArgKind::Value, out);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_core_type_var_kinds(payload, TypeArgKind::Value, out);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_core_type_var_kinds(tail, TypeArgKind::Value, out);
            }
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_core_type_var_kinds(item, TypeArgKind::Effect, out);
            }
            collect_core_type_var_kinds(tail, TypeArgKind::Effect, out);
        }
        core_ir::Type::Recursive { body, .. } => collect_core_type_var_kinds(body, slot, out),
        core_ir::Type::Never | core_ir::Type::Any => {}
    }
}

fn collect_hir_named_arg_kinds(
    ty: &RuntimeType,
    vars: &HashMap<core_ir::TypeVar, TypeArgKind>,
    out: &mut TypeArgKinds,
) {
    match ty {
        RuntimeType::Core(ty) => collect_core_named_arg_kinds(ty, vars, out),
        RuntimeType::Fun { param, ret } => {
            collect_hir_named_arg_kinds(param, vars, out);
            collect_hir_named_arg_kinds(ret, vars, out);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_core_named_arg_kinds(effect, vars, out);
            collect_hir_named_arg_kinds(value, vars, out);
        }
    }
}

fn collect_core_named_arg_kinds(
    ty: &core_ir::Type,
    vars: &HashMap<core_ir::TypeVar, TypeArgKind>,
    out: &mut TypeArgKinds,
) {
    match ty {
        core_ir::Type::Named { path, args } => {
            for (index, arg) in args.iter().enumerate() {
                if let Some(var) = type_arg_single_var(arg)
                    && let Some(kind) = vars.get(&var).copied()
                {
                    merge_type_arg_kind(out, path.clone(), index, kind);
                }
                match arg {
                    core_ir::TypeArg::Type(ty) => collect_core_named_arg_kinds(ty, vars, out),
                    core_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_core_named_arg_kinds(lower, vars, out);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_core_named_arg_kinds(upper, vars, out);
                        }
                    }
                }
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_core_named_arg_kinds(param, vars, out);
            collect_core_named_arg_kinds(param_effect, vars, out);
            collect_core_named_arg_kinds(ret_effect, vars, out);
            collect_core_named_arg_kinds(ret, vars, out);
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_core_named_arg_kinds(item, vars, out);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_named_arg_kinds(&field.value, vars, out);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_core_named_arg_kinds(ty, vars, out);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_core_named_arg_kinds(payload, vars, out);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_core_named_arg_kinds(tail, vars, out);
            }
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_core_named_arg_kinds(item, vars, out);
            }
            collect_core_named_arg_kinds(tail, vars, out);
        }
        core_ir::Type::Recursive { body, .. } => collect_core_named_arg_kinds(body, vars, out),
        core_ir::Type::Var(_) | core_ir::Type::Never | core_ir::Type::Any => {}
    }
}

fn type_arg_single_var(arg: &core_ir::TypeArg) -> Option<core_ir::TypeVar> {
    match arg {
        core_ir::TypeArg::Type(core_ir::Type::Var(var)) => Some(var.clone()),
        core_ir::TypeArg::Bounds(bounds) => {
            match (bounds.lower.as_deref(), bounds.upper.as_deref()) {
                (Some(core_ir::Type::Var(lower)), Some(core_ir::Type::Var(upper)))
                    if lower == upper =>
                {
                    Some(lower.clone())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn merge_var_kind(
    out: &mut HashMap<core_ir::TypeVar, TypeArgKind>,
    var: core_ir::TypeVar,
    kind: TypeArgKind,
) {
    let entry = out.entry(var).or_insert(kind);
    if kind == TypeArgKind::Effect {
        *entry = TypeArgKind::Effect;
    }
}

fn merge_type_arg_kind(
    out: &mut TypeArgKinds,
    path: core_ir::Path,
    index: usize,
    kind: TypeArgKind,
) {
    let kinds = out.entry(path).or_default();
    if kinds.len() <= index {
        kinds.resize(index + 1, TypeArgKind::Value);
    }
    if kind == TypeArgKind::Effect {
        kinds[index] = TypeArgKind::Effect;
    }
}

fn infer_concrete_effect_args_from_hir(ty: &RuntimeType, out: &mut TypeArgKinds) {
    match ty {
        RuntimeType::Core(ty) => infer_concrete_effect_args_from_core(ty, out),
        RuntimeType::Fun { param, ret } => {
            infer_concrete_effect_args_from_hir(param, out);
            infer_concrete_effect_args_from_hir(ret, out);
        }
        RuntimeType::Thunk { effect, value } => {
            infer_concrete_effect_args_from_core(effect, out);
            infer_concrete_effect_args_from_hir(value, out);
        }
    }
}

fn infer_concrete_effect_args_from_expr(expr: &Expr, out: &mut TypeArgKinds) {
    infer_concrete_effect_args_from_hir(&expr.ty, out);
    match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::Pack { expr: body, .. } => infer_concrete_effect_args_from_expr(body, out),
        ExprKind::Apply { callee, arg, .. } => {
            infer_concrete_effect_args_from_expr(callee, out);
            infer_concrete_effect_args_from_expr(arg, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            infer_concrete_effect_args_from_expr(cond, out);
            infer_concrete_effect_args_from_expr(then_branch, out);
            infer_concrete_effect_args_from_expr(else_branch, out);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                infer_concrete_effect_args_from_expr(item, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                infer_concrete_effect_args_from_expr(&field.value, out);
            }
            infer_concrete_effect_args_from_record_spread(spread, out);
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                infer_concrete_effect_args_from_expr(value, out);
            }
        }
        ExprKind::Select { base, .. } => infer_concrete_effect_args_from_expr(base, out),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            infer_concrete_effect_args_from_expr(scrutinee, out);
            for arm in arms {
                infer_concrete_effect_args_from_pattern(&arm.pattern, out);
                if let Some(guard) = &arm.guard {
                    infer_concrete_effect_args_from_expr(guard, out);
                }
                infer_concrete_effect_args_from_expr(&arm.body, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                infer_concrete_effect_args_from_stmt(stmt, out);
            }
            if let Some(tail) = tail {
                infer_concrete_effect_args_from_expr(tail, out);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            infer_concrete_effect_args_from_expr(body, out);
            for arm in arms {
                infer_concrete_effect_args_from_pattern(&arm.payload, out);
                if let Some(resume) = &arm.resume {
                    infer_concrete_effect_args_from_hir(&resume.ty, out);
                }
                if let Some(guard) = &arm.guard {
                    infer_concrete_effect_args_from_expr(guard, out);
                }
                infer_concrete_effect_args_from_expr(&arm.body, out);
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            infer_concrete_effect_args_from_core(effect, out);
            infer_concrete_effect_args_from_hir(value, out);
            infer_concrete_effect_args_from_expr(expr, out);
        }
        ExprKind::AddId { allowed, thunk, .. } => {
            infer_concrete_effect_args_from_core(allowed, out);
            infer_concrete_effect_args_from_expr(thunk, out);
        }
        ExprKind::Coerce { from, to, expr } => {
            infer_concrete_effect_args_from_core(from, out);
            infer_concrete_effect_args_from_core(to, out);
            infer_concrete_effect_args_from_expr(expr, out);
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn infer_concrete_effect_args_from_core(ty: &core_ir::Type, out: &mut TypeArgKinds) {
    match ty {
        core_ir::Type::Named { path, args } => {
            for (index, arg) in args.iter().enumerate() {
                match arg {
                    core_ir::TypeArg::Type(arg_ty) => {
                        if matches!(arg_ty, core_ir::Type::Row { .. }) {
                            merge_type_arg_kind(out, path.clone(), index, TypeArgKind::Effect);
                        }
                        infer_concrete_effect_args_from_core(arg_ty, out);
                    }
                    core_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            infer_concrete_effect_args_from_core(lower, out);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            infer_concrete_effect_args_from_core(upper, out);
                        }
                    }
                }
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            infer_concrete_effect_args_from_core(param, out);
            infer_concrete_effect_args_from_core(param_effect, out);
            infer_concrete_effect_args_from_core(ret_effect, out);
            infer_concrete_effect_args_from_core(ret, out);
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                infer_concrete_effect_args_from_core(item, out);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                infer_concrete_effect_args_from_core(&field.value, out);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        infer_concrete_effect_args_from_core(ty, out);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    infer_concrete_effect_args_from_core(payload, out);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                infer_concrete_effect_args_from_core(tail, out);
            }
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                infer_concrete_effect_args_from_core(item, out);
            }
            infer_concrete_effect_args_from_core(tail, out);
        }
        core_ir::Type::Recursive { body, .. } => infer_concrete_effect_args_from_core(body, out),
        core_ir::Type::Var(_) | core_ir::Type::Never | core_ir::Type::Any => {}
    }
}

fn infer_type_arg_kinds_from_stmt(stmt: &Stmt, out: &mut TypeArgKinds) {
    match stmt {
        Stmt::Let { pattern, value } => {
            infer_type_arg_kinds_from_pattern(pattern, out);
            infer_type_arg_kinds_from_expr(value, out);
        }
        Stmt::Expr(expr) => infer_type_arg_kinds_from_expr(expr, out),
        Stmt::Module { body, .. } => infer_type_arg_kinds_from_expr(body, out),
    }
}

fn infer_concrete_effect_args_from_stmt(stmt: &Stmt, out: &mut TypeArgKinds) {
    match stmt {
        Stmt::Let { pattern, value } => {
            infer_concrete_effect_args_from_pattern(pattern, out);
            infer_concrete_effect_args_from_expr(value, out);
        }
        Stmt::Expr(expr) => infer_concrete_effect_args_from_expr(expr, out),
        Stmt::Module { body, .. } => infer_concrete_effect_args_from_expr(body, out),
    }
}

fn infer_type_arg_kinds_from_pattern(pattern: &Pattern, out: &mut TypeArgKinds) {
    infer_type_arg_kinds_from_hir(pattern_ty(pattern), out);
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                infer_type_arg_kinds_from_pattern(item, out);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter().chain(suffix) {
                infer_type_arg_kinds_from_pattern(item, out);
            }
            if let Some(spread) = spread {
                infer_type_arg_kinds_from_pattern(spread, out);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                infer_type_arg_kinds_from_pattern(&field.pattern, out);
                if let Some(default) = &field.default {
                    infer_type_arg_kinds_from_expr(default, out);
                }
            }
            infer_type_arg_kinds_from_record_spread_pattern(spread, out);
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                infer_type_arg_kinds_from_pattern(value, out);
            }
        }
        Pattern::Or { left, right, .. } => {
            infer_type_arg_kinds_from_pattern(left, out);
            infer_type_arg_kinds_from_pattern(right, out);
        }
        Pattern::As { pattern, .. } => infer_type_arg_kinds_from_pattern(pattern, out),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
    }
}

fn infer_concrete_effect_args_from_pattern(pattern: &Pattern, out: &mut TypeArgKinds) {
    infer_concrete_effect_args_from_hir(pattern_ty(pattern), out);
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                infer_concrete_effect_args_from_pattern(item, out);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter().chain(suffix) {
                infer_concrete_effect_args_from_pattern(item, out);
            }
            if let Some(spread) = spread {
                infer_concrete_effect_args_from_pattern(spread, out);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                infer_concrete_effect_args_from_pattern(&field.pattern, out);
                if let Some(default) = &field.default {
                    infer_concrete_effect_args_from_expr(default, out);
                }
            }
            infer_concrete_effect_args_from_record_spread_pattern(spread, out);
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                infer_concrete_effect_args_from_pattern(value, out);
            }
        }
        Pattern::Or { left, right, .. } => {
            infer_concrete_effect_args_from_pattern(left, out);
            infer_concrete_effect_args_from_pattern(right, out);
        }
        Pattern::As { pattern, .. } => infer_concrete_effect_args_from_pattern(pattern, out),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
    }
}

fn infer_type_arg_kinds_from_record_spread(
    spread: &Option<RecordSpreadExpr>,
    out: &mut TypeArgKinds,
) {
    if let Some(RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr)) = spread {
        infer_type_arg_kinds_from_expr(expr, out);
    }
}

fn infer_concrete_effect_args_from_record_spread(
    spread: &Option<RecordSpreadExpr>,
    out: &mut TypeArgKinds,
) {
    if let Some(RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr)) = spread {
        infer_concrete_effect_args_from_expr(expr, out);
    }
}

fn infer_type_arg_kinds_from_record_spread_pattern(
    spread: &Option<RecordSpreadPattern>,
    out: &mut TypeArgKinds,
) {
    if let Some(RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern)) = spread {
        infer_type_arg_kinds_from_pattern(pattern, out);
    }
}

fn infer_concrete_effect_args_from_record_spread_pattern(
    spread: &Option<RecordSpreadPattern>,
    out: &mut TypeArgKinds,
) {
    if let Some(RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern)) = spread {
        infer_concrete_effect_args_from_pattern(pattern, out);
    }
}
