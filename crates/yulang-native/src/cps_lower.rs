use std::collections::{HashMap, HashSet};
use std::fmt;

use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;

use crate::cps_capture::infer_cps_captures;
use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandler, CpsHandlerArm, CpsHandlerEnv,
    CpsHandlerId, CpsLiteral, CpsModule, CpsRecordField, CpsShotKind, CpsStmt, CpsTerminator,
    CpsValueId,
};

pub type CpsLowerResult<T> = Result<T, CpsLowerError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpsLowerError {
    UnsupportedRoot {
        root: runtime::Root,
    },
    MissingRootExpr {
        index: usize,
    },
    UnsupportedExpr {
        kind: &'static str,
    },
    UnsupportedFreeVar {
        path: typed_ir::Path,
    },
    UnsupportedBareEffectOp {
        path: typed_ir::Path,
    },
    UnsupportedPattern {
        kind: &'static str,
    },
    UnsupportedBinding {
        path: typed_ir::Path,
        reason: &'static str,
    },
    PrimitiveArityMismatch {
        op: typed_ir::PrimitiveOp,
        expected: usize,
        actual: usize,
    },
    CallArityMismatch {
        target: String,
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for CpsLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsLowerError::UnsupportedRoot { root } => {
                write!(f, "CPS lowering does not support root {root:?} yet")
            }
            CpsLowerError::MissingRootExpr { index } => {
                write!(f, "runtime module has no root expression at index {index}")
            }
            CpsLowerError::UnsupportedExpr { kind } => {
                write!(f, "CPS lowering does not support {kind} expressions yet")
            }
            CpsLowerError::UnsupportedFreeVar { path } => {
                write!(
                    f,
                    "CPS lowering does not support free variable `{}` yet",
                    path_name(path)
                )
            }
            CpsLowerError::UnsupportedBareEffectOp { path } => {
                write!(
                    f,
                    "CPS lowering does not support bare effect operation `{}` yet",
                    path_name(path)
                )
            }
            CpsLowerError::UnsupportedPattern { kind } => {
                write!(f, "CPS lowering does not support {kind} patterns yet")
            }
            CpsLowerError::UnsupportedBinding { path, reason } => {
                write!(
                    f,
                    "CPS lowering does not support binding {} yet: {reason}",
                    path_name(path)
                )
            }
            CpsLowerError::PrimitiveArityMismatch {
                op,
                expected,
                actual,
            } => write!(
                f,
                "CPS lowering expected {expected} arguments for primitive {op:?}, got {actual}"
            ),
            CpsLowerError::CallArityMismatch {
                target,
                expected,
                actual,
            } => write!(
                f,
                "CPS lowering expected {expected} arguments for call to {target}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for CpsLowerError {}

pub fn lower_cps_module(module: &runtime::Module) -> CpsLowerResult<CpsModule> {
    let binding_table = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let function_table = module
        .bindings
        .iter()
        .filter_map(binding_function_info)
        .collect::<HashMap<_, _>>();
    let reachable = reachable_binding_paths(module, &function_table, &binding_table);
    let functions = module
        .bindings
        .iter()
        .filter(|binding| reachable.contains(&binding.name))
        .map(|binding| lower_binding(binding, &function_table, &binding_table))
        .collect::<CpsLowerResult<Vec<_>>>()?;

    let mut roots = Vec::new();
    for root in &module.roots {
        match root {
            runtime::Root::Expr(index) => {
                let expr = module
                    .root_exprs
                    .get(*index)
                    .ok_or(CpsLowerError::MissingRootExpr { index: *index })?;
                roots.push(
                    FunctionLowerer::new(
                        format!("root_{index}"),
                        &function_table,
                        &binding_table,
                        Vec::new(),
                        FunctionLoweringTraits::default(),
                    )
                    .lower_root(expr)?,
                );
            }
            runtime::Root::Binding(_) => {
                return Err(CpsLowerError::UnsupportedRoot { root: root.clone() });
            }
        }
    }
    let mut module = CpsModule { functions, roots };
    infer_cps_captures(&mut module);
    make_handler_ids_global(&mut module);
    Ok(module)
}

fn make_handler_ids_global(module: &mut CpsModule) {
    let mut next_handler = 0;
    for function in module.functions.iter_mut().chain(&mut module.roots) {
        let offset = next_handler;
        next_handler += function.handlers.len();
        if offset == 0 {
            continue;
        }
        for handler in &mut function.handlers {
            handler.id.0 += offset;
        }
        for continuation in &mut function.continuations {
            for stmt in &mut continuation.stmts {
                match stmt {
                    CpsStmt::ResumeWithHandler { handler, .. }
                    | CpsStmt::InstallHandler { handler, .. }
                    | CpsStmt::UninstallHandler { handler } => {
                        remap_handler_id(handler, offset);
                    }
                    _ => {}
                }
            }
            if let CpsTerminator::Perform { handler, .. } = &mut continuation.terminator {
                remap_handler_id(handler, offset);
            }
        }
    }
}

fn remap_handler_id(handler: &mut CpsHandlerId, offset: usize) {
    if *handler != dynamic_handler_id() {
        handler.0 += offset;
    }
}

fn reachable_binding_paths(
    module: &runtime::Module,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
) -> HashSet<typed_ir::Path> {
    let binding_bodies = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), &binding.body))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut stack = Vec::new();
    for root in &module.roots {
        match root {
            runtime::Root::Expr(index) => {
                if let Some(expr) = module.root_exprs.get(*index) {
                    collect_expr_direct_calls(expr, functions, bindings, &mut stack);
                }
            }
            runtime::Root::Binding(path) => stack.push(path.clone()),
        }
    }

    while let Some(path) = stack.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        let Some(body) = binding_bodies.get(&path) else {
            continue;
        };
        collect_expr_direct_calls(body, functions, bindings, &mut stack);
    }
    reachable
}

fn collect_expr_direct_calls(
    expr: &runtime::Expr,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
    out: &mut Vec<typed_ir::Path>,
) {
    if let Some((body, arms)) = inline_thunk_handler_apply(expr, functions, bindings) {
        collect_expr_direct_calls(&body, functions, bindings, out);
        let used_effects = collect_expr_performed_effects(&body);
        for arm in &arms {
            if !is_value_handler_arm(arm)
                && !used_effects
                    .iter()
                    .any(|effect| effect_matches(&arm.effect, effect))
            {
                continue;
            }
            collect_pattern_direct_calls(&arm.payload, functions, bindings, out);
            if let Some(guard) = &arm.guard {
                collect_expr_direct_calls(guard, functions, bindings, out);
            }
            collect_expr_direct_calls(&arm.body, functions, bindings, out);
        }
        return;
    }
    if let Ok(Some((target, _info, args))) = direct_apply_path(expr, functions) {
        if !matches!(expr.ty, runtime::Type::Thunk { .. })
            && args.iter().any(|arg| is_inline_argument(arg))
        {
            if let Some(binding) = bindings.get(&target) {
                let mut visiting = HashSet::new();
                let mut memo = HashMap::new();
                if binding_may_perform_when_called(
                    &target,
                    functions,
                    bindings,
                    &mut visiting,
                    &mut memo,
                ) {
                    out.push(target.clone());
                }
                if binding_has_self_direct_call(&target, &binding.body, functions) {
                    out.push(target.clone());
                } else {
                    collect_expr_direct_calls(&binding.body, functions, bindings, out);
                }
            }
        } else {
            out.push(target.clone());
        }
    }
    match &expr.kind {
        runtime::ExprKind::Lambda { body, .. } => {
            collect_expr_direct_calls(body, functions, bindings, out);
        }
        runtime::ExprKind::Apply { callee, arg, .. } => {
            collect_expr_direct_calls(callee, functions, bindings, out);
            collect_expr_direct_calls(arg, functions, bindings, out);
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_direct_calls(cond, functions, bindings, out);
            collect_expr_direct_calls(then_branch, functions, bindings, out);
            collect_expr_direct_calls(else_branch, functions, bindings, out);
        }
        runtime::ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_direct_calls(item, functions, bindings, out);
            }
        }
        runtime::ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_direct_calls(&field.value, functions, bindings, out);
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => {
                        collect_expr_direct_calls(expr, functions, bindings, out);
                    }
                }
            }
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        } => collect_expr_direct_calls(value, functions, bindings, out),
        runtime::ExprKind::Select { base, .. } => {
            collect_expr_direct_calls(base, functions, bindings, out);
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_direct_calls(scrutinee, functions, bindings, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_direct_calls(guard, functions, bindings, out);
                }
                collect_expr_direct_calls(&arm.body, functions, bindings, out);
                collect_pattern_direct_calls(&arm.pattern, functions, bindings, out);
            }
        }
        runtime::ExprKind::Block { stmts, tail } => {
            for (index, stmt) in stmts.iter().enumerate() {
                match stmt {
                    runtime::Stmt::Let { pattern, value } => {
                        if unused_pure_let(
                            pattern,
                            value,
                            &stmts[index + 1..],
                            tail.as_deref(),
                            functions,
                            bindings,
                        ) {
                            continue;
                        }
                        collect_pattern_direct_calls(pattern, functions, bindings, out);
                        collect_expr_direct_calls(value, functions, bindings, out);
                    }
                    runtime::Stmt::Expr(expr) => {
                        collect_expr_direct_calls(expr, functions, bindings, out);
                    }
                    runtime::Stmt::Module { body, .. } => {
                        collect_expr_direct_calls(body, functions, bindings, out);
                    }
                }
            }
            if let Some(tail) = tail {
                collect_expr_direct_calls(tail, functions, bindings, out);
            }
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            collect_expr_direct_calls(body, functions, bindings, out);
            for arm in arms {
                collect_pattern_direct_calls(&arm.payload, functions, bindings, out);
                if let Some(guard) = &arm.guard {
                    collect_expr_direct_calls(guard, functions, bindings, out);
                }
                collect_expr_direct_calls(&arm.body, functions, bindings, out);
            }
        }
        runtime::ExprKind::BindHere { expr }
        | runtime::ExprKind::Thunk { expr, .. }
        | runtime::ExprKind::LocalPushId { body: expr, .. }
        | runtime::ExprKind::AddId { thunk: expr, .. }
        | runtime::ExprKind::Coerce { expr, .. }
        | runtime::ExprKind::Pack { expr, .. } => {
            collect_expr_direct_calls(expr, functions, bindings, out);
        }
        runtime::ExprKind::Var(path) => {
            if let Some(binding) = bindings.get(path)
                && let Some(body) = binding_value_body(binding)
                && !matches!(&body.kind, runtime::ExprKind::Var(inner) if inner == path)
            {
                collect_expr_direct_calls(body, functions, bindings, out);
            }
        }
        runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => {}
    }
}

fn is_value_handler_arm(arm: &runtime::HandleArm) -> bool {
    arm.resume.is_none() && arm.effect.segments.is_empty()
}

fn binding_has_self_direct_call(
    target: &typed_ir::Path,
    expr: &runtime::Expr,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
) -> bool {
    if let Some((called, _)) = direct_apply_target(expr, functions)
        && &called == target
    {
        return true;
    }
    match &expr.kind {
        runtime::ExprKind::Lambda { body, .. }
        | runtime::ExprKind::Thunk { expr: body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => {
            binding_has_self_direct_call(target, body, functions)
        }
        runtime::ExprKind::Apply { callee, arg, .. } => {
            binding_has_self_direct_call(target, callee, functions)
                || binding_has_self_direct_call(target, arg, functions)
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            binding_has_self_direct_call(target, cond, functions)
                || binding_has_self_direct_call(target, then_branch, functions)
                || binding_has_self_direct_call(target, else_branch, functions)
        }
        runtime::ExprKind::Tuple(items) => items
            .iter()
            .any(|item| binding_has_self_direct_call(target, item, functions)),
        runtime::ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| binding_has_self_direct_call(target, &field.value, functions))
                || spread.as_ref().is_some_and(|spread| match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => {
                        binding_has_self_direct_call(target, expr, functions)
                    }
                })
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        }
        | runtime::ExprKind::Select { base: value, .. } => {
            binding_has_self_direct_call(target, value, functions)
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            binding_has_self_direct_call(target, scrutinee, functions)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| binding_has_self_direct_call(target, guard, functions))
                        || binding_has_self_direct_call(target, &arm.body, functions)
                })
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            binding_has_self_direct_call(target, body, functions)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| binding_has_self_direct_call(target, guard, functions))
                        || binding_has_self_direct_call(target, &arm.body, functions)
                })
        }
        runtime::ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| match stmt {
                runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                    binding_has_self_direct_call(target, value, functions)
                }
                runtime::Stmt::Module { body, .. } => {
                    binding_has_self_direct_call(target, body, functions)
                }
            }) || tail
                .as_ref()
                .is_some_and(|tail| binding_has_self_direct_call(target, tail, functions))
        }
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => false,
    }
}

fn collect_expr_performed_effects(expr: &runtime::Expr) -> Vec<typed_ir::Path> {
    let mut effects = Vec::new();
    collect_expr_performed_effects_into(expr, &mut effects);
    effects
}

fn collect_expr_performed_effects_into(expr: &runtime::Expr, out: &mut Vec<typed_ir::Path>) {
    if let Some(request) = effect_apply_nested(expr)
        && !out.iter().any(|seen| seen == &request.effect)
    {
        out.push(request.effect);
    }
    match &expr.kind {
        runtime::ExprKind::Lambda { body, .. }
        | runtime::ExprKind::Thunk { expr: body, .. }
        | runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => {
            collect_expr_performed_effects_into(body, out);
        }
        runtime::ExprKind::Apply { callee, arg, .. } => {
            collect_expr_performed_effects_into(callee, out);
            collect_expr_performed_effects_into(arg, out);
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_performed_effects_into(cond, out);
            collect_expr_performed_effects_into(then_branch, out);
            collect_expr_performed_effects_into(else_branch, out);
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_performed_effects_into(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_performed_effects_into(guard, out);
                }
                collect_expr_performed_effects_into(&arm.body, out);
            }
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            collect_expr_performed_effects_into(body, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_performed_effects_into(guard, out);
                }
                collect_expr_performed_effects_into(&arm.body, out);
            }
        }
        runtime::ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                        collect_expr_performed_effects_into(value, out);
                    }
                    runtime::Stmt::Module { body, .. } => {
                        collect_expr_performed_effects_into(body, out);
                    }
                }
            }
            if let Some(tail) = tail {
                collect_expr_performed_effects_into(tail, out);
            }
        }
        runtime::ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_performed_effects_into(item, out);
            }
        }
        runtime::ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_performed_effects_into(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => {
                        collect_expr_performed_effects_into(expr, out);
                    }
                }
            }
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        }
        | runtime::ExprKind::Select { base: value, .. } => {
            collect_expr_performed_effects_into(value, out);
        }
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => {}
    }
}

fn collect_pattern_direct_calls(
    pattern: &runtime::Pattern,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
    out: &mut Vec<typed_ir::Path>,
) {
    match pattern {
        runtime::Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_direct_calls(item, functions, bindings, out);
            }
        }
        runtime::Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_direct_calls(item, functions, bindings, out);
            }
            if let Some(spread) = spread {
                collect_pattern_direct_calls(spread, functions, bindings, out);
            }
            for item in suffix {
                collect_pattern_direct_calls(item, functions, bindings, out);
            }
        }
        runtime::Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_direct_calls(&field.pattern, functions, bindings, out);
                if let Some(default) = &field.default {
                    collect_expr_direct_calls(default, functions, bindings, out);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadPattern::Head(pattern)
                    | runtime::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_direct_calls(pattern, functions, bindings, out);
                    }
                }
            }
        }
        runtime::Pattern::Variant {
            value: Some(value), ..
        }
        | runtime::Pattern::As { pattern: value, .. } => {
            collect_pattern_direct_calls(value, functions, bindings, out);
        }
        runtime::Pattern::Or { left, right, .. } => {
            collect_pattern_direct_calls(left, functions, bindings, out);
            collect_pattern_direct_calls(right, functions, bindings, out);
        }
        runtime::Pattern::Wildcard { .. }
        | runtime::Pattern::Bind { .. }
        | runtime::Pattern::Lit { .. }
        | runtime::Pattern::Variant { value: None, .. } => {}
    }
}

fn unused_pure_let(
    pattern: &runtime::Pattern,
    value: &runtime::Expr,
    rest: &[runtime::Stmt],
    tail: Option<&runtime::Expr>,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
) -> bool {
    let bound = pattern_bound_paths(pattern);
    !bound.is_empty()
        && pure_unused_expr(value, functions, bindings, &mut HashSet::new())
        && !stmts_or_tail_use_any_path(rest, tail, &bound)
}

fn pattern_bound_paths(pattern: &runtime::Pattern) -> HashSet<typed_ir::Path> {
    let mut paths = HashSet::new();
    collect_pattern_bound_paths(pattern, &mut paths);
    paths
}

fn collect_pattern_bound_paths(pattern: &runtime::Pattern, out: &mut HashSet<typed_ir::Path>) {
    match pattern {
        runtime::Pattern::Bind { name, .. } => {
            out.insert(typed_ir::Path::from_name(name.clone()));
        }
        runtime::Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_bound_paths(item, out);
            }
        }
        runtime::Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_bound_paths(item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_bound_paths(spread, out);
            }
            for item in suffix {
                collect_pattern_bound_paths(item, out);
            }
        }
        runtime::Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_bound_paths(&field.pattern, out);
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadPattern::Head(pattern)
                    | runtime::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_bound_paths(pattern, out);
                    }
                }
            }
        }
        runtime::Pattern::Variant {
            value: Some(value), ..
        }
        | runtime::Pattern::As { pattern: value, .. } => {
            collect_pattern_bound_paths(value, out);
        }
        runtime::Pattern::Or { left, right, .. } => {
            collect_pattern_bound_paths(left, out);
            collect_pattern_bound_paths(right, out);
        }
        runtime::Pattern::Wildcard { .. }
        | runtime::Pattern::Lit { .. }
        | runtime::Pattern::Variant { value: None, .. } => {}
    }
}

fn pure_unused_expr(
    expr: &runtime::Expr,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
    stack: &mut HashSet<typed_ir::Path>,
) -> bool {
    if let Some((op, args)) = primitive_apply(expr) {
        return args.len() == primitive_arity(op)
            && args
                .into_iter()
                .all(|arg| pure_unused_expr(arg, functions, bindings, stack));
    }
    if let Ok(Some((target, _, args))) = direct_apply_path(expr, functions) {
        if !args
            .iter()
            .all(|arg| pure_unused_expr(arg, functions, bindings, stack))
        {
            return false;
        }
        let Some(binding) = bindings.get(target) else {
            return false;
        };
        let (params, body) = collect_lambda_params(&binding.body);
        if params.len() != args.len() || !stack.insert(target.clone()) {
            return false;
        }
        let pure = pure_unused_expr(body, functions, bindings, stack);
        stack.remove(target);
        return pure;
    }

    match &expr.kind {
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Lambda { .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => true,
        runtime::ExprKind::Tuple(items) => items
            .iter()
            .all(|item| pure_unused_expr(item, functions, bindings, stack)),
        runtime::ExprKind::Record { fields, spread } => {
            spread.is_none()
                && fields
                    .iter()
                    .all(|field| pure_unused_expr(&field.value, functions, bindings, stack))
        }
        runtime::ExprKind::Variant { value, .. } => value
            .as_deref()
            .is_none_or(|value| pure_unused_expr(value, functions, bindings, stack)),
        runtime::ExprKind::BindHere { expr }
        | runtime::ExprKind::Thunk { expr, .. }
        | runtime::ExprKind::LocalPushId { body: expr, .. }
        | runtime::ExprKind::AddId { thunk: expr, .. }
        | runtime::ExprKind::Coerce { expr, .. }
        | runtime::ExprKind::Pack { expr, .. } => {
            pure_unused_expr(expr, functions, bindings, stack)
        }
        runtime::ExprKind::Apply { .. }
        | runtime::ExprKind::If { .. }
        | runtime::ExprKind::Select { .. }
        | runtime::ExprKind::Match { .. }
        | runtime::ExprKind::Block { .. }
        | runtime::ExprKind::Handle { .. } => false,
    }
}

fn stmts_or_tail_use_any_path(
    stmts: &[runtime::Stmt],
    tail: Option<&runtime::Expr>,
    paths: &HashSet<typed_ir::Path>,
) -> bool {
    stmts.iter().any(|stmt| stmt_uses_any_path(stmt, paths))
        || tail.is_some_and(|tail| expr_uses_any_path(tail, paths))
}

fn stmt_uses_any_path(stmt: &runtime::Stmt, paths: &HashSet<typed_ir::Path>) -> bool {
    match stmt {
        runtime::Stmt::Let { pattern, value } => {
            pattern_default_uses_any_path(pattern, paths) || expr_uses_any_path(value, paths)
        }
        runtime::Stmt::Expr(expr) | runtime::Stmt::Module { body: expr, .. } => {
            expr_uses_any_path(expr, paths)
        }
    }
}

fn pattern_default_uses_any_path(
    pattern: &runtime::Pattern,
    paths: &HashSet<typed_ir::Path>,
) -> bool {
    match pattern {
        runtime::Pattern::Tuple { items, .. } => items
            .iter()
            .any(|item| pattern_default_uses_any_path(item, paths)),
        runtime::Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            prefix
                .iter()
                .any(|item| pattern_default_uses_any_path(item, paths))
                || spread
                    .as_deref()
                    .is_some_and(|spread| pattern_default_uses_any_path(spread, paths))
                || suffix
                    .iter()
                    .any(|item| pattern_default_uses_any_path(item, paths))
        }
        runtime::Pattern::Record { fields, spread, .. } => {
            fields.iter().any(|field| {
                pattern_default_uses_any_path(&field.pattern, paths)
                    || field
                        .default
                        .as_ref()
                        .is_some_and(|default| expr_uses_any_path(default, paths))
            }) || spread.as_ref().is_some_and(|spread| match spread {
                runtime::RecordSpreadPattern::Head(pattern)
                | runtime::RecordSpreadPattern::Tail(pattern) => {
                    pattern_default_uses_any_path(pattern, paths)
                }
            })
        }
        runtime::Pattern::Variant {
            value: Some(value), ..
        }
        | runtime::Pattern::As { pattern: value, .. } => {
            pattern_default_uses_any_path(value, paths)
        }
        runtime::Pattern::Or { left, right, .. } => {
            pattern_default_uses_any_path(left, paths)
                || pattern_default_uses_any_path(right, paths)
        }
        runtime::Pattern::Wildcard { .. }
        | runtime::Pattern::Bind { .. }
        | runtime::Pattern::Lit { .. }
        | runtime::Pattern::Variant { value: None, .. } => false,
    }
}

fn expr_uses_any_path(expr: &runtime::Expr, paths: &HashSet<typed_ir::Path>) -> bool {
    match &expr.kind {
        runtime::ExprKind::Var(path) => paths.contains(path),
        runtime::ExprKind::Lambda { body, .. }
        | runtime::ExprKind::Thunk { expr: body, .. }
        | runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => expr_uses_any_path(body, paths),
        runtime::ExprKind::Apply { callee, arg, .. } => {
            expr_uses_any_path(callee, paths) || expr_uses_any_path(arg, paths)
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_uses_any_path(cond, paths)
                || expr_uses_any_path(then_branch, paths)
                || expr_uses_any_path(else_branch, paths)
        }
        runtime::ExprKind::Tuple(items) => items.iter().any(|item| expr_uses_any_path(item, paths)),
        runtime::ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_uses_any_path(&field.value, paths))
                || spread.as_ref().is_some_and(|spread| match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => expr_uses_any_path(expr, paths),
                })
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        }
        | runtime::ExprKind::Select { base: value, .. } => expr_uses_any_path(value, paths),
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_uses_any_path(scrutinee, paths)
                || arms.iter().any(|arm| {
                    pattern_default_uses_any_path(&arm.pattern, paths)
                        || arm
                            .guard
                            .as_ref()
                            .is_some_and(|guard| expr_uses_any_path(guard, paths))
                        || expr_uses_any_path(&arm.body, paths)
                })
        }
        runtime::ExprKind::Block { stmts, tail } => {
            stmts_or_tail_use_any_path(stmts, tail.as_deref(), paths)
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            expr_uses_any_path(body, paths)
                || arms.iter().any(|arm| {
                    pattern_default_uses_any_path(&arm.payload, paths)
                        || arm
                            .guard
                            .as_ref()
                            .is_some_and(|guard| expr_uses_any_path(guard, paths))
                        || expr_uses_any_path(&arm.body, paths)
                })
        }
        runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => false,
    }
}

fn direct_apply_target<'expr>(
    expr: &'expr runtime::Expr,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
) -> Option<(typed_ir::Path, Vec<&'expr runtime::Expr>)> {
    direct_apply_path(expr, functions)
        .ok()
        .flatten()
        .map(|(path, _, args)| (path.clone(), args))
}

fn inline_thunk_handler_apply(
    expr: &runtime::Expr,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
) -> Option<(runtime::Expr, Vec<runtime::HandleArm>)> {
    let (target, _, args) = direct_apply_path(expr, functions).ok()??;
    if args.len() != 1 {
        return None;
    }
    let binding = bindings.get(target)?;
    let (params, body) = collect_lambda_params(&binding.body);
    if params.len() != 1 {
        return None;
    }
    let (handled_body, arms) = handler_wrapper_handle(body)?;
    let handled_body = handle_body_execution_inner(handled_body).unwrap_or(handled_body);
    let handled_body = transparent_expr(handled_body);
    let runtime::ExprKind::Var(body_var) = &handled_body.kind else {
        return None;
    };
    if body_var != &typed_ir::Path::from_name(params[0].clone()) {
        return None;
    }
    Some((args[0].clone(), arms.to_vec()))
}

fn transparent_expr(expr: &runtime::Expr) -> &runtime::Expr {
    let mut current = expr;
    loop {
        match &current.kind {
            runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. }
            | runtime::ExprKind::AddId { thunk: expr, .. } => current = expr,
            _ => return current,
        }
    }
}

fn lower_binding(
    binding: &runtime::Binding,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
) -> CpsLowerResult<CpsFunction> {
    if !binding.type_params.is_empty() {
        return Err(CpsLowerError::UnsupportedBinding {
            path: binding.name.clone(),
            reason: "residual type parameters",
        });
    }
    if let runtime::ExprKind::PrimitiveOp(op) = binding.body.kind {
        return Ok(lower_primitive_binding(&binding.name, op));
    }
    let (params, body) = collect_callable_params(&binding.body);
    if params.is_empty() {
        return Err(CpsLowerError::UnsupportedBinding {
            path: binding.name.clone(),
            reason: "non-function body",
        });
    }
    let traits = FunctionLoweringTraits::for_body(&binding.body, functions);
    FunctionLowerer::new(
        path_name(&binding.name),
        functions,
        bindings,
        params,
        traits,
    )
    .lower_root(&body)
    .map_err(|error| match error {
        CpsLowerError::UnsupportedExpr { kind } => CpsLowerError::UnsupportedBinding {
            path: binding.name.clone(),
            reason: kind,
        },
        error => error,
    })
}

fn binding_function_info(binding: &runtime::Binding) -> Option<(typed_ir::Path, FunctionInfo)> {
    if let runtime::ExprKind::PrimitiveOp(op) = binding.body.kind {
        let arity = primitive_arity(op);
        return Some((
            binding.name.clone(),
            FunctionInfo {
                name: path_name(&binding.name),
                arity,
                params: vec![runtime::Type::unknown(); arity],
                ret: runtime::Type::unknown(),
            },
        ));
    }
    let (params, body) = collect_callable_params(&binding.body);
    if params.is_empty() {
        return None;
    }
    let param_types = collect_fun_param_types(&binding.body, params.len());
    Some((
        binding.name.clone(),
        FunctionInfo {
            name: path_name(&binding.name),
            arity: params.len(),
            params: param_types,
            ret: body.ty.clone(),
        },
    ))
}

fn binding_value_body(binding: &runtime::Binding) -> Option<&runtime::Expr> {
    if matches!(binding.body.kind, runtime::ExprKind::PrimitiveOp(_)) {
        return None;
    }
    collect_callable_params(&binding.body)
        .0
        .is_empty()
        .then_some(&binding.body)
}

/// Walk the binding body's nested `Lambda { param, body }` chain, collecting
/// each lambda's argument type from `expr.ty = Fun { param, ret }`.
/// `expected` matches the count produced by `collect_callable_params`.
fn collect_fun_param_types(expr: &runtime::Expr, expected: usize) -> Vec<runtime::Type> {
    let mut params = Vec::with_capacity(expected);
    let mut current = expr;
    while params.len() < expected {
        match &current.kind {
            runtime::ExprKind::Lambda { body, .. } => {
                let arg_ty = match &current.ty {
                    runtime::Type::Fun { param, .. } => (**param).clone(),
                    _ => runtime::Type::unknown(),
                };
                params.push(arg_ty);
                current = body;
            }
            runtime::ExprKind::Block {
                tail: Some(tail), ..
            } => {
                current = tail;
            }
            runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. }
            | runtime::ExprKind::BindHere { expr } => {
                current = expr;
            }
            _ => break,
        }
    }
    while params.len() < expected {
        params.push(runtime::Type::unknown());
    }
    params
}

fn lower_primitive_binding(path: &typed_ir::Path, op: typed_ir::PrimitiveOp) -> CpsFunction {
    let arity = primitive_arity(op);
    let params = (0..arity).map(CpsValueId).collect::<Vec<_>>();
    let dest = CpsValueId(arity);
    CpsFunction {
        name: path_name(path),
        params: params.clone(),
        entry: CpsContinuationId(0),
        continuations: vec![CpsContinuation {
            id: CpsContinuationId(0),
            params: params.clone(),
            captures: Vec::new(),
            shot_kind: CpsShotKind::MultiShot,
            stmts: vec![CpsStmt::Primitive {
                dest,
                op,
                args: params,
            }],
            terminator: CpsTerminator::Return(dest),
        }],
        handlers: Vec::new(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionInfo {
    name: String,
    arity: usize,
    /// Static types of the formal parameters in declaration order. Used at
    /// each call site to decide whether an argument expression has to be
    /// suspended as a Thunk before being passed (`loop(x: [_] _, queue)`
    /// expects `k true` to arrive as a thunk, not as the eager Resume
    /// result).
    params: Vec<runtime::Type>,
    ret: runtime::Type,
}

#[derive(Debug, Clone, Copy, Default)]
struct FunctionLoweringTraits {
    higher_order_helper: bool,
}

impl FunctionLoweringTraits {
    fn for_body(body: &runtime::Expr, functions: &HashMap<typed_ir::Path, FunctionInfo>) -> Self {
        Self {
            higher_order_helper: expr_contains_indirect_apply(body, functions),
        }
    }
}

struct FunctionLowerer<'a> {
    name: String,
    functions: &'a HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &'a HashMap<typed_ir::Path, &'a runtime::Binding>,
    next_value: usize,
    next_continuation: usize,
    next_handler: usize,
    continuations: Vec<CpsContinuation>,
    handlers: Vec<CpsHandler>,
    forced_handler_effects: Vec<(CpsHandlerId, typed_ir::Path)>,
    handlers_with_external_calls: HashSet<CpsHandlerId>,
    current: ContinuationBuilder,
    locals: HashMap<typed_ir::Path, CpsValueId>,
    local_exprs: HashMap<typed_ir::Path, runtime::Expr>,
    resumptions: HashSet<typed_ir::Path>,
    inline_stack: HashSet<typed_ir::Path>,
    active_handler: Option<ActiveHandlerContext>,
    params: Vec<CpsValueId>,
    handler_value_conts: Vec<CpsContinuationId>,
    force_effectful_apply_depth: usize,
    sync_apply_for_immediate_force_depth: usize,
    /// True for helpers whose callback applies / handler bodies may cross
    /// effectful boundaries and therefore need to capture local rest as a
    /// return frame.
    higher_order_helper: bool,
}

#[derive(Clone)]
struct ActiveHandlerContext {
    handler: CpsHandlerId,
    expected_effects: Vec<typed_ir::Path>,
    parent: Option<Box<ActiveHandlerContext>>,
}

impl<'a> FunctionLowerer<'a> {
    fn mark_active_handlers_external_call(&mut self) {
        let mut current = self.active_handler.clone();
        while let Some(context) = current {
            self.handlers_with_external_calls.insert(context.handler);
            current = context.parent.as_deref().cloned();
        }
    }
}

impl<'a> FunctionLowerer<'a> {
    fn new(
        name: String,
        functions: &'a HashMap<typed_ir::Path, FunctionInfo>,
        bindings: &'a HashMap<typed_ir::Path, &'a runtime::Binding>,
        params: Vec<typed_ir::Name>,
        traits: FunctionLoweringTraits,
    ) -> Self {
        let mut next_value = 0;
        let mut param_values = Vec::with_capacity(params.len());
        let mut locals = HashMap::new();
        for param in params {
            let value = CpsValueId(next_value);
            next_value += 1;
            locals.insert(typed_ir::Path::from_name(param), value);
            param_values.push(value);
        }
        Self {
            name,
            functions,
            bindings,
            next_value,
            next_continuation: 1,
            next_handler: 0,
            continuations: Vec::new(),
            handlers: Vec::new(),
            forced_handler_effects: Vec::new(),
            handlers_with_external_calls: HashSet::new(),
            current: ContinuationBuilder::new(CpsContinuationId(0), param_values.clone()),
            locals,
            local_exprs: HashMap::new(),
            resumptions: HashSet::new(),
            inline_stack: HashSet::new(),
            active_handler: None,
            params: param_values,
            handler_value_conts: Vec::new(),
            force_effectful_apply_depth: 0,
            sync_apply_for_immediate_force_depth: 0,
            higher_order_helper: traits.higher_order_helper,
        }
    }

    fn lower_root(mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsFunction> {
        let value = self.lower_expr(expr)?;
        // Force the return value when the static return type demands a
        // plain value. Without this, a body that ends in `MakeThunk` (e.g.
        // a helper fn whose body branches over an effect like `guard`)
        // would leak a Thunk all the way to the root and make CPS eval
        // explode with ExpectedPlainValue.
        let value = self.force_if_non_thunk_demand(value, &expr.ty);
        self.terminate(CpsTerminator::Return(value));
        self.finish_current();
        Ok(CpsFunction {
            name: self.name,
            params: self.params,
            entry: CpsContinuationId(0),
            continuations: self.continuations,
            handlers: self.handlers,
        })
    }

    fn lower_expr(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
        if let Some((body, arms)) = inline_thunk_handler_apply(expr, self.functions, self.bindings)
        {
            return self.lower_handle(&body, &arms);
        }
        if let Some(value) = self.lower_local_expr_apply(expr)? {
            return Ok(value);
        }

        if let Some(request) = effect_apply_body_request(expr) {
            let (expected_effects, handler) =
                self.effect_context_for_request(&request, &[], dynamic_handler_id());
            let (_, value) =
                self.begin_resume_after_perform(request, &expected_effects, handler)?;
            return Ok(value);
        }

        if let runtime::ExprKind::BindHere { expr } = &expr.kind {
            return self.lower_bind_here(expr);
        }

        if let Some((op, args)) = primitive_apply(expr) {
            let expected = primitive_arity(op);
            if args.len() != expected {
                return Err(CpsLowerError::PrimitiveArityMismatch {
                    op,
                    expected,
                    actual: args.len(),
                });
            }
            let args = args
                .into_iter()
                .map(|arg| self.lower_expr(arg))
                .collect::<CpsLowerResult<Vec<_>>>()?;
            let dest = self.fresh_value();
            self.current
                .stmts
                .push(CpsStmt::Primitive { dest, op, args });
            return Ok(dest);
        }

        if let Some((target_path, info, args)) = direct_apply_path(expr, self.functions)? {
            let target = info.name.clone();
            let info_returns_thunk = matches!(info.ret, runtime::Type::Thunk { .. });
            let target_may_perform = self.target_may_perform_when_called(target_path);
            let force_handler_reentry_args =
                self.direct_call_has_handler_reentry_arg(target_path, &args);
            let should_inline_direct = (!matches!(expr.ty, runtime::Type::Thunk { .. })
                && args.iter().any(|arg| is_inline_argument(arg)))
                || (self.active_handler.is_some() && info_returns_thunk && target_may_perform);
            if should_inline_direct {
                if let Some(value) = self.lower_inline_direct_apply(expr)? {
                    return Ok(self.force_if_non_thunk_demand(value, &expr.ty));
                }
            }
            let info_params = info.params.clone();
            let args = args
                .into_iter()
                .enumerate()
                .map(|(idx, arg)| {
                    let expected = info_params
                        .get(idx)
                        .cloned()
                        .unwrap_or_else(runtime::Type::unknown);
                    let lowerer = |this: &mut Self| {
                        let lowered = if matches!(expected, runtime::Type::Thunk { .. }) {
                            this.lower_expr_as_thunk_value(arg)?
                        } else {
                            this.lower_expr(arg)?
                        };
                        Ok(this.force_if_non_thunk_demand(lowered, &expected))
                    };
                    if force_handler_reentry_args && self.expr_contains_resume_apply(arg) {
                        self.force_effectful_apply_depth += 1;
                        let result = lowerer(self);
                        self.force_effectful_apply_depth -= 1;
                        result
                    } else {
                        lowerer(self)
                    }
                })
                .collect::<CpsLowerResult<Vec<_>>>()?;
            // Effectful helpers must cross a continuation boundary even when
            // their surface result is plain: wrapper functions often force an
            // inner thunk before returning, so `info.ret` alone can hide that
            // the call performs under the caller's active handler.
            if (self.higher_order_helper && info_returns_thunk)
                || (target_may_perform && (info_returns_thunk || self.active_handler.is_some()))
            {
                self.mark_active_handlers_external_call();
                let post_cont = self.fresh_continuation();
                let result = self.fresh_value();
                self.terminate(CpsTerminator::EffectfulCall {
                    target,
                    args,
                    resume: post_cont,
                });
                self.finish_current();
                self.current = ContinuationBuilder::new(post_cont, vec![result]);
                // write18: mirror the sync DirectCall path's demand-side
                // forcing. fold_impl/each/once return Thunks via MakeThunk +
                // Return, so the post-call cont receives a Thunk. If the
                // call site's static type is non-Thunk, force the result
                // here so downstream uses see the unwrapped value. Without
                // this, fold_impl's left recursive call returns a Thunk that
                // is silently used as z for the right call without ever
                // running the left iteration — skipping leaves and giving
                // the rightmost element instead of the proper fold.
                return Ok(self.force_if_non_thunk_demand(result, &expr.ty));
            }
            let dest = self.fresh_value();
            self.current
                .stmts
                .push(CpsStmt::DirectCall { dest, target, args });
            if info_returns_thunk || target_may_perform {
                self.mark_active_handlers_external_call();
            }
            // Result demand forcing. Many effectful helpers (`each`, `once`,
            // ...) lower as `MakeThunk` + `Return` so that direct callers
            // that need them as a thunk (`once_mono1` expects each as a
            // thunk arg) receive a thunk handle. But callers that bind the
            // result to a non-thunk static type (`(each ...).once` returns
            // `opt int`) must force it. ForceThunk is a no-op on non-thunk
            // values, so it's safe to insert whenever the consumer's
            // expected type is non-Thunk.
            return Ok(self.force_if_non_thunk_demand(dest, &expr.ty));
        }

        if let Some((resumption, arg)) = self.resume_apply(expr) {
            let arg = self.lower_expr(arg)?;
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::Resume {
                dest,
                resumption,
                arg,
            });
            return Ok(dest);
        }

        match &expr.kind {
            runtime::ExprKind::Lit(lit) => {
                let dest = self.fresh_value();
                self.current.stmts.push(CpsStmt::Literal {
                    dest,
                    literal: lower_literal(lit),
                });
                Ok(dest)
            }
            runtime::ExprKind::PrimitiveOp(_) => Err(CpsLowerError::UnsupportedExpr {
                kind: "bare primitive",
            }),
            runtime::ExprKind::Var(path) => {
                if let Some(expr) = self.local_exprs.get(path).cloned() {
                    return self.lower_expr(&inline_callable_expr(&expr));
                }
                if let Some(expr) = self.bindings.get(path).and_then(|binding| {
                    binding_value_body(binding).filter(
                        |body| !matches!(&body.kind, runtime::ExprKind::Var(inner) if inner == path),
                    )
                }) {
                    let expr = expr.clone();
                    if !self.inline_stack.insert(path.clone()) {
                        return Err(CpsLowerError::UnsupportedFreeVar { path: path.clone() });
                    }
                    let value = self.lower_expr(&expr);
                    self.inline_stack.remove(path);
                    return value;
                }
                self.locals
                    .get(path)
                    .copied()
                    .ok_or_else(|| CpsLowerError::UnsupportedFreeVar { path: path.clone() })
            }
            runtime::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.lower_if(cond, then_branch, else_branch),
            runtime::ExprKind::Block { stmts, tail } => self.lower_block(stmts, tail.as_deref()),
            runtime::ExprKind::EffectOp(path) => {
                Err(CpsLowerError::UnsupportedBareEffectOp { path: path.clone() })
            }
            runtime::ExprKind::Lambda { param, body, .. } => self.lower_lambda(param, body),
            runtime::ExprKind::Apply { callee, arg, .. } => self.lower_apply(expr, callee, arg),
            runtime::ExprKind::Tuple(items) => self.lower_tuple(items),
            runtime::ExprKind::Record { fields, spread } => self.lower_record(fields, spread),
            runtime::ExprKind::Variant { tag, value } => self.lower_variant(tag, value.as_deref()),
            runtime::ExprKind::Select { base, field } => self.lower_select(base, field),
            runtime::ExprKind::Match { .. } => {
                if let Some((cond, then_branch, else_branch)) = bool_match(expr) {
                    self.lower_if(cond, then_branch, else_branch)
                } else {
                    self.lower_match(expr)
                }
            }
            runtime::ExprKind::Handle { body, arms, .. } => self.lower_handle(body, arms),
            runtime::ExprKind::BindHere { expr } => self.lower_bind_here(expr),
            runtime::ExprKind::Thunk { expr, .. } => self.lower_thunk(expr),
            runtime::ExprKind::LocalPushId { id, body } => {
                let dest = self.fresh_value();
                self.current
                    .stmts
                    .push(CpsStmt::FreshGuard { dest, var: *id });
                self.lower_expr(body)
            }
            runtime::ExprKind::AddId { thunk, .. } => self.lower_expr(thunk),
            runtime::ExprKind::Coerce { expr, .. } | runtime::ExprKind::Pack { expr, .. } => {
                self.lower_expr(expr)
            }
            runtime::ExprKind::PeekId => {
                let dest = self.fresh_value();
                self.current.stmts.push(CpsStmt::PeekGuard { dest });
                Ok(dest)
            }
            runtime::ExprKind::FindId { id } => {
                let guard = self.lower_effect_id_ref(*id)?;
                let dest = self.fresh_value();
                self.current.stmts.push(CpsStmt::FindGuard { dest, guard });
                Ok(dest)
            }
        }
    }

    fn lower_effect_id_ref(&mut self, id: runtime::EffectIdRef) -> CpsLowerResult<CpsValueId> {
        match id {
            runtime::EffectIdRef::Peek => {
                let dest = self.fresh_value();
                self.current.stmts.push(CpsStmt::PeekGuard { dest });
                Ok(dest)
            }
            runtime::EffectIdRef::Var(_) => Err(CpsLowerError::UnsupportedExpr {
                kind: "effect id variable",
            }),
        }
    }

    fn lower_bind_here(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
        self.sync_apply_for_immediate_force_depth += 1;
        let thunk = self.lower_expr(expr);
        self.sync_apply_for_immediate_force_depth -= 1;
        let thunk = thunk?;
        let dest = self.fresh_value();
        self.current.stmts.push(CpsStmt::ForceThunk { dest, thunk });
        Ok(dest)
    }

    fn lower_thunk(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
        let entry = self.fresh_continuation();
        let dest = self.fresh_value();
        let saved_current = std::mem::replace(
            &mut self.current,
            ContinuationBuilder::new(entry, Vec::new()),
        );
        let performed_effects = collect_expr_performed_effects(expr);
        let value = if !performed_effects.is_empty() {
            let (mut expected_effects, handler) = self.current_effect_context();
            if expected_effects.is_empty() {
                expected_effects = performed_effects;
            }
            let value_cont = self.fresh_continuation();
            let value = self.fresh_value();
            self.lower_handled_body(expr, &expected_effects, handler, Some(value_cont))?;
            self.current = ContinuationBuilder::new(value_cont, vec![value]);
            value
        } else {
            self.lower_expr(expr)?
        };
        self.terminate(CpsTerminator::Return(value));
        self.finish_current();
        self.current = saved_current;
        self.current.stmts.push(CpsStmt::MakeThunk { dest, entry });
        Ok(dest)
    }

    fn lower_lambda(
        &mut self,
        param: &typed_ir::Name,
        body: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        let entry = self.fresh_continuation();
        let dest = self.fresh_value();
        let param_value = self.fresh_value();
        let saved_current = std::mem::replace(
            &mut self.current,
            ContinuationBuilder::new(entry, vec![param_value]),
        );
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let param_path = typed_ir::Path::from_name(param.clone());
        self.local_exprs.remove(&param_path);
        self.locals.insert(param_path, param_value);
        let value = if let Some(context) = self.active_handler.clone()
            && !collect_expr_performed_effects(body).is_empty()
        {
            let value_cont = self.fresh_continuation();
            let value = self.fresh_value();
            self.lower_handled_body(
                body,
                &context.expected_effects,
                context.handler,
                Some(value_cont),
            )?;
            self.current = ContinuationBuilder::new(value_cont, vec![value]);
            value
        } else {
            self.lower_expr(body)?
        };
        let value = self.force_if_non_thunk_demand(value, &body.ty);
        self.terminate(CpsTerminator::Return(value));
        self.finish_current();
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        self.current = saved_current;
        self.current
            .stmts
            .push(CpsStmt::MakeClosure { dest, entry });
        Ok(dest)
    }

    fn lower_recursive_lambda(
        &mut self,
        name: &typed_ir::Name,
        param: &typed_ir::Name,
        body: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        let entry = self.fresh_continuation();
        let dest = self.fresh_value();
        let param_value = self.fresh_value();
        let saved_current = std::mem::replace(
            &mut self.current,
            ContinuationBuilder::new(entry, vec![param_value]),
        );
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let self_path = typed_ir::Path::from_name(name.clone());
        self.local_exprs.remove(&self_path);
        self.locals.insert(self_path, dest);
        let param_path = typed_ir::Path::from_name(param.clone());
        self.local_exprs.remove(&param_path);
        self.locals.insert(param_path, param_value);
        let value = if let Some(context) = self.active_handler.clone()
            && !collect_expr_performed_effects(body).is_empty()
        {
            let value_cont = self.fresh_continuation();
            let value = self.fresh_value();
            self.lower_handled_body(
                body,
                &context.expected_effects,
                context.handler,
                Some(value_cont),
            )?;
            self.current = ContinuationBuilder::new(value_cont, vec![value]);
            value
        } else {
            self.lower_expr(body)?
        };
        let value = self.force_if_non_thunk_demand(value, &body.ty);
        self.terminate(CpsTerminator::Return(value));
        self.finish_current();
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        self.current = saved_current;
        self.current
            .stmts
            .push(CpsStmt::MakeRecursiveClosure { dest, entry });
        Ok(dest)
    }

    fn lower_apply(
        &mut self,
        expr: &runtime::Expr,
        callee: &runtime::Expr,
        arg: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        let closure = self.lower_expr(callee)?;
        let callee_ty = callable_type_after_force(&callee.ty);
        let forced = self.fresh_value();
        self.current.stmts.push(CpsStmt::ForceThunk {
            dest: forced,
            thunk: closure,
        });
        let closure = forced;
        let arg = self.lower_expr_as_call_arg(callee_ty, arg)?;
        // Higher-order helpers must apply closures through a continuation
        // boundary when the result is effectful.
        if self.force_effectful_apply_depth > 0
            || (self.sync_apply_for_immediate_force_depth == 0
                && self.higher_order_helper
                && matches!(expr.ty, runtime::Type::Thunk { .. }))
        {
            let post_cont = self.fresh_continuation();
            let result = self.fresh_value();
            self.terminate(CpsTerminator::EffectfulApply {
                closure,
                arg,
                resume: post_cont,
            });
            self.finish_current();
            self.current = ContinuationBuilder::new(post_cont, vec![result]);
            return Ok(result);
        }
        let dest = self.fresh_value();
        self.current
            .stmts
            .push(CpsStmt::ApplyClosure { dest, closure, arg });
        // Apply expression that demands a non-thunk static type forces the
        // closure's result so a Thunk that escaped through curried
        // ApplyClosure (e.g. once_mono1's MakeThunk + Return) does not leak
        // into a consumer that needs a plain value (`(each ...).once`).
        Ok(self.force_if_non_thunk_demand(dest, &expr.ty))
    }

    /// Lower a positional call argument. If the callee's first formal
    /// parameter has Thunk type, wrap the argument in MakeThunk so that
    /// `loop(k true, queue)` style sites pass `k true` as a deferred
    /// computation rather than the Resume's eager scalar.
    fn lower_expr_as_call_arg(
        &mut self,
        callee_ty: &runtime::Type,
        arg: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        let param_ty = match callee_ty {
            runtime::Type::Fun { param, .. } => Some(param.as_ref()),
            _ => None,
        };
        let param_is_thunk = matches!(param_ty, Some(runtime::Type::Thunk { .. }));
        if param_is_thunk {
            self.lower_expr_as_thunk_value(arg)
        } else {
            self.lower_expr(arg)
        }
    }

    /// Suspend an arbitrary expression as a Thunk so that it is evaluated
    /// only when the callee forces it (e.g. `loop`'s `catch x:` forcing
    /// `x = each [1,2,3]`). A syntactic Thunk (`{ ... }`) already produces
    /// a thunk handle via `lower_expr`, so we forward it directly. Every
    /// other expression — including `Apply` chains whose static type is
    /// `[eff] T` — must be wrapped via `lower_thunk` so the underlying
    /// `DirectCall` does not run before the caller has installed its
    /// handler scope.
    fn lower_expr_as_thunk_value(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
        // A syntactic Thunk literal `{ ... }` already produces a thunk
        // handle; a `Var` binding to a thunk-typed local just reads the
        // existing handle. Lowering either eagerly is fine — they don't
        // run anything. Anything else (especially `Apply`) would *evaluate*
        // when lowered eagerly, so we wrap it in `MakeThunk` to defer.
        match &expr.kind {
            runtime::ExprKind::Thunk { .. } | runtime::ExprKind::Var(_) => self.lower_expr(expr),
            _ if self.expr_contains_resume_apply(expr) => {
                self.lower_thunk_for_handler_reentry(expr)
            }
            _ => self.lower_thunk(expr),
        }
    }

    fn lower_thunk_for_handler_reentry(
        &mut self,
        expr: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        self.lower_expr_with_forced_effectful_applies_inner(|this| this.lower_thunk(expr))
    }

    fn lower_expr_with_forced_effectful_applies(
        &mut self,
        expr: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        self.lower_expr_with_forced_effectful_applies_inner(|this| this.lower_expr(expr))
    }

    fn lower_expr_with_forced_effectful_applies_inner<T>(
        &mut self,
        lower: impl FnOnce(&mut Self) -> CpsLowerResult<T>,
    ) -> CpsLowerResult<T> {
        self.force_effectful_apply_depth += 1;
        let result = lower(self);
        self.force_effectful_apply_depth -= 1;
        result
    }

    /// Demand-side dual of `lower_expr_as_thunk_value`. When the surrounding
    /// expression expects a non-thunk value but the underlying call/apply may
    /// have produced a Thunk (e.g. an effectful helper that lowers as
    /// `MakeThunk` + `Return`), insert an explicit `ForceThunk` so the value
    /// reaches its consumer un-suspended. `ForceThunk` is a no-op on plain /
    /// resumption / closure values, so over-forcing is safe; we still avoid
    /// it when the consumer's static type is itself a Thunk so first-class
    /// thunk values keep flowing.
    fn force_if_non_thunk_demand(
        &mut self,
        value: CpsValueId,
        expected_ty: &runtime::Type,
    ) -> CpsValueId {
        if matches!(expected_ty, runtime::Type::Thunk { .. }) {
            return value;
        }
        let forced = self.fresh_value();
        self.current.stmts.push(CpsStmt::ForceThunk {
            dest: forced,
            thunk: value,
        });
        forced
    }

    fn lower_tuple(&mut self, items: &[runtime::Expr]) -> CpsLowerResult<CpsValueId> {
        let items = items
            .iter()
            .map(|item| self.lower_expr(item))
            .collect::<CpsLowerResult<Vec<_>>>()?;
        let dest = self.fresh_value();
        self.current.stmts.push(CpsStmt::Tuple { dest, items });
        Ok(dest)
    }

    fn lower_record(
        &mut self,
        fields: &[runtime::RecordExprField],
        spread: &Option<runtime::RecordSpreadExpr>,
    ) -> CpsLowerResult<CpsValueId> {
        if spread.is_some() {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "record spread",
            });
        }
        let fields = fields
            .iter()
            .map(|field| {
                Ok(CpsRecordField {
                    name: field.name.clone(),
                    value: self.lower_expr(&field.value)?,
                })
            })
            .collect::<CpsLowerResult<Vec<_>>>()?;
        let dest = self.fresh_value();
        self.current.stmts.push(CpsStmt::Record { dest, fields });
        Ok(dest)
    }

    fn lower_variant(
        &mut self,
        tag: &typed_ir::Name,
        value: Option<&runtime::Expr>,
    ) -> CpsLowerResult<CpsValueId> {
        let value = value.map(|value| self.lower_expr(value)).transpose()?;
        let dest = self.fresh_value();
        self.current.stmts.push(CpsStmt::Variant {
            dest,
            tag: tag.clone(),
            value,
        });
        Ok(dest)
    }

    fn lower_select(
        &mut self,
        base: &runtime::Expr,
        field: &typed_ir::Name,
    ) -> CpsLowerResult<CpsValueId> {
        let base = self.lower_expr(base)?;
        let dest = self.fresh_value();
        self.current.stmts.push(CpsStmt::Select {
            dest,
            base,
            field: field.clone(),
        });
        Ok(dest)
    }

    fn lower_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        if !collect_expr_performed_effects(cond).is_empty()
            || self.expr_may_perform_when_evaluated(cond)
        {
            let (expected_effects, handler) = self.current_effect_context();
            let value_cont = self.fresh_continuation();
            let result = self.fresh_value();
            self.lower_handled_effect_condition_if(
                cond,
                then_branch,
                else_branch,
                &expected_effects,
                handler,
                Some(value_cont),
            )?;
            self.current = ContinuationBuilder::new(value_cont, vec![result]);
            return Ok(result);
        }

        let cond = self.lower_expr(cond)?;
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let then_cont = self.fresh_continuation();
        let else_cont = self.fresh_continuation();
        let merge_cont = self.fresh_continuation();
        let result = self.fresh_value();

        self.terminate(CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(then_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        let then_value = self.lower_expr(then_branch)?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![then_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(else_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        let else_value = self.lower_expr(else_branch)?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![else_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        Ok(result)
    }

    fn lower_block(
        &mut self,
        stmts: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
    ) -> CpsLowerResult<CpsValueId> {
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        for (index, stmt) in stmts.iter().enumerate() {
            match stmt {
                runtime::Stmt::Let { pattern, value } => {
                    if unused_pure_let(
                        pattern,
                        value,
                        &stmts[index + 1..],
                        tail,
                        self.functions,
                        self.bindings,
                    ) {
                        continue;
                    }
                    if let Some((name, param, body)) = recursive_lambda_let(pattern, value) {
                        let value = self.lower_recursive_lambda(name, param, body)?;
                        self.locals
                            .insert(typed_ir::Path::from_name(name.clone()), value);
                        continue;
                    }
                    let value = self.lower_expr(value)?;
                    self.bind_pattern(pattern, value)?;
                }
                runtime::Stmt::Expr(expr) => {
                    self.lower_expr(expr)?;
                }
                runtime::Stmt::Module { .. } => {
                    self.locals = saved_locals;
                    return Err(CpsLowerError::UnsupportedExpr {
                        kind: "module statement",
                    });
                }
            }
        }
        let value = match tail {
            Some(tail) => self.lower_expr(tail)?,
            None => {
                let value = self.fresh_value();
                self.current.stmts.push(CpsStmt::Literal {
                    dest: value,
                    literal: CpsLiteral::Unit,
                });
                value
            }
        };
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        Ok(value)
    }

    fn lower_match(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
        let runtime::ExprKind::Match {
            scrutinee, arms, ..
        } = &expr.kind
        else {
            return Err(CpsLowerError::UnsupportedExpr { kind: "match" });
        };
        let scrutinee = self.lower_expr(scrutinee)?;
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let merge_cont = self.fresh_continuation();
        let result = self.fresh_value();
        let fallback_cont = self.fresh_continuation();
        let mut arm_conts = Vec::with_capacity(arms.len());
        let mut guard_conts = Vec::with_capacity(arms.len());
        let mut next_conts = Vec::with_capacity(arms.len());
        for _ in arms {
            arm_conts.push(self.fresh_continuation());
            guard_conts.push(None);
        }

        let mut current_test_cont = None;
        for (index, arm) in arms.iter().enumerate() {
            if let Some(test_cont) = current_test_cont {
                self.current = ContinuationBuilder::new(test_cont, Vec::new());
                self.locals = saved_locals.clone();
                self.local_exprs = saved_local_exprs.clone();
                self.resumptions = saved_resumptions.clone();
            }
            let next_cont = if index + 1 == arms.len() {
                fallback_cont
            } else {
                let next = self.fresh_continuation();
                current_test_cont = Some(next);
                next
            };
            next_conts.push(next_cont);
            let success_cont = if arm.guard.is_some() {
                let guard_cont = self.fresh_continuation();
                guard_conts[index] = Some(guard_cont);
                guard_cont
            } else {
                arm_conts[index]
            };
            if self.lower_pattern_test(scrutinee, &arm.pattern, success_cont, next_cont)? {
                self.finish_current();
            }
        }

        self.current = ContinuationBuilder::new(fallback_cont, Vec::new());
        let unit = self.fresh_value();
        self.current.stmts.push(CpsStmt::Literal {
            dest: unit,
            literal: CpsLiteral::Unit,
        });
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![unit],
        });
        self.finish_current();

        for (index, arm) in arms.iter().enumerate() {
            let Some(guard_cont) = guard_conts[index] else {
                continue;
            };
            let Some(guard) = &arm.guard else {
                continue;
            };
            self.current = ContinuationBuilder::new(guard_cont, Vec::new());
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.pattern, scrutinee)?;
            if !collect_expr_performed_effects(guard).is_empty() {
                let (expected_effects, handler) = self.current_effect_context();
                let guard_value_cont = self.fresh_continuation();
                let guard_value = self.fresh_value();
                self.lower_handled_body(guard, &expected_effects, handler, Some(guard_value_cont))?;
                self.current = ContinuationBuilder::new(guard_value_cont, vec![guard_value]);
                self.locals = saved_locals.clone();
                self.local_exprs = saved_local_exprs.clone();
                self.resumptions = saved_resumptions.clone();
                self.terminate(CpsTerminator::Branch {
                    cond: guard_value,
                    then_cont: arm_conts[index],
                    else_cont: next_conts[index],
                });
                self.finish_current();
            } else {
                let guard_value = self.lower_expr(guard)?;
                self.terminate(CpsTerminator::Branch {
                    cond: guard_value,
                    then_cont: arm_conts[index],
                    else_cont: next_conts[index],
                });
                self.finish_current();
            }
        }

        for (arm, arm_cont) in arms.iter().zip(arm_conts) {
            self.current = ContinuationBuilder::new(arm_cont, Vec::new());
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.pattern, scrutinee)?;
            let value = self.lower_expr(&arm.body)?;
            self.terminate(CpsTerminator::Continue {
                target: merge_cont,
                args: vec![value],
            });
            self.finish_current();
        }

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(result)
    }

    fn lower_pattern_test(
        &mut self,
        value: CpsValueId,
        pattern: &runtime::Pattern,
        then_cont: CpsContinuationId,
        else_cont: CpsContinuationId,
    ) -> CpsLowerResult<bool> {
        match pattern {
            runtime::Pattern::Wildcard { .. } | runtime::Pattern::Bind { .. } => {
                self.terminate(CpsTerminator::Continue {
                    target: then_cont,
                    args: Vec::new(),
                });
                Ok(true)
            }
            runtime::Pattern::Lit {
                lit: typed_ir::Lit::Bool(true),
                ..
            } => {
                self.terminate(CpsTerminator::Branch {
                    cond: value,
                    then_cont,
                    else_cont,
                });
                Ok(true)
            }
            runtime::Pattern::Lit {
                lit: typed_ir::Lit::Bool(false),
                ..
            } => {
                let cond = self.fresh_value();
                self.current.stmts.push(CpsStmt::Primitive {
                    dest: cond,
                    op: typed_ir::PrimitiveOp::BoolNot,
                    args: vec![value],
                });
                self.terminate(CpsTerminator::Branch {
                    cond,
                    then_cont,
                    else_cont,
                });
                Ok(true)
            }
            runtime::Pattern::Lit {
                lit: typed_ir::Lit::Unit,
                ..
            } => {
                self.terminate(CpsTerminator::Continue {
                    target: then_cont,
                    args: Vec::new(),
                });
                Ok(true)
            }
            runtime::Pattern::Lit {
                lit: typed_ir::Lit::Int(expected),
                ..
            } => {
                let literal = self.fresh_value();
                self.current.stmts.push(CpsStmt::Literal {
                    dest: literal,
                    literal: CpsLiteral::Int(expected.clone()),
                });
                let cond = self.fresh_value();
                self.current.stmts.push(CpsStmt::Primitive {
                    dest: cond,
                    op: typed_ir::PrimitiveOp::IntEq,
                    args: vec![value, literal],
                });
                self.terminate(CpsTerminator::Branch {
                    cond,
                    then_cont,
                    else_cont,
                });
                Ok(true)
            }
            runtime::Pattern::Variant { tag, .. } => {
                let cond = self.fresh_value();
                self.current.stmts.push(CpsStmt::VariantTagEq {
                    dest: cond,
                    variant: value,
                    tag: tag.clone(),
                });
                self.terminate(CpsTerminator::Branch {
                    cond,
                    then_cont,
                    else_cont,
                });
                Ok(true)
            }
            runtime::Pattern::Or { left, right, .. } => {
                let right_cont = self.fresh_continuation();
                self.lower_pattern_test(value, left, then_cont, right_cont)?;
                self.finish_current();
                self.current = ContinuationBuilder::new(right_cont, Vec::new());
                self.lower_pattern_test(value, right, then_cont, else_cont)
            }
            _ => Err(CpsLowerError::UnsupportedPattern {
                kind: "match pattern",
            }),
        }
    }

    fn lower_handle(
        &mut self,
        body: &runtime::Expr,
        arms: &[runtime::HandleArm],
    ) -> CpsLowerResult<CpsValueId> {
        let mut value_arms = arms
            .iter()
            .filter(|arm| arm.resume.is_none() && arm.effect.segments.is_empty());
        let value_arm = value_arms.next();
        if value_arms.next().is_some() {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "multi-value handler",
            });
        }
        if value_arm.is_some_and(|arm| arm.guard.is_some()) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler guard",
            });
        }

        let effect_arms = arms
            .iter()
            .filter(|arm| arm.resume.is_some())
            .collect::<Vec<_>>();
        if effect_arms.is_empty() {
            let value = self.lower_expr(body)?;
            return self.lower_handle_value(value, value_arm);
        };
        if arms
            .iter()
            .any(|candidate| candidate.resume.is_none() && !candidate.effect.segments.is_empty())
        {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler without resume",
            });
        }
        if effect_arms.iter().any(|arm| arm.guard.is_some()) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler guard",
            });
        }
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let saved_forced_handler_effects_len = self.forced_handler_effects.len();
        let saved_handler_value_conts_len = self.handler_value_conts.len();

        let value_cont = self.fresh_continuation();
        let merge_cont = self.fresh_continuation();
        let handler = self.fresh_handler();
        let result = self.fresh_value();
        let effects = effect_arms
            .iter()
            .map(|arm| arm.effect.clone())
            .collect::<Vec<_>>();

        let saved_active_handler = self.active_handler.clone();
        self.active_handler = Some(ActiveHandlerContext {
            handler,
            expected_effects: effects.clone(),
            parent: saved_active_handler.clone().map(Box::new),
        });
        self.handler_value_conts.push(value_cont);
        self.current.stmts.push(CpsStmt::InstallHandler {
            handler,
            envs: Vec::new(),
            // ScopeReturn (i.e. arm body's non-local return) lands at the
            // merge continuation, NOT the value-arm continuation. Arm bodies
            // already terminate with `Continue merge_cont [arm_value]` in
            // their own lowering; the value arm only applies when the body
            // completes without firing an arm.
            escape: merge_cont,
        });
        self.lower_handled_body(body, &effects, handler, Some(value_cont))?;
        self.handler_value_conts
            .truncate(saved_handler_value_conts_len);
        self.active_handler = saved_active_handler.clone();
        let used_effects = self.performed_effects_for_handler(handler);
        let body_made_external_call = self.handlers_with_external_calls.contains(&handler);
        let mut handler_entries = Vec::with_capacity(effect_arms.len());
        for arm in &effect_arms {
            let directly_used = used_effects.iter().any(|effect| {
                effect_matches(&arm.effect, effect) || effect_matches(effect, &arm.effect)
            });
            // Materialize all handler arms when the body forwards effects through
            // an effectful direct call (e.g. recursive helper returning [eff] T):
            // the callee performs effects with handler = dynamic_handler_id() so
            // performed_effects_for_handler cannot see them statically.
            if directly_used || body_made_external_call {
                handler_entries.push((arm.effect.clone(), self.fresh_continuation()));
            }
        }
        if !handler_entries.is_empty() {
            self.handlers.push(CpsHandler {
                id: handler,
                arms: handler_entries
                    .iter()
                    .map(|(effect, entry)| CpsHandlerArm {
                        effect: effect.clone(),
                        entry: *entry,
                    })
                    .collect(),
            });
        }

        let handled_value = self.fresh_value();
        self.current = ContinuationBuilder::new(value_cont, vec![handled_value]);
        self.current
            .stmts
            .push(CpsStmt::UninstallHandler { handler });
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let handled = self.lower_handle_value(handled_value, value_arm)?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![handled],
        });
        self.finish_current();

        for (effect, handler_cont) in handler_entries {
            let Some(arm) = effect_arms
                .iter()
                .find(|arm| effect_matches(&arm.effect, &effect))
            else {
                return Err(CpsLowerError::UnsupportedExpr {
                    kind: "handler effect mismatch",
                });
            };
            let Some(resume) = &arm.resume else {
                return Err(CpsLowerError::UnsupportedExpr {
                    kind: "handler without resume",
                });
            };
            let handler_payload = self.fresh_value();
            let handler_resume = self.fresh_value();
            self.current =
                ContinuationBuilder::new(handler_cont, vec![handler_payload, handler_resume]);
            self.current
                .stmts
                .push(CpsStmt::UninstallHandler { handler });
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.payload, handler_payload)?;
            let resume_path = typed_ir::Path::from_name(resume.name.clone());
            self.locals.insert(resume_path.clone(), handler_resume);
            self.resumptions.insert(resume_path);
            let handled = self.lower_handler_body_expr(&arm.body, Some(handler))?;
            self.terminate(CpsTerminator::Continue {
                target: merge_cont,
                args: vec![handled],
            });
            self.finish_current();
        }

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        self.active_handler = saved_active_handler;
        self.forced_handler_effects
            .truncate(saved_forced_handler_effects_len);
        self.handler_value_conts
            .truncate(saved_handler_value_conts_len);
        Ok(result)
    }

    fn lower_handle_value(
        &mut self,
        value: CpsValueId,
        value_arm: Option<&runtime::HandleArm>,
    ) -> CpsLowerResult<CpsValueId> {
        let Some(arm) = value_arm else {
            return Ok(value);
        };
        self.bind_pattern(&arm.payload, value)?;
        self.lower_handler_body_expr(&arm.body, None)
    }

    fn lower_handler_body_expr(
        &mut self,
        expr: &runtime::Expr,
        handler: Option<CpsHandlerId>,
    ) -> CpsLowerResult<CpsValueId> {
        if let Some(inner) = handler_body_plain_value_inner(expr) {
            return self.lower_expr(inner);
        }
        if let Some(handler) = handler
            && let Some(reentry) = self.handler_reentry_apply(expr, handler)?
        {
            self.current.stmts.push(CpsStmt::ResumeWithHandler {
                dest: reentry.dest,
                resumption: reentry.resumption,
                arg: reentry.arg,
                handler,
                envs: reentry.envs,
            });
            return Ok(reentry.dest);
        }
        if handler.is_some() && self.apply_chain_contains_resume_argument(expr) {
            return self.lower_expr_with_forced_effectful_applies(expr);
        }
        if let Some(handler) = handler
            && let runtime::ExprKind::Block { stmts, tail } = &expr.kind
        {
            if stmts.is_empty()
                && let Some(tail) = tail
            {
                return self.lower_handler_body_expr(tail, Some(handler));
            }
            return self.lower_handler_body_block(stmts, tail.as_deref(), handler);
        }
        if let Some(handler) = handler
            && let runtime::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } = &expr.kind
        {
            return self.lower_handler_body_if(cond, then_branch, else_branch, handler);
        }
        if let Some(handler) = handler
            && let runtime::ExprKind::Match { .. } = &expr.kind
        {
            return self.lower_handler_body_match(expr, handler);
        }
        self.lower_expr(expr)
    }

    fn lower_handler_body_block(
        &mut self,
        stmts: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
        handler: CpsHandlerId,
    ) -> CpsLowerResult<CpsValueId> {
        let value_cont = self.fresh_continuation();
        let value = self.fresh_value();
        let (expected_effects, condition_handler) = self.handler_body_effect_context(
            tail.unwrap_or_else(|| {
                stmts
                    .last()
                    .and_then(|stmt| match stmt {
                        runtime::Stmt::Let { value, .. }
                        | runtime::Stmt::Expr(value)
                        | runtime::Stmt::Module { body: value, .. } => Some(value),
                    })
                    .expect("non-empty handler block")
            }),
            handler,
        );
        self.lower_handled_block(
            stmts,
            tail,
            &expected_effects,
            condition_handler,
            Some(value_cont),
        )?;
        self.current = ContinuationBuilder::new(value_cont, vec![value]);
        Ok(value)
    }

    fn lower_handler_body_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
        handler: CpsHandlerId,
    ) -> CpsLowerResult<CpsValueId> {
        if !collect_expr_performed_effects(cond).is_empty()
            || self.expr_may_perform_when_evaluated(cond)
        {
            return self.lower_handler_body_effect_condition_if(
                cond,
                then_branch,
                else_branch,
                handler,
            );
        }

        let cond_value = if let Some(reentry) = self.handler_reentry_apply(cond, handler)? {
            self.current.stmts.push(CpsStmt::ResumeWithHandler {
                dest: reentry.dest,
                resumption: reentry.resumption,
                arg: reentry.arg,
                handler,
                envs: reentry.envs,
            });
            reentry.dest
        } else {
            self.lower_expr(cond)?
        };

        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let then_cont = self.fresh_continuation();
        let else_cont = self.fresh_continuation();
        let merge_cont = self.fresh_continuation();
        let result = self.fresh_value();

        self.terminate(CpsTerminator::Branch {
            cond: cond_value,
            then_cont,
            else_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(then_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let then_value = self.lower_handler_body_expr(then_branch, Some(handler))?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![then_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(else_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let else_value = self.lower_handler_body_expr(else_branch, Some(handler))?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![else_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(result)
    }

    fn lower_handler_body_effect_condition_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
        handler: CpsHandlerId,
    ) -> CpsLowerResult<CpsValueId> {
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let cond_cont = self.fresh_continuation();
        let then_cont = self.fresh_continuation();
        let else_cont = self.fresh_continuation();
        let merge_cont = self.fresh_continuation();
        let result = self.fresh_value();
        let cond_value = self.fresh_value();
        let (expected_effects, condition_handler) = self.handler_body_effect_context(cond, handler);

        self.lower_handled_body(cond, &expected_effects, condition_handler, Some(cond_cont))?;

        self.current = ContinuationBuilder::new(cond_cont, vec![cond_value]);
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        self.terminate(CpsTerminator::Branch {
            cond: cond_value,
            then_cont,
            else_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(then_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let then_value = self.lower_handler_body_expr(then_branch, Some(handler))?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![then_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(else_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let else_value = self.lower_handler_body_expr(else_branch, Some(handler))?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![else_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(result)
    }

    fn lower_handler_body_match(
        &mut self,
        expr: &runtime::Expr,
        handler: CpsHandlerId,
    ) -> CpsLowerResult<CpsValueId> {
        let runtime::ExprKind::Match {
            scrutinee, arms, ..
        } = &expr.kind
        else {
            return Err(CpsLowerError::UnsupportedExpr { kind: "match" });
        };
        let scrutinee = if !collect_expr_performed_effects(scrutinee).is_empty()
            || self.expr_may_perform_when_evaluated(scrutinee)
        {
            let scrutinee_cont = self.fresh_continuation();
            let scrutinee_value = self.fresh_value();
            let (expected_effects, condition_handler) =
                self.handler_body_effect_context(scrutinee, handler);
            self.lower_handled_body(
                scrutinee,
                &expected_effects,
                condition_handler,
                Some(scrutinee_cont),
            )?;
            self.current = ContinuationBuilder::new(scrutinee_cont, vec![scrutinee_value]);
            scrutinee_value
        } else if let Some(reentry) = self.handler_reentry_apply(scrutinee, handler)? {
            self.current.stmts.push(CpsStmt::ResumeWithHandler {
                dest: reentry.dest,
                resumption: reentry.resumption,
                arg: reentry.arg,
                handler,
                envs: reentry.envs,
            });
            reentry.dest
        } else {
            self.lower_expr(scrutinee)?
        };

        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let merge_cont = self.fresh_continuation();
        let result = self.fresh_value();
        let fallback_cont = self.fresh_continuation();
        let mut arm_conts = Vec::with_capacity(arms.len());
        let mut guard_conts = Vec::with_capacity(arms.len());
        let mut next_conts = Vec::with_capacity(arms.len());
        for _ in arms {
            arm_conts.push(self.fresh_continuation());
            guard_conts.push(None);
        }

        let mut current_test_cont = None;
        for (index, arm) in arms.iter().enumerate() {
            if let Some(test_cont) = current_test_cont {
                self.current = ContinuationBuilder::new(test_cont, Vec::new());
                self.locals = saved_locals.clone();
                self.local_exprs = saved_local_exprs.clone();
                self.resumptions = saved_resumptions.clone();
            }
            let next_cont = if index + 1 == arms.len() {
                fallback_cont
            } else {
                let next = self.fresh_continuation();
                current_test_cont = Some(next);
                next
            };
            next_conts.push(next_cont);
            let success_cont = if arm.guard.is_some() {
                let guard_cont = self.fresh_continuation();
                guard_conts[index] = Some(guard_cont);
                guard_cont
            } else {
                arm_conts[index]
            };
            if self.lower_pattern_test(scrutinee, &arm.pattern, success_cont, next_cont)? {
                self.finish_current();
            }
        }

        self.current = ContinuationBuilder::new(fallback_cont, Vec::new());
        let unit = self.fresh_value();
        self.current.stmts.push(CpsStmt::Literal {
            dest: unit,
            literal: CpsLiteral::Unit,
        });
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![unit],
        });
        self.finish_current();

        for (index, arm) in arms.iter().enumerate() {
            let Some(guard_cont) = guard_conts[index] else {
                continue;
            };
            let Some(guard) = &arm.guard else {
                continue;
            };
            self.current = ContinuationBuilder::new(guard_cont, Vec::new());
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.pattern, scrutinee)?;
            let guard_value = self.lower_expr(guard)?;
            self.terminate(CpsTerminator::Branch {
                cond: guard_value,
                then_cont: arm_conts[index],
                else_cont: next_conts[index],
            });
            self.finish_current();
        }

        for (arm, arm_cont) in arms.iter().zip(arm_conts) {
            self.current = ContinuationBuilder::new(arm_cont, Vec::new());
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.pattern, scrutinee)?;
            let value = self.lower_handler_body_expr(&arm.body, Some(handler))?;
            self.terminate(CpsTerminator::Continue {
                target: merge_cont,
                args: vec![value],
            });
            self.finish_current();
        }

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(result)
    }

    fn handler_body_effect_context(
        &self,
        expr: &runtime::Expr,
        handler: CpsHandlerId,
    ) -> (Vec<typed_ir::Path>, CpsHandlerId) {
        let performed_effects = collect_expr_performed_effects(expr);
        let (mut expected_effects, mut condition_handler) = self.current_effect_context();
        if expected_effects.is_empty() && !performed_effects.is_empty() {
            expected_effects = performed_effects;
            condition_handler = handler;
        }
        (expected_effects, condition_handler)
    }

    fn lower_handled_body(
        &mut self,
        body: &runtime::Expr,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        if let runtime::ExprKind::Var(path) = &body.kind
            && let Some(expr) = self.local_exprs.get(path).cloned()
        {
            let expr = inline_callable_expr(&expr);
            return self.lower_handled_body(&expr, expected_effects, handler, value_cont);
        }

        if let runtime::ExprKind::LocalPushId { id, body } = &body.kind {
            let dest = self.fresh_value();
            self.current
                .stmts
                .push(CpsStmt::FreshGuard { dest, var: *id });
            return self.lower_handled_body(body, expected_effects, handler, value_cont);
        }

        if let Some(expr) = handle_body_execution_inner(body) {
            return self.lower_handled_body(expr, expected_effects, handler, value_cont);
        }

        if let runtime::ExprKind::BindHere { expr } = &body.kind
            && matches!(expr.kind, runtime::ExprKind::Block { .. })
        {
            return self.lower_handled_body(expr, expected_effects, handler, value_cont);
        }

        if let Some(request) = effect_apply_body_request(body) {
            let (expected_effects, handler) =
                self.effect_context_for_request(&request, expected_effects, handler);
            let (effect, resumed_value) =
                self.begin_resume_after_perform(request, &expected_effects, handler)?;
            self.finish_resumed_handled_value(resumed_value, value_cont);
            return Ok(effect);
        }

        if let runtime::ExprKind::BindHere { expr } = &body.kind {
            let value = self.lower_bind_here(expr)?;
            self.finish_handled_value(value, value_cont);
            return Ok(default_expected_effect(expected_effects));
        }

        if let Some((resumption, arg)) = self.resume_apply(body) {
            let arg = self.lower_expr(arg)?;
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::ResumeWithHandler {
                dest,
                resumption,
                arg,
                handler,
                envs: Vec::new(),
            });
            for effect in expected_effects {
                if !self
                    .forced_handler_effects
                    .iter()
                    .any(|(seen_handler, seen_effect)| {
                        *seen_handler == handler && seen_effect == effect
                    })
                {
                    self.forced_handler_effects.push((handler, effect.clone()));
                }
            }
            self.finish_handled_value(dest, value_cont);
            return Ok(default_expected_effect(expected_effects));
        }

        if let Some(reentry) = self.handler_reentry_apply(body, handler)? {
            self.current.stmts.push(CpsStmt::ResumeWithHandler {
                dest: reentry.dest,
                resumption: reentry.resumption,
                arg: reentry.arg,
                handler,
                envs: reentry.envs,
            });
            for effect in expected_effects {
                if !self
                    .forced_handler_effects
                    .iter()
                    .any(|(seen_handler, seen_effect)| {
                        *seen_handler == handler && seen_effect == effect
                    })
                {
                    self.forced_handler_effects.push((handler, effect.clone()));
                }
            }
            self.finish_handled_value(reentry.dest, value_cont);
            return Ok(default_expected_effect(expected_effects));
        }

        if let Some((op, args)) = primitive_apply(body) {
            let expected = primitive_arity(op);
            if args.len() != expected {
                return Err(CpsLowerError::PrimitiveArityMismatch {
                    op,
                    expected,
                    actual: args.len(),
                });
            }
            let effect_arg = args
                .iter()
                .enumerate()
                .find_map(|(index, arg)| effect_apply_nested(arg).map(|effect| (index, effect)));
            let Some((effect_index, request)) = effect_arg else {
                let value = self.lower_expr(body)?;
                self.finish_handled_value(value, value_cont);
                return Ok(default_expected_effect(expected_effects));
            };
            let (expected_effects, handler) =
                self.effect_context_for_request(&request, expected_effects, handler);
            let (effect, resumed_value) =
                self.begin_resume_after_perform(request, &expected_effects, handler)?;
            let mut lowered_args = Vec::with_capacity(args.len());
            for (index, arg) in args.into_iter().enumerate() {
                if index == effect_index {
                    lowered_args.push(resumed_value);
                } else {
                    lowered_args.push(self.lower_expr(arg)?);
                }
            }
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::Primitive {
                dest,
                op,
                args: lowered_args,
            });
            self.finish_resumed_handled_value(dest, value_cont);
            return Ok(effect);
        }

        if let Some((target_path, info, args)) = direct_apply_path(body, self.functions)? {
            let effect_arg = args
                .iter()
                .enumerate()
                .find_map(|(index, arg)| effect_apply_nested(arg).map(|effect| (index, effect)));
            let Some((effect_index, request)) = effect_arg else {
                let call_may_perform = self.target_may_perform_when_called(target_path);
                if call_may_perform {
                    self.lower_handled_effectful_call_value(
                        info,
                        args,
                        &body.ty,
                        call_may_perform,
                        value_cont,
                    )?;
                } else {
                    let value = self.lower_expr(body)?;
                    self.finish_handled_value(value, value_cont);
                }
                return Ok(default_expected_effect(expected_effects));
            };
            let (expected_effects, handler) =
                self.effect_context_for_request(&request, expected_effects, handler);
            let (effect, resumed_value) =
                self.begin_resume_after_perform(request, &expected_effects, handler)?;
            let mut lowered_args = Vec::with_capacity(args.len());
            for (index, arg) in args.into_iter().enumerate() {
                if index == effect_index {
                    lowered_args.push(resumed_value);
                } else {
                    lowered_args.push(self.lower_expr(arg)?);
                }
            }
            let dest = self.fresh_value();
            let should_force_direct = direct_call_result_needs_force(body, info);
            self.current.stmts.push(CpsStmt::DirectCall {
                dest,
                target: info.name.clone(),
                args: lowered_args,
            });
            let dest = if should_force_direct {
                let forced = self.fresh_value();
                self.current.stmts.push(CpsStmt::ForceThunk {
                    dest: forced,
                    thunk: dest,
                });
                forced
            } else {
                dest
            };
            self.finish_resumed_handled_value(dest, value_cont);
            return Ok(effect);
        }

        if let runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } = &body.kind
        {
            return self.lower_handled_if(
                cond,
                then_branch,
                else_branch,
                expected_effects,
                handler,
                value_cont,
            );
        }

        if let Some((cond, then_branch, else_branch)) = bool_match(body) {
            return self.lower_handled_if(
                cond,
                then_branch,
                else_branch,
                expected_effects,
                handler,
                value_cont,
            );
        }

        if let runtime::ExprKind::Match { .. } = &body.kind {
            return self.lower_handled_match(body, expected_effects, handler, value_cont);
        }

        if let runtime::ExprKind::Block { stmts, tail } = &body.kind {
            return self.lower_handled_block(
                stmts,
                tail.as_deref(),
                expected_effects,
                handler,
                value_cont,
            );
        }

        if body_is_thunk_value(body) {
            let thunk = self.lower_expr(body)?;
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::ForceThunk { dest, thunk });
            for effect in expected_effects {
                if !self
                    .forced_handler_effects
                    .iter()
                    .any(|(seen_handler, seen_effect)| {
                        *seen_handler == handler && seen_effect == effect
                    })
                {
                    self.forced_handler_effects.push((handler, effect.clone()));
                }
            }
            self.finish_handled_value(dest, value_cont);
            return Ok(default_expected_effect(expected_effects));
        }

        let value = match self.lower_expr(body) {
            Ok(value) => value,
            Err(CpsLowerError::UnsupportedExpr { .. }) => {
                return Err(CpsLowerError::UnsupportedExpr {
                    kind: "handler body continuation",
                });
            }
            Err(error) => return Err(error),
        };
        self.finish_handled_value(value, value_cont);
        Ok(default_expected_effect(expected_effects))
    }

    fn finish_handled_value(&mut self, value: CpsValueId, value_cont: Option<CpsContinuationId>) {
        match value_cont {
            Some(value_cont) => self.terminate(CpsTerminator::Continue {
                target: value_cont,
                args: vec![value],
            }),
            None => self.terminate(CpsTerminator::Return(value)),
        }
        self.finish_current();
    }

    fn finish_resumed_handled_value(
        &mut self,
        value: CpsValueId,
        value_cont: Option<CpsContinuationId>,
    ) {
        if value_cont.is_some_and(|value_cont| self.handler_value_conts.contains(&value_cont)) {
            self.terminate(CpsTerminator::Return(value));
            self.finish_current();
            return;
        }
        self.finish_handled_value(value, value_cont);
    }

    fn lower_handled_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        if !collect_expr_performed_effects(cond).is_empty()
            || self.expr_may_perform_when_evaluated(cond)
        {
            return self.lower_handled_effect_condition_if(
                cond,
                then_branch,
                else_branch,
                expected_effects,
                handler,
                value_cont,
            );
        }

        let cond = self.lower_expr(cond)?;
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let then_cont = self.fresh_continuation();
        let else_cont = self.fresh_continuation();

        self.terminate(CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(then_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let then_effect =
            self.lower_handled_body(then_branch, expected_effects, handler, value_cont)?;

        self.current = ContinuationBuilder::new(else_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let else_effect =
            self.lower_handled_body(else_branch, expected_effects, handler, value_cont)?;
        if !handled_effects_compatible(expected_effects, &then_effect, &else_effect) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler effect mismatch",
            });
        }

        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(then_effect)
    }

    fn lower_handled_effect_condition_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let cond_cont = self.fresh_continuation();
        let then_cont = self.fresh_continuation();
        let else_cont = self.fresh_continuation();
        let cond_value = self.fresh_value();

        let cond_effect =
            self.lower_handled_body(cond, expected_effects, handler, Some(cond_cont))?;

        self.current = ContinuationBuilder::new(cond_cont, vec![cond_value]);
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        self.terminate(CpsTerminator::Branch {
            cond: cond_value,
            then_cont,
            else_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(then_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let then_effect =
            self.lower_handled_body(then_branch, expected_effects, handler, value_cont)?;

        self.current = ContinuationBuilder::new(else_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let else_effect =
            self.lower_handled_body(else_branch, expected_effects, handler, value_cont)?;
        if !handled_effects_compatible(expected_effects, &cond_effect, &then_effect)
            || !handled_effects_compatible(expected_effects, &cond_effect, &else_effect)
            || !handled_effects_compatible(expected_effects, &then_effect, &else_effect)
        {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler effect mismatch",
            });
        }

        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(cond_effect)
    }

    fn lower_handled_match(
        &mut self,
        expr: &runtime::Expr,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        let runtime::ExprKind::Match {
            scrutinee, arms, ..
        } = &expr.kind
        else {
            return Err(CpsLowerError::UnsupportedExpr { kind: "match" });
        };
        let scrutinee = self.lower_expr(scrutinee)?;
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let fallback_cont = self.fresh_continuation();
        let mut arm_conts = Vec::with_capacity(arms.len());
        let mut guard_conts = Vec::with_capacity(arms.len());
        let mut next_conts = Vec::with_capacity(arms.len());
        for _ in arms {
            arm_conts.push(self.fresh_continuation());
            guard_conts.push(None);
        }

        let mut current_test_cont = None;
        for (index, arm) in arms.iter().enumerate() {
            if let Some(test_cont) = current_test_cont {
                self.current = ContinuationBuilder::new(test_cont, Vec::new());
                self.locals = saved_locals.clone();
                self.local_exprs = saved_local_exprs.clone();
                self.resumptions = saved_resumptions.clone();
            }
            let next_cont = if index + 1 == arms.len() {
                fallback_cont
            } else {
                let next = self.fresh_continuation();
                current_test_cont = Some(next);
                next
            };
            next_conts.push(next_cont);
            let success_cont = if arm.guard.is_some() {
                let guard_cont = self.fresh_continuation();
                guard_conts[index] = Some(guard_cont);
                guard_cont
            } else {
                arm_conts[index]
            };
            if self.lower_pattern_test(scrutinee, &arm.pattern, success_cont, next_cont)? {
                self.finish_current();
            }
        }

        self.current = ContinuationBuilder::new(fallback_cont, Vec::new());
        let unit = self.fresh_value();
        self.current.stmts.push(CpsStmt::Literal {
            dest: unit,
            literal: CpsLiteral::Unit,
        });
        self.finish_handled_value(unit, value_cont);

        let mut joined_effect: Option<typed_ir::Path> = None;
        for (index, arm) in arms.iter().enumerate() {
            let Some(guard_cont) = guard_conts[index] else {
                continue;
            };
            let Some(guard) = &arm.guard else {
                continue;
            };
            self.current = ContinuationBuilder::new(guard_cont, Vec::new());
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.pattern, scrutinee)?;
            if !collect_expr_performed_effects(guard).is_empty() {
                let guard_value_cont = self.fresh_continuation();
                let guard_value = self.fresh_value();
                let guard_effect = self.lower_handled_body(
                    guard,
                    expected_effects,
                    handler,
                    Some(guard_value_cont),
                )?;
                join_handled_effect(&mut joined_effect, expected_effects, guard_effect)?;
                self.current = ContinuationBuilder::new(guard_value_cont, vec![guard_value]);
                self.locals = saved_locals.clone();
                self.local_exprs = saved_local_exprs.clone();
                self.resumptions = saved_resumptions.clone();
                self.terminate(CpsTerminator::Branch {
                    cond: guard_value,
                    then_cont: arm_conts[index],
                    else_cont: next_conts[index],
                });
                self.finish_current();
            } else {
                let guard_value = self.lower_expr(guard)?;
                self.terminate(CpsTerminator::Branch {
                    cond: guard_value,
                    then_cont: arm_conts[index],
                    else_cont: next_conts[index],
                });
                self.finish_current();
            }
        }

        for (arm, arm_cont) in arms.iter().zip(arm_conts) {
            self.current = ContinuationBuilder::new(arm_cont, Vec::new());
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.pattern, scrutinee)?;
            let effect =
                self.lower_handled_body(&arm.body, expected_effects, handler, value_cont)?;
            join_handled_effect(&mut joined_effect, expected_effects, effect)?;
        }

        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(joined_effect.unwrap_or_else(|| default_expected_effect(expected_effects)))
    }

    fn lower_handled_block(
        &mut self,
        stmts: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        for (index, stmt) in stmts.iter().enumerate() {
            match stmt {
                runtime::Stmt::Let { pattern, value } => {
                    if unused_pure_let(
                        pattern,
                        value,
                        &stmts[index + 1..],
                        tail,
                        self.functions,
                        self.bindings,
                    ) {
                        continue;
                    }
                    if let Some((name, param, body)) = recursive_lambda_let(pattern, value) {
                        let value = self.lower_recursive_lambda(name, param, body)?;
                        self.locals
                            .insert(typed_ir::Path::from_name(name.clone()), value);
                        continue;
                    }
                    if let Some(request) = effect_apply_nested(value) {
                        let (routed_effects, routed_handler) =
                            self.effect_context_for_request(&request, expected_effects, handler);
                        let (effect, resumed_value) = self.begin_resume_after_perform(
                            request,
                            &routed_effects,
                            routed_handler,
                        )?;
                        self.bind_pattern(pattern, resumed_value)?;
                        let rest_effect = self.lower_handled_block(
                            &stmts[index + 1..],
                            tail,
                            expected_effects,
                            handler,
                            None,
                        )?;
                        if !handled_effects_compatible(expected_effects, &rest_effect, &effect) {
                            return Err(CpsLowerError::UnsupportedExpr {
                                kind: "handler effect mismatch",
                            });
                        }
                        return Ok(effect);
                    }

                    // Effectful direct call inside a handler scope: split the
                    // post-call computation off into its own continuation so
                    // the callee's Perform (or nested EffectfulCall) can
                    // capture this function's "rest of the block" as a
                    // return frame in the resumption.
                    if let Some((target_path, info, args)) =
                        direct_apply_path(value, self.functions)?
                    {
                        let target = info.name.clone();
                        let call_may_perform = self.target_may_perform_when_called(target_path);
                        if call_may_perform
                            || (self.active_handler.is_some()
                                && matches!(info.ret, runtime::Type::Thunk { .. }))
                        {
                            return self.lower_handled_effectful_call_let(
                                pattern,
                                target,
                                info,
                                args,
                                &value.ty,
                                call_may_perform,
                                &stmts[index + 1..],
                                tail,
                                expected_effects,
                                handler,
                                value_cont,
                            );
                        }
                    }
                    // Closure application: split into EffectfulApply when the
                    // callee's type indicates a potential effect (write13).
                    // No active_handler gate: helpers like `call_callback` are
                    // separate functions without a local handler scope, yet
                    // their `f 0` callback must still capture the caller rest.
                    if let runtime::ExprKind::Apply { callee, arg, .. } = &value.kind
                        && callee_type_may_perform(&callee.ty)
                    {
                        return self.lower_handled_effectful_apply_let(
                            pattern,
                            callee,
                            arg,
                            &value.ty,
                            &stmts[index + 1..],
                            tail,
                            expected_effects,
                            handler,
                            value_cont,
                        );
                    }

                    let value = self.lower_expr(value)?;
                    self.bind_pattern(pattern, value)?;
                }
                runtime::Stmt::Expr(expr) => {
                    if let Some(request) = effect_apply_nested(expr) {
                        let (routed_effects, routed_handler) =
                            self.effect_context_for_request(&request, expected_effects, handler);
                        let (effect, resumed_value) = self.begin_resume_after_perform(
                            request,
                            &routed_effects,
                            routed_handler,
                        )?;
                        if stmts[index + 1..].is_empty() && tail.is_none() {
                            self.finish_handled_value(resumed_value, value_cont);
                            return Ok(effect);
                        }
                        let rest_effect = self.lower_handled_block(
                            &stmts[index + 1..],
                            tail,
                            expected_effects,
                            handler,
                            None,
                        )?;
                        if !handled_effects_compatible(expected_effects, &rest_effect, &effect) {
                            return Err(CpsLowerError::UnsupportedExpr {
                                kind: "handler effect mismatch",
                            });
                        }
                        return Ok(effect);
                    }

                    let is_direct_call = direct_apply(expr, self.functions)?.is_some();
                    let value = self.lower_expr(expr)?;
                    // A non-tail block expression that calls another function
                    // (or has a Thunk static type) may be returning a Thunk
                    // that wraps effectful work. The runtime FunctionInfo
                    // sometimes hides the Thunk return type behind monomorphized
                    // role-impl wrappers, so force unconditionally for direct
                    // calls; ForceThunk is a no-op on plain values.
                    if is_direct_call || matches!(expr.ty, runtime::Type::Thunk { .. }) {
                        let dest = self.fresh_value();
                        self.current
                            .stmts
                            .push(CpsStmt::ForceThunk { dest, thunk: value });
                    }
                }
                runtime::Stmt::Module { .. } => {
                    return Err(CpsLowerError::UnsupportedExpr {
                        kind: "module statement",
                    });
                }
            }
        }

        match tail {
            Some(tail) => self.lower_handled_body(tail, expected_effects, handler, value_cont),
            None => Err(CpsLowerError::UnsupportedExpr {
                kind: "handler body continuation",
            }),
        }
    }

    /// Lower a `let pattern = direct_call(...)` inside a handler scope as
    /// an `EffectfulCall` terminator. The current continuation terminates
    /// with the call; the post-call binding/rest is moved to a fresh
    /// continuation that receives the call's return value.
    fn lower_handled_effectful_call_value(
        &mut self,
        info: &FunctionInfo,
        args: Vec<&runtime::Expr>,
        call_ty: &runtime::Type,
        call_may_perform: bool,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<()> {
        let info_params = info.params.clone();
        let info_returns_thunk = matches!(info.ret, runtime::Type::Thunk { .. });
        let lowered_args = args
            .into_iter()
            .enumerate()
            .map(|(idx, arg)| -> CpsLowerResult<CpsValueId> {
                let expected = info_params
                    .get(idx)
                    .cloned()
                    .unwrap_or_else(runtime::Type::unknown);
                let lowered = if matches!(expected, runtime::Type::Thunk { .. }) {
                    self.lower_expr_as_thunk_value(arg)?
                } else {
                    self.lower_expr(arg)?
                };
                Ok(self.force_if_non_thunk_demand(lowered, &expected))
            })
            .collect::<CpsLowerResult<Vec<_>>>()?;
        let post_cont = self.fresh_continuation();
        let result_id = self.fresh_value();
        self.terminate(CpsTerminator::EffectfulCall {
            target: info.name.clone(),
            args: lowered_args,
            resume: post_cont,
        });
        self.finish_current();
        if info_returns_thunk || call_may_perform {
            self.mark_active_handlers_external_call();
        }

        self.current = ContinuationBuilder::new(post_cont, vec![result_id]);
        let value = if matches!(call_ty, runtime::Type::Thunk { .. }) && !call_may_perform {
            result_id
        } else {
            // A handler body executes the computation it handles. Direct
            // helpers such as lazy `or` return an effectful thunk from the
            // call itself, so the value path must force that thunk before the
            // handled value reaches a branch or value arm.
            let force_cont = self.fresh_continuation();
            let forced = self.fresh_value();
            self.terminate(CpsTerminator::EffectfulForce {
                thunk: result_id,
                resume: force_cont,
            });
            self.finish_current();
            self.current = ContinuationBuilder::new(force_cont, vec![forced]);
            forced
        };
        self.finish_handled_value(value, value_cont);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_handled_effectful_call_let(
        &mut self,
        pattern: &runtime::Pattern,
        target: String,
        info: &FunctionInfo,
        args: Vec<&runtime::Expr>,
        call_ty: &runtime::Type,
        call_may_perform: bool,
        rest: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        let info_params = info.params.clone();
        let info_returns_thunk = matches!(info.ret, runtime::Type::Thunk { .. });
        let lowered_args = args
            .into_iter()
            .enumerate()
            .map(|(idx, arg)| -> CpsLowerResult<CpsValueId> {
                let expected = info_params
                    .get(idx)
                    .cloned()
                    .unwrap_or_else(runtime::Type::unknown);
                let lowered = if matches!(expected, runtime::Type::Thunk { .. }) {
                    self.lower_expr_as_thunk_value(arg)?
                } else {
                    self.lower_expr(arg)?
                };
                // The runtime IR may surface an argument as a Thunk-wrapped
                // value even when the callee's formal param type is plain
                // (e.g. `f: int -> int -> [e] int` produces a Thunk-wrapped
                // closure at the call site). Force here so the callee
                // receives the plain value its params expect.
                Ok(self.force_if_non_thunk_demand(lowered, &expected))
            })
            .collect::<CpsLowerResult<Vec<_>>>()?;

        let post_cont = self.fresh_continuation();
        let result_id = self.fresh_value();

        self.terminate(CpsTerminator::EffectfulCall {
            target,
            args: lowered_args,
            resume: post_cont,
        });
        self.finish_current();
        if info_returns_thunk || call_may_perform {
            self.mark_active_handlers_external_call();
        }

        self.current = ContinuationBuilder::new(post_cont, vec![result_id]);
        // Inside the handler scope, the call result may be a Thunk wrapping
        // effectful work (helpers lower as MakeThunk + Return). Force it via
        // an EffectfulForce terminator so the Perform inside the thunk's
        // body sees the post-force cont as a return frame, not via a
        // synchronous stmt ForceThunk that would lose the caller context.
        let bound = if matches!(call_ty, runtime::Type::Thunk { .. }) {
            result_id
        } else {
            let force_cont = self.fresh_continuation();
            let forced = self.fresh_value();
            self.terminate(CpsTerminator::EffectfulForce {
                thunk: result_id,
                resume: force_cont,
            });
            self.finish_current();
            self.current = ContinuationBuilder::new(force_cont, vec![forced]);
            forced
        };
        self.bind_pattern(pattern, bound)?;

        let rest_effect =
            self.lower_handled_block(rest, tail, expected_effects, handler, value_cont)?;
        Ok(rest_effect)
    }

    /// Lower a `let pattern = closure_apply(...)` inside a handler scope as
    /// an `EffectfulApply` terminator. Conservatively treats all closure
    /// applications in handler scope as potentially effectful (write13).
    #[allow(clippy::too_many_arguments)]
    fn lower_handled_effectful_apply_let(
        &mut self,
        pattern: &runtime::Pattern,
        callee: &runtime::Expr,
        arg: &runtime::Expr,
        apply_ty: &runtime::Type,
        rest: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        let closure = self.lower_expr(callee)?;
        let arg_value = self.lower_expr_as_call_arg(&callee.ty, arg)?;

        let post_cont = self.fresh_continuation();
        let result_id = self.fresh_value();

        self.terminate(CpsTerminator::EffectfulApply {
            closure,
            arg: arg_value,
            resume: post_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(post_cont, vec![result_id]);
        let bound = if matches!(apply_ty, runtime::Type::Thunk { .. }) {
            result_id
        } else {
            let force_cont = self.fresh_continuation();
            let forced = self.fresh_value();
            self.terminate(CpsTerminator::EffectfulForce {
                thunk: result_id,
                resume: force_cont,
            });
            self.finish_current();
            self.current = ContinuationBuilder::new(force_cont, vec![forced]);
            forced
        };
        self.bind_pattern(pattern, bound)?;

        self.lower_handled_block(rest, tail, expected_effects, handler, value_cont)
    }

    /// Expr-statement variant of `lower_handled_effectful_call_let`. The
    /// post-call continuation discards the result but still routes a Perform
    /// inside the callee through the saved return frame chain.
    ///
    /// Currently unused — the Stmt::Expr path triggers test regressions in
    /// the Cranelift backend (todo!() for EffectfulCall). Kept for write14's
    /// follow-up when cps_repr / Cranelift gain support for these terminators.
    #[allow(dead_code, clippy::too_many_arguments)]
    fn lower_handled_effectful_call_expr(
        &mut self,
        target: String,
        info: &FunctionInfo,
        args: Vec<&runtime::Expr>,
        call_ty: &runtime::Type,
        rest: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        let info_params = info.params.clone();
        let info_returns_thunk = matches!(info.ret, runtime::Type::Thunk { .. });
        let lowered_args = args
            .into_iter()
            .enumerate()
            .map(|(idx, arg)| {
                if matches!(info_params.get(idx), Some(runtime::Type::Thunk { .. })) {
                    self.lower_expr_as_thunk_value(arg)
                } else {
                    self.lower_expr(arg)
                }
            })
            .collect::<CpsLowerResult<Vec<_>>>()?;

        let post_cont = self.fresh_continuation();
        let ignored = self.fresh_value();

        self.terminate(CpsTerminator::EffectfulCall {
            target,
            args: lowered_args,
            resume: post_cont,
        });
        self.finish_current();
        if info_returns_thunk {
            self.mark_active_handlers_external_call();
        }

        self.current = ContinuationBuilder::new(post_cont, vec![ignored]);
        // Even though we discard the value, a Thunk return from an effectful
        // helper still needs to be unwrapped here so its body's Perform sees
        // a return frame (not lost via a sync ForceThunk).
        if !matches!(call_ty, runtime::Type::Thunk { .. }) {
            let force_cont = self.fresh_continuation();
            let forced = self.fresh_value();
            self.terminate(CpsTerminator::EffectfulForce {
                thunk: ignored,
                resume: force_cont,
            });
            self.finish_current();
            self.current = ContinuationBuilder::new(force_cont, vec![forced]);
        }

        self.lower_handled_block(rest, tail, expected_effects, handler, value_cont)
    }

    #[allow(dead_code, clippy::too_many_arguments)]
    fn lower_handled_effectful_apply_expr(
        &mut self,
        callee: &runtime::Expr,
        arg: &runtime::Expr,
        apply_ty: &runtime::Type,
        rest: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<typed_ir::Path> {
        let closure = self.lower_expr(callee)?;
        let arg_value = self.lower_expr_as_call_arg(&callee.ty, arg)?;

        let post_cont = self.fresh_continuation();
        let ignored = self.fresh_value();

        self.terminate(CpsTerminator::EffectfulApply {
            closure,
            arg: arg_value,
            resume: post_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(post_cont, vec![ignored]);
        if !matches!(apply_ty, runtime::Type::Thunk { .. }) {
            let force_cont = self.fresh_continuation();
            let forced = self.fresh_value();
            self.terminate(CpsTerminator::EffectfulForce {
                thunk: ignored,
                resume: force_cont,
            });
            self.finish_current();
            self.current = ContinuationBuilder::new(force_cont, vec![forced]);
        }

        self.lower_handled_block(rest, tail, expected_effects, handler, value_cont)
    }

    fn begin_resume_after_perform(
        &mut self,
        request: CpsEffectApply<'_>,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
    ) -> CpsLowerResult<(typed_ir::Path, CpsValueId)> {
        let effect = request.effect.clone();
        let payload = request.payload;
        let blocked = request.blocked;
        if let Some(payload) = handle_body_execution_inner(payload) {
            return self.begin_resume_after_perform(
                CpsEffectApply {
                    effect,
                    payload,
                    blocked,
                },
                expected_effects,
                handler,
            );
        }

        if let Some((op, args)) = primitive_apply(payload) {
            let expected = primitive_arity(op);
            if args.len() != expected {
                return Err(CpsLowerError::PrimitiveArityMismatch {
                    op,
                    expected,
                    actual: args.len(),
                });
            }
            if let Some((effect_index, inner_request)) = args
                .iter()
                .enumerate()
                .find_map(|(index, arg)| effect_apply_nested(arg).map(|effect| (index, effect)))
            {
                let (_, resumed_value) =
                    self.begin_resume_after_perform(inner_request, expected_effects, handler)?;
                let mut lowered_args = Vec::with_capacity(args.len());
                for (index, arg) in args.into_iter().enumerate() {
                    if index == effect_index {
                        lowered_args.push(resumed_value);
                    } else {
                        lowered_args.push(self.lower_expr(arg)?);
                    }
                }
                let payload = self.fresh_value();
                self.current.stmts.push(CpsStmt::Primitive {
                    dest: payload,
                    op,
                    args: lowered_args,
                });
                return self.begin_resume_after_perform_value(
                    effect,
                    payload,
                    blocked,
                    expected_effects,
                    handler,
                );
            }
        }

        if let Some((target, info, args)) = direct_apply(payload, self.functions)? {
            if let Some((effect_index, inner_request)) = args
                .iter()
                .enumerate()
                .find_map(|(index, arg)| effect_apply_nested(arg).map(|effect| (index, effect)))
            {
                let (_, resumed_value) =
                    self.begin_resume_after_perform(inner_request, expected_effects, handler)?;
                let mut lowered_args = Vec::with_capacity(args.len());
                for (index, arg) in args.into_iter().enumerate() {
                    if index == effect_index {
                        lowered_args.push(resumed_value);
                    } else {
                        lowered_args.push(self.lower_expr(arg)?);
                    }
                }
                let payload_expr = payload;
                let payload = self.fresh_value();
                self.current.stmts.push(CpsStmt::DirectCall {
                    dest: payload,
                    target,
                    args: lowered_args,
                });
                let payload = if direct_call_result_needs_force(payload_expr, info) {
                    let forced = self.fresh_value();
                    self.current.stmts.push(CpsStmt::ForceThunk {
                        dest: forced,
                        thunk: payload,
                    });
                    forced
                } else {
                    payload
                };
                return self.begin_resume_after_perform_value(
                    effect,
                    payload,
                    blocked,
                    expected_effects,
                    handler,
                );
            }
        }

        let payload = self.lower_expr(payload)?;
        self.begin_resume_after_perform_value(effect, payload, blocked, expected_effects, handler)
    }

    fn begin_resume_after_perform_value(
        &mut self,
        effect: typed_ir::Path,
        payload: CpsValueId,
        blocked: Option<runtime::EffectIdRef>,
        _expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
    ) -> CpsLowerResult<(typed_ir::Path, CpsValueId)> {
        let blocked = blocked
            .map(|blocked| self.lower_effect_id_ref(blocked))
            .transpose()?;
        let resume_cont = self.fresh_continuation();
        self.terminate(CpsTerminator::Perform {
            effect: effect.clone(),
            payload,
            resume: resume_cont,
            handler,
            blocked,
        });
        self.finish_current();

        let resumed_value = self.fresh_value();
        self.current = ContinuationBuilder::new(resume_cont, vec![resumed_value]);
        Ok((effect, resumed_value))
    }

    fn bind_pattern(
        &mut self,
        pattern: &runtime::Pattern,
        value: CpsValueId,
    ) -> CpsLowerResult<()> {
        match pattern {
            runtime::Pattern::Wildcard { .. } => Ok(()),
            runtime::Pattern::Bind { name, .. } => {
                let path = typed_ir::Path::from_name(name.clone());
                self.local_exprs.remove(&path);
                self.locals.insert(path, value);
                Ok(())
            }
            runtime::Pattern::Lit { .. } => Ok(()),
            runtime::Pattern::Tuple { items, .. } => {
                for (index, item) in items.iter().enumerate() {
                    let item_value = self.fresh_value();
                    self.current.stmts.push(CpsStmt::TupleGet {
                        dest: item_value,
                        tuple: value,
                        index,
                    });
                    self.bind_pattern(item, item_value)?;
                }
                Ok(())
            }
            runtime::Pattern::List { .. } => {
                Err(CpsLowerError::UnsupportedPattern { kind: "list" })
            }
            runtime::Pattern::Record { .. } => {
                Err(CpsLowerError::UnsupportedPattern { kind: "record" })
            }
            runtime::Pattern::Variant {
                value: Some(payload),
                ..
            } => {
                let payload_value = self.fresh_value();
                self.current.stmts.push(CpsStmt::VariantPayload {
                    dest: payload_value,
                    variant: value,
                });
                self.bind_pattern(payload, payload_value)
            }
            runtime::Pattern::Variant { value: None, .. } => Ok(()),
            runtime::Pattern::Or { .. } => Err(CpsLowerError::UnsupportedPattern { kind: "or" }),
            runtime::Pattern::As { pattern, name, .. } => {
                self.bind_pattern(pattern, value)?;
                self.locals
                    .insert(typed_ir::Path::from_name(name.clone()), value);
                Ok(())
            }
        }
    }

    fn fresh_value(&mut self) -> CpsValueId {
        let value = CpsValueId(self.next_value);
        self.next_value += 1;
        value
    }

    fn fresh_continuation(&mut self) -> CpsContinuationId {
        let continuation = CpsContinuationId(self.next_continuation);
        self.next_continuation += 1;
        continuation
    }

    fn fresh_handler(&mut self) -> CpsHandlerId {
        let handler = CpsHandlerId(self.next_handler);
        self.next_handler += 1;
        handler
    }

    fn current_effect_context(&self) -> (Vec<typed_ir::Path>, CpsHandlerId) {
        self.active_handler
            .as_ref()
            .map(|context| (context.expected_effects.clone(), context.handler))
            .unwrap_or_else(|| (Vec::new(), dynamic_handler_id()))
    }

    fn effect_context_for_request(
        &self,
        request: &CpsEffectApply<'_>,
        expected_effects: &[typed_ir::Path],
        handler: CpsHandlerId,
    ) -> (Vec<typed_ir::Path>, CpsHandlerId) {
        if let Some(context) = self.active_context_for_effect(&request.effect) {
            return (context.expected_effects.clone(), context.handler);
        }
        if matches_any_effect(expected_effects, &request.effect) {
            return (expected_effects.to_vec(), handler);
        }
        (Vec::new(), dynamic_handler_id())
    }

    fn active_context_for_effect(&self, effect: &typed_ir::Path) -> Option<&ActiveHandlerContext> {
        let mut current = self.active_handler.as_ref();
        while let Some(context) = current {
            if matches_any_effect(&context.expected_effects, effect) {
                return Some(context);
            }
            current = context.parent.as_deref();
        }
        None
    }

    fn performed_effects_for_handler(&self, handler: CpsHandlerId) -> Vec<typed_ir::Path> {
        let mut effects = Vec::new();
        for continuation in &self.continuations {
            if let CpsTerminator::Perform {
                effect,
                handler: used,
                ..
            } = &continuation.terminator
                && *used == handler
                && !effects.iter().any(|seen| seen == effect)
            {
                effects.push(effect.clone());
            }
        }
        for (used, effect) in &self.forced_handler_effects {
            if *used == handler && !effects.iter().any(|seen| seen == effect) {
                effects.push(effect.clone());
            }
        }
        effects
    }

    fn target_may_perform_when_called(&self, target: &typed_ir::Path) -> bool {
        let mut visiting = HashSet::new();
        let mut memo = HashMap::new();
        binding_may_perform_when_called(
            target,
            self.functions,
            self.bindings,
            &mut visiting,
            &mut memo,
        )
    }

    fn direct_call_has_handler_reentry_arg(
        &self,
        target: &typed_ir::Path,
        args: &[&runtime::Expr],
    ) -> bool {
        if self.active_handler.is_none() {
            return false;
        }
        let Some(binding) = self.bindings.get(target) else {
            return false;
        };
        if handler_wrapper_info(binding).is_none() {
            return false;
        }
        args.iter().any(|arg| self.expr_contains_resume_apply(arg))
    }

    fn expr_may_perform_when_evaluated(&self, expr: &runtime::Expr) -> bool {
        let mut visiting = HashSet::new();
        let mut memo = HashMap::new();
        expr_may_perform_when_evaluated(
            expr,
            self.functions,
            self.bindings,
            &mut visiting,
            &mut memo,
        )
    }

    fn lower_inline_direct_apply(
        &mut self,
        expr: &runtime::Expr,
    ) -> CpsLowerResult<Option<CpsValueId>> {
        let Some((target, info, args)) = direct_apply_path(expr, self.functions)? else {
            return Ok(None);
        };
        if path_name(target) == self.name || !self.inline_stack.insert(target.clone()) {
            return Ok(None);
        }
        let Some(binding) = self.bindings.get(target) else {
            self.inline_stack.remove(target);
            return Ok(None);
        };
        if binding_has_self_direct_call(target, &binding.body, self.functions) {
            self.inline_stack.remove(target);
            return Ok(None);
        }
        let (params, body) = collect_callable_params(&binding.body);
        if params.len() != args.len() {
            self.inline_stack.remove(target);
            return Ok(None);
        }
        let info_params = info.params.clone();

        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        for (idx, (param, arg)) in params.into_iter().zip(args).enumerate() {
            let path = typed_ir::Path::from_name(param);
            let param_is_thunk = matches!(info_params.get(idx), Some(runtime::Type::Thunk { .. }));
            if is_inline_argument(arg) || matches!(arg.ty, runtime::Type::Thunk { .. }) {
                self.local_exprs.insert(path, arg.clone());
            } else if param_is_thunk {
                let value = self.lower_expr_as_thunk_value(arg)?;
                self.locals.insert(path, value);
            } else {
                let value = self.lower_expr(arg)?;
                self.locals.insert(path, value);
            }
        }
        let value = self.lower_expr(&body);
        self.inline_stack.remove(target);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        value.map(Some)
    }

    fn lower_local_expr_apply(
        &mut self,
        expr: &runtime::Expr,
    ) -> CpsLowerResult<Option<CpsValueId>> {
        let runtime::ExprKind::Apply { callee, arg, .. } = &expr.kind else {
            return Ok(None);
        };
        let callee = transparent_effect_expr(callee);
        let runtime::ExprKind::Var(path) = &callee.kind else {
            return Ok(None);
        };
        let Some(callee) = self.local_exprs.get(path).cloned() else {
            return Ok(None);
        };
        if callable_expr_is_thunk_wrapped(&callee) {
            let closure = self.lower_expr(&callee)?;
            let forced = self.fresh_value();
            self.current.stmts.push(CpsStmt::ForceThunk {
                dest: forced,
                thunk: closure,
            });
            let arg = self.lower_expr_as_call_arg(callable_type_after_force(&callee.ty), arg)?;
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::ApplyClosure {
                dest,
                closure: forced,
                arg,
            });
            return Ok(Some(self.force_if_non_thunk_demand(dest, &expr.ty)));
        }
        let callee = inline_callable_expr(&callee);
        let (params, body) = collect_lambda_params(&callee);
        if params.len() != 1 {
            return Ok(None);
        }
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let path = typed_ir::Path::from_name(params[0].clone());
        if is_inline_argument(arg) || matches!(arg.ty, runtime::Type::Thunk { .. }) {
            self.local_exprs.insert(path, arg.as_ref().clone());
        } else {
            let value = self.lower_expr(arg)?;
            self.locals.insert(path, value);
        }
        let value = self.lower_expr(body);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        value.map(Some)
    }

    fn handler_reentry_apply(
        &mut self,
        expr: &runtime::Expr,
        handler: CpsHandlerId,
    ) -> CpsLowerResult<Option<HandlerReentry>> {
        let Some((target, _, args)) = direct_apply_path(expr, self.functions)? else {
            return Ok(None);
        };
        let Some(binding) = self.bindings.get(target) else {
            return Ok(None);
        };
        let Some(wrapper) = handler_wrapper_info(binding) else {
            return Ok(None);
        };
        if wrapper.params.len() != args.len() || wrapper.params.is_empty() {
            return Ok(None);
        }

        let mut resume_candidate = None;
        for (index, arg) in args.iter().enumerate() {
            let Some((resumption, resume_arg)) = self.resume_thunk_argument(arg) else {
                continue;
            };
            if resume_candidate.is_some() {
                return Ok(None);
            }
            resume_candidate = Some((index, resumption, resume_arg));
        }
        let Some((resume_index, resumption, resume_arg)) = resume_candidate else {
            return Ok(None);
        };

        let state_params = wrapper
            .params
            .iter()
            .enumerate()
            .filter_map(|(index, param)| (index != resume_index).then_some(param))
            .collect::<Vec<_>>();
        let state_args = args
            .iter()
            .enumerate()
            .filter_map(|(index, arg)| (index != resume_index).then_some(*arg))
            .map(|arg| self.lower_expr(arg))
            .collect::<CpsLowerResult<Vec<_>>>()?;
        let arg = self.lower_expr(resume_arg)?;
        let envs = self.handler_reentry_envs(handler, &wrapper.arms, &state_params, &state_args);
        let dest = self.fresh_value();
        Ok(Some(HandlerReentry {
            dest,
            resumption,
            arg,
            envs,
        }))
    }

    fn resume_thunk_argument<'expr>(
        &self,
        expr: &'expr runtime::Expr,
    ) -> Option<(CpsValueId, &'expr runtime::Expr)> {
        let expr = transparent_effect_expr(expr);
        let runtime::ExprKind::Thunk { expr, .. } = &expr.kind else {
            return None;
        };
        let expr = handle_body_execution_inner(expr).unwrap_or(expr);
        self.resume_apply(expr)
    }

    fn handler_reentry_envs(
        &self,
        handler: CpsHandlerId,
        arms: &[runtime::HandleArm],
        state_params: &[&typed_ir::Name],
        state_args: &[CpsValueId],
    ) -> Vec<CpsHandlerEnv> {
        let Some(handler) = self
            .handlers
            .iter()
            .find(|candidate| candidate.id == handler)
        else {
            return Vec::new();
        };
        let mut envs = Vec::new();
        for arm in arms {
            let values = state_params
                .iter()
                .zip(state_args.iter().copied())
                .filter_map(|(param, value)| {
                    expr_uses_path(&arm.body, &typed_ir::Path::from_name((*param).clone()))
                        .then_some(value)
                })
                .collect::<Vec<_>>();
            if values.is_empty() {
                continue;
            }
            let Some(entry) = handler
                .arms
                .iter()
                .find(|candidate| effect_matches(&candidate.effect, &arm.effect))
                .map(|arm| arm.entry)
            else {
                continue;
            };
            envs.push(CpsHandlerEnv { entry, values });
        }
        envs
    }

    fn resume_apply<'expr>(
        &self,
        expr: &'expr runtime::Expr,
    ) -> Option<(CpsValueId, &'expr runtime::Expr)> {
        let runtime::ExprKind::Apply { callee, arg, .. } = &expr.kind else {
            return None;
        };
        let runtime::ExprKind::Var(path) = &callee.kind else {
            return None;
        };
        if !self.resumptions.contains(path) {
            return None;
        }
        let resumption = *self.locals.get(path)?;
        Some((resumption, arg.as_ref()))
    }

    fn apply_chain_contains_resume_argument(&self, expr: &runtime::Expr) -> bool {
        let mut current = transparent_effect_expr(expr);
        while let runtime::ExprKind::Apply { callee, arg, .. } = &current.kind {
            if self.expr_contains_resume_apply(arg) {
                return true;
            }
            current = transparent_effect_expr(callee);
        }
        false
    }

    fn expr_contains_resume_apply(&self, expr: &runtime::Expr) -> bool {
        if self.resume_apply(expr).is_some() {
            return true;
        }
        match &expr.kind {
            runtime::ExprKind::Lambda { body, .. }
            | runtime::ExprKind::Thunk { expr: body, .. }
            | runtime::ExprKind::LocalPushId { body, .. }
            | runtime::ExprKind::BindHere { expr: body }
            | runtime::ExprKind::AddId { thunk: body, .. }
            | runtime::ExprKind::Coerce { expr: body, .. }
            | runtime::ExprKind::Pack { expr: body, .. } => self.expr_contains_resume_apply(body),
            runtime::ExprKind::Apply { callee, arg, .. } => {
                self.expr_contains_resume_apply(callee) || self.expr_contains_resume_apply(arg)
            }
            runtime::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.expr_contains_resume_apply(cond)
                    || self.expr_contains_resume_apply(then_branch)
                    || self.expr_contains_resume_apply(else_branch)
            }
            runtime::ExprKind::Tuple(items) => items
                .iter()
                .any(|item| self.expr_contains_resume_apply(item)),
            runtime::ExprKind::Record { fields, spread } => {
                fields
                    .iter()
                    .any(|field| self.expr_contains_resume_apply(&field.value))
                    || spread.as_ref().is_some_and(|spread| match spread {
                        runtime::RecordSpreadExpr::Head(expr)
                        | runtime::RecordSpreadExpr::Tail(expr) => {
                            self.expr_contains_resume_apply(expr)
                        }
                    })
            }
            runtime::ExprKind::Variant {
                value: Some(value), ..
            }
            | runtime::ExprKind::Select { base: value, .. } => {
                self.expr_contains_resume_apply(value)
            }
            runtime::ExprKind::Match {
                scrutinee, arms, ..
            } => {
                self.expr_contains_resume_apply(scrutinee)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| self.expr_contains_resume_apply(guard))
                            || self.expr_contains_resume_apply(&arm.body)
                    })
            }
            runtime::ExprKind::Block { stmts, tail } => {
                stmts.iter().any(|stmt| match stmt {
                    runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                        self.expr_contains_resume_apply(value)
                    }
                    runtime::Stmt::Module { body, .. } => self.expr_contains_resume_apply(body),
                }) || tail
                    .as_ref()
                    .is_some_and(|tail| self.expr_contains_resume_apply(tail))
            }
            runtime::ExprKind::Handle { body, arms, .. } => {
                self.expr_contains_resume_apply(body)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| self.expr_contains_resume_apply(guard))
                            || self.expr_contains_resume_apply(&arm.body)
                    })
            }
            runtime::ExprKind::Var(_)
            | runtime::ExprKind::EffectOp(_)
            | runtime::ExprKind::PrimitiveOp(_)
            | runtime::ExprKind::Lit(_)
            | runtime::ExprKind::Variant { value: None, .. }
            | runtime::ExprKind::PeekId
            | runtime::ExprKind::FindId { .. } => false,
        }
    }

    fn terminate(&mut self, terminator: CpsTerminator) {
        self.current.terminator = Some(terminator);
    }

    fn finish_current(&mut self) {
        let terminator = self
            .current
            .terminator
            .take()
            .expect("CPS lowerer finished an unterminated continuation");
        self.continuations.push(CpsContinuation {
            id: self.current.id,
            params: std::mem::take(&mut self.current.params),
            captures: std::mem::take(&mut self.current.captures),
            shot_kind: CpsShotKind::MultiShot,
            stmts: std::mem::take(&mut self.current.stmts),
            terminator,
        });
    }
}

fn effect_matches(expected: &typed_ir::Path, actual: &typed_ir::Path) -> bool {
    actual == expected
        || (!expected.segments.is_empty()
            && actual.segments.len() == expected.segments.len() + 1
            && actual.segments.starts_with(&expected.segments))
        || (expected.segments.len() == 1 && actual.segments.last() == expected.segments.first())
}

fn is_inline_argument(expr: &runtime::Expr) -> bool {
    match &expr.kind {
        runtime::ExprKind::Lambda { .. }
        | runtime::ExprKind::Thunk { .. }
        | runtime::ExprKind::LocalPushId { .. } => true,
        runtime::ExprKind::BindHere { expr }
        | runtime::ExprKind::AddId { thunk: expr, .. }
        | runtime::ExprKind::Coerce { expr, .. }
        | runtime::ExprKind::Pack { expr, .. } => is_inline_argument(expr),
        _ => false,
    }
}

fn inline_callable_expr(expr: &runtime::Expr) -> runtime::Expr {
    match &expr.kind {
        runtime::ExprKind::Thunk { expr, .. }
        | runtime::ExprKind::LocalPushId { body: expr, .. }
        | runtime::ExprKind::BindHere { expr }
        | runtime::ExprKind::AddId { thunk: expr, .. }
        | runtime::ExprKind::Coerce { expr, .. }
        | runtime::ExprKind::Pack { expr, .. } => inline_callable_expr(expr),
        _ => expr.clone(),
    }
}

fn callable_expr_is_thunk_wrapped(expr: &runtime::Expr) -> bool {
    match &expr.kind {
        runtime::ExprKind::Thunk { .. } => true,
        runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => callable_expr_is_thunk_wrapped(body),
        _ => false,
    }
}

struct HandlerWrapperInfo {
    params: Vec<typed_ir::Name>,
    arms: Vec<runtime::HandleArm>,
}

struct HandlerReentry {
    dest: CpsValueId,
    resumption: CpsValueId,
    arg: CpsValueId,
    envs: Vec<CpsHandlerEnv>,
}

fn handler_wrapper_info(binding: &runtime::Binding) -> Option<HandlerWrapperInfo> {
    let (params, body) = collect_lambda_params(&binding.body);
    let handled_param = params.last()?;
    let (handled_body, arms) = handler_wrapper_handle(body)?;
    let handled_body = handle_body_execution_inner(handled_body).unwrap_or(handled_body);
    let handled_body = transparent_expr(handled_body);
    let runtime::ExprKind::Var(body_var) = &handled_body.kind else {
        return None;
    };
    if body_var != &typed_ir::Path::from_name(handled_param.clone()) {
        return None;
    }
    Some(HandlerWrapperInfo {
        params,
        arms: arms.to_vec(),
    })
}

fn handler_wrapper_handle(expr: &runtime::Expr) -> Option<(&runtime::Expr, &[runtime::HandleArm])> {
    let mut current = expr;
    loop {
        match &current.kind {
            runtime::ExprKind::LocalPushId { body, .. } => current = body,
            runtime::ExprKind::BindHere { expr }
            | runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. } => current = expr,
            runtime::ExprKind::AddId { thunk, .. }
            | runtime::ExprKind::Thunk { expr: thunk, .. } => {
                current = thunk;
            }
            runtime::ExprKind::Handle { body, arms, .. } => return Some((body, arms)),
            _ => return None,
        }
    }
}

fn binding_may_perform_when_called(
    target: &typed_ir::Path,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
    visiting: &mut HashSet<typed_ir::Path>,
    memo: &mut HashMap<typed_ir::Path, bool>,
) -> bool {
    if let Some(result) = memo.get(target) {
        return *result;
    }
    if !visiting.insert(target.clone()) {
        return false;
    }
    let result = bindings.get(target).is_some_and(|binding| {
        if matches!(binding.body.kind, runtime::ExprKind::PrimitiveOp(_)) {
            return false;
        }
        let (_, body) = collect_callable_params(&binding.body);
        expr_may_perform_when_evaluated(&body, functions, bindings, visiting, memo)
    });
    visiting.remove(target);
    memo.insert(target.clone(), result);
    result
}

fn expr_may_perform_when_evaluated(
    expr: &runtime::Expr,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
    bindings: &HashMap<typed_ir::Path, &runtime::Binding>,
    visiting: &mut HashSet<typed_ir::Path>,
    memo: &mut HashMap<typed_ir::Path, bool>,
) -> bool {
    if let Some(inner) = handle_body_execution_inner(expr) {
        return expr_may_perform_when_evaluated(inner, functions, bindings, visiting, memo);
    }
    if effect_apply_body_request(expr).is_some() {
        return true;
    }
    if let Ok(Some((target, _, args))) = direct_apply_path(expr, functions) {
        return args
            .iter()
            .any(|arg| expr_may_perform_when_evaluated(arg, functions, bindings, visiting, memo))
            || binding_may_perform_when_called(target, functions, bindings, visiting, memo);
    }
    if let Some((_, args)) = primitive_apply(expr) {
        return args
            .iter()
            .any(|arg| expr_may_perform_when_evaluated(arg, functions, bindings, visiting, memo));
    }

    match &expr.kind {
        runtime::ExprKind::Apply { callee, arg, .. } => {
            expr_may_perform_when_evaluated(callee, functions, bindings, visiting, memo)
                || expr_may_perform_when_evaluated(arg, functions, bindings, visiting, memo)
                || callee_type_may_perform(&callee.ty)
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_may_perform_when_evaluated(cond, functions, bindings, visiting, memo)
                || expr_may_perform_when_evaluated(then_branch, functions, bindings, visiting, memo)
                || expr_may_perform_when_evaluated(else_branch, functions, bindings, visiting, memo)
        }
        runtime::ExprKind::Tuple(items) => items
            .iter()
            .any(|item| expr_may_perform_when_evaluated(item, functions, bindings, visiting, memo)),
        runtime::ExprKind::Record { fields, spread } => {
            fields.iter().any(|field| {
                expr_may_perform_when_evaluated(&field.value, functions, bindings, visiting, memo)
            }) || spread.as_ref().is_some_and(|spread| match spread {
                runtime::RecordSpreadExpr::Head(expr) | runtime::RecordSpreadExpr::Tail(expr) => {
                    expr_may_perform_when_evaluated(expr, functions, bindings, visiting, memo)
                }
            })
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        }
        | runtime::ExprKind::Select { base: value, .. } => {
            expr_may_perform_when_evaluated(value, functions, bindings, visiting, memo)
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_may_perform_when_evaluated(scrutinee, functions, bindings, visiting, memo)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|guard| {
                        expr_may_perform_when_evaluated(guard, functions, bindings, visiting, memo)
                    }) || expr_may_perform_when_evaluated(
                        &arm.body, functions, bindings, visiting, memo,
                    )
                })
        }
        runtime::ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| match stmt {
                runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                    expr_may_perform_when_evaluated(value, functions, bindings, visiting, memo)
                }
                runtime::Stmt::Module { body, .. } => {
                    expr_may_perform_when_evaluated(body, functions, bindings, visiting, memo)
                }
            }) || tail.as_ref().is_some_and(|tail| {
                expr_may_perform_when_evaluated(tail, functions, bindings, visiting, memo)
            })
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            expr_may_perform_when_evaluated(body, functions, bindings, visiting, memo)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|guard| {
                        expr_may_perform_when_evaluated(guard, functions, bindings, visiting, memo)
                    }) || expr_may_perform_when_evaluated(
                        &arm.body, functions, bindings, visiting, memo,
                    )
                })
        }
        runtime::ExprKind::Lambda { .. } | runtime::ExprKind::Thunk { .. } => false,
        runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => {
            expr_may_perform_when_evaluated(body, functions, bindings, visiting, memo)
        }
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => false,
    }
}

fn expr_contains_indirect_apply(
    expr: &runtime::Expr,
    functions: &HashMap<typed_ir::Path, FunctionInfo>,
) -> bool {
    let this_is_indirect_apply = matches!(expr.kind, runtime::ExprKind::Apply { .. })
        && primitive_apply(expr).is_none()
        && effect_apply_body_request(expr).is_none()
        && direct_apply_path(expr, functions).ok().flatten().is_none();
    if this_is_indirect_apply {
        return true;
    }

    match &expr.kind {
        runtime::ExprKind::Lambda { body, .. }
        | runtime::ExprKind::Thunk { expr: body, .. }
        | runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => {
            expr_contains_indirect_apply(body, functions)
        }
        runtime::ExprKind::Apply { callee, arg, .. } => {
            expr_contains_indirect_apply(callee, functions)
                || expr_contains_indirect_apply(arg, functions)
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_contains_indirect_apply(cond, functions)
                || expr_contains_indirect_apply(then_branch, functions)
                || expr_contains_indirect_apply(else_branch, functions)
        }
        runtime::ExprKind::Tuple(items) => items
            .iter()
            .any(|item| expr_contains_indirect_apply(item, functions)),
        runtime::ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_contains_indirect_apply(&field.value, functions))
                || spread.as_ref().is_some_and(|spread| match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => {
                        expr_contains_indirect_apply(expr, functions)
                    }
                })
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        }
        | runtime::ExprKind::Select { base: value, .. } => {
            expr_contains_indirect_apply(value, functions)
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_contains_indirect_apply(scrutinee, functions)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_contains_indirect_apply(guard, functions))
                        || expr_contains_indirect_apply(&arm.body, functions)
                })
        }
        runtime::ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| match stmt {
                runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                    expr_contains_indirect_apply(value, functions)
                }
                runtime::Stmt::Module { body, .. } => expr_contains_indirect_apply(body, functions),
            }) || tail
                .as_ref()
                .is_some_and(|tail| expr_contains_indirect_apply(tail, functions))
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            expr_contains_indirect_apply(body, functions)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_contains_indirect_apply(guard, functions))
                        || expr_contains_indirect_apply(&arm.body, functions)
                })
        }
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => false,
    }
}

fn expr_uses_path(expr: &runtime::Expr, path: &typed_ir::Path) -> bool {
    match &expr.kind {
        runtime::ExprKind::Var(candidate) => candidate == path,
        runtime::ExprKind::Lambda { body, .. }
        | runtime::ExprKind::Thunk { expr: body, .. }
        | runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => expr_uses_path(body, path),
        runtime::ExprKind::Apply { callee, arg, .. } => {
            expr_uses_path(callee, path) || expr_uses_path(arg, path)
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_uses_path(cond, path)
                || expr_uses_path(then_branch, path)
                || expr_uses_path(else_branch, path)
        }
        runtime::ExprKind::Tuple(items) => items.iter().any(|item| expr_uses_path(item, path)),
        runtime::ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_uses_path(&field.value, path))
                || spread.as_ref().is_some_and(|spread| match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => expr_uses_path(expr, path),
                })
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        }
        | runtime::ExprKind::Select { base: value, .. } => expr_uses_path(value, path),
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_uses_path(scrutinee, path)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_uses_path(guard, path))
                        || expr_uses_path(&arm.body, path)
                })
        }
        runtime::ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| match stmt {
                runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                    expr_uses_path(value, path)
                }
                runtime::Stmt::Module { body, .. } => expr_uses_path(body, path),
            }) || tail.as_ref().is_some_and(|tail| expr_uses_path(tail, path))
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            expr_uses_path(body, path)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_uses_path(guard, path))
                        || expr_uses_path(&arm.body, path)
                })
        }
        runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => false,
    }
}

fn matches_any_effect(expected: &[typed_ir::Path], actual: &typed_ir::Path) -> bool {
    expected
        .iter()
        .any(|expected| effect_matches(expected, actual))
}

fn handled_effects_compatible(
    expected: &[typed_ir::Path],
    left: &typed_ir::Path,
    right: &typed_ir::Path,
) -> bool {
    left == right || matches_any_effect(expected, left) || matches_any_effect(expected, right)
}

fn join_handled_effect(
    joined: &mut Option<typed_ir::Path>,
    expected: &[typed_ir::Path],
    effect: typed_ir::Path,
) -> CpsLowerResult<()> {
    if let Some(previous) = joined {
        if !handled_effects_compatible(expected, previous, &effect) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler effect mismatch",
            });
        }
    } else {
        *joined = Some(effect);
    }
    Ok(())
}

fn default_expected_effect(expected: &[typed_ir::Path]) -> typed_ir::Path {
    expected.first().cloned().unwrap_or_default()
}

fn dynamic_handler_id() -> CpsHandlerId {
    CpsHandlerId(usize::MAX)
}

fn body_is_thunk_value(expr: &runtime::Expr) -> bool {
    matches!(expr.ty, runtime::Type::Thunk { .. })
        && !matches!(expr.kind, runtime::ExprKind::Thunk { .. })
}

struct ContinuationBuilder {
    id: CpsContinuationId,
    params: Vec<CpsValueId>,
    captures: Vec<CpsValueId>,
    stmts: Vec<CpsStmt>,
    terminator: Option<CpsTerminator>,
}

impl ContinuationBuilder {
    fn new(id: CpsContinuationId, params: Vec<CpsValueId>) -> Self {
        Self {
            id,
            params,
            captures: Vec::new(),
            stmts: Vec::new(),
            terminator: None,
        }
    }
}

fn collect_lambda_params(expr: &runtime::Expr) -> (Vec<typed_ir::Name>, &runtime::Expr) {
    let mut params = Vec::new();
    let mut current = expr;
    while let runtime::ExprKind::Lambda { param, body, .. } = &current.kind {
        params.push(param.clone());
        current = body;
    }
    (params, current)
}

fn collect_callable_params(expr: &runtime::Expr) -> (Vec<typed_ir::Name>, runtime::Expr) {
    let (mut params, body) = collect_lambda_params(expr);
    let mut body = body.clone();
    while let runtime::ExprKind::Block {
        stmts,
        tail: Some(tail),
    } = &body.kind
    {
        let (tail_params, tail_body) = collect_lambda_params(tail);
        if tail_params.is_empty() {
            break;
        }
        params.extend(tail_params);
        body = runtime::Expr::typed(
            runtime::ExprKind::Block {
                stmts: stmts.clone(),
                tail: Some(Box::new(tail_body.clone())),
            },
            body.ty.clone(),
        );
    }
    (params, body)
}

fn recursive_lambda_let<'a>(
    pattern: &'a runtime::Pattern,
    value: &'a runtime::Expr,
) -> Option<(&'a typed_ir::Name, &'a typed_ir::Name, &'a runtime::Expr)> {
    let runtime::Pattern::Bind { name, .. } = pattern else {
        return None;
    };
    let runtime::ExprKind::Lambda { param, body, .. } = &value.kind else {
        return None;
    };
    let self_path = typed_ir::Path::from_name(name.clone());
    expr_uses_path(body, &self_path).then_some((name, param, body.as_ref()))
}

fn lower_literal(lit: &typed_ir::Lit) -> CpsLiteral {
    match lit {
        typed_ir::Lit::Int(value) => CpsLiteral::Int(value.clone()),
        typed_ir::Lit::Float(value) => CpsLiteral::Float(value.clone()),
        typed_ir::Lit::String(value) => CpsLiteral::String(value.clone()),
        typed_ir::Lit::Bool(value) => CpsLiteral::Bool(*value),
        typed_ir::Lit::Unit => CpsLiteral::Unit,
    }
}

fn primitive_apply(expr: &runtime::Expr) -> Option<(typed_ir::PrimitiveOp, Vec<&runtime::Expr>)> {
    let mut args = Vec::new();
    let mut current = expr;
    loop {
        current = transparent_effect_expr(current);
        match &current.kind {
            runtime::ExprKind::Apply { callee, arg, .. } => {
                args.push(arg.as_ref());
                current = callee;
            }
            _ => break,
        }
    }
    let runtime::ExprKind::PrimitiveOp(op) = &current.kind else {
        return None;
    };
    args.reverse();
    Some((*op, args))
}

#[derive(Debug, Clone)]
struct CpsEffectApply<'a> {
    effect: typed_ir::Path,
    payload: &'a runtime::Expr,
    blocked: Option<runtime::EffectIdRef>,
}

fn effect_apply(expr: &runtime::Expr) -> Option<CpsEffectApply<'_>> {
    let runtime::ExprKind::Apply { callee, arg, .. } = &expr.kind else {
        return None;
    };
    let callee = transparent_effect_expr(callee);
    let runtime::ExprKind::EffectOp(effect) = &callee.kind else {
        return None;
    };
    Some(CpsEffectApply {
        effect: effect.clone(),
        payload: arg.as_ref(),
        blocked: None,
    })
}

fn effect_apply_nested(expr: &runtime::Expr) -> Option<CpsEffectApply<'_>> {
    if let Some(inner) = handle_body_execution_inner(expr) {
        return effect_apply_nested(inner);
    }
    let mut current = expr;
    let mut blocked = None;
    loop {
        match &current.kind {
            runtime::ExprKind::BindHere { expr }
            | runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. } => current = expr,
            runtime::ExprKind::AddId { id, allowed, thunk } => {
                let request = effect_apply_nested(thunk)?;
                if blocked.is_none() && !effect_allowed_by_type(allowed, &request.effect) {
                    blocked = Some(*id);
                }
                return Some(CpsEffectApply {
                    blocked: blocked.or(request.blocked),
                    ..request
                });
            }
            _ => {
                let mut request = effect_apply(current)?;
                request.blocked = blocked.or(request.blocked);
                return Some(request);
            }
        }
    }
}

fn effect_apply_body_request(expr: &runtime::Expr) -> Option<CpsEffectApply<'_>> {
    match &expr.kind {
        runtime::ExprKind::BindHere { .. }
        | runtime::ExprKind::AddId { .. }
        | runtime::ExprKind::Coerce { .. }
        | runtime::ExprKind::Pack { .. } => effect_apply_nested(expr),
        _ => effect_apply(expr),
    }
}

fn transparent_effect_expr(expr: &runtime::Expr) -> &runtime::Expr {
    let mut current = expr;
    loop {
        match &current.kind {
            runtime::ExprKind::BindHere { expr }
            | runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. }
            | runtime::ExprKind::AddId { thunk: expr, .. } => current = expr,
            _ => return current,
        }
    }
}

fn effect_allowed_by_type(allowed: &typed_ir::Type, effect: &typed_ir::Path) -> bool {
    match allowed {
        typed_ir::Type::Any => true,
        typed_ir::Type::Never => false,
        typed_ir::Type::Named { path, .. } => effect_path_matches_allowed(path, effect),
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| effect_allowed_by_type(item, effect))
                || matches!(tail.as_ref(), typed_ir::Type::Any)
        }
        _ => false,
    }
}

fn effect_path_matches_allowed(allowed: &typed_ir::Path, effect: &typed_ir::Path) -> bool {
    if effect.segments.starts_with(&allowed.segments) {
        return true;
    }
    allowed.segments.split_last().is_some_and(|(_, namespace)| {
        !namespace.is_empty() && effect.segments.starts_with(namespace)
    })
}

fn handle_body_execution_inner(expr: &runtime::Expr) -> Option<&runtime::Expr> {
    // VM handle evaluation runs a thunk-valued body inside the handler boundary.
    // Treat only the whole BindHere* -> AddId* -> Thunk wrapper as that
    // execution marker.
    let mut current = expr;
    loop {
        match &current.kind {
            runtime::ExprKind::BindHere { expr }
            | runtime::ExprKind::AddId { thunk: expr, .. }
            | runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. } => current = expr,
            _ => break,
        }
    }
    let runtime::ExprKind::Thunk { expr, .. } = &current.kind else {
        return None;
    };
    let mut inner = expr.as_ref();
    loop {
        match &inner.kind {
            runtime::ExprKind::BindHere { expr }
            | runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. } => inner = expr,
            _ => break,
        }
    }
    Some(inner)
}

fn handler_body_plain_value_inner(expr: &runtime::Expr) -> Option<&runtime::Expr> {
    let inner = handle_body_execution_inner(expr)?;
    match inner.kind {
        runtime::ExprKind::Var(_) | runtime::ExprKind::Lit(_) => Some(inner),
        _ => None,
    }
}

fn direct_apply<'expr, 'functions>(
    expr: &'expr runtime::Expr,
    functions: &'functions HashMap<typed_ir::Path, FunctionInfo>,
) -> CpsLowerResult<Option<(String, &'functions FunctionInfo, Vec<&'expr runtime::Expr>)>> {
    let Some((_, target, args)) = direct_apply_path(expr, functions)? else {
        return Ok(None);
    };
    Ok(Some((target.name.clone(), target, args)))
}

fn direct_call_result_needs_force(expr: &runtime::Expr, target: &FunctionInfo) -> bool {
    matches!(target.ret, runtime::Type::Thunk { .. })
        && !matches!(expr.ty, runtime::Type::Thunk { .. })
}

fn bool_match(expr: &runtime::Expr) -> Option<(&runtime::Expr, &runtime::Expr, &runtime::Expr)> {
    let runtime::ExprKind::Match {
        scrutinee, arms, ..
    } = &expr.kind
    else {
        return None;
    };
    if arms.len() != 2 || arms.iter().any(|arm| arm.guard.is_some()) {
        return None;
    }
    let mut then_branch = None;
    let mut else_branch = None;
    for arm in arms {
        match &arm.pattern {
            runtime::Pattern::Lit {
                lit: typed_ir::Lit::Bool(true),
                ..
            } => then_branch = Some(&arm.body),
            runtime::Pattern::Lit {
                lit: typed_ir::Lit::Bool(false),
                ..
            } => else_branch = Some(&arm.body),
            _ => return None,
        }
    }
    Some((scrutinee, then_branch?, else_branch?))
}

/// Conservatively report whether a function-typed value may perform an
/// effect when applied. Used by lower_handled_block to decide between
/// EffectfulApply (terminator, captures caller rest) and ApplyClosure
/// (stmt, synchronous). Unknown / polymorphic types are treated as
/// effectful so we don't lose caller rest at a callback boundary
/// (e.g. std::fold's `f z x`).
fn callee_type_may_perform(ty: &runtime::Type) -> bool {
    match ty {
        runtime::Type::Fun { ret, .. } => {
            matches!(ret.as_ref(), runtime::Type::Thunk { .. }) || callee_type_may_perform(ret)
        }
        runtime::Type::Thunk { .. } => true,
        runtime::Type::Unknown => true,
        runtime::Type::Core(_) => false,
    }
}

fn callable_type_after_force(ty: &runtime::Type) -> &runtime::Type {
    match ty {
        runtime::Type::Thunk { value, .. } => value,
        _ => ty,
    }
}

fn direct_apply_path<'expr, 'functions>(
    expr: &'expr runtime::Expr,
    functions: &'functions HashMap<typed_ir::Path, FunctionInfo>,
) -> CpsLowerResult<
    Option<(
        &'expr typed_ir::Path,
        &'functions FunctionInfo,
        Vec<&'expr runtime::Expr>,
    )>,
> {
    let mut args = Vec::new();
    let mut current = expr;
    loop {
        current = transparent_effect_expr(current);
        match &current.kind {
            runtime::ExprKind::Apply { callee, arg, .. } => {
                args.push(arg.as_ref());
                current = callee;
            }
            _ => break,
        }
    }
    let runtime::ExprKind::Var(path) = &current.kind else {
        return Ok(None);
    };
    let Some(target) = functions.get(path) else {
        return Ok(None);
    };
    if args.len() != target.arity {
        return Err(CpsLowerError::CallArityMismatch {
            target: target.name.clone(),
            expected: target.arity,
            actual: args.len(),
        });
    }
    args.reverse();
    Ok(Some((path, target, args)))
}

fn primitive_arity(op: typed_ir::PrimitiveOp) -> usize {
    use typed_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot
        | PrimitiveOp::ListEmpty
        | PrimitiveOp::ListSingleton
        | PrimitiveOp::ListLen
        | PrimitiveOp::ListViewRaw
        | PrimitiveOp::StringLen
        | PrimitiveOp::IntToString
        | PrimitiveOp::IntToHex
        | PrimitiveOp::IntToUpperHex
        | PrimitiveOp::FloatToString
        | PrimitiveOp::BoolToString => 1,
        PrimitiveOp::BoolEq
        | PrimitiveOp::ListMerge
        | PrimitiveOp::ListIndex
        | PrimitiveOp::ListIndexRange
        | PrimitiveOp::StringIndex
        | PrimitiveOp::StringIndexRange
        | PrimitiveOp::IntAdd
        | PrimitiveOp::IntSub
        | PrimitiveOp::IntMul
        | PrimitiveOp::IntDiv
        | PrimitiveOp::IntEq
        | PrimitiveOp::IntLt
        | PrimitiveOp::IntLe
        | PrimitiveOp::IntGt
        | PrimitiveOp::IntGe
        | PrimitiveOp::FloatAdd
        | PrimitiveOp::FloatSub
        | PrimitiveOp::FloatMul
        | PrimitiveOp::FloatDiv
        | PrimitiveOp::FloatEq
        | PrimitiveOp::FloatLt
        | PrimitiveOp::FloatLe
        | PrimitiveOp::FloatGt
        | PrimitiveOp::FloatGe
        | PrimitiveOp::StringEq
        | PrimitiveOp::StringConcat => 2,
        PrimitiveOp::ListSplice
        | PrimitiveOp::ListIndexRangeRaw
        | PrimitiveOp::StringSplice
        | PrimitiveOp::StringIndexRangeRaw => 3,
        PrimitiveOp::ListSpliceRaw | PrimitiveOp::StringSpliceRaw => 4,
    }
}

fn path_name(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod tests {
    use crate::cps_eval::eval_cps_module;
    use crate::cps_validate::validate_cps_module;

    use super::*;

    fn unknown_lit(lit: typed_ir::Lit) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Lit(lit), runtime::Type::unknown())
    }

    fn primitive(op: typed_ir::PrimitiveOp) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::PrimitiveOp(op), runtime::Type::unknown())
    }

    fn apply(callee: runtime::Expr, arg: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn if_expr(
        cond: runtime::Expr,
        then_branch: runtime::Expr,
        else_branch: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
                evidence: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn var(name: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Var(typed_ir::Path::from_name(typed_ir::Name(name.to_string()))),
            runtime::Type::unknown(),
        )
    }

    fn effect_op(name: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::EffectOp(typed_ir::Path::from_name(typed_ir::Name(
                name.to_string(),
            ))),
            runtime::Type::unknown(),
        )
    }

    fn effect_op_path(path: typed_ir::Path) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::EffectOp(path), runtime::Type::unknown())
    }

    fn bind_pattern(name: &str) -> runtime::Pattern {
        runtime::Pattern::Bind {
            name: typed_ir::Name(name.to_string()),
            ty: runtime::Type::unknown(),
        }
    }

    fn handle_once(
        effect: &str,
        payload: &str,
        resume: &str,
        body: runtime::Expr,
        arm_body: runtime::Expr,
    ) -> runtime::Expr {
        let effect = typed_ir::Path::from_name(typed_ir::Name(effect.to_string()));
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![runtime::HandleArm {
                    effect: effect.clone(),
                    payload: bind_pattern(payload),
                    resume: Some(runtime::ResumeBinding {
                        name: typed_ir::Name(resume.to_string()),
                        ty: runtime::Type::unknown(),
                    }),
                    guard: None,
                    body: arm_body,
                }],
                evidence: runtime::JoinEvidence {
                    result: typed_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: vec![effect],
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn handle_once_with_value(
        effect: &str,
        payload: &str,
        resume: &str,
        body: runtime::Expr,
        arm_body: runtime::Expr,
        value_payload: &str,
        value_body: runtime::Expr,
    ) -> runtime::Expr {
        let effect = typed_ir::Path::from_name(typed_ir::Name(effect.to_string()));
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![
                    runtime::HandleArm {
                        effect: effect.clone(),
                        payload: bind_pattern(payload),
                        resume: Some(runtime::ResumeBinding {
                            name: typed_ir::Name(resume.to_string()),
                            ty: runtime::Type::unknown(),
                        }),
                        guard: None,
                        body: arm_body,
                    },
                    runtime::HandleArm {
                        effect: typed_ir::Path::default(),
                        payload: bind_pattern(value_payload),
                        resume: None,
                        guard: None,
                        body: value_body,
                    },
                ],
                evidence: runtime::JoinEvidence {
                    result: typed_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: vec![effect],
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn handle_value(
        body: runtime::Expr,
        value_payload: &str,
        value_body: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![runtime::HandleArm {
                    effect: typed_ir::Path::default(),
                    payload: bind_pattern(value_payload),
                    resume: None,
                    guard: None,
                    body: value_body,
                }],
                evidence: runtime::JoinEvidence {
                    result: typed_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: Vec::new(),
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn handle_once_expr(
        effect: typed_ir::Path,
        payload: &str,
        resume: &str,
        body: runtime::Expr,
        arm_body: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![runtime::HandleArm {
                    effect: effect.clone(),
                    payload: bind_pattern(payload),
                    resume: Some(runtime::ResumeBinding {
                        name: typed_ir::Name(resume.to_string()),
                        ty: runtime::Type::unknown(),
                    }),
                    guard: None,
                    body: arm_body,
                }],
                evidence: runtime::JoinEvidence {
                    result: typed_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: vec![effect],
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn block(stmts: Vec<runtime::Stmt>, tail: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Block {
                stmts,
                tail: Some(Box::new(tail)),
            },
            runtime::Type::unknown(),
        )
    }

    fn thunk(expr: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Thunk {
                effect: typed_ir::Type::Unknown,
                value: runtime::Type::unknown(),
                expr: Box::new(expr),
            },
            runtime::Type::unknown(),
        )
    }

    fn bind_here(expr: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::BindHere {
                expr: Box::new(expr),
            },
            runtime::Type::unknown(),
        )
    }

    fn local_push_id(id: usize, body: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::LocalPushId {
                id: runtime::EffectIdVar(id),
                body: Box::new(body),
            },
            runtime::Type::unknown(),
        )
    }

    fn peek_id() -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::PeekId, runtime::Type::unknown())
    }

    fn add_id(
        id: runtime::EffectIdRef,
        allowed: typed_ir::Type,
        thunk: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::AddId {
                id,
                allowed,
                thunk: Box::new(thunk),
            },
            runtime::Type::unknown(),
        )
    }

    fn lambda(param: &str, body: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Lambda {
                param: typed_ir::Name(param.to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(body),
            },
            runtime::Type::unknown(),
        )
    }

    fn binding(name: &str, body: runtime::Expr) -> runtime::Binding {
        runtime::Binding {
            name: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Unknown,
            },
            body,
        }
    }

    fn effect_path(effect: &str, op: &str) -> typed_ir::Path {
        typed_ir::Path {
            segments: vec![
                typed_ir::Name(effect.to_string()),
                typed_ir::Name(op.to_string()),
            ],
        }
    }

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        module_with_bindings_and_root(Vec::new(), expr)
    }

    fn module_with_bindings_and_root(
        bindings: Vec<runtime::Binding>,
        expr: runtime::Expr,
    ) -> runtime::Module {
        runtime::Module {
            path: typed_ir::Path::default(),
            bindings,
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    #[test]
    fn lowers_pure_int_add_to_multishot_cps() {
        let expr = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                unknown_lit(typed_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(typed_ir::Lit::Int("22".to_string())),
        );
        let module = module_with_root(expr);
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(lowered.roots.len(), 1);
        assert_eq!(lowered.roots[0].continuations.len(), 1);
        assert_eq!(
            lowered.roots[0].continuations[0].shot_kind,
            CpsShotKind::MultiShot
        );
        assert_eq!(
            lowered.roots[0].continuations[0].stmts,
            vec![
                CpsStmt::Literal {
                    dest: CpsValueId(0),
                    literal: CpsLiteral::Int("20".to_string()),
                },
                CpsStmt::Literal {
                    dest: CpsValueId(1),
                    literal: CpsLiteral::Int("22".to_string()),
                },
                CpsStmt::Primitive {
                    dest: CpsValueId(2),
                    op: typed_ir::PrimitiveOp::IntAdd,
                    args: vec![CpsValueId(0), CpsValueId(1)],
                },
                // lower_root forces the return value when the static
                // return type is non-Thunk; ForceThunk is a no-op on
                // plain values.
                CpsStmt::ForceThunk {
                    dest: CpsValueId(3),
                    thunk: CpsValueId(2),
                },
            ]
        );
        assert_eq!(
            lowered.roots[0].continuations[0].terminator,
            CpsTerminator::Return(CpsValueId(3))
        );
    }

    #[test]
    fn lowers_local_push_and_peek_id_to_guard_statements() {
        let module = module_with_root(local_push_id(0, peek_id()));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        let stmts = &lowered.roots[0].continuations[0].stmts;
        assert!(matches!(stmts[0], CpsStmt::FreshGuard { .. }));
        assert!(matches!(stmts[1], CpsStmt::PeekGuard { .. }));
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::EffectId(0)]
        );
    }

    #[test]
    fn lowers_add_id_blocked_effect_to_perform_blocked_guard() {
        let body = add_id(
            runtime::EffectIdRef::Peek,
            typed_ir::Type::Never,
            apply(
                effect_op("choose"),
                unknown_lit(typed_ir::Lit::Int("1".to_string())),
            ),
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, var("x")));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        let perform = lowered.roots[0]
            .continuations
            .iter()
            .find_map(|continuation| match &continuation.terminator {
                CpsTerminator::Perform { blocked, .. } => *blocked,
                _ => None,
            })
            .expect("blocked perform guard");
        assert!(
            lowered.roots[0].continuations[0]
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, CpsStmt::PeekGuard { dest } if *dest == perform))
        );
    }

    #[test]
    fn skips_unreachable_non_function_binding() {
        let module = runtime::Module {
            path: typed_ir::Path::default(),
            bindings: vec![runtime::Binding {
                name: typed_ir::Path::from_name(typed_ir::Name("unused".to_string())),
                type_params: Vec::new(),
                scheme: typed_ir::Scheme {
                    requirements: Vec::new(),
                    body: typed_ir::Type::Unknown,
                },
                body: unknown_lit(typed_ir::Lit::Int("0".to_string())),
            }],
            root_exprs: vec![unknown_lit(typed_ir::Lit::Int("41".to_string()))],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        };
        let lowered = lower_cps_module(&module).expect("lowered");

        assert!(lowered.functions.is_empty());
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("41".to_string())]
        );
    }

    #[test]
    fn inlines_thunk_handler_wrapper_call() {
        let effect = effect_path("sub", "return");
        let handler = binding(
            "run",
            lambda(
                "x",
                handle_once_expr(effect.clone(), "a", "_k", var("x"), thunk(var("a"))),
            ),
        );
        let root = apply(
            var("run"),
            thunk(apply(
                effect_op_path(effect),
                unknown_lit(typed_ir::Lit::Int("41".to_string())),
            )),
        );
        let module = module_with_bindings_and_root(vec![handler], root);
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert!(lowered.functions.is_empty());
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("41".to_string())]
        );
    }

    #[test]
    fn lowers_if_to_multishot_continuation_graph() {
        let module = module_with_root(if_expr(
            unknown_lit(typed_ir::Lit::Bool(true)),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
            unknown_lit(typed_ir::Lit::Int("2".to_string())),
        ));
        let lowered = lower_cps_module(&module).expect("lowered");
        let root = &lowered.roots[0];

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(root.continuations.len(), 4);
        assert!(
            root.continuations
                .iter()
                .all(|continuation| continuation.shot_kind == CpsShotKind::MultiShot)
        );
        assert_eq!(
            root.continuations[0].terminator,
            CpsTerminator::Branch {
                cond: CpsValueId(0),
                then_cont: CpsContinuationId(1),
                else_cont: CpsContinuationId(2),
            }
        );
        assert_eq!(root.continuations[3].params, vec![CpsValueId(1)]);
        // lower_root force-emits a ForceThunk on the join-block's incoming
        // value before the Return, so the returned slot is the forced one
        // rather than the join parameter directly.
        assert_eq!(root.continuations[3].stmts.len(), 1);
        assert!(matches!(
            root.continuations[3].stmts[0],
            CpsStmt::ForceThunk {
                dest: CpsValueId(4),
                thunk: CpsValueId(1),
            }
        ));
        assert_eq!(
            root.continuations[3].terminator,
            CpsTerminator::Return(CpsValueId(4))
        );
    }

    #[test]
    fn lowers_direct_call_to_cps() {
        let inc = binding(
            "inc",
            lambda(
                "x",
                apply(
                    apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            ),
        );
        let root = apply(
            var("inc"),
            unknown_lit(typed_ir::Lit::Int("41".to_string())),
        );
        let module = module_with_bindings_and_root(vec![inc], root);
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(lowered.functions.len(), 1);
        assert_eq!(lowered.functions[0].name, "inc");
        assert_eq!(lowered.functions[0].params, vec![CpsValueId(0)]);
        assert_eq!(
            lowered.roots[0].continuations[0].stmts,
            vec![
                CpsStmt::Literal {
                    dest: CpsValueId(0),
                    literal: CpsLiteral::Int("41".to_string()),
                },
                CpsStmt::DirectCall {
                    dest: CpsValueId(1),
                    target: "inc".to_string(),
                    args: vec![CpsValueId(0)],
                },
                // force_if_non_thunk_demand always emits a ForceThunk after
                // a direct call whose static result type is non-Thunk; it's
                // a runtime no-op on plain values but covers callees that
                // wrap their result in MakeThunk (e.g. effectful helpers).
                CpsStmt::ForceThunk {
                    dest: CpsValueId(2),
                    thunk: CpsValueId(1),
                },
                // lower_root also forces the final return value when the
                // root expression's type is non-Thunk, so the body's already-
                // forced direct-call result gets one more (no-op) force.
                CpsStmt::ForceThunk {
                    dest: CpsValueId(3),
                    thunk: CpsValueId(2),
                },
            ]
        );
    }

    #[test]
    fn lowers_single_effect_handler_with_resumption() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");
        let root = &lowered.roots[0];

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(root.handlers.len(), 1);
        assert!(
            root.continuations.iter().any(|continuation| matches!(
                continuation.terminator,
                CpsTerminator::Perform { .. }
            ))
        );
        assert!(
            root.continuations
                .iter()
                .flat_map(|continuation| &continuation.stmts)
                .any(|stmt| matches!(stmt, CpsStmt::Resume { .. }))
        );
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("3".to_string())]
        );
    }

    #[test]
    fn lowers_value_handler_arm() {
        let body = unknown_lit(typed_ir::Lit::Int("1".to_string()));
        let value_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("value")),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
        );
        let module = module_with_root(handle_value(body, "value", value_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("11".to_string())]
        );
    }

    #[test]
    fn leaves_resume_result_outside_value_arm() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        );
        let arm_body = apply(var("k"), var("x"));
        let value_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("value")),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
        );
        let module = module_with_root(handle_once_with_value(
            "choose", "x", "k", body, arm_body, "value", value_body,
        ));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("1".to_string())]
        );
    }

    #[test]
    fn leaves_multishot_resume_results_outside_value_arm() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let value_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("value")),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
        );
        let module = module_with_root(handle_once_with_value(
            "choose", "x", "k", body, arm_body, "value", value_body,
        ));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("3".to_string())]
        );
    }

    #[test]
    fn lowers_effect_handler_body_rest_into_resumption_continuation() {
        let choose_one = apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        );
        let body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), choose_one),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn lowers_direct_call_rest_into_resumption_continuation() {
        let inc = binding(
            "inc",
            lambda(
                "x",
                apply(
                    apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(typed_ir::Lit::Int("10".to_string())),
                ),
            ),
        );
        let body = apply(
            var("inc"),
            apply(
                effect_op("choose"),
                unknown_lit(typed_ir::Lit::Int("1".to_string())),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_bindings_and_root(
            vec![inc],
            handle_once("choose", "x", "k", body, arm_body),
        );
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn lowers_block_rest_into_resumption_continuation() {
        let body = block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("y"),
                value: apply(
                    effect_op("choose"),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            }],
            apply(
                apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("y")),
                unknown_lit(typed_ir::Lit::Int("10".to_string())),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn lowers_multiple_block_effects_into_nested_resumption_continuations() {
        let body = block(
            vec![
                runtime::Stmt::Let {
                    pattern: bind_pattern("a"),
                    value: apply(
                        effect_op("choose"),
                        unknown_lit(typed_ir::Lit::Int("1".to_string())),
                    ),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("b"),
                    value: apply(
                        effect_op("choose"),
                        unknown_lit(typed_ir::Lit::Int("2".to_string())),
                    ),
                },
            ],
            apply(
                apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("a")),
                var("b"),
            ),
        );
        let arm_body = apply(var("k"), var("x"));
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert!(
            lowered.roots[0]
                .continuations
                .iter()
                .filter(|continuation| matches!(
                    continuation.terminator,
                    CpsTerminator::Perform { .. }
                ))
                .count()
                >= 2
        );
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("3".to_string())]
        );
    }

    #[test]
    fn lowers_block_expr_statement_rest_into_resumption_continuation() {
        let body = block(
            vec![runtime::Stmt::Expr(apply(
                effect_op("choose"),
                unknown_lit(typed_ir::Lit::Int("1".to_string())),
            ))],
            apply(
                apply(
                    primitive(typed_ir::PrimitiveOp::IntAdd),
                    unknown_lit(typed_ir::Lit::Int("10".to_string())),
                ),
                unknown_lit(typed_ir::Lit::Int("20".to_string())),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("60".to_string())]
        );
    }

    #[test]
    fn unwraps_thunked_handle_body_before_cps_effect_lowering() {
        let body = bind_here(thunk(block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("y"),
                value: apply(
                    effect_op("choose"),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            }],
            apply(
                apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("y")),
                unknown_lit(typed_ir::Lit::Int("10".to_string())),
            ),
        )));
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn infers_capture_for_block_value_used_after_effect() {
        let body = block(
            vec![
                runtime::Stmt::Let {
                    pattern: bind_pattern("z"),
                    value: unknown_lit(typed_ir::Lit::Int("10".to_string())),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("y"),
                    value: apply(
                        effect_op("choose"),
                        unknown_lit(typed_ir::Lit::Int("1".to_string())),
                    ),
                },
            ],
            apply(
                apply(primitive(typed_ir::PrimitiveOp::IntAdd), var("y")),
                var("z"),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(typed_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert!(
            lowered.roots[0]
                .continuations
                .iter()
                .any(|continuation| !continuation.captures.is_empty())
        );
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn lowers_bind_here_tail_effect_statement() {
        let body = bind_here(apply(
            effect_op("choose"),
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
        ));
        let arm_body = apply(var("k"), var("x"));
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));

        let lowered = lower_cps_module(&module).expect("lowered");
        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("1".to_string())]
        );
    }

    #[test]
    fn lowers_if_branches_with_distinct_resume_continuations() {
        let then_branch = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                apply(
                    effect_op("choose"),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
            ),
            unknown_lit(typed_ir::Lit::Int("10".to_string())),
        );
        let else_branch = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                apply(
                    effect_op("choose"),
                    unknown_lit(typed_ir::Lit::Int("2".to_string())),
                ),
            ),
            unknown_lit(typed_ir::Lit::Int("20".to_string())),
        );
        let body = if_expr(
            unknown_lit(typed_ir::Lit::Bool(true)),
            then_branch,
            else_branch,
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_three = apply(var("k"), unknown_lit(typed_ir::Lit::Int("3".to_string())));
        let arm_body = apply(
            apply(primitive(typed_ir::PrimitiveOp::IntAdd), resume_x),
            resume_three,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("24".to_string())]
        );
    }

    #[test]
    fn rejects_direct_call_arity_mismatch() {
        let inc = binding("inc", lambda("x", var("x")));
        let root = apply(
            apply(var("inc"), unknown_lit(typed_ir::Lit::Int("1".to_string()))),
            unknown_lit(typed_ir::Lit::Int("2".to_string())),
        );
        let module = module_with_bindings_and_root(vec![inc], root);

        assert_eq!(
            lower_cps_module(&module).expect_err("arity mismatch"),
            CpsLowerError::CallArityMismatch {
                target: "inc".to_string(),
                expected: 1,
                actual: 2,
            }
        );
    }
}
