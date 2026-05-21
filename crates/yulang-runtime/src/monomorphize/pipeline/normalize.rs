use super::*;
use crate::runtime_intrinsic::binding_is_parametric_runtime_intrinsic;
use crate::types::{
    BoundsChoice, choose_bounds_type, core_type_contains_unknown,
    core_type_is_imprecise_runtime_slot, runtime_core_type, type_compatible,
};
use std::collections::VecDeque;

pub(super) fn normalize_hir_function_type(ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Core(typed_ir::Type::Fun { .. }) => core_function_as_hir_type(&ty),
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            normalize_hir_function_type(*param),
            normalize_hir_function_type(*ret),
        ),
        RuntimeType::Thunk { effect, value } => {
            let value = normalize_hir_function_type(*value);
            RuntimeType::thunk(effect, value)
        }
        other => other,
    }
}

pub(super) fn refresh_binding_type_params(binding: &mut Binding) {
    let mut params = BTreeSet::new();
    collect_binding_type_params(binding, &mut params);
    binding.type_params = params.into_iter().collect();
}

pub(super) fn refresh_specialized_scheme_from_body(binding: &mut Binding) {
    if hir_type_has_vars(&binding.body.ty) {
        return;
    }
    if matches!(binding.body.kind, ExprKind::PrimitiveOp(_)) {
        return;
    }
    let body_scheme = core_value_type(&binding.body.ty);
    if core_type_choice_widens(&binding.scheme.body, &body_scheme) {
        binding.body.ty =
            normalize_hir_function_type(RuntimeType::core(binding.scheme.body.clone()));
        refresh_binding_type_params(binding);
        return;
    }
    binding.scheme = typed_ir::Scheme {
        requirements: Vec::new(),
        body: body_scheme,
    };
    refresh_binding_type_params(binding);
}

fn core_type_choice_widens(projected: &typed_ir::Type, current: &typed_ir::Type) -> bool {
    match (projected, current) {
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), current) => {
            items.iter().any(|item| item == current)
        }
        (
            typed_ir::Type::Fun {
                param: projected_param,
                param_effect: projected_param_effect,
                ret_effect: projected_ret_effect,
                ret: projected_ret,
            },
            typed_ir::Type::Fun {
                param: current_param,
                param_effect: current_param_effect,
                ret_effect: current_ret_effect,
                ret: current_ret,
            },
        ) => {
            core_type_choice_widens(projected_param, current_param)
                || core_type_choice_widens(projected_param_effect, current_param_effect)
                || core_type_choice_widens(projected_ret_effect, current_ret_effect)
                || core_type_choice_widens(projected_ret, current_ret)
        }
        (
            typed_ir::Type::Named {
                path: projected_path,
                args: projected_args,
            },
            typed_ir::Type::Named {
                path: current_path,
                args: current_args,
            },
        ) if projected_path == current_path && projected_args.len() == current_args.len() => {
            projected_args
                .iter()
                .zip(current_args)
                .any(|(projected, current)| type_arg_choice_widens(projected, current))
        }
        _ => false,
    }
}

fn type_arg_choice_widens(projected: &typed_ir::TypeArg, current: &typed_ir::TypeArg) -> bool {
    match (projected, current) {
        (typed_ir::TypeArg::Type(projected), typed_ir::TypeArg::Type(current)) => {
            core_type_choice_widens(projected, current)
        }
        (typed_ir::TypeArg::Bounds(projected), typed_ir::TypeArg::Bounds(current)) => {
            projected
                .lower
                .as_deref()
                .zip(current.lower.as_deref())
                .is_some_and(|(projected, current)| core_type_choice_widens(projected, current))
                || projected
                    .upper
                    .as_deref()
                    .zip(current.upper.as_deref())
                    .is_some_and(|(projected, current)| core_type_choice_widens(projected, current))
        }
        _ => false,
    }
}

pub(super) fn refresh_closed_specialized_schemes(mut module: Module) -> Module {
    for binding in &mut module.bindings {
        let was_closed_binding = binding.type_params.is_empty();
        close_unbound_effect_vars(binding);
        if is_specialized_path(&binding.name)
            || (was_closed_binding && is_synthetic_local_act_helper_path(&binding.name))
        {
            refresh_specialized_scheme_from_body(binding);
        }
    }
    module
}

pub(super) fn normalize_parametric_primitive_intrinsics(mut module: Module) -> Module {
    for binding in &mut module.bindings {
        if binding_is_parametric_runtime_intrinsic(binding) {
            binding.type_params.clear();
        }
    }
    module
}

pub(super) fn normalize_semantic_cast_coercions(mut module: Module) -> Module {
    let role_impls = module.role_impls.clone();
    for binding in &mut module.bindings {
        binding.body = normalize_semantic_cast_coercions_expr(binding.body.clone(), &role_impls);
    }
    for root in &mut module.root_exprs {
        *root = normalize_semantic_cast_coercions_expr(root.clone(), &role_impls);
    }
    module
}

fn normalize_semantic_cast_coercions_expr(
    expr: Expr,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> Expr {
    let ty = expr.ty.clone();
    let kind = match expr.kind {
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(normalize_semantic_cast_coercions_expr(*body, role_impls)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(normalize_semantic_cast_coercions_expr(*callee, role_impls)),
            arg: Box::new(normalize_semantic_cast_coercions_expr(*arg, role_impls)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(normalize_semantic_cast_coercions_expr(*cond, role_impls)),
            then_branch: Box::new(normalize_semantic_cast_coercions_expr(
                *then_branch,
                role_impls,
            )),
            else_branch: Box::new(normalize_semantic_cast_coercions_expr(
                *else_branch,
                role_impls,
            )),
            evidence,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| normalize_semantic_cast_coercions_expr(item, role_impls))
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: normalize_semantic_cast_coercions_expr(field.value, role_impls),
                })
                .collect(),
            spread: spread
                .map(|spread| normalize_semantic_cast_coercions_record_spread(spread, role_impls)),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value
                .map(|value| Box::new(normalize_semantic_cast_coercions_expr(*value, role_impls))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(normalize_semantic_cast_coercions_expr(*base, role_impls)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(normalize_semantic_cast_coercions_expr(
                *scrutinee, role_impls,
            )),
            arms: arms
                .into_iter()
                .map(|arm| normalize_semantic_cast_coercions_match_arm(arm, role_impls))
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(|stmt| normalize_semantic_cast_coercions_stmt(stmt, role_impls))
                .collect(),
            tail: tail
                .map(|tail| Box::new(normalize_semantic_cast_coercions_expr(*tail, role_impls))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(normalize_semantic_cast_coercions_expr(*body, role_impls)),
            arms: arms
                .into_iter()
                .map(|arm| normalize_semantic_cast_coercions_handle_arm(arm, role_impls))
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(normalize_semantic_cast_coercions_expr(*expr, role_impls)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value,
            expr: Box::new(normalize_semantic_cast_coercions_expr(*expr, role_impls)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(normalize_semantic_cast_coercions_expr(*body, role_impls)),
        },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(normalize_semantic_cast_coercions_expr(*thunk, role_impls)),
        },
        ExprKind::Coerce { from, to, expr } => {
            let expr = normalize_semantic_cast_coercions_expr(*expr, role_impls);
            let actual = precise_coerce_actual_type(&expr, &from);
            if actual == to {
                return expr;
            }
            if let Some(steps) = semantic_cast_path(role_impls, &actual, &to) {
                return apply_semantic_cast_path(expr, steps);
            }
            ExprKind::Coerce {
                from: actual,
                to,
                expr: Box::new(expr),
            }
        }
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(normalize_semantic_cast_coercions_expr(*expr, role_impls)),
        },
        ExprKind::Var(path) => ExprKind::Var(path),
        ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit),
        ExprKind::PeekId => ExprKind::PeekId,
        ExprKind::FindId { id } => ExprKind::FindId { id },
    };
    Expr::typed(kind, ty)
}

fn precise_coerce_actual_type(expr: &Expr, fallback: &typed_ir::Type) -> typed_ir::Type {
    let actual = runtime_core_type(&expr.ty);
    if implicit_cast_endpoint_is_open(&actual) {
        fallback.clone()
    } else {
        actual
    }
}

fn normalize_semantic_cast_coercions_stmt(
    stmt: Stmt,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern: normalize_semantic_cast_coercions_pattern(pattern, role_impls),
            value: normalize_semantic_cast_coercions_expr(value, role_impls),
        },
        Stmt::Expr(expr) => Stmt::Expr(normalize_semantic_cast_coercions_expr(expr, role_impls)),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: normalize_semantic_cast_coercions_expr(body, role_impls),
        },
    }
}

fn normalize_semantic_cast_coercions_match_arm(
    arm: MatchArm,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> MatchArm {
    MatchArm {
        pattern: normalize_semantic_cast_coercions_pattern(arm.pattern, role_impls),
        guard: arm
            .guard
            .map(|guard| normalize_semantic_cast_coercions_expr(guard, role_impls)),
        body: normalize_semantic_cast_coercions_expr(arm.body, role_impls),
    }
}

fn normalize_semantic_cast_coercions_handle_arm(
    arm: HandleArm,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> HandleArm {
    HandleArm {
        effect: arm.effect,
        payload: normalize_semantic_cast_coercions_pattern(arm.payload, role_impls),
        resume: arm.resume,
        guard: arm
            .guard
            .map(|guard| normalize_semantic_cast_coercions_expr(guard, role_impls)),
        body: normalize_semantic_cast_coercions_expr(arm.body, role_impls),
    }
}

fn normalize_semantic_cast_coercions_pattern(
    pattern: Pattern,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> Pattern {
    match pattern {
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(|item| normalize_semantic_cast_coercions_pattern(item, role_impls))
                .collect(),
            ty,
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(|item| normalize_semantic_cast_coercions_pattern(item, role_impls))
                .collect(),
            spread: spread.map(|spread| {
                Box::new(normalize_semantic_cast_coercions_pattern(
                    *spread, role_impls,
                ))
            }),
            suffix: suffix
                .into_iter()
                .map(|item| normalize_semantic_cast_coercions_pattern(item, role_impls))
                .collect(),
            ty,
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordPatternField {
                    name: field.name,
                    pattern: normalize_semantic_cast_coercions_pattern(field.pattern, role_impls),
                    default: field
                        .default
                        .map(|expr| normalize_semantic_cast_coercions_expr(expr, role_impls)),
                })
                .collect(),
            spread: spread.map(|spread| {
                normalize_semantic_cast_coercions_record_pattern_spread(spread, role_impls)
            }),
            ty,
        },
        Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| {
                Box::new(normalize_semantic_cast_coercions_pattern(
                    *value, role_impls,
                ))
            }),
            ty,
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(normalize_semantic_cast_coercions_pattern(*left, role_impls)),
            right: Box::new(normalize_semantic_cast_coercions_pattern(
                *right, role_impls,
            )),
            ty,
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(normalize_semantic_cast_coercions_pattern(
                *pattern, role_impls,
            )),
            name,
            ty,
        },
        Pattern::Wildcard { ty } => Pattern::Wildcard { ty },
        Pattern::Bind { name, ty } => Pattern::Bind { name, ty },
        Pattern::Lit { lit, ty } => Pattern::Lit { lit, ty },
    }
}

fn normalize_semantic_cast_coercions_record_spread(
    spread: RecordSpreadExpr,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> RecordSpreadExpr {
    match spread {
        RecordSpreadExpr::Head(expr) => RecordSpreadExpr::Head(Box::new(
            normalize_semantic_cast_coercions_expr(*expr, role_impls),
        )),
        RecordSpreadExpr::Tail(expr) => RecordSpreadExpr::Tail(Box::new(
            normalize_semantic_cast_coercions_expr(*expr, role_impls),
        )),
    }
}

fn normalize_semantic_cast_coercions_record_pattern_spread(
    spread: RecordSpreadPattern,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> RecordSpreadPattern {
    match spread {
        RecordSpreadPattern::Head(pattern) => RecordSpreadPattern::Head(Box::new(
            normalize_semantic_cast_coercions_pattern(*pattern, role_impls),
        )),
        RecordSpreadPattern::Tail(pattern) => RecordSpreadPattern::Tail(Box::new(
            normalize_semantic_cast_coercions_pattern(*pattern, role_impls),
        )),
    }
}

#[derive(Clone)]
struct SemanticCastStep {
    method: typed_ir::Path,
    from: typed_ir::Type,
    to: typed_ir::Type,
}

fn apply_semantic_cast_path(expr: Expr, steps: Vec<SemanticCastStep>) -> Expr {
    steps.into_iter().fold(expr, |value, step| {
        let callee_ty = RuntimeType::fun(
            RuntimeType::core(step.from.clone()),
            RuntimeType::core(step.to.clone()),
        );
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(ExprKind::Var(step.method), callee_ty)),
                arg: Box::new(value),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::core(step.to),
        )
    })
}

fn semantic_cast_path(
    role_impls: &[typed_ir::RoleImplGraphNode],
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
) -> Option<Vec<SemanticCastStep>> {
    if !semantic_cast_target_needs_apply(expected) {
        return None;
    }
    if primitive_runtime_coercion_covers(actual, expected) {
        return None;
    }
    if implicit_cast_endpoint_is_open(actual) || implicit_cast_endpoint_is_open(expected) {
        return None;
    }
    if type_compatible(actual, expected) && type_compatible(expected, actual) {
        return None;
    }
    let edges = semantic_cast_edges(role_impls);
    let mut seen = Vec::new();
    let mut queue = VecDeque::from([(actual.clone(), Vec::new())]);

    while let Some((current, path)) = queue.pop_front() {
        if seen.iter().any(|seen| same_core_type(seen, &current)) {
            continue;
        }
        seen.push(current.clone());
        for edge in &edges {
            if !same_core_type(&edge.from, &current) {
                continue;
            }
            let mut next_path = path.clone();
            next_path.push(edge.clone());
            if same_core_type(&edge.to, expected) {
                return Some(next_path);
            }
            queue.push_back((edge.to.clone(), next_path));
        }
    }
    None
}

fn semantic_cast_edges(role_impls: &[typed_ir::RoleImplGraphNode]) -> Vec<SemanticCastStep> {
    role_impls
        .iter()
        .filter(|role_impl| {
            role_impl
                .role
                .segments
                .last()
                .is_some_and(|name| name.0 == "Cast")
        })
        .filter_map(|role_impl| {
            let input = role_impl.inputs.first()?;
            let input = choose_bounds_type(input, BoundsChoice::ValidationEvidence)?;
            let target = role_impl
                .associated_types
                .iter()
                .find(|associated| associated.name.0 == "to")?;
            let target = choose_bounds_type(&target.value, BoundsChoice::ValidationEvidence)?;
            let method = role_impl
                .members
                .iter()
                .find(|member| member.name.0 == "cast")
                .map(|member| member.value.clone())?;
            Some(SemanticCastStep {
                method,
                from: input,
                to: target,
            })
        })
        .collect()
}

fn same_core_type(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    type_compatible(left, right) && type_compatible(right, left)
}

fn implicit_cast_endpoint_is_open(ty: &typed_ir::Type) -> bool {
    core_type_is_imprecise_runtime_slot(ty)
        || core_type_has_vars(ty)
        || core_type_contains_unknown(ty)
}

fn semantic_cast_target_needs_apply(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Named { path, args }
            if args.is_empty()
                && path
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "float")
    )
}

fn primitive_runtime_coercion_covers(actual: &typed_ir::Type, expected: &typed_ir::Type) -> bool {
    is_bare_named_type(actual, "int") && is_bare_named_type(expected, "float")
}

fn is_bare_named_type(ty: &typed_ir::Type, name: &str) -> bool {
    matches!(
        ty,
        typed_ir::Type::Named { path, args }
            if args.is_empty()
                && path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.0 == name)
    )
}

fn is_synthetic_local_act_helper_path(path: &typed_ir::Path) -> bool {
    path.segments
        .first()
        .is_some_and(|segment| segment.0.starts_with('&') && segment.0.contains('#'))
}

fn close_unbound_effect_vars(binding: &mut Binding) {
    let mut effect_vars = BTreeSet::new();
    collect_expr_effect_vars(&binding.body, &mut effect_vars);
    let mut non_effect_vars = BTreeSet::new();
    collect_expr_non_effect_vars(&binding.body, &mut non_effect_vars);
    collect_core_non_effect_vars(&binding.scheme.body, &mut non_effect_vars);
    for requirement in &binding.scheme.requirements {
        for arg in &requirement.args {
            match arg {
                typed_ir::RoleRequirementArg::Input(bounds)
                | typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    collect_bounds_non_effect_vars(bounds, &mut non_effect_vars);
                }
            }
        }
    }
    let substitutions = effect_vars
        .into_iter()
        .filter(|var| !binding.type_params.contains(var) && !non_effect_vars.contains(var))
        .map(|var| (var, typed_ir::Type::Never))
        .collect::<BTreeMap<_, _>>();
    if substitutions.is_empty() {
        return;
    }
    *binding = substitute_binding(binding.clone(), &substitutions);
    refresh_binding_type_params(binding);
}

pub(super) fn collect_binding_type_params(
    binding: &Binding,
    params: &mut BTreeSet<typed_ir::TypeVar>,
) {
    collect_core_type_vars(&binding.scheme.body, params);
    for requirement in &binding.scheme.requirements {
        collect_role_requirement_vars(requirement, params);
    }
    collect_hir_type_vars(&binding.body.ty, params);
}

fn collect_type_bounds_effect_vars(
    bounds: &typed_ir::TypeBounds,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_effect_position_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_effect_position_vars(upper, vars);
    }
}

fn collect_hir_effect_vars(ty: &RuntimeType, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        RuntimeType::Unknown => {}
        RuntimeType::Core(ty) => collect_effect_position_vars(ty, vars),
        RuntimeType::Fun { param, ret } => {
            collect_hir_effect_vars(param, vars);
            collect_hir_effect_vars(ret, vars);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_effect_vars(effect, vars);
            collect_hir_effect_vars(value, vars);
        }
    }
}

fn collect_expr_effect_vars(expr: &Expr, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    collect_hir_effect_vars(&expr.ty, vars);
    match &expr.kind {
        ExprKind::Lambda { body, .. } => collect_expr_effect_vars(body, vars),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_effect_vars(callee, vars);
            collect_expr_effect_vars(arg, vars);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_effect_vars(cond, vars);
            collect_expr_effect_vars(then_branch, vars);
            collect_expr_effect_vars(else_branch, vars);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_effect_vars(item, vars);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_effect_vars(&field.value, vars);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_effect_vars(expr, vars);
                    }
                }
            }
        }
        ExprKind::Variant {
            value: Some(value), ..
        }
        | ExprKind::Select { base: value, .. }
        | ExprKind::BindHere { expr: value }
        | ExprKind::LocalPushId { body: value, .. }
        | ExprKind::Pack { expr: value, .. } => collect_expr_effect_vars(value, vars),
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            collect_effect_vars(effect, vars);
            collect_hir_effect_vars(value, vars);
            collect_expr_effect_vars(expr, vars);
        }
        ExprKind::AddId { allowed, thunk, .. } => {
            collect_effect_vars(allowed, vars);
            collect_expr_effect_vars(thunk, vars);
        }
        ExprKind::Coerce { from, to, expr } => {
            collect_effect_position_vars(from, vars);
            collect_effect_position_vars(to, vars);
            collect_expr_effect_vars(expr, vars);
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_effect_vars(scrutinee, vars);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_effect_vars(guard, vars);
                }
                collect_expr_effect_vars(&arm.body, vars);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_effect_vars(stmt, vars);
            }
            if let Some(tail) = tail {
                collect_expr_effect_vars(tail, vars);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_effect_vars(body, vars);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_effect_vars(guard, vars);
                }
                collect_expr_effect_vars(&arm.body, vars);
            }
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_stmt_effect_vars(stmt: &Stmt, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_effect_vars(value, vars);
        }
    }
}

fn collect_expr_non_effect_vars(expr: &Expr, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    collect_hir_non_effect_vars(&expr.ty, vars);
    match &expr.kind {
        ExprKind::Lambda { body, .. } => collect_expr_non_effect_vars(body, vars),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_non_effect_vars(callee, vars);
            collect_expr_non_effect_vars(arg, vars);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_non_effect_vars(cond, vars);
            collect_expr_non_effect_vars(then_branch, vars);
            collect_expr_non_effect_vars(else_branch, vars);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_non_effect_vars(item, vars);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_non_effect_vars(&field.value, vars);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_non_effect_vars(expr, vars);
                    }
                }
            }
        }
        ExprKind::Variant {
            value: Some(value), ..
        }
        | ExprKind::Select { base: value, .. }
        | ExprKind::BindHere { expr: value }
        | ExprKind::LocalPushId { body: value, .. }
        | ExprKind::Pack { expr: value, .. } => collect_expr_non_effect_vars(value, vars),
        ExprKind::Thunk { value, expr, .. } => {
            collect_hir_non_effect_vars(value, vars);
            collect_expr_non_effect_vars(expr, vars);
        }
        ExprKind::AddId { thunk, .. } => collect_expr_non_effect_vars(thunk, vars),
        ExprKind::Coerce { from, to, expr } => {
            collect_core_non_effect_vars(from, vars);
            collect_core_non_effect_vars(to, vars);
            collect_expr_non_effect_vars(expr, vars);
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_non_effect_vars(scrutinee, vars);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_non_effect_vars(guard, vars);
                }
                collect_expr_non_effect_vars(&arm.body, vars);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_non_effect_vars(stmt, vars);
            }
            if let Some(tail) = tail {
                collect_expr_non_effect_vars(tail, vars);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_non_effect_vars(body, vars);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_non_effect_vars(guard, vars);
                }
                collect_expr_non_effect_vars(&arm.body, vars);
            }
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_stmt_non_effect_vars(stmt: &Stmt, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match stmt {
        Stmt::Let { pattern, value } => {
            collect_pattern_non_effect_vars(pattern, vars);
            collect_expr_non_effect_vars(value, vars);
        }
        Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_non_effect_vars(value, vars);
        }
    }
}

fn collect_pattern_non_effect_vars(pattern: &Pattern, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    collect_hir_non_effect_vars(&pattern_type(pattern), vars);
}

fn collect_hir_non_effect_vars(ty: &RuntimeType, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        RuntimeType::Unknown => {}
        RuntimeType::Core(ty) => collect_core_non_effect_vars(ty, vars),
        RuntimeType::Fun { param, ret } => {
            collect_hir_non_effect_vars(param, vars);
            collect_hir_non_effect_vars(ret, vars);
        }
        RuntimeType::Thunk { value, .. } => collect_hir_non_effect_vars(value, vars),
    }
}

fn collect_bounds_non_effect_vars(
    bounds: &typed_ir::TypeBounds,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_non_effect_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_non_effect_vars(upper, vars);
    }
}

fn collect_core_non_effect_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Fun { param, ret, .. } => {
            collect_core_non_effect_vars(param, vars);
            collect_core_non_effect_vars(ret, vars);
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    typed_ir::TypeArg::Type(ty) => collect_core_non_effect_vars(ty, vars),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        collect_bounds_non_effect_vars(bounds, vars);
                    }
                }
            }
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_core_non_effect_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_non_effect_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_core_non_effect_vars(ty, vars);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_core_non_effect_vars(payload, vars);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_core_non_effect_vars(tail, vars);
            }
        }
        typed_ir::Type::Recursive { body, .. } => collect_core_non_effect_vars(body, vars),
        typed_ir::Type::Row { .. }
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => {}
    }
}

pub(super) fn collect_role_requirement_vars(
    requirement: &typed_ir::RoleRequirement,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    for arg in &requirement.args {
        match arg {
            typed_ir::RoleRequirementArg::Input(bounds)
            | typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                collect_type_bounds_vars(bounds, vars);
            }
        }
    }
}

pub(super) fn collect_type_bounds_vars(
    bounds: &typed_ir::TypeBounds,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_type_vars(upper, vars);
    }
}

pub(super) fn collect_effect_position_vars(
    ty: &typed_ir::Type,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_effect_vars(param_effect, vars);
            collect_effect_vars(ret_effect, vars);
            collect_effect_position_vars(param, vars);
            collect_effect_position_vars(ret, vars);
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    typed_ir::TypeArg::Type(ty) => collect_effect_position_vars(ty, vars),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        collect_type_bounds_effect_vars(bounds, vars);
                    }
                }
            }
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_position_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_effect_position_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_effect_position_vars(ty, vars);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_effect_position_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_effect_position_vars(tail, vars);
            }
        }
        typed_ir::Type::Recursive { body, .. } => collect_effect_position_vars(body, vars),
        typed_ir::Type::Row { .. }
        | typed_ir::Type::Unknown
        | typed_ir::Type::Var(_)
        | typed_ir::Type::Never
        | typed_ir::Type::Any => {}
    }
}

pub(super) fn collect_effect_vars(effect: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match effect {
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_vars(item, vars);
            }
            collect_effect_vars(tail, vars);
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_vars(item, vars);
            }
        }
        typed_ir::Type::Recursive { body, .. } => collect_effect_vars(body, vars),
        typed_ir::Type::Named { .. }
        | typed_ir::Type::Fun { .. }
        | typed_ir::Type::Tuple(_)
        | typed_ir::Type::Record(_)
        | typed_ir::Type::Variant(_)
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_cast_coercion_is_reachable_before_prune() {
        let frac = named_type(&["std", "frac", "frac"]);
        let float = named_type(&["float"]);
        let value_path = path(&["local", "value"]);
        let cast_path = path(&["std", "prelude", "&cast#0", "cast"]);
        let cast_ty = typed_ir::Type::Fun {
            param: Box::new(frac.clone()),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(float.clone()),
        };
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: vec![
                Binding {
                    name: value_path.clone(),
                    type_params: Vec::new(),
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: frac.clone(),
                    },
                    body: Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Unit),
                        RuntimeType::core(frac.clone()),
                    ),
                },
                Binding {
                    name: cast_path.clone(),
                    type_params: Vec::new(),
                    scheme: typed_ir::Scheme {
                        requirements: Vec::new(),
                        body: cast_ty.clone(),
                    },
                    body: Expr::typed(
                        ExprKind::Lambda {
                            param: typed_ir::Name("x".to_string()),
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(Expr::typed(
                                ExprKind::Lit(typed_ir::Lit::Float("0.0".to_string())),
                                RuntimeType::core(float.clone()),
                            )),
                        },
                        RuntimeType::core(cast_ty),
                    ),
                },
            ],
            root_exprs: vec![Expr::typed(
                ExprKind::Coerce {
                    from: frac.clone(),
                    to: float.clone(),
                    expr: Box::new(Expr::typed(
                        ExprKind::Var(value_path),
                        RuntimeType::core(frac.clone()),
                    )),
                },
                RuntimeType::core(float.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: vec![typed_ir::RoleImplGraphNode {
                role: path(&["std", "prelude", "Cast"]),
                inputs: vec![typed_ir::TypeBounds::exact(frac)],
                associated_types: vec![typed_ir::RecordField {
                    name: typed_ir::Name("to".to_string()),
                    value: typed_ir::TypeBounds::exact(float),
                    optional: false,
                }],
                members: vec![typed_ir::RecordField {
                    name: typed_ir::Name("cast".to_string()),
                    value: cast_path.clone(),
                    optional: false,
                }],
            }],
        };

        let module = prune_unreachable_bindings(normalize_semantic_cast_coercions(module));

        assert!(
            module
                .bindings
                .iter()
                .any(|binding| binding.name == cast_path)
        );
        let ExprKind::Apply { callee, .. } = &module.root_exprs[0].kind else {
            panic!("semantic Cast coercion should become an apply before pruning");
        };
        assert!(matches!(&callee.kind, ExprKind::Var(path) if path == &cast_path));
    }

    #[test]
    fn semantic_cast_coercion_uses_inner_runtime_type_when_from_is_stale() {
        let frac = named_type(&["std", "frac", "frac"]);
        let float = named_type(&["float"]);
        let root = Expr::typed(
            ExprKind::Coerce {
                from: frac,
                to: float.clone(),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Float("1.0".to_string())),
                    RuntimeType::core(float.clone()),
                )),
            },
            RuntimeType::core(float),
        );
        let module = normalize_semantic_cast_coercions(Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        });

        assert!(matches!(module.root_exprs[0].kind, ExprKind::Lit(_)));
    }

    #[test]
    fn semantic_cast_coercion_leaves_primitive_int_to_float_runtime_coerce() {
        let int = named_type(&["int"]);
        let frac = named_type(&["std", "frac", "frac"]);
        let float = named_type(&["float"]);
        let root = Expr::typed(
            ExprKind::Coerce {
                from: int.clone(),
                to: float.clone(),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("3".to_string())),
                    RuntimeType::core(int.clone()),
                )),
            },
            RuntimeType::core(float.clone()),
        );
        let module = normalize_semantic_cast_coercions(Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
            role_impls: vec![
                cast_role_impl(int.clone(), frac.clone(), path(&["cast", "int_to_frac"])),
                cast_role_impl(frac, float.clone(), path(&["cast", "frac_to_float"])),
            ],
        });

        let ExprKind::Coerce { from, to, .. } = &module.root_exprs[0].kind else {
            panic!("primitive int -> float should stay a runtime coercion");
        };
        assert_eq!(from, &int);
        assert_eq!(to, &float);
    }

    fn cast_role_impl(
        from: typed_ir::Type,
        to: typed_ir::Type,
        method: typed_ir::Path,
    ) -> typed_ir::RoleImplGraphNode {
        typed_ir::RoleImplGraphNode {
            role: path(&["std", "prelude", "Cast"]),
            inputs: vec![typed_ir::TypeBounds::exact(from)],
            associated_types: vec![typed_ir::RecordField {
                name: typed_ir::Name("to".to_string()),
                value: typed_ir::TypeBounds::exact(to),
                optional: false,
            }],
            members: vec![typed_ir::RecordField {
                name: typed_ir::Name("cast".to_string()),
                value: method,
                optional: false,
            }],
        }
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).to_string()))
                .collect(),
        )
    }

    fn named_type(segments: &[&str]) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(segments),
            args: Vec::new(),
        }
    }
}
