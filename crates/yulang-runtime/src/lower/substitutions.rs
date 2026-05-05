use super::*;

pub(super) fn principal_module_type_vars(
    module: &core_ir::PrincipalModule,
) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    for binding in &module.bindings {
        collect_type_vars(&binding.scheme.body, &mut vars);
        collect_expr_type_vars(&binding.body, &mut vars);
        for requirement in &binding.scheme.requirements {
            for arg in &requirement.args {
                match arg {
                    core_ir::RoleRequirementArg::Input(bounds)
                    | core_ir::RoleRequirementArg::Associated { bounds, .. } => {
                        collect_type_bounds_vars(bounds, &mut vars);
                    }
                }
            }
        }
    }
    for expr in &module.root_exprs {
        collect_expr_type_vars(expr, &mut vars);
    }
    vars
}

fn collect_expr_type_vars(expr: &core_ir::Expr, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match expr {
        core_ir::Expr::Lit(_) | core_ir::Expr::Var(_) | core_ir::Expr::PrimitiveOp(_) => {}
        core_ir::Expr::Lambda { body, .. } => collect_expr_type_vars(body, vars),
        core_ir::Expr::Apply {
            callee,
            arg,
            evidence,
        } => {
            collect_expr_type_vars(callee, vars);
            collect_expr_type_vars(arg, vars);
            if let Some(evidence) = evidence {
                collect_apply_evidence_type_vars(evidence, vars);
            }
        }
        core_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            collect_expr_type_vars(cond, vars);
            collect_expr_type_vars(then_branch, vars);
            collect_expr_type_vars(else_branch, vars);
            if let Some(evidence) = evidence {
                collect_type_bounds_vars(&evidence.result, vars);
            }
        }
        core_ir::Expr::Tuple(items) => {
            for item in items {
                collect_expr_type_vars(item, vars);
            }
        }
        core_ir::Expr::Record { fields, spread } => {
            for field in fields {
                collect_expr_type_vars(&field.value, vars);
            }
            if let Some(spread) = spread {
                collect_record_spread_expr_type_vars(spread, vars);
            }
        }
        core_ir::Expr::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_type_vars(value, vars);
            }
        }
        core_ir::Expr::Select { base, .. } => collect_expr_type_vars(base, vars),
        core_ir::Expr::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            collect_expr_type_vars(scrutinee, vars);
            if let Some(evidence) = evidence {
                collect_type_bounds_vars(&evidence.result, vars);
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_type_vars(guard, vars);
                }
                collect_expr_type_vars(&arm.body, vars);
            }
        }
        core_ir::Expr::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_type_vars(stmt, vars);
            }
            if let Some(tail) = tail {
                collect_expr_type_vars(tail, vars);
            }
        }
        core_ir::Expr::Handle {
            body,
            arms,
            evidence,
        } => {
            collect_expr_type_vars(body, vars);
            if let Some(evidence) = evidence {
                collect_type_bounds_vars(&evidence.result, vars);
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_type_vars(guard, vars);
                }
                collect_expr_type_vars(&arm.body, vars);
            }
        }
        core_ir::Expr::Coerce { expr, evidence } => {
            collect_expr_type_vars(expr, vars);
            if let Some(evidence) = evidence {
                collect_type_bounds_vars(&evidence.actual, vars);
                collect_type_bounds_vars(&evidence.expected, vars);
            }
        }
        core_ir::Expr::Pack { expr, .. } => {
            collect_expr_type_vars(expr, vars);
        }
    }
}

fn collect_stmt_type_vars(stmt: &core_ir::Stmt, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match stmt {
        core_ir::Stmt::Let { value, .. } => collect_expr_type_vars(value, vars),
        core_ir::Stmt::Expr(expr) => collect_expr_type_vars(expr, vars),
        core_ir::Stmt::Module { body, .. } => collect_expr_type_vars(body, vars),
    }
}

fn collect_record_spread_expr_type_vars(
    spread: &core_ir::RecordSpreadExpr,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    match spread {
        core_ir::RecordSpreadExpr::Head(expr) | core_ir::RecordSpreadExpr::Tail(expr) => {
            collect_expr_type_vars(expr, vars);
        }
    }
}

fn collect_apply_evidence_type_vars(
    evidence: &core_ir::ApplyEvidence,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    collect_type_bounds_vars(&evidence.callee, vars);
    if let Some(expected) = &evidence.expected_callee {
        collect_type_bounds_vars(expected, vars);
    }
    collect_type_bounds_vars(&evidence.arg, vars);
    if let Some(expected) = &evidence.expected_arg {
        collect_type_bounds_vars(expected, vars);
    }
    collect_type_bounds_vars(&evidence.result, vars);
    if let Some(principal) = &evidence.principal_callee {
        collect_type_vars(principal, vars);
    }
    for substitution in &evidence.substitutions {
        vars.insert(substitution.var.clone());
        collect_type_vars(&substitution.ty, vars);
    }
    for candidate in &evidence.substitution_candidates {
        vars.insert(candidate.var.clone());
        collect_type_vars(&candidate.ty, vars);
    }
    if let Some(plan) = &evidence.principal_elaboration {
        collect_principal_elaboration_plan_type_vars(plan, vars);
    }
}

fn collect_principal_elaboration_plan_type_vars(
    plan: &core_ir::PrincipalElaborationPlan,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    collect_type_vars(&plan.principal_callee, vars);
    for substitution in &plan.substitutions {
        vars.insert(substitution.var.clone());
        collect_type_vars(&substitution.ty, vars);
    }
    for arg in &plan.args {
        collect_type_bounds_vars(&arg.intrinsic, vars);
        if let Some(contextual) = &arg.contextual {
            collect_type_bounds_vars(contextual, vars);
        }
        if let Some(expected) = &arg.expected_runtime {
            collect_type_vars(expected, vars);
        }
    }
    collect_type_bounds_vars(&plan.result.intrinsic, vars);
    if let Some(contextual) = &plan.result.contextual {
        collect_type_bounds_vars(contextual, vars);
    }
    if let Some(expected) = &plan.result.expected_runtime {
        collect_type_vars(expected, vars);
    }
    for adapter in &plan.adapters {
        collect_type_vars(&adapter.actual, vars);
        collect_type_vars(&adapter.expected, vars);
    }
    for reason in &plan.incomplete_reasons {
        match reason {
            core_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(var)
            | core_ir::PrincipalElaborationIncompleteReason::ConflictingSubstitution(var)
            | core_ir::PrincipalElaborationIncompleteReason::OpenCandidate(var) => {
                vars.insert(var.clone());
            }
            _ => {}
        }
    }
}

fn collect_type_bounds_vars(bounds: &core_ir::TypeBounds, vars: &mut BTreeSet<core_ir::TypeVar>) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_type_vars(upper, vars);
    }
}

pub(super) fn infer_hir_type_substitutions(
    template: &RuntimeType,
    actual: &RuntimeType,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    match (template, actual) {
        (RuntimeType::Core(template), RuntimeType::Core(actual)) => {
            infer_type_substitutions(template, actual, params, substitutions);
        }
        (
            RuntimeType::Fun {
                param: template_param,
                ret: template_ret,
            },
            RuntimeType::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => {
            infer_hir_type_substitutions(template_param, actual_param, params, substitutions);
            infer_hir_type_substitutions(template_ret, actual_ret, params, substitutions);
        }
        (
            RuntimeType::Thunk {
                effect: template_effect,
                value: template_value,
            },
            RuntimeType::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => {
            infer_type_substitutions(template_effect, actual_effect, params, substitutions);
            infer_hir_type_substitutions(template_value, actual_value, params, substitutions);
        }
        (RuntimeType::Thunk { effect, value }, actual) => {
            infer_type_substitutions(effect, &core_ir::Type::Never, params, substitutions);
            infer_hir_type_substitutions(value, actual, params, substitutions);
        }
        _ => {}
    }
}

pub(super) fn infer_role_requirement_substitutions(
    requirements: &[core_ir::RoleRequirement],
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    for requirement in requirements {
        let inputs = requirement
            .args
            .iter()
            .filter_map(|arg| match arg {
                core_ir::RoleRequirementArg::Input(bounds) => {
                    substituted_requirement_bound(bounds, substitutions)
                }
                core_ir::RoleRequirementArg::Associated { .. } => None,
            })
            .collect::<Vec<_>>();
        for arg in &requirement.args {
            let core_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            let Some(resolved) = resolve_associated_requirement(requirement, name, &inputs) else {
                continue;
            };
            let Some(template) = substituted_requirement_bound(bounds, substitutions) else {
                continue;
            };
            infer_type_substitutions(&template, &resolved, params, substitutions);
        }
    }
}

pub(super) fn substituted_requirement_bound(
    bounds: &core_ir::TypeBounds,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<core_ir::Type> {
    choose_bounds_type(bounds, BoundsChoice::TirEvidence)
        .map(|ty| substitute_type(&ty, substitutions))
}

pub(super) fn resolve_associated_requirement(
    requirement: &core_ir::RoleRequirement,
    name: &core_ir::Name,
    inputs: &[core_ir::Type],
) -> Option<core_ir::Type> {
    let role = requirement.role.segments.last()?;
    match (role.0.as_str(), name.0.as_str(), inputs) {
        ("Fold", "item", [container]) => list_item_type(container),
        ("Index", "value", [container, key]) => index_value_type(container, key),
        _ => None,
    }
}

pub(super) fn visible_apply_result_type(
    callee_ty: &core_ir::Type,
    arg_ty: Option<&core_ir::Type>,
) -> Option<core_ir::Type> {
    let core_ir::Type::Fun { param, ret, .. } = callee_ty else {
        return None;
    };
    let Some(arg_ty) = arg_ty else {
        return Some((**ret).clone());
    };
    let mut params = BTreeSet::new();
    collect_type_vars(callee_ty, &mut params);
    let mut substitutions = BTreeMap::new();
    infer_type_substitutions(param, arg_ty, &params, &mut substitutions);
    Some(substitute_type(ret, &substitutions))
}

pub(super) fn principal_hir_type_params(ty: &RuntimeType) -> Vec<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_hir_type_vars(ty, &mut vars);
    vars.retain(|var| !is_anonymous_type_var(var));
    vars.into_iter().collect()
}

pub(super) fn refine_lambda_hir_type(expected: &RuntimeType, actual: &RuntimeType) -> RuntimeType {
    match (expected, actual) {
        (
            RuntimeType::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            RuntimeType::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => RuntimeType::fun(
            refine_lambda_param_type(expected_param, actual_param),
            refine_lambda_ret_type(expected_ret, actual_ret),
        ),
        _ => refine_anonymous_hir_type(expected, actual),
    }
}

pub(super) fn refine_lambda_param_type(
    expected: &RuntimeType,
    actual: &RuntimeType,
) -> RuntimeType {
    match (expected, actual) {
        (
            RuntimeType::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
            RuntimeType::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => RuntimeType::thunk(
            refine_effect_slot(expected_effect, actual_effect),
            refine_lambda_param_type(expected_value, actual_value),
        ),
        (expected @ RuntimeType::Thunk { .. }, actual)
            if hir_type_compatible(expected, actual)
                || hir_type_compatible(value_hir_type(expected), actual) =>
        {
            expected.clone()
        }
        (expected, actual @ RuntimeType::Thunk { value, .. })
            if hir_type_compatible(expected, value) =>
        {
            actual.clone()
        }
        _ => refine_anonymous_hir_type(expected, actual),
    }
}

pub(super) fn refine_lambda_ret_type(expected: &RuntimeType, actual: &RuntimeType) -> RuntimeType {
    if matches!(
        (expected, actual),
        (RuntimeType::Fun { .. }, RuntimeType::Fun { .. })
    ) {
        return refine_lambda_hir_type(expected, actual);
    }
    if runtime_type_is_imprecise_runtime_slot(expected)
        && !runtime_type_is_imprecise_runtime_slot(actual)
    {
        return actual.clone();
    }
    refine_anonymous_hir_type(expected, actual)
}

pub(super) fn refine_effect_slot(
    expected: &core_ir::Type,
    actual: &core_ir::Type,
) -> core_ir::Type {
    if core_type_is_imprecise_runtime_slot(expected) && !core_type_is_imprecise_runtime_slot(actual)
    {
        return actual.clone();
    }
    refine_anonymous_type(expected, actual)
}

pub(super) fn hir_type_has_type_vars(ty: &RuntimeType) -> bool {
    let mut vars = BTreeSet::new();
    collect_hir_type_vars(ty, &mut vars);
    !vars.is_empty()
}

pub(super) fn refine_anonymous_hir_type(
    expected: &RuntimeType,
    actual: &RuntimeType,
) -> RuntimeType {
    match (expected, actual) {
        (RuntimeType::Core(expected), RuntimeType::Core(actual)) => {
            RuntimeType::core(refine_anonymous_type(expected, actual))
        }
        (
            RuntimeType::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            RuntimeType::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => RuntimeType::fun(
            refine_anonymous_hir_type(expected_param, actual_param),
            refine_anonymous_hir_type(expected_ret, actual_ret),
        ),
        (
            RuntimeType::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
            RuntimeType::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => RuntimeType::thunk(
            refine_anonymous_type(expected_effect, actual_effect),
            refine_anonymous_hir_type(expected_value, actual_value),
        ),
        (RuntimeType::Thunk { value, .. }, actual) if hir_type_compatible(value, actual) => {
            actual.clone()
        }
        _ => expected.clone(),
    }
}

pub(super) fn refine_anonymous_type(
    expected: &core_ir::Type,
    actual: &core_ir::Type,
) -> core_ir::Type {
    match (expected, actual) {
        (core_ir::Type::Var(var), actual) if is_anonymous_type_var(var) => actual.clone(),
        (
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                args: actual_args, ..
            },
        ) if args.len() == actual_args.len() => core_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .zip(actual_args)
                .map(|(arg, actual)| refine_anonymous_type_arg(arg, actual))
                .collect(),
        },
        (
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            core_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => core_ir::Type::Fun {
            param: Box::new(refine_anonymous_type(param, actual_param)),
            param_effect: Box::new(refine_anonymous_type(param_effect, actual_param_effect)),
            ret_effect: Box::new(refine_anonymous_type(ret_effect, actual_ret_effect)),
            ret: Box::new(refine_anonymous_type(ret, actual_ret)),
        },
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            core_ir::Type::Tuple(
                items
                    .iter()
                    .zip(actual_items)
                    .map(|(item, actual)| refine_anonymous_type(item, actual))
                    .collect(),
            )
        }
        (
            core_ir::Type::Row { items, tail },
            core_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) if items.len() == actual_items.len() => core_ir::Type::Row {
            items: items
                .iter()
                .zip(actual_items)
                .map(|(item, actual)| refine_anonymous_type(item, actual))
                .collect(),
            tail: Box::new(refine_anonymous_type(tail, actual_tail)),
        },
        (core_ir::Type::Recursive { var, body }, core_ir::Type::Recursive { body: actual, .. }) => {
            core_ir::Type::Recursive {
                var: var.clone(),
                body: Box::new(refine_anonymous_type(body, actual)),
            }
        }
        _ => expected.clone(),
    }
}

pub(super) fn refine_anonymous_type_arg(
    expected: &core_ir::TypeArg,
    actual: &core_ir::TypeArg,
) -> core_ir::TypeArg {
    match (expected, actual) {
        (core_ir::TypeArg::Type(expected), core_ir::TypeArg::Type(actual)) => {
            core_ir::TypeArg::Type(refine_anonymous_type(expected, actual))
        }
        _ => expected.clone(),
    }
}

pub(super) fn is_anonymous_type_var(var: &core_ir::TypeVar) -> bool {
    var.0 == "_"
}
