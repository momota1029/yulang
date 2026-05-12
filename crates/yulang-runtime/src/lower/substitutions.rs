use super::*;

pub(super) fn principal_module_type_vars(
    module: &typed_ir::PrincipalModule,
) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    for binding in &module.bindings {
        collect_type_vars(&binding.scheme.body, &mut vars);
        collect_expr_type_vars(&binding.body, &mut vars);
        for requirement in &binding.scheme.requirements {
            for arg in &requirement.args {
                match arg {
                    typed_ir::RoleRequirementArg::Input(bounds)
                    | typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
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

fn collect_expr_type_vars(expr: &typed_ir::Expr, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match expr {
        typed_ir::Expr::Lit(_) | typed_ir::Expr::Var(_) | typed_ir::Expr::PrimitiveOp(_) => {}
        typed_ir::Expr::Lambda { body, .. } => collect_expr_type_vars(body, vars),
        typed_ir::Expr::Apply {
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
        typed_ir::Expr::If {
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
        typed_ir::Expr::Tuple(items) => {
            for item in items {
                collect_expr_type_vars(item, vars);
            }
        }
        typed_ir::Expr::Record { fields, spread } => {
            for field in fields {
                collect_expr_type_vars(&field.value, vars);
            }
            if let Some(spread) = spread {
                collect_record_spread_expr_type_vars(spread, vars);
            }
        }
        typed_ir::Expr::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_type_vars(value, vars);
            }
        }
        typed_ir::Expr::Select { base, .. } => collect_expr_type_vars(base, vars),
        typed_ir::Expr::Match {
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
        typed_ir::Expr::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_type_vars(stmt, vars);
            }
            if let Some(tail) = tail {
                collect_expr_type_vars(tail, vars);
            }
        }
        typed_ir::Expr::Handle {
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
        typed_ir::Expr::Coerce { expr, evidence } => {
            collect_expr_type_vars(expr, vars);
            if let Some(evidence) = evidence {
                collect_type_bounds_vars(&evidence.actual, vars);
                collect_type_bounds_vars(&evidence.expected, vars);
            }
        }
        typed_ir::Expr::BindHere { expr } => {
            collect_expr_type_vars(expr, vars);
        }
        typed_ir::Expr::Pack { expr, .. } => {
            collect_expr_type_vars(expr, vars);
        }
    }
}

fn collect_stmt_type_vars(stmt: &typed_ir::Stmt, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match stmt {
        typed_ir::Stmt::Let { value, .. } => collect_expr_type_vars(value, vars),
        typed_ir::Stmt::Expr(expr) => collect_expr_type_vars(expr, vars),
        typed_ir::Stmt::Module { body, .. } => collect_expr_type_vars(body, vars),
    }
}

fn collect_record_spread_expr_type_vars(
    spread: &typed_ir::RecordSpreadExpr,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match spread {
        typed_ir::RecordSpreadExpr::Head(expr) | typed_ir::RecordSpreadExpr::Tail(expr) => {
            collect_expr_type_vars(expr, vars);
        }
    }
}

fn collect_apply_evidence_type_vars(
    evidence: &typed_ir::ApplyEvidence,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
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
    plan: &typed_ir::PrincipalElaborationPlan,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
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
            typed_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(var)
            | typed_ir::PrincipalElaborationIncompleteReason::ConflictingSubstitution(var)
            | typed_ir::PrincipalElaborationIncompleteReason::OpenCandidate(var) => {
                vars.insert(var.clone());
            }
            _ => {}
        }
    }
}

fn collect_type_bounds_vars(bounds: &typed_ir::TypeBounds, vars: &mut BTreeSet<typed_ir::TypeVar>) {
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
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
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
            infer_type_substitutions(effect, &typed_ir::Type::Never, params, substitutions);
            infer_hir_type_substitutions(value, actual, params, substitutions);
        }
        _ => {}
    }
}

pub(super) fn infer_role_requirement_substitutions(
    requirements: &[typed_ir::RoleRequirement],
    role_impls: &[typed_ir::RoleImplGraphNode],
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    for requirement in requirements {
        let inputs = requirement
            .args
            .iter()
            .filter_map(|arg| match arg {
                typed_ir::RoleRequirementArg::Input(bounds) => {
                    substituted_requirement_bound(bounds, substitutions)
                }
                typed_ir::RoleRequirementArg::Associated { .. } => None,
            })
            .collect::<Vec<_>>();
        for arg in &requirement.args {
            let typed_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            let Some(resolved) =
                resolve_associated_requirement(requirement, name, &inputs, role_impls)
            else {
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
    bounds: &typed_ir::TypeBounds,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Option<typed_ir::Type> {
    choose_bounds_type(bounds, BoundsChoice::TirEvidence)
        .map(|ty| substitute_type(&ty, substitutions))
}

pub(super) fn resolve_associated_requirement(
    requirement: &typed_ir::RoleRequirement,
    name: &typed_ir::Name,
    inputs: &[typed_ir::Type],
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> Option<typed_ir::Type> {
    let mut resolved = None;
    for role_impl in role_impls.iter().filter(|role_impl| {
        role_impl.role == requirement.role && role_impl.inputs.len() == inputs.len()
    }) {
        let Some(associated) = role_impl
            .associated_types
            .iter()
            .find(|associated| associated.name == *name)
        else {
            continue;
        };
        let Some(candidate) =
            project_role_impl_associated_type(&role_impl.inputs, inputs, &associated.value)
        else {
            continue;
        };
        match &resolved {
            Some(existing) if existing != &candidate => return None,
            Some(_) => {}
            None => resolved = Some(candidate),
        }
    }
    resolved
}

fn project_role_impl_associated_type(
    impl_inputs: &[typed_ir::TypeBounds],
    actual_inputs: &[typed_ir::Type],
    associated: &typed_ir::TypeBounds,
) -> Option<typed_ir::Type> {
    let mut impl_vars = BTreeSet::new();
    let templates = impl_inputs
        .iter()
        .map(|bounds| {
            let template = choose_bounds_type(bounds, BoundsChoice::TirEvidence)?;
            collect_type_vars(&template, &mut impl_vars);
            Some(template)
        })
        .collect::<Option<Vec<_>>>()?;
    collect_type_bounds_vars(associated, &mut impl_vars);
    let mut substitutions = BTreeMap::new();
    for (template, actual) in templates.iter().zip(actual_inputs) {
        infer_type_substitutions(template, actual, &impl_vars, &mut substitutions);
    }
    choose_bounds_type(
        &substitute_bounds(associated.clone(), &substitutions),
        BoundsChoice::TirEvidence,
    )
}

pub(super) fn visible_apply_result_type(
    callee_ty: &typed_ir::Type,
    arg_ty: Option<&typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let typed_ir::Type::Fun { param, ret, .. } = callee_ty else {
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

pub(super) fn principal_hir_type_params(ty: &RuntimeType) -> Vec<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_hir_type_vars(ty, &mut vars);
    vars.retain(|var| !is_anonymous_type_var(var));
    vars.into_iter().collect()
}

pub(super) fn principal_core_type_params(ty: &typed_ir::Type) -> Vec<typed_ir::TypeVar> {
    if !matches!(ty, typed_ir::Type::Fun { .. }) {
        return Vec::new();
    }
    let mut vars = BTreeSet::new();
    collect_core_variant_payload_type_vars(ty, &mut vars);
    vars.retain(|var| !is_anonymous_type_var(var));
    vars.into_iter().collect()
}

pub(super) fn principal_core_constructor_type_params(
    ty: &typed_ir::Type,
) -> Vec<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars.retain(|var| !is_anonymous_type_var(var));
    vars.into_iter().collect()
}

fn collect_core_variant_payload_type_vars(
    ty: &typed_ir::Type,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match ty {
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_)
        | typed_ir::Type::Named { .. }
        | typed_ir::Type::Row { .. } => {}
        typed_ir::Type::Fun { param, ret, .. } => {
            collect_core_variant_payload_type_vars(param, vars);
            collect_core_variant_payload_type_vars(ret, vars);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_core_variant_payload_type_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_variant_payload_type_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_core_variant_payload_type_vars(ty, vars);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_core_variant_payload_type_vars(tail, vars);
            }
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_core_variant_payload_type_vars(body, vars)
        }
    }
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
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> typed_ir::Type {
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
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> typed_ir::Type {
    match (expected, actual) {
        (typed_ir::Type::Var(var), actual) if is_anonymous_type_var(var) => actual.clone(),
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                args: actual_args, ..
            },
        ) if args.len() == actual_args.len() => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .zip(actual_args)
                .map(|(arg, actual)| refine_anonymous_type_arg(arg, actual))
                .collect(),
        },
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => typed_ir::Type::Fun {
            param: Box::new(refine_anonymous_type(param, actual_param)),
            param_effect: Box::new(refine_anonymous_type(param_effect, actual_param_effect)),
            ret_effect: Box::new(refine_anonymous_type(ret_effect, actual_ret_effect)),
            ret: Box::new(refine_anonymous_type(ret, actual_ret)),
        },
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            typed_ir::Type::Tuple(
                items
                    .iter()
                    .zip(actual_items)
                    .map(|(item, actual)| refine_anonymous_type(item, actual))
                    .collect(),
            )
        }
        (
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) if items.len() == actual_items.len() => typed_ir::Type::Row {
            items: items
                .iter()
                .zip(actual_items)
                .map(|(item, actual)| refine_anonymous_type(item, actual))
                .collect(),
            tail: Box::new(refine_anonymous_type(tail, actual_tail)),
        },
        (
            typed_ir::Type::Recursive { var, body },
            typed_ir::Type::Recursive { body: actual, .. },
        ) => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(refine_anonymous_type(body, actual)),
        },
        _ => expected.clone(),
    }
}

pub(super) fn refine_anonymous_type_arg(
    expected: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
) -> typed_ir::TypeArg {
    match (expected, actual) {
        (typed_ir::TypeArg::Type(expected), typed_ir::TypeArg::Type(actual)) => {
            typed_ir::TypeArg::Type(refine_anonymous_type(expected, actual))
        }
        _ => expected.clone(),
    }
}

pub(super) fn is_anonymous_type_var(var: &typed_ir::TypeVar) -> bool {
    var.0 == "_"
}
