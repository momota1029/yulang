use super::*;

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
    binding.scheme = typed_ir::Scheme {
        requirements: Vec::new(),
        body: core_value_type(&binding.body.ty),
    };
    refresh_binding_type_params(binding);
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

pub(super) fn substitute_type_instantiation(
    instantiation: TypeInstantiation,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> TypeInstantiation {
    TypeInstantiation {
        target: instantiation.target,
        args: instantiation
            .args
            .into_iter()
            .map(|arg| crate::ir::TypeSubstitution {
                var: arg.var,
                ty: substitute_type(&arg.ty, substitutions),
            })
            .collect(),
    }
}
