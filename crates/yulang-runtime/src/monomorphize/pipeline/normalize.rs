use super::*;

pub(super) fn normalize_hir_function_type(ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Core(core_ir::Type::Fun { .. }) => core_function_as_hir_type(&ty),
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            normalize_hir_function_type(*param),
            normalize_hir_function_type(*ret),
        ),
        RuntimeType::Thunk { effect, value } => {
            let value = normalize_hir_function_type(*value);
            let effect = specialize_sub_effect_payload_from_value(effect, &value);
            RuntimeType::thunk(effect, value)
        }
        other => other,
    }
}

pub(super) fn specialize_sub_effect_payload_from_value(
    effect: core_ir::Type,
    value: &RuntimeType,
) -> core_ir::Type {
    let payload = core_value_type(value);
    if core_type_has_vars(&payload) || matches!(payload, core_ir::Type::Any) {
        return effect;
    }
    specialize_sub_effect_payload(effect, &payload)
}

fn specialize_sub_effect_payload(effect: core_ir::Type, payload: &core_ir::Type) -> core_ir::Type {
    match effect {
        core_ir::Type::Named { path, args }
            if path.segments.last().is_some_and(|name| name.0 == "sub")
                && args.iter().any(type_arg_needs_mono_payload) =>
        {
            core_ir::Type::Named {
                path,
                args: vec![core_ir::TypeArg::Type(payload.clone())],
            }
        }
        core_ir::Type::Row { items, tail } => core_ir::Type::Row {
            items: items
                .into_iter()
                .map(|item| specialize_sub_effect_payload(item, payload))
                .collect(),
            tail: Box::new(specialize_sub_effect_payload(*tail, payload)),
        },
        core_ir::Type::Union(items) => core_ir::Type::Union(
            items
                .into_iter()
                .map(|item| specialize_sub_effect_payload(item, payload))
                .collect(),
        ),
        core_ir::Type::Inter(items) => core_ir::Type::Inter(
            items
                .into_iter()
                .map(|item| specialize_sub_effect_payload(item, payload))
                .collect(),
        ),
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var,
            body: Box::new(specialize_sub_effect_payload(*body, payload)),
        },
        other => other,
    }
}

fn type_arg_needs_mono_payload(arg: &core_ir::TypeArg) -> bool {
    match arg {
        core_ir::TypeArg::Type(core_ir::Type::Any | core_ir::Type::Var(_)) => true,
        core_ir::TypeArg::Type(ty) => core_type_has_vars(ty),
        core_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(core_type_has_vars)
                || bounds.upper.as_deref().is_some_and(core_type_has_vars)
        }
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
    binding.scheme = core_ir::Scheme {
        requirements: Vec::new(),
        body: core_value_type(&binding.body.ty),
    };
    refresh_binding_type_params(binding);
}

pub(super) fn refresh_closed_specialized_schemes(mut module: Module) -> Module {
    for binding in &mut module.bindings {
        close_unbound_effect_vars(binding);
        if is_specialized_path(&binding.name) {
            refresh_specialized_scheme_from_body(binding);
        }
    }
    module
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
                core_ir::RoleRequirementArg::Input(bounds)
                | core_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    collect_bounds_non_effect_vars(bounds, &mut non_effect_vars);
                }
            }
        }
    }
    let substitutions = effect_vars
        .into_iter()
        .filter(|var| !binding.type_params.contains(var) && !non_effect_vars.contains(var))
        .map(|var| (var, core_ir::Type::Never))
        .collect::<BTreeMap<_, _>>();
    if substitutions.is_empty() {
        return;
    }
    *binding = substitute_binding(binding.clone(), &substitutions);
    refresh_binding_type_params(binding);
}

pub(super) fn collect_binding_type_params(
    binding: &Binding,
    params: &mut BTreeSet<core_ir::TypeVar>,
) {
    collect_core_type_vars(&binding.scheme.body, params);
    for requirement in &binding.scheme.requirements {
        collect_role_requirement_vars(requirement, params);
    }
    collect_hir_type_vars(&binding.body.ty, params);
}

fn collect_type_bounds_effect_vars(
    bounds: &core_ir::TypeBounds,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_effect_position_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_effect_position_vars(upper, vars);
    }
}

fn collect_hir_effect_vars(ty: &RuntimeType, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match ty {
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

fn collect_expr_effect_vars(expr: &Expr, vars: &mut BTreeSet<core_ir::TypeVar>) {
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

fn collect_stmt_effect_vars(stmt: &Stmt, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_effect_vars(value, vars);
        }
    }
}

fn collect_expr_non_effect_vars(expr: &Expr, vars: &mut BTreeSet<core_ir::TypeVar>) {
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

fn collect_stmt_non_effect_vars(stmt: &Stmt, vars: &mut BTreeSet<core_ir::TypeVar>) {
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

fn collect_pattern_non_effect_vars(pattern: &Pattern, vars: &mut BTreeSet<core_ir::TypeVar>) {
    collect_hir_non_effect_vars(&pattern_type(pattern), vars);
}

fn collect_hir_non_effect_vars(ty: &RuntimeType, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match ty {
        RuntimeType::Core(ty) => collect_core_non_effect_vars(ty, vars),
        RuntimeType::Fun { param, ret } => {
            collect_hir_non_effect_vars(param, vars);
            collect_hir_non_effect_vars(ret, vars);
        }
        RuntimeType::Thunk { value, .. } => collect_hir_non_effect_vars(value, vars),
    }
}

fn collect_bounds_non_effect_vars(
    bounds: &core_ir::TypeBounds,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_non_effect_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_non_effect_vars(upper, vars);
    }
}

fn collect_core_non_effect_vars(ty: &core_ir::Type, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match ty {
        core_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        core_ir::Type::Fun { param, ret, .. } => {
            collect_core_non_effect_vars(param, vars);
            collect_core_non_effect_vars(ret, vars);
        }
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    core_ir::TypeArg::Type(ty) => collect_core_non_effect_vars(ty, vars),
                    core_ir::TypeArg::Bounds(bounds) => {
                        collect_bounds_non_effect_vars(bounds, vars);
                    }
                }
            }
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_core_non_effect_vars(item, vars);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_non_effect_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_core_non_effect_vars(ty, vars);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_core_non_effect_vars(payload, vars);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_core_non_effect_vars(tail, vars);
            }
        }
        core_ir::Type::Recursive { body, .. } => collect_core_non_effect_vars(body, vars),
        core_ir::Type::Row { .. } | core_ir::Type::Never | core_ir::Type::Any => {}
    }
}

pub(super) fn collect_role_requirement_vars(
    requirement: &core_ir::RoleRequirement,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    for arg in &requirement.args {
        match arg {
            core_ir::RoleRequirementArg::Input(bounds)
            | core_ir::RoleRequirementArg::Associated { bounds, .. } => {
                collect_type_bounds_vars(bounds, vars);
            }
        }
    }
}

pub(super) fn collect_type_bounds_vars(
    bounds: &core_ir::TypeBounds,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_type_vars(upper, vars);
    }
}

pub(super) fn collect_effect_position_vars(
    ty: &core_ir::Type,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    match ty {
        core_ir::Type::Fun {
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
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    core_ir::TypeArg::Type(ty) => collect_effect_position_vars(ty, vars),
                    core_ir::TypeArg::Bounds(bounds) => {
                        collect_type_bounds_effect_vars(bounds, vars);
                    }
                }
            }
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_position_vars(item, vars);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_effect_position_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_effect_position_vars(ty, vars);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_effect_position_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_effect_position_vars(tail, vars);
            }
        }
        core_ir::Type::Recursive { body, .. } => collect_effect_position_vars(body, vars),
        core_ir::Type::Row { .. }
        | core_ir::Type::Var(_)
        | core_ir::Type::Never
        | core_ir::Type::Any => {}
    }
}

pub(super) fn collect_effect_vars(effect: &core_ir::Type, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match effect {
        core_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_vars(item, vars);
            }
            collect_effect_vars(tail, vars);
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_vars(item, vars);
            }
        }
        core_ir::Type::Recursive { body, .. } => collect_effect_vars(body, vars),
        core_ir::Type::Named { .. }
        | core_ir::Type::Fun { .. }
        | core_ir::Type::Tuple(_)
        | core_ir::Type::Record(_)
        | core_ir::Type::Variant(_)
        | core_ir::Type::Never
        | core_ir::Type::Any => {}
    }
}

pub(super) fn substitute_type_instantiation(
    instantiation: TypeInstantiation,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
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
