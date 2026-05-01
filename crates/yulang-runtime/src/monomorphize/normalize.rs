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

pub(super) fn role_method_candidate_score(candidate: &RuntimeType, actual: &RuntimeType) -> usize {
    usize::from(candidate == actual) * 1000
        + usize::from(function_param(candidate) == function_param(actual)) * 200
        + usize::from(!hir_type_has_vars(candidate)) * 100
        + usize::from(hir_type_compatible(candidate, actual))
}

pub(super) fn receiver_type_matches(candidate: &RuntimeType, arg_ty: &RuntimeType) -> bool {
    function_param(candidate).is_some_and(|param| {
        hir_type_compatible(param, arg_ty)
            || hir_type_compatible(arg_ty, param)
            || matches!(param, RuntimeType::Core(core_ir::Type::Any))
    })
}

pub(super) fn binding_receiver_matches(candidate: &RuntimeType, receiver_ty: &RuntimeType) -> bool {
    function_param(candidate).is_some_and(|param| {
        hir_type_compatible(param, receiver_ty) || hir_type_compatible(receiver_ty, param)
    })
}

pub(super) fn path_key(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

pub(super) fn binding_with_complete_type_params(mut binding: Binding) -> Binding {
    let mut params = binding.type_params.iter().cloned().collect::<BTreeSet<_>>();
    collect_binding_type_params(&binding, &mut params);
    binding.type_params = params.into_iter().collect();
    binding
}

pub(super) fn refresh_binding_type_params(binding: &mut Binding) {
    let mut params = BTreeSet::new();
    collect_binding_type_params(binding, &mut params);
    binding.type_params = params.into_iter().collect();
}

pub(super) fn fill_residual_effect_params(mut binding: Binding) -> Binding {
    if binding.type_params.is_empty() {
        return binding;
    }
    let mut effect_vars = BTreeSet::new();
    collect_binding_effect_vars(&binding, &mut effect_vars);
    let substitutions = binding
        .type_params
        .iter()
        .filter(|param| effect_vars.contains(*param))
        .map(|param| (param.clone(), binding_concrete_effect_row(&binding)))
        .collect::<BTreeMap<_, _>>();
    if substitutions.is_empty() {
        return binding;
    }
    binding = substitute_binding(binding, &substitutions);
    refresh_binding_type_params(&mut binding);
    binding
}

pub(super) fn binding_principal_hir_type(binding: &Binding) -> RuntimeType {
    let vars = binding.type_params.iter().cloned().collect::<BTreeSet<_>>();
    let scheme_ty = normalize_hir_function_type(project_runtime_hir_type_with_vars(
        &binding.scheme.body,
        &vars,
    ));
    preserve_runtime_thunk_shape(scheme_ty, &binding.body.ty)
}

pub(super) fn refresh_binding_body_type_from_scheme(binding: &mut Binding) {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&binding.scheme.body, &mut vars);
    let scheme_ty = normalize_hir_function_type(project_runtime_hir_type_with_vars(
        &binding.scheme.body,
        &vars,
    ));
    binding.body.ty = preserve_runtime_thunk_shape(scheme_ty, &binding.body.ty);
}

fn preserve_runtime_thunk_shape(scheme: RuntimeType, body: &RuntimeType) -> RuntimeType {
    match (scheme, body) {
        (
            RuntimeType::Fun {
                param: scheme_param,
                ret: scheme_ret,
            },
            RuntimeType::Fun {
                param: body_param,
                ret: body_ret,
            },
        ) => RuntimeType::fun(
            preserve_runtime_thunk_shape(*scheme_param, body_param),
            preserve_runtime_thunk_shape(*scheme_ret, body_ret),
        ),
        (
            RuntimeType::Thunk {
                effect: scheme_effect,
                value: scheme_value,
            },
            RuntimeType::Thunk {
                effect: body_effect,
                value: body_value,
            },
        ) => RuntimeType::thunk(
            choose_runtime_thunk_effect(scheme_effect, body_effect),
            preserve_runtime_thunk_shape(*scheme_value, body_value),
        ),
        (
            scheme,
            RuntimeType::Thunk {
                effect: body_effect,
                value: body_value,
            },
        ) if hir_type_compatible(&scheme, body_value)
            || hir_type_compatible(body_value, &scheme) =>
        {
            RuntimeType::thunk(
                body_effect.clone(),
                preserve_runtime_thunk_shape(scheme, body_value),
            )
        }
        (scheme, _) => scheme,
    }
}

fn choose_runtime_thunk_effect(
    scheme_effect: core_ir::Type,
    body_effect: &core_ir::Type,
) -> core_ir::Type {
    if effect_is_empty(&scheme_effect) && !effect_is_empty(body_effect) {
        body_effect.clone()
    } else {
        scheme_effect
    }
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

pub(super) fn resolve_residual_associated_bindings(mut module: Module) -> Module {
    for binding in &mut module.bindings {
        if binding.type_params.is_empty() {
            continue;
        }
        resolve_binding_associated_requirements(binding);
    }
    module
}

pub(super) fn resolve_specialized_residual_associated_bindings(mut module: Module) -> Module {
    for binding in &mut module.bindings {
        if binding.type_params.is_empty()
            || !is_specialized_path(&binding.name)
            || unspecialized_path(&binding.name).is_some_and(|path| is_role_method_path(&path))
            || !contains_role_method_named(&binding.body, "fold")
        {
            continue;
        }
        resolve_binding_associated_requirements(binding);
    }
    module
}

fn resolve_binding_associated_requirements(binding: &mut Binding) {
    let mut substitutions = BTreeMap::new();
    infer_direct_associated_requirement_substitutions(
        &binding.scheme.requirements,
        &binding.type_params.iter().cloned().collect(),
        &mut substitutions,
    );
    normalize_substitutions(&mut substitutions);
    if substitutions.is_empty() {
        return;
    }
    *binding = substitute_binding(binding.clone(), &substitutions);
    refresh_binding_type_params(binding);
    refresh_specialized_scheme_from_body(binding);
}

fn contains_role_method_named(expr: &Expr, method: &str) -> bool {
    match &expr.kind {
        ExprKind::Var(path) | ExprKind::EffectOp(path) => {
            is_role_method_path(path)
                && path
                    .segments
                    .last()
                    .is_some_and(|name| name.0.as_str() == method)
        }
        ExprKind::Lambda { body, .. } => contains_role_method_named(body, method),
        ExprKind::Apply { callee, arg, .. } => {
            contains_role_method_named(callee, method) || contains_role_method_named(arg, method)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            contains_role_method_named(cond, method)
                || contains_role_method_named(then_branch, method)
                || contains_role_method_named(else_branch, method)
        }
        ExprKind::Tuple(items) => items
            .iter()
            .any(|item| contains_role_method_named(item, method)),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| contains_role_method_named(&field.value, method))
                || spread.as_ref().is_some_and(|spread| match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        contains_role_method_named(expr, method)
                    }
                })
        }
        ExprKind::Variant {
            value: Some(value), ..
        }
        | ExprKind::Select { base: value, .. } => contains_role_method_named(value, method),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            contains_role_method_named(scrutinee, method)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| contains_role_method_named(guard, method))
                        || contains_role_method_named(&arm.body, method)
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts
                .iter()
                .any(|stmt| contains_role_method_named_in_stmt(stmt, method))
                || tail
                    .as_ref()
                    .is_some_and(|tail| contains_role_method_named(tail, method))
        }
        ExprKind::Handle { body, arms, .. } => {
            contains_role_method_named(body, method)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| contains_role_method_named(guard, method))
                        || contains_role_method_named(&arm.body, method)
                })
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => contains_role_method_named(expr, method),
        ExprKind::LocalPushId { body, .. } => contains_role_method_named(body, method),
        ExprKind::AddId { thunk, .. } => contains_role_method_named(thunk, method),
        ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}

fn contains_role_method_named_in_stmt(stmt: &Stmt, method: &str) -> bool {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            contains_role_method_named(value, method)
        }
    }
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

pub(super) fn collect_binding_effect_vars(
    binding: &Binding,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    collect_effect_position_vars(&binding.scheme.body, vars);
    for requirement in &binding.scheme.requirements {
        for arg in &requirement.args {
            match arg {
                core_ir::RoleRequirementArg::Input(bounds)
                | core_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    collect_type_bounds_effect_vars(bounds, vars);
                }
            }
        }
    }
    collect_hir_effect_vars(&binding.body.ty, vars);
}

pub(super) fn collect_type_bounds_effect_vars(
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

pub(super) fn collect_hir_effect_vars(ty: &RuntimeType, vars: &mut BTreeSet<core_ir::TypeVar>) {
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

pub(super) fn binding_concrete_effect_row(binding: &Binding) -> core_ir::Type {
    let mut effects = Vec::new();
    collect_concrete_effects_from_core_type(&binding.scheme.body, &mut effects);
    for requirement in &binding.scheme.requirements {
        for arg in &requirement.args {
            match arg {
                core_ir::RoleRequirementArg::Input(bounds)
                | core_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    collect_concrete_effects_from_bounds(bounds, &mut effects);
                }
            }
        }
    }
    collect_concrete_effects_from_hir_type(&binding.body.ty, &mut effects);
    mono_effect_row(effects)
}

pub(super) fn fill_call_effect_substitutions(
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    effect_params: &BTreeSet<core_ir::TypeVar>,
    actuals: &[&RuntimeType],
) {
    let unresolved = effect_params
        .iter()
        .filter(|param| {
            substitutions
                .get(*param)
                .is_none_or(|ty| effect_is_empty(ty) || matches!(ty, core_ir::Type::Var(_)))
        })
        .cloned()
        .collect::<Vec<_>>();
    let [param] = unresolved.as_slice() else {
        return;
    };
    let mut effects = Vec::new();
    for actual in actuals {
        collect_concrete_effects_from_hir_type(actual, &mut effects);
    }
    let effect = mono_effect_row(effects);
    if !effect_is_empty(&effect) {
        substitutions.insert(param.clone(), effect);
    }
}

pub(super) fn collect_concrete_effects_from_bounds(
    bounds: &core_ir::TypeBounds,
    out: &mut Vec<core_ir::Type>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_concrete_effects_from_core_type(lower, out);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_concrete_effects_from_core_type(upper, out);
    }
}

pub(super) fn collect_concrete_effects_from_hir_type(
    ty: &RuntimeType,
    out: &mut Vec<core_ir::Type>,
) {
    match ty {
        RuntimeType::Core(ty) => collect_concrete_effects_from_core_type(ty, out),
        RuntimeType::Fun { param, ret } => {
            collect_concrete_effects_from_hir_type(param, out);
            collect_concrete_effects_from_hir_type(ret, out);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_concrete_effects_from_effect(effect, out);
            collect_concrete_effects_from_hir_type(value, out);
        }
    }
}

pub(super) fn collect_concrete_effects_from_core_type(
    ty: &core_ir::Type,
    out: &mut Vec<core_ir::Type>,
) {
    match ty {
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_concrete_effects_from_effect(param_effect, out);
            collect_concrete_effects_from_effect(ret_effect, out);
            collect_concrete_effects_from_core_type(param, out);
            collect_concrete_effects_from_core_type(ret, out);
        }
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    core_ir::TypeArg::Type(ty) => collect_concrete_effects_from_core_type(ty, out),
                    core_ir::TypeArg::Bounds(bounds) => {
                        collect_concrete_effects_from_bounds(bounds, out);
                    }
                }
            }
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_concrete_effects_from_core_type(item, out);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_concrete_effects_from_core_type(&field.value, out);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_concrete_effects_from_core_type(ty, out);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_concrete_effects_from_core_type(payload, out);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_concrete_effects_from_core_type(tail, out);
            }
        }
        core_ir::Type::Recursive { body, .. } => collect_concrete_effects_from_core_type(body, out),
        core_ir::Type::Row { .. }
        | core_ir::Type::Var(_)
        | core_ir::Type::Never
        | core_ir::Type::Any => {}
    }
}

pub(super) fn collect_concrete_effects_from_effect(
    effect: &core_ir::Type,
    out: &mut Vec<core_ir::Type>,
) {
    match project_runtime_effect(effect) {
        core_ir::Type::Named { path, args } => push_unique_mono_effect(
            out,
            core_ir::Type::Named {
                path,
                args: args.into_iter().map(canonicalize_mono_type_arg).collect(),
            },
        ),
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_concrete_effects_from_effect(&item, out);
            }
            collect_concrete_effects_from_effect(&tail, out);
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_concrete_effects_from_effect(&item, out);
            }
        }
        core_ir::Type::Recursive { body, .. } => collect_concrete_effects_from_effect(&body, out),
        core_ir::Type::Fun { .. }
        | core_ir::Type::Tuple(_)
        | core_ir::Type::Record(_)
        | core_ir::Type::Variant(_)
        | core_ir::Type::Var(_)
        | core_ir::Type::Never
        | core_ir::Type::Any => {}
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

pub(super) fn effect_position_vars(ty: &core_ir::Type) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_effect_position_vars(ty, &mut vars);
    vars
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

pub(super) fn normalize_type_instantiation(
    instantiation: &TypeInstantiation,
    effect_params: &BTreeSet<core_ir::TypeVar>,
) -> Option<TypeInstantiation> {
    let args = instantiation
        .args
        .iter()
        .filter_map(|arg| {
            let ty = if effect_params.contains(&arg.var) {
                normalize_mono_effect_substitution(&arg.ty)
            } else {
                normalize_mono_type(&arg.ty)
            };
            if is_identity_substitution(&arg.var, &ty)
                || matches!(ty, core_ir::Type::Any)
                || (core_type_has_vars(&ty)
                    && !(effect_params.contains(&arg.var) && matches!(ty, core_ir::Type::Var(_))))
            {
                return None;
            }
            Some(crate::ir::TypeSubstitution {
                var: arg.var.clone(),
                ty,
            })
        })
        .collect::<Vec<_>>();
    if args.is_empty() {
        return None;
    }
    Some(TypeInstantiation {
        target: instantiation.target.clone(),
        args,
    })
}

pub(super) fn normalize_substitutions(
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    for ty in substitutions.values_mut() {
        *ty = normalize_mono_type(ty);
    }
    substitutions.retain(|var, ty| {
        !is_identity_substitution(var, ty)
            && !matches!(ty, core_ir::Type::Any)
            && !core_type_has_vars(ty)
    });
}

pub(super) fn normalize_call_substitutions(
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    effect_params: &BTreeSet<core_ir::TypeVar>,
) {
    for (var, ty) in substitutions.iter_mut() {
        *ty = if effect_params.contains(var) {
            normalize_mono_effect_substitution(ty)
        } else {
            normalize_mono_type(ty)
        };
    }
    substitutions.retain(|var, ty| {
        !is_identity_substitution(var, ty)
            && !matches!(ty, core_ir::Type::Any)
            && (!core_type_has_vars(ty)
                || (effect_params.contains(var) && matches!(ty, core_ir::Type::Var(_))))
    });
}

pub(super) fn normalize_mono_type(ty: &core_ir::Type) -> core_ir::Type {
    canonicalize_mono_type(project_runtime_type_with_vars(ty, &BTreeSet::new()))
}

pub(super) fn normalize_mono_effect_substitution(ty: &core_ir::Type) -> core_ir::Type {
    match ty {
        core_ir::Type::Var(var) => core_ir::Type::Var(var.clone()),
        ty => canonicalize_mono_effect(project_runtime_effect(ty)),
    }
}

pub(super) fn canonicalize_mono_type(ty: core_ir::Type) -> core_ir::Type {
    match ty {
        core_ir::Type::Named { path, args } => core_ir::Type::Named {
            path,
            args: args.into_iter().map(canonicalize_mono_type_arg).collect(),
        },
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => core_ir::Type::Fun {
            param: Box::new(canonicalize_mono_type(*param)),
            param_effect: Box::new(canonicalize_mono_effect(*param_effect)),
            ret_effect: Box::new(canonicalize_mono_effect(*ret_effect)),
            ret: Box::new(canonicalize_mono_type(*ret)),
        },
        core_ir::Type::Tuple(items) => {
            core_ir::Type::Tuple(items.into_iter().map(canonicalize_mono_type).collect())
        }
        core_ir::Type::Record(record) => core_ir::Type::Record(core_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| core_ir::RecordField {
                    name: field.name,
                    value: canonicalize_mono_type(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(|spread| match spread {
                core_ir::RecordSpread::Head(ty) => {
                    core_ir::RecordSpread::Head(Box::new(canonicalize_mono_type(*ty)))
                }
                core_ir::RecordSpread::Tail(ty) => {
                    core_ir::RecordSpread::Tail(Box::new(canonicalize_mono_type(*ty)))
                }
            }),
        }),
        core_ir::Type::Variant(variant) => core_ir::Type::Variant(core_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| core_ir::VariantCase {
                    name: case.name,
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(canonicalize_mono_type)
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(canonicalize_mono_type(*tail))),
        }),
        core_ir::Type::Union(items) => {
            core_ir::Type::Union(items.into_iter().map(canonicalize_mono_type).collect())
        }
        core_ir::Type::Inter(items) => {
            core_ir::Type::Inter(items.into_iter().map(canonicalize_mono_type).collect())
        }
        core_ir::Type::Row { items, tail } => core_ir::Type::Row {
            items: items
                .into_iter()
                .map(canonicalize_mono_effect)
                .filter(|effect| !effect_is_empty(effect))
                .collect(),
            tail: Box::new(canonicalize_mono_effect(*tail)),
        },
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var,
            body: Box::new(canonicalize_mono_type(*body)),
        },
        other @ (core_ir::Type::Never | core_ir::Type::Any | core_ir::Type::Var(_)) => other,
    }
}

pub(super) fn canonicalize_mono_type_arg(arg: core_ir::TypeArg) -> core_ir::TypeArg {
    match arg {
        core_ir::TypeArg::Type(ty) => core_ir::TypeArg::Type(canonicalize_mono_type(ty)),
        core_ir::TypeArg::Bounds(bounds) => {
            core_ir::TypeArg::Bounds(canonicalize_mono_bounds(bounds))
        }
    }
}

pub(super) fn canonicalize_mono_bounds(bounds: core_ir::TypeBounds) -> core_ir::TypeBounds {
    core_ir::TypeBounds {
        lower: bounds.lower.map(|ty| Box::new(canonicalize_mono_type(*ty))),
        upper: bounds.upper.map(|ty| Box::new(canonicalize_mono_type(*ty))),
    }
}

pub(super) fn canonicalize_mono_effect(effect: core_ir::Type) -> core_ir::Type {
    match project_runtime_effect(&effect) {
        core_ir::Type::Any | core_ir::Type::Var(_) => core_ir::Type::Never,
        core_ir::Type::Named { path, args } => {
            let effect = core_ir::Type::Named {
                path,
                args: args.into_iter().map(canonicalize_mono_type_arg).collect(),
            };
            empty_uninhabited_effect_atom(effect)
        }
        core_ir::Type::Row { items, tail } => {
            let mut items = items
                .into_iter()
                .map(canonicalize_mono_effect)
                .filter(|effect| !effect_is_empty(effect))
                .collect::<Vec<_>>();
            let tail = canonicalize_mono_effect(*tail);
            if !effect_is_empty(&tail) {
                push_unique_mono_effect(&mut items, tail);
            }
            mono_effect_row(items)
        }
        core_ir::Type::Union(items) => mono_effect_row(
            items
                .into_iter()
                .map(canonicalize_mono_effect)
                .filter(|effect| !effect_is_empty(effect))
                .collect(),
        ),
        core_ir::Type::Inter(items) => {
            let items = items
                .into_iter()
                .map(canonicalize_mono_effect)
                .filter(|effect| !effect_is_empty(effect))
                .collect::<Vec<_>>();
            if items.is_empty() {
                core_ir::Type::Never
            } else {
                mono_effect_row(items)
            }
        }
        core_ir::Type::Recursive { var, body } => {
            let body = canonicalize_mono_effect(*body);
            if effect_is_empty(&body) {
                core_ir::Type::Never
            } else {
                core_ir::Type::Recursive {
                    var,
                    body: Box::new(body),
                }
            }
        }
        effect => effect,
    }
}

pub(super) fn empty_uninhabited_effect_atom(effect: core_ir::Type) -> core_ir::Type {
    let core_ir::Type::Named { path, args } = &effect else {
        return effect;
    };
    if !type_path_last_is(path, "sub") {
        return effect;
    }
    if args.iter().any(|arg| match arg {
        core_ir::TypeArg::Type(ty) => matches!(ty, core_ir::Type::Never),
        core_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_deref()
                .is_some_and(|ty| matches!(ty, core_ir::Type::Never))
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(|ty| matches!(ty, core_ir::Type::Never))
        }
    }) {
        core_ir::Type::Never
    } else {
        effect
    }
}

pub(super) fn mono_effect_row(items: Vec<core_ir::Type>) -> core_ir::Type {
    let mut deduped = Vec::new();
    for item in items {
        push_unique_mono_effect(&mut deduped, item);
    }
    if deduped.is_empty() {
        core_ir::Type::Never
    } else {
        core_ir::Type::Row {
            items: deduped,
            tail: Box::new(core_ir::Type::Never),
        }
    }
}

pub(super) fn push_unique_mono_effect(out: &mut Vec<core_ir::Type>, effect: core_ir::Type) {
    if !effect_is_empty(&effect) && !out.contains(&effect) {
        out.push(effect);
    }
}

pub(super) fn is_identity_substitution(var: &core_ir::TypeVar, ty: &core_ir::Type) -> bool {
    matches!(ty, core_ir::Type::Var(actual) if actual == var)
}
