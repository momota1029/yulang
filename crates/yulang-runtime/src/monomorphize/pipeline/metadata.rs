use super::*;
use crate::types::{effect_paths, effect_paths_match, type_compatible};

/// Normalize typed metadata after monomorphization so it obeys the same
/// concrete runtime contract as the surrounding `Expr.ty` slots. The
/// monomorphize substitute pass only rewrites variables that appear in
/// the binding scheme's quantified list, so inference vars that live
/// solely inside evidence `TypeBounds` can survive untouched.
///
/// This pass is not a source-level type inference step. It lowers
/// monomorphized metadata to the minimal concrete shape consumed by
/// validate/runtime: Apply evidence mirrors callee/arg/result slots,
/// join evidence mirrors the enclosing result, and principal inference
/// traces that runtime never reads are dropped.
pub(super) fn normalize_monomorphized_metadata(mut module: Module) -> Module {
    let binding_types = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.body.ty.clone()))
        .collect::<HashMap<_, _>>();
    let specialization_aliases = specialization_aliases_by_original(&binding_types);
    for binding in &mut module.bindings {
        refresh_global_var_types(
            &mut binding.body,
            &binding_types,
            &specialization_aliases,
            &mut BTreeSet::new(),
        );
        binding.body = normalize_runtime_metadata_expr(take_expr(&mut binding.body));
        preserve_closed_specialized_binding_scheme(binding);
    }
    for root in &mut module.root_exprs {
        refresh_global_var_types(
            root,
            &binding_types,
            &specialization_aliases,
            &mut BTreeSet::new(),
        );
        *root = normalize_runtime_metadata_expr(take_expr(root));
    }
    for binding in &mut module.bindings {
        refresh_expr(&mut binding.body);
    }
    for root in &mut module.root_exprs {
        refresh_expr(root);
    }
    let never_effect_ops = collect_never_effect_ops(&module);
    normalize_never_effect_join_arms(&mut module, &never_effect_ops);
    module
}

fn take_expr(expr: &mut Expr) -> Expr {
    std::mem::replace(
        expr,
        Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), RuntimeType::Unknown),
    )
}

fn normalize_runtime_metadata_expr(expr: Expr) -> Expr {
    project_runtime_expr_types(refresh_local_expr_types(project_runtime_expr_types(expr)))
}

fn preserve_closed_specialized_binding_scheme(binding: &mut Binding) {
    if !is_specialized_path(&binding.name) {
        return;
    }
    if !binding.type_params.is_empty() {
        return;
    }
    let scheme_ty = normalize_hir_function_type(RuntimeType::core(binding.scheme.body.clone()));
    if runtime_type_choice_widens(&scheme_ty, &binding.body.ty) {
        binding.body = retag_expr_spine_type(take_expr(&mut binding.body), scheme_ty);
    }
}

fn retag_expr_spine_type(expr: Expr, ty: RuntimeType) -> Expr {
    match expr {
        Expr {
            kind:
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body,
                },
            ..
        } => {
            let body_ty = match &ty {
                RuntimeType::Fun { ret, .. } => ret.as_ref().clone(),
                _ => body.ty.clone(),
            };
            Expr::typed(
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body: Box::new(retag_expr_spine_type(*body, body_ty)),
                },
                ty,
            )
        }
        Expr {
            kind: ExprKind::Block { stmts, tail },
            ..
        } => {
            let tail = tail.map(|tail| Box::new(retag_expr_spine_type(*tail, ty.clone())));
            let ty = tail
                .as_ref()
                .map(|tail| tail.ty.clone())
                .unwrap_or(RuntimeType::Core(typed_ir::Type::Never));
            Expr::typed(ExprKind::Block { stmts, tail }, ty)
        }
        Expr { kind, .. } => Expr::typed(kind, ty),
    }
}

fn runtime_type_choice_widens(projected: &RuntimeType, current: &RuntimeType) -> bool {
    match (projected, current) {
        (RuntimeType::Core(projected), RuntimeType::Core(current)) => {
            metadata_core_type_choice_widens(projected, current)
        }
        (
            RuntimeType::Fun {
                param: projected_param,
                ret: projected_ret,
            },
            RuntimeType::Fun {
                param: current_param,
                ret: current_ret,
            },
        ) => {
            runtime_type_choice_widens(projected_param, current_param)
                || runtime_type_choice_widens(projected_ret, current_ret)
        }
        (
            RuntimeType::Thunk {
                value: projected_value,
                ..
            },
            RuntimeType::Thunk {
                value: current_value,
                ..
            },
        ) => runtime_type_choice_widens(projected_value, current_value),
        _ => false,
    }
}

fn metadata_core_type_choice_widens(projected: &typed_ir::Type, current: &typed_ir::Type) -> bool {
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
            metadata_core_type_choice_widens(projected_param, current_param)
                || metadata_core_type_choice_widens(projected_param_effect, current_param_effect)
                || metadata_core_type_choice_widens(projected_ret_effect, current_ret_effect)
                || metadata_core_type_choice_widens(projected_ret, current_ret)
        }
        _ => false,
    }
}

fn refresh_global_var_types(
    expr: &mut Expr,
    binding_types: &HashMap<typed_ir::Path, RuntimeType>,
    specialization_aliases: &HashMap<typed_ir::Path, Vec<(typed_ir::Path, RuntimeType)>>,
    shadowed: &mut BTreeSet<typed_ir::Name>,
) {
    match &mut expr.kind {
        ExprKind::Var(path) => {
            if !path_is_shadowed(path, shadowed)
                && let Some(ty) = binding_types.get(path)
            {
                expr.ty = ty.clone();
            } else if !path_is_shadowed(path, shadowed)
                && let Some((specialized, ty)) =
                    select_specialization_alias(path, &expr.ty, specialization_aliases)
            {
                *path = specialized;
                expr.ty = ty;
            }
        }
        ExprKind::Lambda { param, body, .. } => {
            let inserted = shadowed.insert(param.clone());
            refresh_global_var_types(body, binding_types, specialization_aliases, shadowed);
            if inserted {
                shadowed.remove(param);
            }
        }
        ExprKind::Apply {
            callee,
            arg,
            instantiation,
            ..
        } => {
            refresh_global_var_types(callee, binding_types, specialization_aliases, shadowed);
            refresh_global_var_types(arg, binding_types, specialization_aliases, shadowed);
            if let Some((original, specialized, ty)) = select_apply_specialization_alias(
                callee,
                arg,
                &expr.ty,
                binding_types,
                specialization_aliases,
                shadowed,
            ) {
                callee.kind = ExprKind::Var(specialized);
                callee.ty = ty;
                if instantiation
                    .as_ref()
                    .is_some_and(|instantiation| instantiation.target == original)
                {
                    *instantiation = None;
                }
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            refresh_global_var_types(cond, binding_types, specialization_aliases, shadowed);
            refresh_global_var_types(then_branch, binding_types, specialization_aliases, shadowed);
            refresh_global_var_types(else_branch, binding_types, specialization_aliases, shadowed);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                refresh_global_var_types(item, binding_types, specialization_aliases, shadowed);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                refresh_global_var_types(
                    &mut field.value,
                    binding_types,
                    specialization_aliases,
                    shadowed,
                );
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        refresh_global_var_types(
                            expr,
                            binding_types,
                            specialization_aliases,
                            shadowed,
                        );
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                refresh_global_var_types(value, binding_types, specialization_aliases, shadowed);
            }
        }
        ExprKind::Select { base, .. } => {
            refresh_global_var_types(base, binding_types, specialization_aliases, shadowed)
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            refresh_global_var_types(scrutinee, binding_types, specialization_aliases, shadowed);
            for arm in arms {
                let saved = shadowed.clone();
                collect_pattern_bind_names(&arm.pattern, shadowed);
                if let Some(guard) = &mut arm.guard {
                    refresh_global_var_types(
                        guard,
                        binding_types,
                        specialization_aliases,
                        shadowed,
                    );
                }
                refresh_global_var_types(
                    &mut arm.body,
                    binding_types,
                    specialization_aliases,
                    shadowed,
                );
                *shadowed = saved;
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = shadowed.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { pattern, value } => {
                        refresh_global_var_types(
                            value,
                            binding_types,
                            specialization_aliases,
                            shadowed,
                        );
                        collect_pattern_bind_names(pattern, shadowed);
                    }
                    Stmt::Expr(expr) => refresh_global_var_types(
                        expr,
                        binding_types,
                        specialization_aliases,
                        shadowed,
                    ),
                    Stmt::Module { def, body } => {
                        refresh_global_var_types(
                            body,
                            binding_types,
                            specialization_aliases,
                            shadowed,
                        );
                        if let Some(ty) = binding_types.get(def) {
                            body.ty = ty.clone();
                        }
                        if let [name] = def.segments.as_slice() {
                            shadowed.insert(name.clone());
                        }
                    }
                }
            }
            if let Some(tail) = tail {
                refresh_global_var_types(tail, binding_types, specialization_aliases, shadowed);
            }
            *shadowed = saved;
        }
        ExprKind::Handle { body, arms, .. } => {
            refresh_global_var_types(body, binding_types, specialization_aliases, shadowed);
            for arm in arms {
                let saved = shadowed.clone();
                collect_pattern_bind_names(&arm.payload, shadowed);
                if let Some(resume) = &arm.resume {
                    shadowed.insert(resume.name.clone());
                }
                if let Some(guard) = &mut arm.guard {
                    refresh_global_var_types(
                        guard,
                        binding_types,
                        specialization_aliases,
                        shadowed,
                    );
                }
                refresh_global_var_types(
                    &mut arm.body,
                    binding_types,
                    specialization_aliases,
                    shadowed,
                );
                *shadowed = saved;
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => {
            refresh_global_var_types(expr, binding_types, specialization_aliases, shadowed)
        }
        ExprKind::LocalPushId { body, .. } => {
            refresh_global_var_types(body, binding_types, specialization_aliases, shadowed)
        }
        ExprKind::AddId { thunk, .. } => {
            refresh_global_var_types(thunk, binding_types, specialization_aliases, shadowed)
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn specialization_aliases_by_original(
    binding_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> HashMap<typed_ir::Path, Vec<(typed_ir::Path, RuntimeType)>> {
    let mut out = HashMap::<typed_ir::Path, Vec<(typed_ir::Path, RuntimeType)>>::new();
    for (path, ty) in binding_types {
        let Some(original) = unspecialized_path(path) else {
            continue;
        };
        out.entry(original)
            .or_default()
            .push((path.clone(), ty.clone()));
    }
    out
}

fn select_specialization_alias(
    path: &typed_ir::Path,
    expr_ty: &RuntimeType,
    aliases: &HashMap<typed_ir::Path, Vec<(typed_ir::Path, RuntimeType)>>,
) -> Option<(typed_ir::Path, RuntimeType)> {
    let candidates = aliases.get(path)?;
    let mut matches = candidates
        .iter()
        .filter_map(|(candidate, ty)| {
            let expected = normalize_hir_function_type(ty.clone());
            let fit = metadata_runtime_type_score(expr_ty, &expected)?;
            let precision = metadata_type_precision_score(&expected);
            let suffix = specialization_suffix(candidate).unwrap_or(0);
            Some((candidate.clone(), expected, fit, precision, suffix))
        })
        .collect::<Vec<_>>();
    if let Some(best) = matches.iter().map(|(_, _, fit, _, _)| *fit).max() {
        matches.retain(|(_, _, fit, _, _)| *fit == best);
    }
    if let Some(best) = matches
        .iter()
        .map(|(_, _, _, precision, _)| *precision)
        .max()
    {
        matches.retain(|(_, _, _, precision, _)| *precision == best);
    }
    matches.sort_by_key(|(_, _, _, _, suffix)| *suffix);
    matches.pop().map(|(path, ty, _, _, _)| (path, ty))
}

fn select_apply_specialization_alias(
    callee: &Expr,
    arg: &Expr,
    result_ty: &RuntimeType,
    binding_types: &HashMap<typed_ir::Path, RuntimeType>,
    aliases: &HashMap<typed_ir::Path, Vec<(typed_ir::Path, RuntimeType)>>,
    shadowed: &BTreeSet<typed_ir::Name>,
) -> Option<(typed_ir::Path, typed_ir::Path, RuntimeType)> {
    let ExprKind::Var(path) = &callee.kind else {
        return None;
    };
    if path_is_shadowed(path, shadowed) || binding_types.contains_key(path) {
        return None;
    }
    let candidates = aliases.get(path)?;
    let mut matches = candidates
        .iter()
        .filter_map(|(candidate, ty)| {
            let expected = normalize_hir_function_type(ty.clone());
            let RuntimeType::Fun { param, ret } = &expected else {
                return None;
            };
            let arg_score = metadata_runtime_type_score(&arg.ty, param)?;
            let result_score = metadata_runtime_type_score(result_ty, ret)?;
            let precision = metadata_type_precision_score(&expected);
            let suffix = specialization_suffix(candidate).unwrap_or(0);
            Some((
                candidate.clone(),
                expected,
                arg_score + result_score,
                precision,
                suffix,
            ))
        })
        .collect::<Vec<_>>();
    if let Some(best) = matches.iter().map(|(_, _, score, _, _)| *score).max() {
        matches.retain(|(_, _, score, _, _)| *score == best);
    }
    if let Some(best) = matches
        .iter()
        .map(|(_, _, _, precision, _)| *precision)
        .max()
    {
        matches.retain(|(_, _, _, precision, _)| *precision == best);
    }
    matches.sort_by_key(|(_, _, _, _, suffix)| *suffix);
    matches
        .pop()
        .map(|(specialized, ty, _, _, _)| (path.clone(), specialized, ty))
}

fn metadata_runtime_type_score(actual: &RuntimeType, expected: &RuntimeType) -> Option<usize> {
    if actual == expected {
        return Some(8);
    }
    let actual_effects = metadata_runtime_type_effect_paths(actual);
    let expected_effects = metadata_runtime_type_effect_paths(expected);
    let actual = runtime_core_type(actual);
    let expected = runtime_core_type(expected);
    if (!actual_effects.is_empty() || !expected_effects.is_empty())
        && !metadata_effect_path_sets_match(&actual_effects, &expected_effects)
    {
        return None;
    }
    if !type_compatible(&expected, &actual) {
        return None;
    }
    Some(1 + usize::from(actual == expected) * 2 + usize::from(!actual_effects.is_empty()) * 4)
}

fn metadata_type_precision_score(ty: &RuntimeType) -> usize {
    1024usize.saturating_sub(metadata_core_type_imprecision_score(&runtime_core_type(ty)) * 16)
}

fn metadata_runtime_type_effect_paths(ty: &RuntimeType) -> Vec<typed_ir::Path> {
    let mut paths = Vec::new();
    collect_metadata_runtime_type_effect_paths(ty, &mut paths);
    paths
}

fn collect_metadata_runtime_type_effect_paths(ty: &RuntimeType, paths: &mut Vec<typed_ir::Path>) {
    match ty {
        RuntimeType::Core(ty) => collect_metadata_core_type_effect_paths(ty, paths),
        RuntimeType::Fun { param, ret } => {
            collect_metadata_runtime_type_effect_paths(param, paths);
            collect_metadata_runtime_type_effect_paths(ret, paths);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_metadata_effect_paths(effect, paths);
            collect_metadata_runtime_type_effect_paths(value, paths);
        }
        RuntimeType::Unknown => {}
    }
}

fn metadata_core_type_imprecision_score(ty: &typed_ir::Type) -> usize {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => 1,
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            metadata_core_type_imprecision_score(param)
                + metadata_core_type_imprecision_score(param_effect)
                + metadata_core_type_imprecision_score(ret_effect)
                + metadata_core_type_imprecision_score(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            items.iter().map(metadata_core_type_imprecision_score).sum()
        }
        typed_ir::Type::Record(record) => {
            let fields = record
                .fields
                .iter()
                .map(|field| metadata_core_type_imprecision_score(&field.value))
                .sum::<usize>();
            let spread = record
                .spread
                .as_ref()
                .map(|spread| match spread {
                    typed_ir::RecordSpread::Head(spread) | typed_ir::RecordSpread::Tail(spread) => {
                        metadata_core_type_imprecision_score(spread)
                    }
                })
                .unwrap_or(0);
            fields + spread
        }
        typed_ir::Type::Variant(variant) => {
            let payloads = variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .map(metadata_core_type_imprecision_score)
                .sum::<usize>();
            let tail = variant
                .tail
                .as_ref()
                .map(|tail| metadata_core_type_imprecision_score(tail))
                .unwrap_or(0);
            payloads + tail
        }
        typed_ir::Type::Named { args, .. } => args
            .iter()
            .map(|arg| match arg {
                typed_ir::TypeArg::Type(ty) => metadata_core_type_imprecision_score(ty),
                typed_ir::TypeArg::Bounds(bounds) => {
                    bounds
                        .lower
                        .as_deref()
                        .map(metadata_core_type_imprecision_score)
                        .unwrap_or(0)
                        + bounds
                            .upper
                            .as_deref()
                            .map(metadata_core_type_imprecision_score)
                            .unwrap_or(0)
                }
            })
            .sum(),
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .map(metadata_core_type_imprecision_score)
                .sum::<usize>()
                + metadata_core_type_imprecision_score(tail)
        }
        typed_ir::Type::Recursive { body, .. } => metadata_core_type_imprecision_score(body),
        typed_ir::Type::Never => 0,
    }
}

fn collect_metadata_core_type_effect_paths(ty: &typed_ir::Type, paths: &mut Vec<typed_ir::Path>) {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_metadata_effect_paths(param_effect, paths);
            collect_metadata_effect_paths(ret_effect, paths);
            collect_metadata_core_type_effect_paths(param, paths);
            collect_metadata_core_type_effect_paths(ret, paths);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_metadata_core_type_effect_paths(item, paths);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_metadata_core_type_effect_paths(&field.value, paths);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(spread) | typed_ir::RecordSpread::Tail(spread) => {
                        collect_metadata_core_type_effect_paths(spread, paths);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_metadata_core_type_effect_paths(payload, paths);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_metadata_core_type_effect_paths(tail, paths);
            }
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    typed_ir::TypeArg::Type(ty) => {
                        collect_metadata_core_type_effect_paths(ty, paths);
                    }
                    typed_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_metadata_core_type_effect_paths(lower, paths);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_metadata_core_type_effect_paths(upper, paths);
                        }
                    }
                }
            }
        }
        typed_ir::Type::Row { items, tail } => {
            collect_metadata_effect_paths(ty, paths);
            for item in items {
                collect_metadata_core_type_effect_paths(item, paths);
            }
            collect_metadata_core_type_effect_paths(tail, paths);
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_metadata_core_type_effect_paths(body, paths)
        }
        typed_ir::Type::Var(_)
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Unknown => {}
    }
}

fn collect_metadata_effect_paths(effect: &typed_ir::Type, paths: &mut Vec<typed_ir::Path>) {
    for path in effect_paths(effect) {
        if !paths
            .iter()
            .any(|existing| effect_paths_match(existing, &path))
        {
            paths.push(path);
        }
    }
}

fn metadata_effect_path_sets_match(left: &[typed_ir::Path], right: &[typed_ir::Path]) -> bool {
    left.iter()
        .all(|left| right.iter().any(|right| effect_paths_match(left, right)))
        && right
            .iter()
            .all(|right| left.iter().any(|left| effect_paths_match(left, right)))
}

fn collect_pattern_bind_names(pattern: &Pattern, names: &mut BTreeSet<typed_ir::Name>) {
    match pattern {
        Pattern::Bind { name, .. } => {
            names.insert(name.clone());
        }
        Pattern::As { pattern, name, .. } => {
            collect_pattern_bind_names(pattern, names);
            names.insert(name.clone());
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_bind_names(item, names);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_bind_names(item, names);
            }
            if let Some(spread) = spread {
                collect_pattern_bind_names(spread, names);
            }
            for item in suffix {
                collect_pattern_bind_names(item, names);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_bind_names(&field.pattern, names);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_bind_names(pattern, names);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_bind_names(value, names);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_bind_names(left, names);
            collect_pattern_bind_names(right, names);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn path_is_shadowed(path: &typed_ir::Path, shadowed: &BTreeSet<typed_ir::Name>) -> bool {
    path.segments
        .as_slice()
        .first()
        .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name))
}

fn refresh_expr(expr: &mut Expr) {
    match &mut expr.kind {
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            refresh_expr(callee);
            refresh_expr(arg);
            if let Some(evidence) = evidence {
                let callee_ty = runtime_core_type(&callee.ty);
                let arg_ty = runtime_core_type(&arg.ty);
                let result_ty = runtime_core_type(&expr.ty);
                evidence.callee = typed_ir::TypeBounds::exact(callee_ty.clone());
                evidence.expected_callee = None;
                evidence.arg = typed_ir::TypeBounds::exact(arg_ty);
                evidence.expected_arg = None;
                evidence.result = typed_ir::TypeBounds::exact(result_ty);
                evidence.principal_callee = Some(callee_ty);
                evidence.substitutions = Vec::new();
                evidence.substitution_candidates = Vec::new();
                evidence.principal_elaboration = None;
            }
            // `instantiation` only describes the principal substitution
            // chosen at inference time. The arguments here are already
            // monomorphic Types, but their inner TypeVar payloads can be
            // stale; replace them with the resolved callee type so the
            // residual walker sees no var.
            if let Some(instantiation) = instantiation {
                let arg_ty = runtime_core_type(&arg.ty);
                instantiation.args = instantiation
                    .args
                    .iter()
                    .map(|substitution| crate::ir::TypeSubstitution {
                        var: substitution.var.clone(),
                        ty: arg_ty.clone(),
                    })
                    .collect();
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            refresh_expr(cond);
            refresh_expr(then_branch);
            refresh_expr(else_branch);
            if let Some(evidence) = evidence {
                evidence.result = runtime_core_type(&expr.ty);
            }
        }
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            refresh_expr(scrutinee);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    refresh_expr(guard);
                }
                refresh_expr(&mut arm.body);
            }
            evidence.result = runtime_core_type(&expr.ty);
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler: _,
        } => {
            refresh_expr(body);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    refresh_expr(guard);
                }
                refresh_expr(&mut arm.body);
            }
            evidence.result = runtime_core_type(&expr.ty);
        }
        ExprKind::Lambda { body, .. } => refresh_expr(body),
        ExprKind::Tuple(items) => {
            for item in items {
                refresh_expr(item);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                refresh_expr(&mut field.value);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        refresh_expr(expr);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                refresh_expr(value);
            }
        }
        ExprKind::Select { base, .. } => refresh_expr(base),
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                refresh_stmt(stmt);
            }
            if let Some(tail) = tail {
                refresh_expr(tail);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => refresh_expr(expr),
        ExprKind::LocalPushId { body, .. } => refresh_expr(body),
        ExprKind::AddId { thunk, .. } => refresh_expr(thunk),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn refresh_stmt(stmt: &mut Stmt) {
    match stmt {
        Stmt::Let { value, .. } => refresh_expr(value),
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => refresh_expr(expr),
    }
}
