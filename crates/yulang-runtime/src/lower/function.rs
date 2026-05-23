use super::*;

#[derive(Clone)]
pub(super) struct FunctionParts {
    pub(super) param: RuntimeType,
    pub(super) ret: RuntimeType,
}

pub(super) fn function_parts(ty: &RuntimeType) -> RuntimeResult<FunctionParts> {
    match ty {
        RuntimeType::Fun { param, ret } => Ok(FunctionParts {
            param: (**param).clone(),
            ret: (**ret).clone(),
        }),
        RuntimeType::Core(core @ typed_ir::Type::Fun { .. }) => {
            let ty = project_runtime_hir_type_with_vars(core, &BTreeSet::new());
            function_parts(&ty)
        }
        RuntimeType::Thunk { value, .. } => function_parts(value),
        other => Err(RuntimeError::NonFunctionCallee {
            ty: diagnostic_core_type(other),
        }),
    }
}

pub(super) fn bind_here_if_thunk(expr: Expr, value_ty: RuntimeType) -> Expr {
    if matches!(expr.ty, RuntimeType::Thunk { .. }) {
        Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(expr),
            },
            value_ty,
        )
    } else {
        expr
    }
}

pub(super) fn erased_fun_type(param: RuntimeType, ret: RuntimeType) -> RuntimeType {
    RuntimeType::fun(param, ret)
}

pub(super) fn runtime_bounds_type(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    project_runtime_bounds(bounds)
}

pub(super) fn record_field_expected(
    expected: Option<&typed_ir::Type>,
    name: &typed_ir::Name,
) -> Option<typed_ir::Type> {
    match expected {
        Some(typed_ir::Type::Record(record)) => record
            .fields
            .iter()
            .find(|field| field.name == *name)
            .map(|field| field.value.clone()),
        _ => None,
    }
}

pub(super) fn variant_payload_expected(
    lowerer: &Lowerer<'_>,
    expected: Option<&typed_ir::Type>,
    tag: &typed_ir::Name,
) -> Option<typed_ir::Type> {
    match expected {
        Some(typed_ir::Type::Variant(variant)) => {
            variant_payload_expected_from_variant(variant, tag)
        }
        Some(typed_ir::Type::Named { path, args }) => {
            named_variant_payload_expected_from_graph(lowerer, path, args, tag).or_else(|| {
                named_variant_payload_expected_from_constructor(lowerer, path, args, tag)
            })
        }
        Some(typed_ir::Type::Union(items) | typed_ir::Type::Inter(items)) => items
            .iter()
            .find_map(|item| variant_payload_expected(lowerer, Some(item), tag)),
        _ => None,
    }
}

fn named_variant_payload_expected_from_graph(
    lowerer: &Lowerer<'_>,
    path: &typed_ir::Path,
    args: &[typed_ir::TypeArg],
    tag: &typed_ir::Name,
) -> Option<typed_ir::Type> {
    let node = lowerer
        .graph
        .enum_variants
        .iter()
        .find(|node| node.enum_path == *path && node.tag == *tag)?;
    let payload = node.payload.as_ref()?;
    let substitutions = node
        .type_params
        .iter()
        .zip(args.iter())
        .filter_map(|(param, arg)| type_arg_to_core_type(arg).map(|ty| (param.clone(), ty)))
        .collect::<HashMap<_, _>>();
    Some(substitute_pattern_type_vars(payload, &substitutions))
}

fn type_arg_to_core_type(arg: &typed_ir::TypeArg) -> Option<typed_ir::Type> {
    match arg {
        typed_ir::TypeArg::Type(ty) => Some(ty.clone()),
        typed_ir::TypeArg::Bounds(bounds) => runtime_bounds_type(bounds),
    }
}

fn named_variant_payload_expected_from_constructor(
    lowerer: &Lowerer<'_>,
    path: &typed_ir::Path,
    args: &[typed_ir::TypeArg],
    tag: &typed_ir::Name,
) -> Option<typed_ir::Type> {
    let mut constructor_path = path.clone();
    constructor_path.push(tag.clone());
    named_variant_payload_from_constructor(lowerer.env.get(&constructor_path), path, args).or_else(
        || {
            lowerer.env.iter().find_map(|(candidate_path, candidate)| {
                (candidate_path.segments.last() == Some(tag))
                    .then(|| named_variant_payload_from_constructor(Some(candidate), path, args))
                    .flatten()
            })
        },
    )
}

fn named_variant_payload_from_constructor(
    constructor: Option<&RuntimeType>,
    path: &typed_ir::Path,
    args: &[typed_ir::TypeArg],
) -> Option<typed_ir::Type> {
    let (param, ret) = runtime_constructor_parts(constructor?)?;
    let RuntimeType::Core(typed_ir::Type::Named {
        path: ret_path,
        args: ret_args,
    }) = &ret
    else {
        return None;
    };
    if ret_path != path || ret_args.len() != args.len() {
        return None;
    }
    let RuntimeType::Core(param) = param else {
        return None;
    };
    let substitutions = ret_args
        .iter()
        .zip(args.iter())
        .filter_map(|(from, to)| match (from, to) {
            (typed_ir::TypeArg::Type(typed_ir::Type::Var(var)), typed_ir::TypeArg::Type(ty)) => {
                Some((var.clone(), ty.clone()))
            }
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    Some(substitute_pattern_type_vars(&param, &substitutions))
}

fn variant_payload_expected_from_variant(
    variant: &typed_ir::VariantType,
    tag: &typed_ir::Name,
) -> Option<typed_ir::Type> {
    variant
        .cases
        .iter()
        .find(|case| case.name == *tag)
        .and_then(|case| variant_case_payload_value_type(&case.payloads))
}

fn variant_case_payload_value_type(payloads: &[typed_ir::Type]) -> Option<typed_ir::Type> {
    match payloads {
        [] => None,
        [payload] => Some(payload.clone()),
        payloads => Some(typed_ir::Type::Tuple(payloads.to_vec())),
    }
}

pub(super) fn runtime_constructor_parts(ty: &RuntimeType) -> Option<(RuntimeType, RuntimeType)> {
    match ty {
        RuntimeType::Fun { param, ret } => Some((param.as_ref().clone(), ret.as_ref().clone())),
        RuntimeType::Core(typed_ir::Type::Fun { param, ret, .. }) => Some((
            RuntimeType::core((**param).clone()),
            RuntimeType::core((**ret).clone()),
        )),
        _ => None,
    }
}

pub(super) fn select_field_type(
    ty: &typed_ir::Type,
    field: &typed_ir::Name,
) -> RuntimeResult<typed_ir::Type> {
    match ty {
        typed_ir::Type::Any => Ok(typed_ir::Type::Any),
        typed_ir::Type::Record(record) => record
            .fields
            .iter()
            .find(|candidate| candidate.name == *field)
            .map(|candidate| candidate.value.clone())
            .ok_or_else(|| RuntimeError::UnsupportedSelectBase {
                field: field.clone(),
                ty: ty.clone(),
            }),
        _ => Err(RuntimeError::UnsupportedSelectBase {
            field: field.clone(),
            ty: ty.clone(),
        }),
    }
}

pub(super) fn unary_runtime_container_item_type(ty: &typed_ir::Type) -> Option<typed_ir::Type> {
    match ty {
        typed_ir::Type::Named { args, .. } if args.len() == 1 => {
            args.first().and_then(|arg| match arg {
                typed_ir::TypeArg::Type(ty) => Some(ty.clone()),
                typed_ir::TypeArg::Bounds(bounds) => runtime_bounds_type(bounds),
            })
        }
        _ => None,
    }
}

pub(super) fn require_same_type(
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
    source: TypeSource,
) -> RuntimeResult<()> {
    if core_types_compatible(expected, actual)
        || effect_compatible(expected, actual)
        || effect_compatible(actual, expected)
    {
        return Ok(());
    }
    if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
        eprintln!("lower require_same_type {source:?}: {expected:?} / {actual:?}");
    }
    Err(RuntimeError::TypeMismatch {
        expected: expected.clone(),
        actual: actual.clone(),
        source,
        context: None,
    })
}

pub(super) fn should_use_visible_root_type(
    graph: &typed_ir::Type,
    visible: &typed_ir::Type,
) -> bool {
    (matches!(graph, typed_ir::Type::Any) && !matches!(visible, typed_ir::Type::Any))
        || matches!(
            (graph, visible),
            (typed_ir::Type::Tuple(graph_items), typed_ir::Type::Tuple(visible_items))
                if graph_items.len() != visible_items.len()
        )
        || (!is_concrete_visible_root_type(graph)
            && !core_types_compatible(graph, visible)
            && is_concrete_visible_root_type(visible)
            && !contains_non_runtime_type(visible))
}

pub(super) fn can_use_visible_root_type_without_graph(
    expr: &typed_ir::Expr,
    visible: &typed_ir::Type,
) -> bool {
    matches!(expr, typed_ir::Expr::Var(_) | typed_ir::Expr::Tuple(_))
        || (matches!(expr, typed_ir::Expr::Apply { .. }) && is_concrete_visible_root_type(visible))
}

pub(super) fn is_concrete_visible_root_type(ty: &typed_ir::Type) -> bool {
    if matches!(ty, typed_ir::Type::Any) {
        return false;
    }
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars.is_empty()
}

pub(super) fn require_same_hir_type(
    expected: &RuntimeType,
    actual: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
    if runtime_type_contains_unknown(expected) || runtime_type_contains_unknown(actual) {
        return Ok(());
    }
    match (expected, actual) {
        (RuntimeType::Core(expected), RuntimeType::Core(actual)) => {
            require_same_type(expected, actual, source)
        }
        (RuntimeType::Core(expected), actual @ RuntimeType::Fun { .. })
        | (actual @ RuntimeType::Fun { .. }, RuntimeType::Core(expected)) => {
            require_same_type(expected, &diagnostic_core_type(actual), source)
        }
        (RuntimeType::Core(expected), RuntimeType::Thunk { value, .. }) => {
            require_same_type(expected, &diagnostic_core_type(value), source)
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
        ) => {
            require_same_hir_type(expected_param, actual_param, source)?;
            require_same_hir_type(expected_ret, actual_ret, source)
        }
        (
            RuntimeType::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
            RuntimeType::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => {
            if !effect_compatible(expected_effect, actual_effect)
                && !effect_compatible(actual_effect, expected_effect)
            {
                if apply_evidence_allows_residual_thunk_effect(source, expected_value, actual_value)
                {
                    return Ok(());
                }
                return Err(RuntimeError::TypeMismatch {
                    expected: expected_effect.clone(),
                    actual: actual_effect.clone(),
                    source,
                    context: None,
                });
            }
            require_same_hir_type(expected_value, actual_value, source)
        }
        (RuntimeType::Thunk { value, .. }, actual) => require_same_hir_type(value, actual, source),
        (expected, actual)
            if core_types_compatible(
                &diagnostic_core_type(expected),
                &diagnostic_core_type(actual),
            ) =>
        {
            Ok(())
        }
        (expected, actual) => Err(RuntimeError::TypeMismatch {
            expected: diagnostic_core_type(expected),
            actual: diagnostic_core_type(actual),
            source,
            context: None,
        }),
    }
}

pub(super) fn require_apply_arg_compatible(
    expected: &RuntimeType,
    actual: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
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
        ) => {
            if !effect_compatible(expected_effect, actual_effect)
                && !effect_compatible(actual_effect, expected_effect)
            {
                if apply_evidence_allows_residual_thunk_effect(source, expected_value, actual_value)
                {
                    return Ok(());
                }
                return Err(RuntimeError::TypeMismatch {
                    expected: expected_effect.clone(),
                    actual: actual_effect.clone(),
                    source,
                    context: None,
                });
            }
            require_same_hir_type(expected_value, actual_value, source)
        }
        _ => require_same_hir_type(expected, actual, source),
    }
}

fn apply_evidence_allows_residual_thunk_effect(
    source: TypeSource,
    expected_value: &RuntimeType,
    actual_value: &RuntimeType,
) -> bool {
    matches!(
        source,
        TypeSource::ApplyEvidence
            | TypeSource::ApplyArgumentEvidence
            | TypeSource::ApplyArgumentSourceEdge
    ) && hir_type_compatible(expected_value, actual_value)
}
