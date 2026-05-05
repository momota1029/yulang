use super::*;

pub(super) fn should_use_graph_binding_type(
    scheme_ty: &core_ir::Type,
    graph_ty: &core_ir::Type,
) -> bool {
    matches!(scheme_ty, core_ir::Type::Any) && !matches!(graph_ty, core_ir::Type::Any)
}

pub(super) fn prefer_alias_target_runtime_type(
    current: &RuntimeType,
    target: &RuntimeType,
) -> bool {
    if !hir_type_compatible(current, target) {
        return false;
    }
    let current_imprecision = hir_type_imprecision_count(current);
    let target_imprecision = hir_type_imprecision_count(target);
    if target_imprecision != current_imprecision {
        return target_imprecision < current_imprecision;
    }
    hir_type_var_count(target) < hir_type_var_count(current)
}

pub(super) fn choose_local_type_hint(
    stored: Option<RuntimeType>,
    expected: Option<RuntimeType>,
) -> Option<RuntimeType> {
    match (stored, expected) {
        (Some(stored @ RuntimeType::Core(core_ir::Type::Never)), _) => Some(stored),
        (Some(RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_))), Some(expected)) => {
            Some(expected)
        }
        (Some(stored), Some(expected)) if hir_type_compatible(&expected, &stored) => {
            Some(more_informative_hir_type(&expected, &stored))
        }
        (Some(stored), _) => Some(stored),
        (None, expected) => expected,
    }
}

pub(super) fn choose_polymorphic_binding_type_hint(
    stored: Option<RuntimeType>,
    expected: Option<RuntimeType>,
) -> Option<RuntimeType> {
    match (stored, expected) {
        (Some(_), Some(expected)) if !runtime_type_is_imprecise_runtime_slot(&expected) => {
            Some(expected)
        }
        (Some(stored), _) => Some(stored),
        (None, expected) => expected,
    }
}

pub(super) fn choose_hir_type_hint(
    primary: Option<RuntimeType>,
    fallback: Option<RuntimeType>,
) -> Option<RuntimeType> {
    match primary {
        Some(primary) if runtime_type_is_imprecise_runtime_slot(&primary) => {
            fallback.or(Some(primary))
        }
        Some(primary) => Some(primary),
        None => fallback,
    }
}

pub(super) fn choose_apply_arg_type(
    evidence_arg: Option<RuntimeType>,
    param_hint: Option<RuntimeType>,
) -> Option<RuntimeType> {
    match (&evidence_arg, &param_hint) {
        (_, Some(param @ RuntimeType::Thunk { .. })) => Some(param.clone()),
        _ => choose_hir_type_hint(evidence_arg, param_hint),
    }
}

pub(super) fn expected_arg_evidence_runtime_usable(ty: &RuntimeType) -> bool {
    !hir_type_has_type_vars(ty)
        && !hir_type_is_hole(ty)
        && !matches!(
            ty,
            RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Never | core_ir::Type::Var(_))
        )
}

pub(super) fn choose_apply_callee_type(
    evidence_callee: Option<RuntimeType>,
    stored_callee: Option<RuntimeType>,
) -> Option<RuntimeType> {
    choose_local_type_hint(stored_callee, evidence_callee)
}

pub(super) fn choose_apply_result_type(
    evidence_result: Option<RuntimeType>,
    ret_hint: Option<RuntimeType>,
    callee_is_local: bool,
) -> Option<RuntimeType> {
    match (callee_is_local, evidence_result, ret_hint) {
        (true, _, Some(ret_hint)) => Some(ret_hint),
        (_, evidence_result, ret_hint) => choose_hir_type_hint(evidence_result, ret_hint),
    }
}

pub(super) fn choose_expected_hir_type(
    ty: RuntimeType,
    expected: Option<RuntimeType>,
) -> Option<RuntimeType> {
    match (&ty, expected) {
        (RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_)), Some(expected)) => {
            Some(expected)
        }
        (_, Some(expected)) if hir_type_compatible(&expected, &ty) => {
            Some(more_informative_hir_type(&expected, &ty))
        }
        _ => Some(ty),
    }
}

pub(super) fn more_informative_hir_type(
    expected: &RuntimeType,
    actual: &RuntimeType,
) -> RuntimeType {
    let expected_imprecision = hir_type_imprecision_count(expected);
    let actual_imprecision = hir_type_imprecision_count(actual);
    if actual_imprecision < expected_imprecision
        || actual_imprecision == expected_imprecision
            && hir_type_var_count(actual) < hir_type_var_count(expected)
    {
        actual.clone()
    } else {
        expected.clone()
    }
}

fn hir_type_var_count(ty: &RuntimeType) -> usize {
    let mut vars = BTreeSet::new();
    collect_hir_type_vars(ty, &mut vars);
    vars.len()
}

pub(super) fn merge_visible_type_options(
    left: Option<core_ir::Type>,
    right: Option<core_ir::Type>,
) -> Option<core_ir::Type> {
    choose_optional_core_type(left, right, TypeChoice::VisiblePrincipal)
}

pub(super) fn require_apply_result_compatible(
    expected: &RuntimeType,
    actual: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
    if runtime_type_contains_unknown(expected) || runtime_type_contains_unknown(actual) {
        return Ok(());
    }
    let expected_core = diagnostic_core_type(expected);
    let actual_core = diagnostic_core_type(actual);
    if core_types_compatible(&expected_core, &actual_core)
        || effect_compatible(&expected_core, &actual_core)
        || effect_compatible(&actual_core, &expected_core)
        || apply_result_includes_expected(expected, actual)
        || hir_type_compatible(expected, actual)
        || hir_type_compatible(expected, value_hir_type(actual))
    {
        Ok(())
    } else {
        if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
            eprintln!("lower apply result {source:?}: {expected:?} / {actual:?}");
        }
        Err(RuntimeError::TypeMismatch {
            expected: diagnostic_core_type(expected),
            actual: diagnostic_core_type(actual),
            source,
            context: None,
        })
    }
}

fn apply_result_includes_expected(expected: &RuntimeType, actual: &RuntimeType) -> bool {
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
            effect_compatible(actual_effect, expected_effect)
                && hir_type_compatible(expected_value, actual_value)
        }
        (expected, RuntimeType::Thunk { value, .. }) => hir_type_compatible(expected, value),
        _ => false,
    }
}

pub(super) fn hir_type_compatible(expected: &RuntimeType, actual: &RuntimeType) -> bool {
    match (expected, actual) {
        (RuntimeType::Core(expected), RuntimeType::Core(actual)) => {
            core_types_compatible(expected, actual)
        }
        (RuntimeType::Core(expected), actual @ RuntimeType::Fun { .. })
        | (actual @ RuntimeType::Fun { .. }, RuntimeType::Core(expected)) => {
            core_types_compatible(expected, &diagnostic_core_type(actual))
        }
        (RuntimeType::Core(expected), RuntimeType::Thunk { value, .. }) => {
            core_types_compatible(expected, &diagnostic_core_type(value))
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
            hir_type_compatible(expected_param, actual_param)
                && hir_type_compatible(expected_ret, actual_ret)
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
            type_compatible(expected_effect, actual_effect)
                && hir_type_compatible(expected_value, actual_value)
        }
        (RuntimeType::Thunk { value, .. }, actual) => hir_type_compatible(value, actual),
        _ => false,
    }
}
