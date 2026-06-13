//! Runtime boundary checks shared by validation and execution.

use mono::Type;

pub(crate) fn function_parts(ty: &Type) -> Option<(&Type, &Type)> {
    let Type::Fun { arg, ret, .. } = ty else {
        return None;
    };
    Some((arg, ret))
}

pub(crate) fn thunk_value_type(ty: &Type) -> Option<&Type> {
    let Type::Thunk { value, .. } = ty else {
        return None;
    };
    Some(value)
}

pub(crate) fn equivalent_runtime_types(source: &Type, target: &Type) -> bool {
    if source == target || source.is_pure_effect() && target.is_pure_effect() {
        return true;
    }
    match (source, target) {
        (source, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            equivalent_runtime_types(source, value)
        }
        (Type::Thunk { effect, value }, target) if effect.is_pure_effect() => {
            equivalent_runtime_types(value, target)
        }
        _ => false,
    }
}

pub(crate) fn value_boundary_supported(source: &Type, target: &Type) -> bool {
    if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
        return true;
    }
    if matches!(source, Type::Never) {
        return true;
    }
    match (source, target) {
        (Type::Thunk { value: source, .. }, Type::Thunk { value: target, .. }) => {
            value_boundary_supported(source, target)
        }
        (Type::Thunk { value: source, .. }, target) => value_boundary_supported(source, target),
        (source, Type::Thunk { value: target, .. }) => value_boundary_supported(source, target),
        _ => false,
    }
}

pub(crate) fn function_boundary_supported(source: &Type, target: &Type) -> bool {
    let Some((source_arg, source_ret)) = function_parts(source) else {
        return false;
    };
    let Some((target_arg, target_ret)) = function_parts(target) else {
        return false;
    };
    value_boundary_supported(target_arg, source_arg)
        && value_boundary_supported(source_ret, target_ret)
}
