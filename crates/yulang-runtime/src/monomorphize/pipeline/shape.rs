use super::*;

pub(super) fn core_value_type(ty: &RuntimeType) -> core_ir::Type {
    match ty {
        RuntimeType::Unknown => core_ir::Type::Unknown,
        RuntimeType::Core(ty) => ty.clone(),
        RuntimeType::Fun { param, ret } => effected_function_core_type(param, ret),
        RuntimeType::Thunk { value, .. } => core_value_type(value),
    }
}

pub(super) fn core_function_as_hir_type(ty: &RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Core(core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        }) => RuntimeType::fun(
            effected_core_as_hir_type(param, param_effect),
            effected_core_as_hir_type(ret, ret_effect),
        ),
        other => other.clone(),
    }
}

fn effected_function_core_type(param: &RuntimeType, ret: &RuntimeType) -> core_ir::Type {
    let (param, param_effect) = effected_core_type(param);
    let (ret, ret_effect) = effected_core_type(ret);
    core_ir::Type::Fun {
        param: Box::new(param),
        param_effect: Box::new(param_effect),
        ret_effect: Box::new(ret_effect),
        ret: Box::new(ret),
    }
}

fn effected_core_type(ty: &RuntimeType) -> (core_ir::Type, core_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (core_value_type(value), effect.clone()),
        other => (core_value_type(other), core_ir::Type::Never),
    }
}

fn effected_core_as_hir_type(value: &core_ir::Type, effect: &core_ir::Type) -> RuntimeType {
    let value = normalize_hir_function_type(RuntimeType::core(value.clone()));
    let effect = project_runtime_effect(effect);
    if should_thunk_effect(&effect) {
        RuntimeType::thunk(effect, value)
    } else {
        value
    }
}
