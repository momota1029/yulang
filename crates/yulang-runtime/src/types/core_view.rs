use super::*;

pub(crate) fn strict_core_type(ty: &RuntimeType) -> &core_ir::Type {
    ty.as_core()
        .expect("runtime IR expected a first-order core type")
}

pub(crate) fn diagnostic_core_type(ty: &RuntimeType) -> core_ir::Type {
    match ty {
        RuntimeType::Unknown => core_ir::Type::Unknown,
        RuntimeType::Core(ty) => ty.clone(),
        RuntimeType::Fun { param, ret } => core_ir::Type::Fun {
            param: Box::new(diagnostic_core_type(param)),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(diagnostic_core_type(ret)),
        },
        RuntimeType::Thunk { value, .. } => diagnostic_core_type(value),
    }
}

pub(crate) fn runtime_core_type(ty: &RuntimeType) -> core_ir::Type {
    match ty {
        RuntimeType::Unknown => core_ir::Type::Unknown,
        RuntimeType::Core(ty) => ty.clone(),
        RuntimeType::Fun { param, ret } => runtime_core_function_type(param, ret),
        RuntimeType::Thunk { value, .. } => runtime_core_type(value),
    }
}

fn runtime_effected_core_type(ty: &RuntimeType) -> (core_ir::Type, core_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (runtime_core_type(value), effect.clone()),
        other => (runtime_core_type(other), core_ir::Type::Never),
    }
}

fn runtime_core_function_type(param: &RuntimeType, ret: &RuntimeType) -> core_ir::Type {
    let (param, param_effect) = runtime_effected_core_type(param);
    let (ret, ret_effect) = runtime_effected_core_type(ret);
    core_ir::Type::Fun {
        param: Box::new(param),
        param_effect: Box::new(param_effect),
        ret_effect: Box::new(ret_effect),
        ret: Box::new(ret),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_core_type_erases_thunk_effects() {
        let ty = RuntimeType::fun(
            RuntimeType::thunk(named("io"), RuntimeType::core(named("int"))),
            RuntimeType::thunk(named("undet"), RuntimeType::core(named("bool"))),
        );

        let core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = diagnostic_core_type(&ty)
        else {
            panic!("expected function");
        };

        assert_eq!(*param, named("int"));
        assert_eq!(*param_effect, core_ir::Type::Never);
        assert_eq!(*ret_effect, core_ir::Type::Never);
        assert_eq!(*ret, named("bool"));
    }

    #[test]
    fn runtime_core_type_preserves_function_effect_slots() {
        let ty = RuntimeType::fun(
            RuntimeType::thunk(named("io"), RuntimeType::core(named("int"))),
            RuntimeType::thunk(named("undet"), RuntimeType::core(named("bool"))),
        );

        let core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = runtime_core_type(&ty)
        else {
            panic!("expected function");
        };

        assert_eq!(*param, named("int"));
        assert_eq!(*param_effect, named("io"));
        assert_eq!(*ret_effect, named("undet"));
        assert_eq!(*ret, named("bool"));
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
