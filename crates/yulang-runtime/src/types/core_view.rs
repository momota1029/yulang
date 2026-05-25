use super::*;

pub(crate) fn strict_core_type(ty: &RuntimeType) -> &typed_ir::Type {
    ty.as_value()
        .expect("runtime IR expected a first-order core type")
}

pub(crate) fn diagnostic_core_type(ty: &RuntimeType) -> typed_ir::Type {
    match ty {
        RuntimeType::Unknown => typed_ir::Type::Unknown,
        RuntimeType::Value(ty) => ty.clone(),
        RuntimeType::Fun { param, ret } => typed_ir::Type::Fun {
            param: Box::new(diagnostic_core_type(param)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(diagnostic_core_type(ret)),
        },
        RuntimeType::Thunk { value, .. } => diagnostic_core_type(value),
    }
}

pub(crate) fn runtime_core_type(ty: &RuntimeType) -> typed_ir::Type {
    match ty {
        RuntimeType::Unknown => typed_ir::Type::Unknown,
        RuntimeType::Value(ty) => ty.clone(),
        RuntimeType::Fun { param, ret } => runtime_core_function_type(param, ret),
        RuntimeType::Thunk { value, .. } => runtime_core_type(value),
    }
}

fn runtime_effected_core_type(ty: &RuntimeType) -> (typed_ir::Type, typed_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (runtime_core_type(value), effect.clone()),
        other => (runtime_core_type(other), typed_ir::Type::Never),
    }
}

fn runtime_core_function_type(param: &RuntimeType, ret: &RuntimeType) -> typed_ir::Type {
    let (param, param_effect) = runtime_effected_core_type(param);
    let (ret, ret_effect) = runtime_effected_core_type(ret);
    typed_ir::Type::Fun {
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
            RuntimeType::thunk(named("io"), RuntimeType::value(named("int"))),
            RuntimeType::thunk(named("undet"), RuntimeType::value(named("bool"))),
        );

        let typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = diagnostic_core_type(&ty)
        else {
            panic!("expected function");
        };

        assert_eq!(*param, named("int"));
        assert_eq!(*param_effect, typed_ir::Type::Never);
        assert_eq!(*ret_effect, typed_ir::Type::Never);
        assert_eq!(*ret, named("bool"));
    }

    #[test]
    fn runtime_core_type_preserves_function_effect_slots() {
        let ty = RuntimeType::fun(
            RuntimeType::thunk(named("io"), RuntimeType::value(named("int"))),
            RuntimeType::thunk(named("undet"), RuntimeType::value(named("bool"))),
        );

        let typed_ir::Type::Fun {
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

    fn named(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
