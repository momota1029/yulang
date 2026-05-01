use super::*;

/// Preserve thunk boundaries that runtime lowering already introduced.
///
/// Monomorphization may make scheme-derived types more concrete, but it must
/// not silently erase `Thunk` wrappers that carry runtime effect semantics.
/// This helper copies the body-side thunk boundary back onto the refreshed
/// scheme type when the two value shapes are compatible.  It is preservation,
/// not thunk creation: new effect boundaries belong in runtime lowering.
pub(super) fn preserve_runtime_thunk_shape(scheme: RuntimeType, body: &RuntimeType) -> RuntimeType {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn named_type(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn row(name: &str) -> core_ir::Type {
        core_ir::Type::Row {
            items: vec![named_type(name)],
            tail: Box::new(core_ir::Type::Never),
        }
    }

    #[test]
    fn preserves_body_thunk_around_compatible_scheme_value() {
        let int = RuntimeType::core(named_type("int"));
        let effect = row("io");
        let body = RuntimeType::thunk(effect.clone(), int.clone());

        let preserved = preserve_runtime_thunk_shape(int.clone(), &body);

        assert_eq!(preserved, RuntimeType::thunk(effect, int));
    }

    #[test]
    fn keeps_nonempty_body_effect_when_scheme_effect_is_empty() {
        let int = RuntimeType::core(named_type("int"));
        let effect = row("undet");
        let scheme = RuntimeType::thunk(core_ir::Type::Never, int.clone());
        let body = RuntimeType::thunk(effect.clone(), int.clone());

        let preserved = preserve_runtime_thunk_shape(scheme, &body);

        assert_eq!(preserved, RuntimeType::thunk(effect, int));
    }

    #[test]
    fn preserves_function_parameter_and_return_thunks_recursively() {
        let unit = RuntimeType::core(named_type("unit"));
        let int = RuntimeType::core(named_type("int"));
        let arg_effect = row("io");
        let ret_effect = row("undet");
        let scheme = RuntimeType::fun(unit.clone(), int.clone());
        let body = RuntimeType::fun(
            RuntimeType::thunk(arg_effect.clone(), unit.clone()),
            RuntimeType::thunk(ret_effect.clone(), int.clone()),
        );

        let preserved = preserve_runtime_thunk_shape(scheme, &body);

        assert_eq!(
            preserved,
            RuntimeType::fun(
                RuntimeType::thunk(arg_effect, unit),
                RuntimeType::thunk(ret_effect, int),
            )
        );
    }
}
