use super::*;
use std::borrow::Cow;

pub(super) fn binding_info_generality(info: &BindingInfo) -> usize {
    info.type_params.len()
}

pub(super) fn require_same_hir_type(
    expected: &RuntimeType,
    actual: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
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
                if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                    eprintln!(
                        "validate same hir thunk {source:?}: {expected_effect:?} / {actual_effect:?}"
                    );
                }
                return Err(RuntimeError::TypeMismatch {
                    expected: expected_effect.clone(),
                    actual: actual_effect.clone(),
                    source,
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
        (expected, actual) => {
            if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                eprintln!("validate same hir fallback {source:?}: {expected:?} / {actual:?}");
            }
            Err(RuntimeError::TypeMismatch {
                expected: diagnostic_core_type(expected),
                actual: diagnostic_core_type(actual),
                source,
            })
        }
    }
}

pub(super) fn require_apply_result_hir_type(
    declared: &RuntimeType,
    actual: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
    match (declared, actual) {
        (
            RuntimeType::Thunk {
                effect: declared_effect,
                value: declared_value,
            },
            RuntimeType::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => {
            if !effect_compatible(actual_effect, declared_effect) {
                if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                    eprintln!(
                        "validate apply result {source:?}: {declared_effect:?} / {actual_effect:?}"
                    );
                }
                return Err(RuntimeError::TypeMismatch {
                    expected: declared_effect.clone(),
                    actual: actual_effect.clone(),
                    source,
                });
            }
            require_same_hir_type(declared_value, actual_value, source)
        }
        (declared, RuntimeType::Thunk { value, .. }) => {
            require_same_hir_type(declared, value, source)
        }
        _ => require_same_hir_type(declared, actual, source),
    }
}

pub(super) fn validate_hir_type_no_any(
    ty: &RuntimeType,
    source: TypeSource,
    type_arg_kinds: &TypeArgKinds,
) -> RuntimeResult<()> {
    match ty {
        RuntimeType::Core(ty) => validate_core_type_no_any(ty, source, type_arg_kinds),
        RuntimeType::Fun { param, ret } => {
            validate_hir_type_no_any(param, source, type_arg_kinds)?;
            validate_hir_type_no_any(ret, source, type_arg_kinds)
        }
        RuntimeType::Thunk { effect, value } => {
            validate_effect_type_no_any(effect, source, type_arg_kinds)?;
            validate_hir_type_no_any(value, source, type_arg_kinds)
        }
    }
}

pub(super) fn validate_effect_type_no_any(
    ty: &core_ir::Type,
    source: TypeSource,
    type_arg_kinds: &TypeArgKinds,
) -> RuntimeResult<()> {
    let mut allowed_vars = BTreeSet::new();
    collect_type_vars(ty, &mut allowed_vars);
    if contains_non_runtime_type_inner(ty, true, &allowed_vars, type_arg_kinds) {
        return Err(RuntimeError::NonRuntimeType {
            ty: ty.clone(),
            source,
        });
    }
    Ok(())
}

pub(super) fn validate_substitution_type_no_any(
    ty: &core_ir::Type,
    source: TypeSource,
    type_arg_kinds: &TypeArgKinds,
) -> RuntimeResult<()> {
    let mut allowed_vars = BTreeSet::new();
    collect_type_vars(ty, &mut allowed_vars);
    if contains_non_runtime_type_inner(ty, false, &allowed_vars, type_arg_kinds)
        && contains_non_runtime_type_inner(ty, true, &allowed_vars, type_arg_kinds)
    {
        return Err(RuntimeError::NonRuntimeType {
            ty: ty.clone(),
            source,
        });
    }
    Ok(())
}

pub(super) fn validate_core_type_no_any(
    ty: &core_ir::Type,
    source: TypeSource,
    type_arg_kinds: &TypeArgKinds,
) -> RuntimeResult<()> {
    let mut allowed_vars = BTreeSet::new();
    collect_type_vars(ty, &mut allowed_vars);
    if contains_non_runtime_type_inner(ty, false, &allowed_vars, type_arg_kinds) {
        return Err(RuntimeError::NonRuntimeType {
            ty: ty.clone(),
            source,
        });
    }
    Ok(())
}

fn contains_non_runtime_type_inner(
    ty: &core_ir::Type,
    effect_slot: bool,
    allowed_vars: &BTreeSet<core_ir::TypeVar>,
    type_arg_kinds: &TypeArgKinds,
) -> bool {
    match ty {
        core_ir::Type::Never | core_ir::Type::Any => false,
        core_ir::Type::Var(var) => !allowed_vars.contains(var),
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) if effect_slot => items
            .iter()
            .any(|item| contains_non_runtime_type_inner(item, true, allowed_vars, type_arg_kinds)),
        core_ir::Type::Union(items) | core_ir::Type::Inter(items)
            if same_runtime_value_choice(items, allowed_vars, type_arg_kinds) =>
        {
            false
        }
        core_ir::Type::Union(_) | core_ir::Type::Inter(_) => true,
        core_ir::Type::Row { .. } => !effect_slot,
        core_ir::Type::Named { path, args } => args.iter().enumerate().any(|(index, arg)| {
            let arg_effect_slot = type_arg_kinds
                .get(path)
                .and_then(|kinds| kinds.get(index))
                .is_some_and(|kind| *kind == TypeArgKind::Effect);
            match arg {
                core_ir::TypeArg::Type(ty) => contains_non_runtime_type_inner(
                    ty,
                    arg_effect_slot,
                    allowed_vars,
                    type_arg_kinds,
                ),
                core_ir::TypeArg::Bounds(bounds) => {
                    choose_bounds_type(bounds, BoundsChoice::RuntimeValue).is_some_and(|ty| {
                        contains_non_runtime_type_inner(
                            &ty,
                            arg_effect_slot,
                            allowed_vars,
                            type_arg_kinds,
                        )
                    })
                }
            }
        }),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            contains_non_runtime_type_inner(param, false, allowed_vars, type_arg_kinds)
                || contains_non_runtime_type_inner(param_effect, true, allowed_vars, type_arg_kinds)
                || contains_non_runtime_type_inner(ret_effect, true, allowed_vars, type_arg_kinds)
                || contains_non_runtime_type_inner(ret, false, allowed_vars, type_arg_kinds)
        }
        core_ir::Type::Tuple(items) => items
            .iter()
            .any(|item| contains_non_runtime_type_inner(item, false, allowed_vars, type_arg_kinds)),
        core_ir::Type::Record(record) => {
            record.fields.iter().any(|field| {
                contains_non_runtime_type_inner(&field.value, false, allowed_vars, type_arg_kinds)
            }) || record.spread.as_ref().is_some_and(|spread| match spread {
                core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                    contains_non_runtime_type_inner(ty, false, allowed_vars, type_arg_kinds)
                }
            })
        }
        core_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads.iter().any(|payload| {
                    contains_non_runtime_type_inner(payload, false, allowed_vars, type_arg_kinds)
                })
            }) || variant.tail.as_deref().is_some_and(|tail| {
                contains_non_runtime_type_inner(tail, false, allowed_vars, type_arg_kinds)
            })
        }
        core_ir::Type::Recursive { body, .. } => {
            contains_non_runtime_type_inner(body, false, allowed_vars, type_arg_kinds)
        }
    }
}

pub(super) fn require_apply_arg_hir_type(
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
                if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                    eprintln!(
                        "validate apply arg {source:?}: {expected_effect:?} / {actual_effect:?}"
                    );
                }
                return Err(RuntimeError::TypeMismatch {
                    expected: expected_effect.clone(),
                    actual: actual_effect.clone(),
                    source,
                });
            }
            require_same_hir_type(expected_value, actual_value, source)
        }
        _ => require_same_hir_type(expected, actual, source),
    }
}

fn same_runtime_value_choice(
    items: &[core_ir::Type],
    allowed_vars: &BTreeSet<core_ir::TypeVar>,
    type_arg_kinds: &TypeArgKinds,
) -> bool {
    let Some(first) = items.first() else {
        return false;
    };
    !contains_non_runtime_type_inner(first, false, allowed_vars, type_arg_kinds)
        && items.iter().skip(1).all(|item| {
            !contains_non_runtime_type_inner(item, false, allowed_vars, type_arg_kinds)
                && core_types_compatible(first, item)
                && core_types_compatible(item, first)
        })
}

pub(super) fn hir_value_core_type(ty: &RuntimeType) -> Cow<'_, core_ir::Type> {
    match ty {
        RuntimeType::Core(ty) => Cow::Borrowed(ty),
        RuntimeType::Thunk { value, .. } => match value.as_ref() {
            RuntimeType::Core(ty) => Cow::Borrowed(ty),
            other => Cow::Owned(runtime_core_type(other)),
        },
        RuntimeType::Fun { .. } => Cow::Owned(runtime_core_type(ty)),
    }
}

pub(super) fn is_constructor_path_for_type(path: &core_ir::Path, ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Core(core_ir::Type::Named {
            path: type_path, ..
        }) => constructor_parent_matches(path, type_path, "nil"),
        RuntimeType::Fun { ret, .. } => {
            let RuntimeType::Core(core_ir::Type::Named {
                path: type_path, ..
            }) = ret.as_ref()
            else {
                return false;
            };
            constructor_parent_matches(path, type_path, "just")
        }
        _ => false,
    }
}

pub(super) fn constructor_parent_matches(
    path: &core_ir::Path,
    type_path: &core_ir::Path,
    tag: &str,
) -> bool {
    path.segments.len() == type_path.segments.len() + 1
        && path.segments.last().is_some_and(|name| name.0 == tag)
        && path
            .segments
            .iter()
            .zip(&type_path.segments)
            .all(|(left, right)| left == right)
}

pub(super) fn bool_type() -> core_ir::Type {
    core_ir::Type::Named {
        path: core_ir::Path::from_name(core_ir::Name("bool".to_string())),
        args: Vec::new(),
    }
}

pub(super) fn effect_id_type() -> core_ir::Type {
    core_ir::Type::Named {
        path: core_ir::Path::from_name(core_ir::Name("__effect_id".to_string())),
        args: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Expr, ExprKind, Module, Root, Type};

    #[test]
    fn thunk_type_allows_effect_row() {
        let value_ty = bool_type();
        let effect = core_ir::Type::Row {
            items: vec![named_type("junction")],
            tail: Box::new(core_ir::Type::Never),
        };
        let inner = Expr::typed(ExprKind::Lit(core_ir::Lit::Bool(true)), value_ty.clone());
        let thunk_ty = Type::thunk(effect.clone(), Type::core(value_ty.clone()));
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Thunk {
                    effect,
                    value: Type::core(value_ty),
                    expr: Box::new(inner),
                },
                thunk_ty,
            )],
            roots: vec![Root::Expr(0)],
        };

        validate_module(&module).expect("valid thunk row");
    }

    #[test]
    fn record_pattern_default_allows_missing_expected_field() {
        let int = named_type("int");
        let value_ty = core_ir::Type::Record(core_ir::RecordType {
            fields: vec![core_ir::RecordField {
                name: core_ir::Name("base".to_string()),
                value: int.clone(),
                optional: false,
            }],
            spread: None,
        });
        let pattern_ty = Type::core(core_ir::Type::Record(core_ir::RecordType {
            fields: vec![
                core_ir::RecordField {
                    name: core_ir::Name("base".to_string()),
                    value: int.clone(),
                    optional: false,
                },
                core_ir::RecordField {
                    name: core_ir::Name("extra".to_string()),
                    value: int.clone(),
                    optional: true,
                },
            ],
            spread: None,
        }));
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Block {
                    stmts: vec![crate::ir::Stmt::Let {
                        pattern: crate::ir::Pattern::Record {
                            fields: vec![
                                crate::ir::RecordPatternField {
                                    name: core_ir::Name("base".to_string()),
                                    pattern: crate::ir::Pattern::Bind {
                                        name: core_ir::Name("base".to_string()),
                                        ty: Type::core(int.clone()),
                                    },
                                    default: None,
                                },
                                crate::ir::RecordPatternField {
                                    name: core_ir::Name("extra".to_string()),
                                    pattern: crate::ir::Pattern::Bind {
                                        name: core_ir::Name("extra".to_string()),
                                        ty: Type::core(int.clone()),
                                    },
                                    default: Some(Expr::typed(
                                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                        Type::core(int.clone()),
                                    )),
                                },
                            ],
                            spread: None,
                            ty: pattern_ty,
                        },
                        value: Expr::typed(
                            ExprKind::Record {
                                fields: vec![crate::ir::RecordExprField {
                                    name: core_ir::Name("base".to_string()),
                                    value: Expr::typed(
                                        ExprKind::Lit(core_ir::Lit::Int("3".to_string())),
                                        Type::core(int.clone()),
                                    ),
                                }],
                                spread: None,
                            },
                            Type::core(value_ty),
                        ),
                    }],
                    tail: Some(Box::new(Expr::typed(
                        ExprKind::Var(core_ir::Path::from_name(core_ir::Name("extra".to_string()))),
                        Type::core(int.clone()),
                    ))),
                },
                Type::core(int),
            )],
            roots: vec![Root::Expr(0)],
        };

        validate_module(&module).expect("valid record default pattern");
    }

    fn named_type(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
