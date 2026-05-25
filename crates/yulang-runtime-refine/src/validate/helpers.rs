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
    if runtime_type_contains_unknown(expected) || runtime_type_contains_unknown(actual) {
        return Ok(());
    }
    match (expected, actual) {
        (RuntimeType::Value(expected), RuntimeType::Value(actual)) => {
            require_same_type(expected, actual, source)
        }
        (RuntimeType::Value(expected), actual @ RuntimeType::Fun { .. })
        | (actual @ RuntimeType::Fun { .. }, RuntimeType::Value(expected)) => {
            require_same_type(expected, &diagnostic_core_type(actual), source)
        }
        (RuntimeType::Value(expected), RuntimeType::Thunk { value, .. }) => {
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
                if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                    eprintln!(
                        "validate same hir thunk {source:?}: {expected_effect:?} / {actual_effect:?}"
                    );
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
        (expected, actual) => {
            if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                eprintln!("validate same hir fallback {source:?}: {expected:?} / {actual:?}");
            }
            Err(RuntimeError::TypeMismatch {
                expected: diagnostic_core_type(expected),
                actual: diagnostic_core_type(actual),
                source,
                context: None,
            })
        }
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

fn hir_type_compatible(expected: &RuntimeType, actual: &RuntimeType) -> bool {
    match (expected, actual) {
        (RuntimeType::Value(expected), RuntimeType::Value(actual)) => {
            core_types_compatible(expected, actual)
        }
        (RuntimeType::Value(expected), actual @ RuntimeType::Fun { .. })
        | (actual @ RuntimeType::Fun { .. }, RuntimeType::Value(expected)) => {
            core_types_compatible(expected, &diagnostic_core_type(actual))
        }
        (RuntimeType::Value(expected), RuntimeType::Thunk { value, .. }) => {
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
            effect_compatible(expected_effect, actual_effect)
                && hir_type_compatible(expected_value, actual_value)
        }
        (RuntimeType::Thunk { value, .. }, actual) => hir_type_compatible(value, actual),
        _ => false,
    }
}

pub(super) fn require_apply_result_hir_type(
    declared: &RuntimeType,
    actual: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
    if runtime_type_contains_unknown(declared) || runtime_type_contains_unknown(actual) {
        return Ok(());
    }
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
            if !effect_compatible(declared_effect, actual_effect)
                && !effect_compatible(actual_effect, declared_effect)
            {
                if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                    eprintln!(
                        "validate apply result {source:?}: {declared_effect:?} / {actual_effect:?}"
                    );
                }
                return Err(RuntimeError::TypeMismatch {
                    expected: declared_effect.clone(),
                    actual: actual_effect.clone(),
                    source,
                    context: None,
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
        RuntimeType::Unknown => Ok(()),
        RuntimeType::Value(ty) => validate_core_type_no_any(ty, source, type_arg_kinds),
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
    ty: &typed_ir::Type,
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
    ty: &typed_ir::Type,
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
    ty: &typed_ir::Type,
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
    ty: &typed_ir::Type,
    effect_slot: bool,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
    type_arg_kinds: &TypeArgKinds,
) -> bool {
    match ty {
        typed_ir::Type::Unknown => false,
        typed_ir::Type::Never | typed_ir::Type::Any => false,
        typed_ir::Type::Var(var) => !allowed_vars.contains(var),
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) if effect_slot => items
            .iter()
            .any(|item| contains_non_runtime_type_inner(item, true, allowed_vars, type_arg_kinds)),
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items)
            if same_runtime_value_choice(items, allowed_vars, type_arg_kinds) =>
        {
            false
        }
        typed_ir::Type::Union(_) | typed_ir::Type::Inter(_) => true,
        typed_ir::Type::Row { .. } => !effect_slot,
        typed_ir::Type::Named { path, args } => args.iter().enumerate().any(|(index, arg)| {
            let arg_effect_slot = type_arg_kinds
                .get(path)
                .and_then(|kinds| kinds.get(index))
                .is_some_and(|kind| *kind == TypeArgKind::Effect);
            match arg {
                typed_ir::TypeArg::Type(ty) => contains_non_runtime_type_inner(
                    ty,
                    arg_effect_slot,
                    allowed_vars,
                    type_arg_kinds,
                ),
                typed_ir::TypeArg::Bounds(bounds) => {
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
        typed_ir::Type::Fun {
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
        typed_ir::Type::Tuple(items) => items
            .iter()
            .any(|item| contains_non_runtime_type_inner(item, false, allowed_vars, type_arg_kinds)),
        typed_ir::Type::Record(record) => {
            record.fields.iter().any(|field| {
                contains_non_runtime_type_inner(&field.value, false, allowed_vars, type_arg_kinds)
            }) || record.spread.as_ref().is_some_and(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                    contains_non_runtime_type_inner(ty, false, allowed_vars, type_arg_kinds)
                }
            })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads.iter().any(|payload| {
                    contains_non_runtime_type_inner(payload, false, allowed_vars, type_arg_kinds)
                })
            }) || variant.tail.as_deref().is_some_and(|tail| {
                contains_non_runtime_type_inner(tail, false, allowed_vars, type_arg_kinds)
            })
        }
        typed_ir::Type::Recursive { body, .. } => {
            contains_non_runtime_type_inner(body, effect_slot, allowed_vars, type_arg_kinds)
        }
    }
}

pub(super) fn require_apply_arg_hir_type(
    expected: &RuntimeType,
    actual: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
    if runtime_type_contains_unknown(expected) || runtime_type_contains_unknown(actual) {
        return Ok(());
    }
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
                    context: None,
                });
            }
            require_same_hir_type(expected_value, actual_value, source)
        }
        _ => require_same_hir_type(expected, actual, source),
    }
}

fn same_runtime_value_choice(
    items: &[typed_ir::Type],
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
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

pub(super) fn hir_value_core_type(ty: &RuntimeType) -> Cow<'_, typed_ir::Type> {
    match ty {
        RuntimeType::Unknown => Cow::Owned(typed_ir::Type::Unknown),
        RuntimeType::Value(ty) => Cow::Borrowed(ty),
        RuntimeType::Thunk { value, .. } => match value.as_ref() {
            RuntimeType::Value(ty) => Cow::Borrowed(ty),
            other => Cow::Owned(runtime_core_type(other)),
        },
        RuntimeType::Fun { .. } => Cow::Owned(runtime_core_type(ty)),
    }
}

pub(super) fn is_constructor_path_for_type(path: &typed_ir::Path, ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Value(typed_ir::Type::Named {
            path: type_path, ..
        }) => constructor_parent_matches(path, type_path),
        RuntimeType::Fun { ret, .. } => {
            let RuntimeType::Value(typed_ir::Type::Named {
                path: type_path, ..
            }) = ret.as_ref()
            else {
                return false;
            };
            constructor_parent_matches(path, type_path)
        }
        _ => false,
    }
}

pub(super) fn constructor_parent_matches(
    path: &typed_ir::Path,
    type_path: &typed_ir::Path,
) -> bool {
    path.segments.len() == type_path.segments.len() + 1
        && path
            .segments
            .iter()
            .zip(&type_path.segments)
            .all(|(left, right)| left == right)
}

pub(super) fn bool_type() -> typed_ir::Type {
    typed_ir::Type::Named {
        path: typed_ir::Path::from_name(typed_ir::Name("bool".to_string())),
        args: Vec::new(),
    }
}

pub(super) fn literal_core_type(lit: &typed_ir::Lit) -> typed_ir::Type {
    let path = match lit {
        typed_ir::Lit::Int(_) => typed_ir::Path::from_name(typed_ir::Name("int".to_string())),
        typed_ir::Lit::Float(_) => typed_ir::Path::from_name(typed_ir::Name("float".to_string())),
        typed_ir::Lit::String(_) => typed_ir::Path {
            segments: vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("str".to_string()),
                typed_ir::Name("str".to_string()),
            ],
        },
        typed_ir::Lit::Bool(_) => typed_ir::Path::from_name(typed_ir::Name("bool".to_string())),
        typed_ir::Lit::Unit => typed_ir::Path::from_name(typed_ir::Name("unit".to_string())),
    };
    typed_ir::Type::Named {
        path,
        args: Vec::new(),
    }
}

pub(super) fn literal_core_type_accepts(lit: &typed_ir::Lit, actual: &typed_ir::Type) -> bool {
    if core_types_compatible(&literal_core_type(lit), actual) {
        return true;
    }
    let typed_ir::Type::Named { path, args } = actual else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    path.segments
        .last()
        .is_some_and(|name| name.0 == literal_primitive_leaf_name(lit))
}

fn literal_primitive_leaf_name(lit: &typed_ir::Lit) -> &'static str {
    match lit {
        typed_ir::Lit::Int(_) => "int",
        typed_ir::Lit::Float(_) => "float",
        typed_ir::Lit::String(_) => "str",
        typed_ir::Lit::Bool(_) => "bool",
        typed_ir::Lit::Unit => "unit",
    }
}

pub(super) fn effect_id_type() -> typed_ir::Type {
    typed_ir::Type::Named {
        path: typed_ir::Path::from_name(typed_ir::Name("__effect_id".to_string())),
        args: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_runtime_types::ir::{Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence, Module, Root, Type};

    #[test]
    fn thunk_type_allows_effect_row() {
        let value_ty = bool_type();
        let effect = typed_ir::Type::Row {
            items: vec![named_type("junction")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let inner = Expr::typed(ExprKind::Lit(typed_ir::Lit::Bool(true)), value_ty.clone());
        let thunk_ty = Type::thunk(effect.clone(), Type::value(value_ty.clone()));
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Thunk {
                    effect,
                    value: Type::value(value_ty),
                    expr: Box::new(inner),
                },
                thunk_ty,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        validate_module(&module).expect("valid thunk row");
    }

    #[test]
    fn thunk_type_allows_recursive_effect_row() {
        let value_ty = bool_type();
        let effect = typed_ir::Type::Recursive {
            var: typed_ir::TypeVar("e".to_string()),
            body: Box::new(typed_ir::Type::Row {
                items: vec![named_type("undet")],
                tail: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("e".to_string()))),
            }),
        };
        let inner = Expr::typed(ExprKind::Lit(typed_ir::Lit::Bool(true)), value_ty.clone());
        let thunk_ty = Type::thunk(effect.clone(), Type::value(value_ty.clone()));
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Thunk {
                    effect,
                    value: Type::value(value_ty),
                    expr: Box::new(inner),
                },
                thunk_ty,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        validate_module(&module).expect("valid recursive thunk row");
    }

    #[test]
    fn record_pattern_default_allows_missing_expected_field() {
        let int = named_type("int");
        let value_ty = typed_ir::Type::Record(typed_ir::RecordType {
            fields: vec![typed_ir::RecordField {
                name: typed_ir::Name("base".to_string()),
                value: int.clone(),
                optional: false,
            }],
            spread: None,
        });
        let pattern_ty = Type::value(typed_ir::Type::Record(typed_ir::RecordType {
            fields: vec![
                typed_ir::RecordField {
                    name: typed_ir::Name("base".to_string()),
                    value: int.clone(),
                    optional: false,
                },
                typed_ir::RecordField {
                    name: typed_ir::Name("extra".to_string()),
                    value: int.clone(),
                    optional: true,
                },
            ],
            spread: None,
        }));
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Block {
                    stmts: vec![yulang_runtime_types::ir::Stmt::Let {
                        pattern: yulang_runtime_types::ir::Pattern::Record {
                            fields: vec![
                                yulang_runtime_types::ir::RecordPatternField {
                                    name: typed_ir::Name("base".to_string()),
                                    pattern: yulang_runtime_types::ir::Pattern::Bind {
                                        name: typed_ir::Name("base".to_string()),
                                        ty: Type::value(int.clone()),
                                    },
                                    default: None,
                                },
                                yulang_runtime_types::ir::RecordPatternField {
                                    name: typed_ir::Name("extra".to_string()),
                                    pattern: yulang_runtime_types::ir::Pattern::Bind {
                                        name: typed_ir::Name("extra".to_string()),
                                        ty: Type::value(int.clone()),
                                    },
                                    default: Some(Expr::typed(
                                        ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
                                        Type::value(int.clone()),
                                    )),
                                },
                            ],
                            spread: None,
                            ty: pattern_ty,
                        },
                        value: Expr::typed(
                            ExprKind::Record {
                                fields: vec![yulang_runtime_types::ir::RecordExprField {
                                    name: typed_ir::Name("base".to_string()),
                                    value: Expr::typed(
                                        ExprKind::Lit(typed_ir::Lit::Int("3".to_string())),
                                        Type::value(int.clone()),
                                    ),
                                }],
                                spread: None,
                            },
                            Type::value(value_ty),
                        ),
                    }],
                    tail: Some(Box::new(Expr::typed(
                        ExprKind::Var(typed_ir::Path::from_name(typed_ir::Name(
                            "extra".to_string(),
                        ))),
                        Type::value(int.clone()),
                    ))),
                },
                Type::value(int),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        validate_module(&module).expect("valid record default pattern");
    }

    #[test]
    fn pure_value_handler_body_can_be_plain_value() {
        let int = named_type("int");
        let body = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
            Type::value(int.clone()),
        );
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Handle {
                    body: Box::new(body),
                    arms: vec![HandleArm {
                        effect: typed_ir::Path::default(),
                        payload: yulang_runtime_types::ir::Pattern::Wildcard {
                            ty: Type::value(int.clone()),
                        },
                        resume: None,
                        guard: None,
                        body: Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
                            Type::value(int.clone()),
                        ),
                    }],
                    evidence: JoinEvidence {
                        result: int.clone(),
                    },
                    handler: HandleEffect {
                        consumes: Vec::new(),
                        residual_before: None,
                        residual_after: None,
                    },
                },
                Type::value(int.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        validate_module(&module).expect("plain value body for value-only handler");
    }

    #[test]
    fn effectful_handle_body_must_be_a_thunk() {
        let int = named_type("int");
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
        let body = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
            Type::value(int.clone()),
        );
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Handle {
                    body: Box::new(body),
                    arms: vec![HandleArm {
                        effect: effect.clone(),
                        payload: yulang_runtime_types::ir::Pattern::Wildcard {
                            ty: Type::value(int.clone()),
                        },
                        resume: None,
                        guard: None,
                        body: Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("1".to_string())),
                            Type::value(int.clone()),
                        ),
                    }],
                    evidence: JoinEvidence {
                        result: int.clone(),
                    },
                    handler: HandleEffect {
                        consumes: vec![effect],
                        residual_before: None,
                        residual_after: None,
                    },
                },
                Type::value(int.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        assert_eq!(
            validate_module(&module),
            Err(RuntimeError::ExpectedThunk { ty: int })
        );
    }

    fn named_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
