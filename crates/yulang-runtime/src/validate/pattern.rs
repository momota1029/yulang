use super::*;

pub(super) fn validate_pattern(
    pattern: &Pattern,
    expected: &core_ir::Type,
    type_arg_kinds: &TypeArgKinds,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    require_same_type(
        expected,
        core_type(pattern_ty(pattern)),
        TypeSource::Validation,
    )?;
    match pattern {
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
        Pattern::Bind { name, ty } => {
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
        }
        Pattern::Tuple { items, .. } => {
            let erased_items;
            let item_tys = match expected {
                core_ir::Type::Tuple(item_tys) => item_tys.as_slice(),
                core_ir::Type::Any => {
                    erased_items = vec![core_ir::Type::Any; items.len()];
                    erased_items.as_slice()
                }
                _ => {
                    return Err(RuntimeError::UnsupportedPatternShape {
                        pattern: "tuple",
                        ty: expected.clone(),
                    });
                }
            };
            for (item, item_ty) in items.iter().zip(item_tys) {
                validate_pattern(item, item_ty, type_arg_kinds, locals)?;
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter().chain(suffix) {
                let item_ty = if matches!(expected, core_ir::Type::Any) {
                    &core_ir::Type::Any
                } else {
                    core_type(pattern_ty(item))
                };
                validate_pattern(item, item_ty, type_arg_kinds, locals)?;
            }
            if let Some(spread) = spread {
                validate_pattern(spread, expected, type_arg_kinds, locals)?;
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                let erased_field_ty;
                let field_ty = match expected {
                    core_ir::Type::Record(record) => match record
                        .fields
                        .iter()
                        .find(|candidate| candidate.name == field.name)
                        .map(|field| &field.value)
                    {
                        Some(field_ty) => field_ty,
                        None if field.default.is_some() => core_type(pattern_ty(&field.pattern)),
                        None => {
                            return Err(RuntimeError::UnsupportedPatternShape {
                                pattern: "record field",
                                ty: expected.clone(),
                            });
                        }
                    },
                    core_ir::Type::Any => {
                        erased_field_ty = core_ir::Type::Any;
                        &erased_field_ty
                    }
                    _ => {
                        return Err(RuntimeError::UnsupportedPatternShape {
                            pattern: "record",
                            ty: expected.clone(),
                        });
                    }
                };
                validate_pattern(&field.pattern, field_ty, type_arg_kinds, locals)?;
                if let Some(default) = &field.default {
                    require_same_type(field_ty, core_type(&default.ty), TypeSource::Expected)?;
                }
            }
            validate_record_spread_pattern(spread, expected, type_arg_kinds, locals)?;
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                validate_pattern(value, core_type(pattern_ty(value)), type_arg_kinds, locals)?;
            }
        }
        Pattern::Or { left, right, .. } => {
            validate_pattern(left, expected, type_arg_kinds, locals)?;
            validate_pattern(right, expected, type_arg_kinds, locals)?;
        }
        Pattern::As { pattern, name, ty } => {
            validate_pattern(pattern, expected, type_arg_kinds, locals)?;
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
        }
    }
    Ok(())
}

pub(super) fn validate_hir_pattern(
    pattern: &Pattern,
    expected: &RuntimeType,
    type_arg_kinds: &TypeArgKinds,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    require_same_hir_type(expected, pattern_ty(pattern), TypeSource::Validation)?;
    match pattern {
        Pattern::Wildcard { .. } => Ok(()),
        Pattern::Bind { name, ty } => {
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
            Ok(())
        }
        Pattern::Or { left, right, .. } => {
            validate_hir_pattern(left, expected, type_arg_kinds, locals)?;
            validate_hir_pattern(right, expected, type_arg_kinds, locals)
        }
        Pattern::As { pattern, name, ty } => {
            validate_hir_pattern(pattern, expected, type_arg_kinds, locals)?;
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
            Ok(())
        }
        pattern => {
            let Some(expected) = expected.as_core() else {
                return Err(RuntimeError::UnsupportedPatternShape {
                    pattern: pattern_shape_name(pattern),
                    ty: diagnostic_core_type(expected),
                });
            };
            validate_pattern(pattern, expected, type_arg_kinds, locals)
        }
    }
}

pub(super) fn validate_record_spread_expr(
    spread: &Option<RecordSpreadExpr>,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
    type_arg_kinds: &TypeArgKinds,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    match spread {
        Some(RecordSpreadExpr::Head(expr)) | Some(RecordSpreadExpr::Tail(expr)) => {
            validate_expr(expr, bindings, type_arg_kinds, locals)
        }
        None => Ok(()),
    }
}

pub(super) fn validate_record_spread_pattern(
    spread: &Option<RecordSpreadPattern>,
    expected: &core_ir::Type,
    type_arg_kinds: &TypeArgKinds,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    match spread {
        Some(RecordSpreadPattern::Head(pattern)) | Some(RecordSpreadPattern::Tail(pattern)) => {
            validate_pattern(pattern, expected, type_arg_kinds, locals)
        }
        None => Ok(()),
    }
}

pub(super) fn pattern_ty(pattern: &Pattern) -> &RuntimeType {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty,
    }
}

pub(super) fn pattern_shape_name(pattern: &Pattern) -> &'static str {
    match pattern {
        Pattern::Wildcard { .. } => "wildcard",
        Pattern::Bind { .. } => "bind",
        Pattern::Lit { .. } => "literal",
        Pattern::Tuple { .. } => "tuple",
        Pattern::List { .. } => "list",
        Pattern::Record { .. } => "record",
        Pattern::Variant { .. } => "variant",
        Pattern::Or { .. } => "or",
        Pattern::As { .. } => "as",
    }
}

pub(super) fn restore_local(
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    local: core_ir::Path,
    previous: Option<RuntimeType>,
) {
    match previous {
        Some(previous) => {
            locals.insert(local, previous);
        }
        None => {
            locals.remove(&local);
        }
    }
}
