use super::*;

pub(super) fn lower_pattern(
    pattern: core_ir::Pattern,
    ty: &core_ir::Type,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<Pattern> {
    lower_hir_pattern(pattern, &RuntimeType::core(ty.clone()), locals)
}

pub(super) fn lower_hir_pattern(
    pattern: core_ir::Pattern,
    ty: &RuntimeType,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<Pattern> {
    match pattern {
        core_ir::Pattern::Wildcard => Ok(Pattern::Wildcard { ty: ty.clone() }),
        core_ir::Pattern::Bind(name) => {
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
            Ok(Pattern::Bind {
                name,
                ty: ty.clone(),
            })
        }
        core_ir::Pattern::Or { left, right } => Ok(Pattern::Or {
            left: Box::new(lower_hir_pattern(*left, ty, locals)?),
            right: Box::new(lower_hir_pattern(*right, ty, locals)?),
            ty: ty.clone(),
        }),
        core_ir::Pattern::As { pattern, name } => {
            let pattern = lower_hir_pattern(*pattern, ty, locals)?;
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
            Ok(Pattern::As {
                pattern: Box::new(pattern),
                name,
                ty: ty.clone(),
            })
        }
        pattern => {
            let Some(core_ty) = ty.as_core() else {
                return Err(RuntimeError::UnsupportedPatternShape {
                    pattern: pattern_shape_name(&pattern),
                    ty: diagnostic_core_type(ty),
                });
            };
            lower_core_pattern(pattern, core_ty, locals)
        }
    }
}

pub(super) fn lower_core_pattern(
    pattern: core_ir::Pattern,
    ty: &core_ir::Type,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<Pattern> {
    match pattern {
        core_ir::Pattern::Wildcard => Ok(Pattern::Wildcard {
            ty: ty.clone().into(),
        }),
        core_ir::Pattern::Bind(name) => {
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone().into());
            Ok(Pattern::Bind {
                name,
                ty: ty.clone().into(),
            })
        }
        core_ir::Pattern::Lit(lit) => {
            let lit_ty = lit_type(&lit);
            require_same_type(ty, &lit_ty, TypeSource::Literal)?;
            Ok(Pattern::Lit {
                lit,
                ty: lit_ty.into(),
            })
        }
        core_ir::Pattern::Tuple(items) => {
            let erased_items;
            let item_tys = match ty {
                core_ir::Type::Tuple(item_tys) => item_tys.as_slice(),
                core_ir::Type::Any => {
                    erased_items = vec![core_ir::Type::Any; items.len()];
                    erased_items.as_slice()
                }
                _ => {
                    return Err(RuntimeError::UnsupportedPatternShape {
                        pattern: "tuple",
                        ty: ty.clone(),
                    });
                }
            };
            if items.len() != item_tys.len() {
                return Err(RuntimeError::UnsupportedPatternShape {
                    pattern: "tuple",
                    ty: ty.clone(),
                });
            }
            let items = items
                .into_iter()
                .zip(item_tys)
                .map(|(item, item_ty)| lower_pattern(item, item_ty, locals))
                .collect::<RuntimeResult<Vec<_>>>()?;
            Ok(Pattern::Tuple {
                items,
                ty: ty.clone().into(),
            })
        }
        core_ir::Pattern::List {
            prefix,
            spread,
            suffix,
        } => {
            let item_ty = list_item_type(ty)
                .or_else(|| matches!(ty, core_ir::Type::Any).then_some(core_ir::Type::Any))
                .ok_or_else(|| RuntimeError::UnsupportedPatternShape {
                    pattern: "list",
                    ty: ty.clone(),
                })?;
            let prefix = prefix
                .into_iter()
                .map(|item| lower_pattern(item, &item_ty, locals))
                .collect::<RuntimeResult<Vec<_>>>()?;
            let spread = spread
                .map(|spread| lower_pattern(*spread, ty, locals).map(Box::new))
                .transpose()?;
            let suffix = suffix
                .into_iter()
                .map(|item| lower_pattern(item, &item_ty, locals))
                .collect::<RuntimeResult<Vec<_>>>()?;
            Ok(Pattern::List {
                prefix,
                spread,
                suffix,
                ty: ty.clone().into(),
            })
        }
        core_ir::Pattern::Record { fields, spread } => {
            let fields = fields
                .into_iter()
                .map(|field| {
                    let field_ty = match ty {
                        core_ir::Type::Record(record) => record
                            .fields
                            .iter()
                            .find(|candidate| candidate.name == field.name)
                            .map(|candidate| candidate.value.clone())
                            .ok_or_else(|| RuntimeError::UnsupportedPatternShape {
                                pattern: "record field",
                                ty: ty.clone(),
                            })?,
                        core_ir::Type::Any => core_ir::Type::Any,
                        _ => {
                            return Err(RuntimeError::UnsupportedPatternShape {
                                pattern: "record",
                                ty: ty.clone(),
                            });
                        }
                    };
                    Ok(RecordPatternField {
                        name: field.name,
                        pattern: lower_pattern(field.pattern, &field_ty, locals)?,
                        default: None,
                    })
                })
                .collect::<RuntimeResult<Vec<_>>>()?;
            let spread = spread
                .map(|spread| lower_record_spread_pattern(spread, ty, locals))
                .transpose()?;
            Ok(Pattern::Record {
                fields,
                spread,
                ty: ty.clone().into(),
            })
        }
        core_ir::Pattern::Variant { tag, value } => {
            let payload_ty = variant_payload_expected(Some(ty), &tag);
            let value = value
                .map(|value| {
                    let erased_payload = core_ir::Type::Any;
                    let payload_ty = payload_ty.as_ref().unwrap_or(&erased_payload);
                    lower_pattern(*value, payload_ty, locals).map(Box::new)
                })
                .transpose()?;
            Ok(Pattern::Variant {
                tag,
                value,
                ty: ty.clone().into(),
            })
        }
        core_ir::Pattern::Or { left, right } => Ok(Pattern::Or {
            left: Box::new(lower_pattern(*left, ty, locals)?),
            right: Box::new(lower_pattern(*right, ty, locals)?),
            ty: ty.clone().into(),
        }),
        core_ir::Pattern::As { pattern, name } => {
            let pattern = lower_pattern(*pattern, ty, locals)?;
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone().into());
            Ok(Pattern::As {
                pattern: Box::new(pattern),
                name,
                ty: ty.clone().into(),
            })
        }
    }
}

pub(super) fn pattern_shape_name(pattern: &core_ir::Pattern) -> &'static str {
    match pattern {
        core_ir::Pattern::Wildcard => "wildcard",
        core_ir::Pattern::Bind(_) => "bind",
        core_ir::Pattern::Lit(_) => "literal",
        core_ir::Pattern::Tuple(_) => "tuple",
        core_ir::Pattern::List { .. } => "list",
        core_ir::Pattern::Record { .. } => "record",
        core_ir::Pattern::Variant { .. } => "variant",
        core_ir::Pattern::Or { .. } => "or",
        core_ir::Pattern::As { .. } => "as",
    }
}

pub(super) fn lower_record_spread_pattern(
    spread: core_ir::RecordSpreadPattern,
    ty: &core_ir::Type,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<RecordSpreadPattern> {
    match spread {
        core_ir::RecordSpreadPattern::Head(pattern) => Ok(RecordSpreadPattern::Head(Box::new(
            lower_pattern(*pattern, ty, locals)?,
        ))),
        core_ir::RecordSpreadPattern::Tail(pattern) => Ok(RecordSpreadPattern::Tail(Box::new(
            lower_pattern(*pattern, ty, locals)?,
        ))),
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

pub(super) fn propagate_refined_locals(
    parent: &mut HashMap<core_ir::Path, RuntimeType>,
    child: &HashMap<core_ir::Path, RuntimeType>,
) {
    let keys = parent.keys().cloned().collect::<Vec<_>>();
    for key in keys {
        let Some(child_ty) = child.get(&key).cloned() else {
            continue;
        };
        let parent_ty = parent.get(&key).cloned();
        if let Some(ty) = choose_local_type_hint(parent_ty, Some(child_ty)) {
            parent.insert(key, ty);
        }
    }
}
