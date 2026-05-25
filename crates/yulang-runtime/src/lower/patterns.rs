use super::*;

pub(super) fn lower_pattern(
    lowerer: &mut Lowerer<'_>,
    pattern: typed_ir::Pattern,
    ty: &typed_ir::Type,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> RuntimeResult<Pattern> {
    lower_hir_pattern(lowerer, pattern, &RuntimeType::value(ty.clone()), locals)
}

pub(super) fn lower_hir_pattern(
    lowerer: &mut Lowerer<'_>,
    pattern: typed_ir::Pattern,
    ty: &RuntimeType,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> RuntimeResult<Pattern> {
    match pattern {
        typed_ir::Pattern::Wildcard => Ok(Pattern::Wildcard { ty: ty.clone() }),
        typed_ir::Pattern::Bind(name) => {
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone());
            Ok(Pattern::Bind {
                name,
                ty: ty.clone(),
            })
        }
        typed_ir::Pattern::Or { left, right } => Ok(Pattern::Or {
            left: Box::new(lower_hir_pattern(lowerer, *left, ty, locals)?),
            right: Box::new(lower_hir_pattern(lowerer, *right, ty, locals)?),
            ty: ty.clone(),
        }),
        typed_ir::Pattern::As { pattern, name } => {
            let pattern = lower_hir_pattern(lowerer, *pattern, ty, locals)?;
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone());
            Ok(Pattern::As {
                pattern: Box::new(pattern),
                name,
                ty: ty.clone(),
            })
        }
        pattern => {
            let Some(core_ty) = ty.as_value() else {
                return Err(RuntimeError::UnsupportedPatternShape {
                    pattern: pattern_shape_name(&pattern),
                    ty: diagnostic_core_type(ty),
                });
            };
            lower_core_pattern(lowerer, pattern, core_ty, locals)
        }
    }
}

pub(super) fn lower_core_pattern(
    lowerer: &mut Lowerer<'_>,
    pattern: typed_ir::Pattern,
    ty: &typed_ir::Type,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> RuntimeResult<Pattern> {
    match pattern {
        typed_ir::Pattern::Wildcard => Ok(Pattern::Wildcard {
            ty: ty.clone().into(),
        }),
        typed_ir::Pattern::Bind(name) => {
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone().into());
            Ok(Pattern::Bind {
                name,
                ty: ty.clone().into(),
            })
        }
        typed_ir::Pattern::Lit(lit) => {
            let lit_ty = lowerer.primitive_paths.lit_type(&lit);
            require_same_type(ty, &lit_ty, TypeSource::Literal)?;
            Ok(Pattern::Lit {
                lit,
                ty: lit_ty.into(),
            })
        }
        typed_ir::Pattern::Tuple(items) => {
            let erased_items;
            let item_tys = match ty {
                typed_ir::Type::Tuple(item_tys) => item_tys.as_slice(),
                typed_ir::Type::Any => {
                    erased_items = vec![typed_ir::Type::Any; items.len()];
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
                .map(|(item, item_ty)| lower_pattern(lowerer, item, item_ty, locals))
                .collect::<RuntimeResult<Vec<_>>>()?;
            Ok(Pattern::Tuple {
                items,
                ty: ty.clone().into(),
            })
        }
        typed_ir::Pattern::List {
            prefix,
            spread,
            suffix,
        } => {
            let item_ty = unary_runtime_container_item_type(ty)
                .or_else(|| matches!(ty, typed_ir::Type::Any).then_some(typed_ir::Type::Any))
                .ok_or_else(|| RuntimeError::UnsupportedPatternShape {
                    pattern: "list",
                    ty: ty.clone(),
                })?;
            let prefix = prefix
                .into_iter()
                .map(|item| lower_pattern(lowerer, item, &item_ty, locals))
                .collect::<RuntimeResult<Vec<_>>>()?;
            let spread = spread
                .map(|spread| lower_pattern(lowerer, *spread, ty, locals).map(Box::new))
                .transpose()?;
            let suffix = suffix
                .into_iter()
                .map(|item| lower_pattern(lowerer, item, &item_ty, locals))
                .collect::<RuntimeResult<Vec<_>>>()?;
            Ok(Pattern::List {
                prefix,
                spread,
                suffix,
                ty: ty.clone().into(),
            })
        }
        typed_ir::Pattern::Record { fields, spread } => {
            let named_record = named_struct_record_type(lowerer, ty);
            let fields = fields
                .into_iter()
                .map(|field| {
                    let record_field_ty = match ty {
                        typed_ir::Type::Record(record) => record
                            .fields
                            .iter()
                            .find(|candidate| candidate.name == field.name)
                            .map(|candidate| candidate.value.clone()),
                        typed_ir::Type::Any => Some(typed_ir::Type::Any),
                        typed_ir::Type::Named { .. } => named_record.as_ref().and_then(|record| {
                            record
                                .fields
                                .iter()
                                .find(|candidate| candidate.name == field.name)
                                .map(|candidate| candidate.value.clone())
                        }),
                        _ => {
                            return Err(RuntimeError::UnsupportedPatternShape {
                                pattern: "record",
                                ty: ty.clone(),
                            });
                        }
                    };
                    let default = match (field.default, record_field_ty.as_ref()) {
                        (Some(default), Some(field_ty)) => Some(
                            force_value_expr_profiled(
                                lowerer.lower_expr(
                                    default,
                                    Some(&RuntimeType::value(field_ty.clone())),
                                    locals,
                                    TypeSource::Expected,
                                )?,
                                &mut lowerer.runtime_adapter_profile,
                            )
                            .0,
                        ),
                        (Some(default), None) => {
                            let default = force_value_expr_profiled(
                                lowerer.lower_expr(default, None, locals, TypeSource::Expected)?,
                                &mut lowerer.runtime_adapter_profile,
                            )
                            .0;
                            Some(default)
                        }
                        (None, Some(_)) => None,
                        (None, None) => {
                            return Err(RuntimeError::UnsupportedPatternShape {
                                pattern: "record field",
                                ty: ty.clone(),
                            });
                        }
                    };
                    let field_ty = record_field_ty.unwrap_or_else(|| {
                        default
                            .as_ref()
                            .map_or(typed_ir::Type::Any, |expr| core_type(&expr.ty).clone())
                    });
                    Ok(RecordPatternField {
                        name: field.name,
                        pattern: lower_pattern(lowerer, field.pattern, &field_ty, locals)?,
                        default,
                    })
                })
                .collect::<RuntimeResult<Vec<_>>>()?;
            let spread = spread
                .map(|spread| lower_record_spread_pattern(lowerer, spread, ty, locals))
                .transpose()?;
            Ok(Pattern::Record {
                fields,
                spread,
                ty: ty.clone().into(),
            })
        }
        typed_ir::Pattern::Variant { tag, value } => {
            let payload_ty = variant_payload_expected(lowerer, Some(ty), &tag);
            let value = value
                .map(|value| {
                    let erased_payload = typed_ir::Type::Any;
                    let payload_ty = payload_ty.as_ref().unwrap_or(&erased_payload);
                    lower_pattern(lowerer, *value, payload_ty, locals).map(Box::new)
                })
                .transpose()?;
            Ok(Pattern::Variant {
                tag,
                value,
                ty: ty.clone().into(),
            })
        }
        typed_ir::Pattern::Or { left, right } => Ok(Pattern::Or {
            left: Box::new(lower_pattern(lowerer, *left, ty, locals)?),
            right: Box::new(lower_pattern(lowerer, *right, ty, locals)?),
            ty: ty.clone().into(),
        }),
        typed_ir::Pattern::As { pattern, name } => {
            let pattern = lower_pattern(lowerer, *pattern, ty, locals)?;
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone().into());
            Ok(Pattern::As {
                pattern: Box::new(pattern),
                name,
                ty: ty.clone().into(),
            })
        }
    }
}

fn named_struct_record_type(
    lowerer: &Lowerer<'_>,
    ty: &typed_ir::Type,
) -> Option<typed_ir::RecordType> {
    let typed_ir::Type::Named { path, args } = ty else {
        return None;
    };
    let (param, ret) = lowerer
        .env
        .get(path)
        .and_then(runtime_constructor_parts)
        .or_else(|| {
            lowerer.env.values().find_map(|candidate| {
                runtime_constructor_parts(candidate)
                    .filter(|(_, ret)| named_type_path(ret) == Some(path))
            })
        })?;
    let RuntimeType::Value(typed_ir::Type::Named {
        path: ret_path,
        args: ret_args,
    }) = &ret
    else {
        return None;
    };
    if ret_path != path || ret_args.len() != args.len() {
        return None;
    }
    let RuntimeType::Value(typed_ir::Type::Record(record)) = &param else {
        return None;
    };
    let substitutions = ret_args
        .iter()
        .zip(args.iter())
        .filter_map(|(from, to)| match (from, to) {
            (typed_ir::TypeArg::Type(typed_ir::Type::Var(var)), typed_ir::TypeArg::Type(ty)) => {
                Some((var.clone(), ty.clone()))
            }
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    Some(substitute_record_type_vars(record, &substitutions))
}

fn named_type_path(ty: &RuntimeType) -> Option<&typed_ir::Path> {
    let RuntimeType::Value(typed_ir::Type::Named { path, args: _ }) = ty else {
        return None;
    };
    Some(path)
}

fn substitute_record_type_vars(
    record: &typed_ir::RecordType,
    substitutions: &HashMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::RecordType {
    typed_ir::RecordType {
        fields: record
            .fields
            .iter()
            .map(|field| typed_ir::RecordField {
                name: field.name.clone(),
                value: substitute_pattern_type_vars(&field.value, substitutions),
                optional: field.optional,
            })
            .collect(),
        spread: record.spread.as_ref().map(|spread| match spread {
            typed_ir::RecordSpread::Head(ty) => typed_ir::RecordSpread::Head(Box::new(
                substitute_pattern_type_vars(ty, substitutions),
            )),
            typed_ir::RecordSpread::Tail(ty) => typed_ir::RecordSpread::Tail(Box::new(
                substitute_pattern_type_vars(ty, substitutions),
            )),
        }),
    }
}

pub(super) fn substitute_pattern_type_vars(
    ty: &typed_ir::Type,
    substitutions: &HashMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Var(var) => substitutions
            .get(var)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| substitute_pattern_type_arg_vars(arg, substitutions))
                .collect(),
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(substitute_pattern_type_vars(param, substitutions)),
            param_effect: Box::new(substitute_pattern_type_vars(param_effect, substitutions)),
            ret_effect: Box::new(substitute_pattern_type_vars(ret_effect, substitutions)),
            ret: Box::new(substitute_pattern_type_vars(ret, substitutions)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| substitute_pattern_type_vars(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Record(record) => {
            typed_ir::Type::Record(substitute_record_type_vars(record, substitutions))
        }
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| substitute_pattern_type_vars(payload, substitutions))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(substitute_pattern_type_vars(tail, substitutions))),
        }),
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| substitute_pattern_type_vars(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| substitute_pattern_type_vars(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| substitute_pattern_type_vars(item, substitutions))
                .collect(),
            tail: Box::new(substitute_pattern_type_vars(tail, substitutions)),
        },
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(substitute_pattern_type_vars(body, substitutions)),
        },
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => ty.clone(),
    }
}

fn substitute_pattern_type_arg_vars(
    arg: &typed_ir::TypeArg,
    substitutions: &HashMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(substitute_pattern_type_vars(ty, substitutions))
        }
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(substitute_pattern_type_vars(ty, substitutions))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(substitute_pattern_type_vars(ty, substitutions))),
        }),
    }
}

pub(super) fn pattern_shape_name(pattern: &typed_ir::Pattern) -> &'static str {
    match pattern {
        typed_ir::Pattern::Wildcard => "wildcard",
        typed_ir::Pattern::Bind(_) => "bind",
        typed_ir::Pattern::Lit(_) => "literal",
        typed_ir::Pattern::Tuple(_) => "tuple",
        typed_ir::Pattern::List { .. } => "list",
        typed_ir::Pattern::Record { .. } => "record",
        typed_ir::Pattern::Variant { .. } => "variant",
        typed_ir::Pattern::Or { .. } => "or",
        typed_ir::Pattern::As { .. } => "as",
    }
}

pub(super) fn lower_record_spread_pattern(
    lowerer: &mut Lowerer<'_>,
    spread: typed_ir::RecordSpreadPattern,
    ty: &typed_ir::Type,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> RuntimeResult<RecordSpreadPattern> {
    match spread {
        typed_ir::RecordSpreadPattern::Head(pattern) => Ok(RecordSpreadPattern::Head(Box::new(
            lower_pattern(lowerer, *pattern, ty, locals)?,
        ))),
        typed_ir::RecordSpreadPattern::Tail(pattern) => Ok(RecordSpreadPattern::Tail(Box::new(
            lower_pattern(lowerer, *pattern, ty, locals)?,
        ))),
    }
}

pub(super) fn restore_local(
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
    local: typed_ir::Path,
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
    parent: &mut HashMap<typed_ir::Path, RuntimeType>,
    child: &HashMap<typed_ir::Path, RuntimeType>,
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
