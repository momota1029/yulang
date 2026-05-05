use super::*;

pub(super) fn bind_pattern_with_defaults(
    pattern: &Pattern,
    value: VmValue,
    env: &mut Env,
    eval_default: &mut impl FnMut(&Expr, &Env) -> Result<VmValue, VmError>,
) -> Result<(), VmError> {
    match pattern {
        Pattern::Wildcard { .. } => Ok(()),
        Pattern::Bind { name, .. } => {
            env.insert(core_ir::Path::from_name(name.clone()), value);
            Ok(())
        }
        Pattern::Lit { lit, .. } if value == value_from_lit(lit) => Ok(()),
        Pattern::Lit { .. } => Err(VmError::PatternMismatch),
        Pattern::Tuple { items, .. } => {
            let VmValue::Tuple(values) = value else {
                return Err(VmError::PatternMismatch);
            };
            if items.len() != values.len() {
                return Err(VmError::PatternMismatch);
            }
            for (item, value) in items.iter().zip(values) {
                bind_pattern_with_defaults(item, value, env, eval_default)?;
            }
            Ok(())
        }
        Pattern::Variant {
            tag,
            value: pattern_value,
            ..
        } => {
            let VmValue::Variant {
                tag: actual,
                value: actual_value,
            } = value
            else {
                return Err(VmError::PatternMismatch);
            };
            if tag != &actual {
                return Err(VmError::PatternMismatch);
            }
            match (pattern_value, actual_value) {
                (Some(pattern), Some(value)) => {
                    bind_pattern_with_defaults(pattern, *value, env, eval_default)
                }
                (None, None) => Ok(()),
                _ => Err(VmError::PatternMismatch),
            }
        }
        Pattern::Or { left, right, .. } => {
            let snapshot = env.clone();
            if bind_pattern_with_defaults(left, value.clone(), env, eval_default).is_ok() {
                return Ok(());
            }
            *env = snapshot;
            bind_pattern_with_defaults(right, value, env, eval_default)
        }
        Pattern::As { pattern, name, .. } => {
            bind_pattern_with_defaults(pattern, value.clone(), env, eval_default)?;
            env.insert(core_ir::Path::from_name(name.clone()), value);
            Ok(())
        }
        Pattern::Record { fields, .. } => {
            let VmValue::Record(values) = value else {
                return Err(VmError::PatternMismatch);
            };
            for field in fields {
                let Some(value) = values.get(&field.name).cloned() else {
                    let Some(default) = &field.default else {
                        return Err(VmError::PatternMismatch);
                    };
                    let value = eval_default(default, env)?;
                    bind_pattern_with_defaults(&field.pattern, value, env, eval_default)?;
                    continue;
                };
                bind_pattern_with_defaults(&field.pattern, value, env, eval_default)?;
            }
            Ok(())
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            let VmValue::List(values) = value else {
                return Err(VmError::PatternMismatch);
            };
            if values.len() < prefix.len() + suffix.len() {
                return Err(VmError::PatternMismatch);
            }
            if spread.is_none() && values.len() != prefix.len() + suffix.len() {
                return Err(VmError::PatternMismatch);
            }
            for (index, pattern) in prefix.iter().enumerate() {
                let Some(value) = values.index(index) else {
                    return Err(VmError::PatternMismatch);
                };
                bind_pattern_with_defaults(pattern, (*value).clone(), env, eval_default)?;
            }
            if let Some(spread) = spread {
                let start = prefix.len();
                let end = values.len() - suffix.len();
                let Some(slice) = values.index_range(start, end) else {
                    return Err(VmError::PatternMismatch);
                };
                bind_pattern_with_defaults(spread, VmValue::List(slice), env, eval_default)?;
            }
            let suffix_start = values.len() - suffix.len();
            for (offset, pattern) in suffix.iter().enumerate() {
                let Some(value) = values.index(suffix_start + offset) else {
                    return Err(VmError::PatternMismatch);
                };
                bind_pattern_with_defaults(pattern, (*value).clone(), env, eval_default)?;
            }
            Ok(())
        }
    }
}

pub(super) fn value_from_lit(lit: &core_ir::Lit) -> VmValue {
    match lit {
        core_ir::Lit::Int(value) => VmValue::Int(value.clone()),
        core_ir::Lit::Float(value) => VmValue::Float(value.clone()),
        core_ir::Lit::String(value) => VmValue::String(StringTree::from_str(value)),
        core_ir::Lit::Bool(value) => VmValue::Bool(*value),
        core_ir::Lit::Unit => VmValue::Unit,
    }
}

pub(super) fn cast_value(value: VmValue, expected: &core_ir::Type) -> VmValue {
    if is_float_type(expected) {
        if let VmValue::Int(value) = value {
            return VmValue::Float(if value.contains('.') {
                value
            } else {
                format!("{value}.0")
            });
        }
    }
    value
}

pub(super) fn wrap_result_for_type(result: VmResult, expected_ty: &Type) -> VmResult {
    if !matches!(expected_ty, Type::Thunk { .. }) {
        return result;
    }
    match result {
        VmResult::Value(value) => VmResult::Value(wrap_value_for_type(value, expected_ty)),
        VmResult::Request(request) => VmResult::Request(push_frame(
            request,
            Frame::WrapThunkResult {
                expected_ty: expected_ty.clone(),
            },
        )),
    }
}

pub(super) fn wrap_value_for_type(value: VmValue, expected_ty: &Type) -> VmValue {
    if !matches!(expected_ty, Type::Thunk { .. }) || matches!(value, VmValue::Thunk(_)) {
        return value;
    }
    VmValue::Thunk(Rc::new(VmThunk {
        body: ThunkBody::Value(value),
        env: Env::new(),
        guard_stack: GuardStack::default(),
        blocked: Vec::new(),
    }))
}

pub(super) fn expects_thunk_arg(ty: &Type) -> bool {
    match ty {
        Type::Fun { param, .. } => matches!(param.as_ref(), Type::Thunk { .. }),
        Type::Unknown | Type::Core(_) | Type::Thunk { .. } => false,
    }
}

pub(super) fn int_value(value: &VmValue) -> Result<i64, VmError> {
    match value {
        VmValue::Int(value) => value
            .parse()
            .map_err(|_| VmError::ExpectedInt(value_from_string(value))),
        other => Err(VmError::ExpectedInt(other.clone())),
    }
}

pub(super) fn float_value(value: &VmValue) -> Result<f64, VmError> {
    match value {
        VmValue::Float(value) => value
            .parse()
            .map_err(|_| VmError::ExpectedFloat(VmValue::Float(value.clone()))),
        other => Err(VmError::ExpectedFloat(other.clone())),
    }
}

pub(super) fn format_float_value(value: f64) -> String {
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

pub(super) fn value_from_string(value: &str) -> VmValue {
    VmValue::String(StringTree::from_str(value))
}

pub(super) fn bool_value(value: &VmValue) -> Result<bool, VmError> {
    match value {
        VmValue::Bool(value) => Ok(*value),
        other => Err(VmError::ExpectedBool(other.clone())),
    }
}

pub(super) fn list_value(value: &VmValue) -> Result<&ListTree<VmValue>, VmError> {
    match value {
        VmValue::List(value) => Ok(value),
        other => Err(VmError::ExpectedList(other.clone())),
    }
}

pub(super) fn string_value(value: &VmValue) -> Result<&StringTree, VmError> {
    match value {
        VmValue::String(value) => Ok(value),
        other => Err(VmError::ExpectedString(other.clone())),
    }
}

pub(super) fn normalized_int_range_value(
    value: &VmValue,
    len: usize,
) -> Result<(usize, usize), VmError> {
    let original = value.clone();
    let VmValue::Variant { tag, value } = value else {
        return Err(VmError::ExpectedVariant(original));
    };
    if tag.0 != "within" {
        return Err(VmError::ExpectedVariant(original));
    }
    let Some(value) = value.as_ref() else {
        return Err(VmError::ExpectedVariant(original));
    };
    let VmValue::Tuple(items) = value.as_ref() else {
        return Err(VmError::ExpectedVariant((**value).clone()));
    };
    let [start, end] = items.as_slice() else {
        return Err(VmError::ExpectedVariant((**value).clone()));
    };
    let start = normalized_start_bound_value(start)?;
    let end = normalized_end_bound_value(end, len)?;
    if start > end || end > len {
        return Err(VmError::ExpectedVariant(value.as_ref().clone()));
    }
    Ok((start, end))
}

pub(super) fn normalized_start_bound_value(value: &VmValue) -> Result<usize, VmError> {
    let original = value.clone();
    let VmValue::Variant { tag, value } = value else {
        return Err(VmError::ExpectedVariant(original));
    };
    match tag.0.as_str() {
        "unbounded" => Ok(0),
        "included" => {
            let Some(value) = value.as_ref() else {
                return Err(VmError::ExpectedVariant(original));
            };
            usize::try_from(int_value(value)?).map_err(|_| VmError::ExpectedInt((**value).clone()))
        }
        "excluded" => {
            let Some(value) = value.as_ref() else {
                return Err(VmError::ExpectedVariant(original));
            };
            usize::try_from(int_value(value)? + 1)
                .map_err(|_| VmError::ExpectedInt((**value).clone()))
        }
        _ => Err(VmError::ExpectedVariant(original)),
    }
}

pub(super) fn normalized_end_bound_value(value: &VmValue, len: usize) -> Result<usize, VmError> {
    let original = value.clone();
    let VmValue::Variant { tag, value } = value else {
        return Err(VmError::ExpectedVariant(original));
    };
    match tag.0.as_str() {
        "unbounded" => Ok(len),
        "included" => {
            let Some(value) = value.as_ref() else {
                return Err(VmError::ExpectedVariant(original));
            };
            usize::try_from(int_value(value)? + 1)
                .map_err(|_| VmError::ExpectedInt((**value).clone()))
        }
        "excluded" => {
            let Some(value) = value.as_ref() else {
                return Err(VmError::ExpectedVariant(original));
            };
            usize::try_from(int_value(value)?).map_err(|_| VmError::ExpectedInt((**value).clone()))
        }
        _ => Err(VmError::ExpectedVariant(original)),
    }
}
