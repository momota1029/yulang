use super::*;

pub(super) fn close_known_associated_type_signature(
    target: &core_ir::Path,
    signature: DemandSignature,
) -> DemandSignature {
    if path_ends_with(target, &["std", "flow", "loop", "for_in"]) {
        return close_for_in_signature(signature);
    }
    let Some(name) = target.segments.last() else {
        return signature;
    };
    if name.0 != "fold" && name.0 != "fold_impl" {
        return signature;
    }
    close_fold_signature(signature, name.0 == "fold_impl")
}

fn close_for_in_signature(signature: DemandSignature) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 2 {
        return curried_signatures(&args, ret);
    }
    let Some(item) = fold_item_signature(&args[0]) else {
        return curried_signatures(&args, ret);
    };
    args[1] = close_for_in_callback(args[1].clone(), &item);
    curried_signatures(&args, ret)
}

fn close_for_in_callback(callback: DemandSignature, item: &DemandSignature) -> DemandSignature {
    match callback {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect,
            value: Box::new(close_for_in_callback(*value, item)),
        },
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(prefer_signature(item, *param)),
            ret: Box::new(close_ignored_callback_return(*ret)),
        },
        other => other,
    }
}

fn close_ignored_callback_return(ret: DemandSignature) -> DemandSignature {
    match ret {
        DemandSignature::Thunk { effect, .. } => DemandSignature::Thunk {
            effect,
            value: Box::new(DemandSignature::Ignored),
        },
        other => other,
    }
}

fn close_fold_signature(signature: DemandSignature, thunk_callback: bool) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 3 {
        return curried_signatures(&args, ret);
    }
    let Some(item) = fold_item_signature(&args[0]) else {
        return curried_signatures(&args, ret);
    };
    let acc = signature_value(&args[1]);
    let result_effect = fold_result_effect(&ret);
    args[2] = close_fold_callback(args[2].clone(), &acc, &item, result_effect.as_ref());
    let ret = close_fold_return(ret, &acc);
    if thunk_callback {
        args[2] = ensure_empty_thunk_signature(args[2].clone());
        return curried_signatures_with_intermediate_ret_thunks(&args, ret);
    }
    curried_signatures(&args, ret)
}

fn ensure_empty_thunk_signature(signature: DemandSignature) -> DemandSignature {
    match signature {
        thunk @ DemandSignature::Thunk { .. } => thunk,
        value => DemandSignature::Thunk {
            effect: DemandEffect::Empty,
            value: Box::new(value),
        },
    }
}

fn uncurried_signatures(signature: DemandSignature) -> (Vec<DemandSignature>, DemandSignature) {
    let mut args = Vec::new();
    let mut current = signature;
    loop {
        match current {
            DemandSignature::Fun { param, ret } => {
                args.push(*param);
                current = *ret;
            }
            ret => return (args, ret),
        }
    }
}

fn curried_signatures_with_intermediate_ret_thunks(
    args: &[DemandSignature],
    ret: DemandSignature,
) -> DemandSignature {
    match args {
        [] => ret,
        [last] => DemandSignature::Fun {
            param: Box::new(last.clone()),
            ret: Box::new(ret),
        },
        [first, rest @ ..] => DemandSignature::Fun {
            param: Box::new(first.clone()),
            ret: Box::new(DemandSignature::Thunk {
                effect: DemandEffect::Empty,
                value: Box::new(curried_signatures_with_intermediate_ret_thunks(rest, ret)),
            }),
        },
    }
}

fn fold_item_signature(container: &DemandSignature) -> Option<DemandSignature> {
    match signature_core_value(container) {
        DemandCoreType::Named { path, args } if path_ends_with(&path, &["std", "list", "list"]) => {
            single_type_arg(&args).map(DemandSignature::Core)
        }
        DemandCoreType::Named { path, .. } if path_ends_with(&path, &["std", "range", "range"]) => {
            Some(DemandSignature::Core(DemandCoreType::Named {
                path: core_ir::Path::from_name(core_ir::Name("int".to_string())),
                args: Vec::new(),
            }))
        }
        _ => None,
    }
}

fn single_type_arg(args: &[DemandTypeArg]) -> Option<DemandCoreType> {
    let [arg] = args else {
        return None;
    };
    match arg {
        DemandTypeArg::Type(ty) => Some(ty.clone()),
        DemandTypeArg::Bounds {
            lower: Some(ty), ..
        }
        | DemandTypeArg::Bounds {
            lower: None,
            upper: Some(ty),
        } => Some(ty.clone()),
        DemandTypeArg::Bounds {
            lower: None,
            upper: None,
        } => None,
    }
}

fn close_fold_callback(
    callback: DemandSignature,
    acc: &DemandSignature,
    item: &DemandSignature,
    result_effect: Option<&DemandEffect>,
) -> DemandSignature {
    match callback {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect,
            value: Box::new(close_fold_callback(*value, acc, item, result_effect)),
        },
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(prefer_signature(acc, *param)),
            ret: Box::new(ensure_result_effect_thunk(
                close_fold_callback_item(*ret, acc, item, result_effect),
                result_effect,
            )),
        },
        other => other,
    }
}

fn close_fold_callback_item(
    callback: DemandSignature,
    acc: &DemandSignature,
    item: &DemandSignature,
    result_effect: Option<&DemandEffect>,
) -> DemandSignature {
    match callback {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect: prefer_effect(result_effect, effect),
            value: Box::new(close_fold_callback_item(*value, acc, item, result_effect)),
        },
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(prefer_signature(item, *param)),
            ret: Box::new(close_fold_callback_return(*ret, acc, result_effect)),
        },
        other => other,
    }
}

fn close_fold_callback_return(
    ret: DemandSignature,
    acc: &DemandSignature,
    result_effect: Option<&DemandEffect>,
) -> DemandSignature {
    match ret {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect: prefer_effect(result_effect, effect),
            value: Box::new(prefer_signature(acc, *value)),
        },
        other => {
            let value = prefer_signature(acc, other);
            match result_effect {
                Some(effect) if !matches!(effect, DemandEffect::Empty) => DemandSignature::Thunk {
                    effect: effect.clone(),
                    value: Box::new(value),
                },
                _ => value,
            }
        }
    }
}

fn close_fold_return(ret: DemandSignature, acc: &DemandSignature) -> DemandSignature {
    match ret {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect,
            value: Box::new(prefer_signature(acc, *value)),
        },
        other => prefer_signature(acc, other),
    }
}

fn prefer_signature(preferred: &DemandSignature, current: DemandSignature) -> DemandSignature {
    if current.is_closed() {
        return current;
    }
    if DemandUnifier::new()
        .unify_signature(&current, preferred)
        .is_ok()
    {
        preferred.clone()
    } else {
        current
    }
}

fn fold_result_effect(ret: &DemandSignature) -> Option<DemandEffect> {
    match ret {
        DemandSignature::Thunk { effect, .. } if !matches!(effect, DemandEffect::Empty) => {
            Some(effect.clone())
        }
        _ => None,
    }
}

fn ensure_result_effect_thunk(
    signature: DemandSignature,
    result_effect: Option<&DemandEffect>,
) -> DemandSignature {
    match (signature, result_effect) {
        (thunk @ DemandSignature::Thunk { .. }, _) => thunk,
        (signature, Some(effect)) if !matches!(effect, DemandEffect::Empty) => {
            DemandSignature::Thunk {
                effect: effect.clone(),
                value: Box::new(signature),
            }
        }
        (signature, _) => signature,
    }
}

fn prefer_effect(preferred: Option<&DemandEffect>, current: DemandEffect) -> DemandEffect {
    match (preferred, &current) {
        (Some(preferred), DemandEffect::Empty) => preferred.clone(),
        _ => current,
    }
}

fn path_ends_with(path: &core_ir::Path, suffix: &[&str]) -> bool {
    path.segments.len() >= suffix.len()
        && path
            .segments
            .iter()
            .rev()
            .zip(suffix.iter().rev())
            .all(|(segment, expected)| segment.0 == *expected)
}
