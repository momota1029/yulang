use super::*;

pub(super) fn close_known_associated_type_signature(
    target: &core_ir::Path,
    signature: DemandSignature,
) -> DemandSignature {
    let Some(name) = target.segments.last() else {
        return signature;
    };
    if name.0 != "fold" && name.0 != "fold_impl" {
        return signature;
    }
    close_fold_signature(signature, name.0 == "fold_impl")
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
    args[2] = close_fold_callback(args[2].clone(), &acc, &item);
    if thunk_callback {
        args[2] = ensure_empty_thunk_signature(args[2].clone());
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
) -> DemandSignature {
    match callback {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect,
            value: Box::new(close_fold_callback(*value, acc, item)),
        },
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(prefer_signature(acc, *param)),
            ret: Box::new(close_fold_callback_item(*ret, acc, item)),
        },
        other => other,
    }
}

fn close_fold_callback_item(
    callback: DemandSignature,
    acc: &DemandSignature,
    item: &DemandSignature,
) -> DemandSignature {
    match callback {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect,
            value: Box::new(close_fold_callback_item(*value, acc, item)),
        },
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(prefer_signature(item, *param)),
            ret: Box::new(close_fold_callback_return(*ret, acc)),
        },
        other => other,
    }
}

fn close_fold_callback_return(ret: DemandSignature, acc: &DemandSignature) -> DemandSignature {
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

fn path_ends_with(path: &core_ir::Path, suffix: &[&str]) -> bool {
    path.segments.len() >= suffix.len()
        && path
            .segments
            .iter()
            .rev()
            .zip(suffix.iter().rev())
            .all(|(segment, expected)| segment.0 == *expected)
}
