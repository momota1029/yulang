use super::*;

pub(super) fn close_known_associated_type_signature_with_semantics(
    semantics: &DemandSemantics,
    target: &core_ir::Path,
    signature: DemandSignature,
) -> DemandSignature {
    match semantics.associated_signature_kind(target) {
        Some(AssociatedSignatureKind::ForIn { loop_effects }) => {
            close_for_in_signature(semantics, signature, &loop_effects)
        }
        Some(AssociatedSignatureKind::SubHandler { effect }) => {
            close_sub_handler_signature(signature, effect)
        }
        Some(AssociatedSignatureKind::LocalVarRef { effect }) => {
            close_local_var_ref_signature(signature, effect)
        }
        Some(AssociatedSignatureKind::LocalVarRun { effect }) => {
            close_local_var_run_signature(signature, effect)
        }
        Some(AssociatedSignatureKind::ListViewRaw { result }) => {
            close_list_view_raw_signature(semantics, signature, result)
        }
        Some(AssociatedSignatureKind::ListIndexRaw) => close_list_index_raw_signature(signature),
        Some(AssociatedSignatureKind::ListIndexRangeRaw) => {
            close_list_index_range_raw_signature(signature)
        }
        Some(AssociatedSignatureKind::ListBinary) => close_list_binary_signature(signature),
        Some(AssociatedSignatureKind::HandlerCollection { .. }) => {
            close_handler_collection_signature(signature)
        }
        Some(AssociatedSignatureKind::FoldFind) => close_find_signature(semantics, signature),
        Some(AssociatedSignatureKind::Fold { thunk_callback }) => {
            close_fold_signature(semantics, signature, thunk_callback)
        }
        None => signature,
    }
}

pub(super) fn close_default_effect_holes(signature: DemandSignature) -> DemandSignature {
    match signature {
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(close_default_effect_holes(*param)),
            ret: Box::new(close_default_effect_holes(*ret)),
        },
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect: close_default_effect(effect),
            value: Box::new(close_default_effect_holes(*value)),
        },
        DemandSignature::Core(ty) => DemandSignature::Core(close_default_core_effect_holes(ty)),
        other => other,
    }
}

fn close_default_core_effect_holes(ty: DemandCoreType) -> DemandCoreType {
    match ty {
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => DemandCoreType::Fun {
            param: Box::new(close_default_core_effect_holes(*param)),
            param_effect: Box::new(close_default_effect(*param_effect)),
            ret_effect: Box::new(close_default_effect(*ret_effect)),
            ret: Box::new(close_default_core_effect_holes(*ret)),
        },
        DemandCoreType::Named { path, args } => DemandCoreType::Named {
            path,
            args: args
                .into_iter()
                .map(close_default_type_arg_effects)
                .collect(),
        },
        DemandCoreType::Tuple(items) => DemandCoreType::Tuple(
            items
                .into_iter()
                .map(close_default_core_effect_holes)
                .collect(),
        ),
        DemandCoreType::Record(fields) => DemandCoreType::Record(
            fields
                .into_iter()
                .map(|field| DemandRecordField {
                    value: close_default_core_effect_holes(field.value),
                    ..field
                })
                .collect(),
        ),
        DemandCoreType::Variant(cases) => DemandCoreType::Variant(
            cases
                .into_iter()
                .map(|case| DemandVariantCase {
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(close_default_core_effect_holes)
                        .collect(),
                    ..case
                })
                .collect(),
        ),
        DemandCoreType::RowAsValue(items) => {
            DemandCoreType::RowAsValue(items.into_iter().map(close_default_effect).collect())
        }
        DemandCoreType::Union(items) => DemandCoreType::Union(
            items
                .into_iter()
                .map(close_default_core_effect_holes)
                .collect(),
        ),
        DemandCoreType::Inter(items) => DemandCoreType::Inter(
            items
                .into_iter()
                .map(close_default_core_effect_holes)
                .collect(),
        ),
        DemandCoreType::Recursive { var, body } => DemandCoreType::Recursive {
            var,
            body: Box::new(close_default_core_effect_holes(*body)),
        },
        other => other,
    }
}

fn close_default_type_arg_effects(arg: DemandTypeArg) -> DemandTypeArg {
    match arg {
        DemandTypeArg::Type(ty) => DemandTypeArg::Type(close_default_core_effect_holes(ty)),
        DemandTypeArg::Bounds { lower, upper } => DemandTypeArg::Bounds {
            lower: lower.map(close_default_core_effect_holes),
            upper: upper.map(close_default_core_effect_holes),
        },
    }
}

fn close_default_effect(effect: DemandEffect) -> DemandEffect {
    match effect {
        DemandEffect::Hole(_) => DemandEffect::Empty,
        DemandEffect::Atom(ty) => DemandEffect::Atom(close_default_core_effect_holes(ty)),
        DemandEffect::Row(items) => normalize_effect_row(
            items
                .into_iter()
                .map(close_default_effect)
                .collect::<Vec<_>>(),
        ),
        DemandEffect::Empty => DemandEffect::Empty,
    }
}

fn close_for_in_signature(
    semantics: &DemandSemantics,
    signature: DemandSignature,
    loop_effects: &[core_ir::Path],
) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 2 {
        return curried_signatures(&args, ret);
    }
    let Some(item) = fold_item_signature(semantics, &args[0]) else {
        return curried_signatures(&args, ret);
    };
    let result_effect = for_in_result_effect(&ret)
        .or_else(|| for_in_callback_residual_effect(&args[1], loop_effects));
    args[1] = close_for_in_callback(args[1].clone(), &item, result_effect.as_ref());
    let ret = close_for_in_return(ret, result_effect.as_ref());
    curried_signatures(&args, ret)
}

fn close_handler_collection_signature(signature: DemandSignature) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.is_empty() {
        return curried_signatures(&args, ret);
    }
    let Some(result) = collection_result_signature(&ret) else {
        return curried_signatures(&args, ret);
    };
    let Some(item) = collection_result_item(&result) else {
        return curried_signatures(&args, result);
    };
    args[0] = close_handler_input_value(args[0].clone(), &item);
    curried_signatures(&args, result)
}

fn close_sub_handler_signature(
    signature: DemandSignature,
    effect_path: core_ir::Path,
) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.is_empty() {
        return curried_signatures(&args, ret);
    }
    let value = signature_value(&ret);
    if !value.is_closed() || matches!(signature_core_value(&value), DemandCoreType::Never) {
        return curried_signatures(&args, ret);
    }
    let residual = match &ret {
        DemandSignature::Thunk { effect, .. } => effect.clone(),
        _ => DemandEffect::Empty,
    };
    let sub_effect = DemandEffect::Atom(DemandCoreType::Named {
        path: effect_path,
        args: vec![DemandTypeArg::Type(signature_core_value(&value))],
    });
    args[0] = DemandSignature::Thunk {
        effect: normalize_effect_row(vec![sub_effect, residual]),
        value: Box::new(value),
    };
    curried_signatures(&args, ret)
}

fn handler_result_effect(signature: &DemandSignature) -> Option<DemandEffect> {
    match signature {
        DemandSignature::Thunk { effect, .. } => {
            let effect = drop_open_effect_holes(effect.clone());
            (!effect_is_empty(&effect)).then_some(effect)
        }
        _ => None,
    }
}

fn handler_input_effect(signature: &DemandSignature) -> Option<DemandEffect> {
    match signature {
        DemandSignature::Thunk { effect, .. } => Some(effect.clone()),
        _ => None,
    }
}

fn handler_input_value(signature: &DemandSignature) -> Option<DemandSignature> {
    match signature {
        DemandSignature::Thunk { value, .. } => Some((**value).clone()),
        _ => None,
    }
}

fn remove_effect(effect: DemandEffect, consumed: &core_ir::Path) -> DemandEffect {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { path, .. })
            if effect_path_matches(&path, consumed) =>
        {
            DemandEffect::Empty
        }
        DemandEffect::Row(items) => normalize_effect_row(
            items
                .into_iter()
                .map(|item| remove_effect(item, consumed))
                .collect::<Vec<_>>(),
        ),
        other => other,
    }
}

fn named_effect(path: core_ir::Path) -> DemandEffect {
    DemandEffect::Atom(DemandCoreType::Named {
        path,
        args: Vec::new(),
    })
}

fn close_local_var_ref_signature(
    signature: DemandSignature,
    effect: core_ir::Path,
) -> DemandSignature {
    let (args, ret) = uncurried_signatures(signature);
    let Some(value) = var_ref_value_arg(&ret) else {
        return curried_signatures(&args, ret);
    };
    if !value.is_closed() {
        return curried_signatures(&args, ret);
    }
    let Some(ret) = named_core_with_args_like(
        &ret,
        vec![
            DemandTypeArg::Type(local_ref_effect_arg(effect)),
            DemandTypeArg::Type(value),
        ],
    ) else {
        return curried_signatures(&args, ret);
    };
    let ret = DemandSignature::Core(ret);
    curried_signatures(&args, ret)
}

fn close_local_var_run_signature(
    signature: DemandSignature,
    effect: core_ir::Path,
) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 2 {
        return curried_signatures(&args, ret);
    }
    let value = handler_input_value(&args[1])
        .filter(DemandSignature::is_closed)
        .or_else(|| {
            let value = signature_value(&ret);
            value.is_closed().then_some(value)
        });
    let Some(value) = value else {
        return curried_signatures(&args, ret);
    };
    let residual = handler_result_effect(&ret)
        .or_else(|| {
            handler_input_effect(&args[1]).map(|effect_row| remove_effect(effect_row, &effect))
        })
        .map(drop_open_effect_holes)
        .filter(|effect| !effect_is_empty(effect))
        .unwrap_or(DemandEffect::Empty);
    args[0] = close_local_var_run_state(args[0].clone(), &value);
    args[1] = DemandSignature::Thunk {
        effect: normalize_effect_row(vec![named_effect(effect), residual.clone()]),
        value: Box::new(value.clone()),
    };
    let ret = match residual {
        DemandEffect::Empty => value,
        effect => DemandSignature::Thunk {
            effect,
            value: Box::new(value),
        },
    };
    curried_signatures(&args, ret)
}

fn close_local_var_run_state(state: DemandSignature, value: &DemandSignature) -> DemandSignature {
    match state {
        DemandSignature::Ignored | DemandSignature::Hole(_) => value.clone(),
        DemandSignature::Core(DemandCoreType::Hole(_)) => value.clone(),
        other => other,
    }
}

fn local_ref_effect_arg(effect: core_ir::Path) -> DemandCoreType {
    effect_arg_core(DemandEffect::Atom(DemandCoreType::Named {
        path: effect,
        args: Vec::new(),
    }))
}

fn effect_arg_core(effect: DemandEffect) -> DemandCoreType {
    match effect {
        DemandEffect::Empty => DemandCoreType::Never,
        DemandEffect::Row(items) => DemandCoreType::RowAsValue(items),
        effect => DemandCoreType::RowAsValue(vec![effect]),
    }
}

fn close_list_view_raw_signature(
    semantics: &DemandSemantics,
    signature: DemandSignature,
    result: Option<core_ir::Path>,
) -> DemandSignature {
    let (args, ret) = uncurried_signatures(signature);
    let Some(xs) = args.first() else {
        return curried_signatures(&args, ret);
    };
    let Some(item) = fold_item_signature(semantics, xs) else {
        return curried_signatures(&args, ret);
    };
    let Some(ret) = named_core_with_single_arg_path_like(&ret, result, signature_core_value(&item))
    else {
        return curried_signatures(&args, ret);
    };
    let ret = DemandSignature::Core(ret);
    curried_signatures(&args, ret)
}

fn close_list_index_raw_signature(signature: DemandSignature) -> DemandSignature {
    let (mut args, ret) = uncurried_application_signatures(signature);
    if args.len() < 2 {
        return curried_signatures(&args, ret);
    }
    let item = prefer_closed_core([list_item_arg(&args[0]), {
        let value = signature_core_value(&ret);
        value.is_closed().then_some(value)
    }]);
    let Some(item) = item else {
        return curried_signatures(&args, ret);
    };
    if !item.is_closed() {
        return curried_signatures(&args, ret);
    }
    let Some(xs) = named_core_with_single_arg_like(&args[0], item.clone()) else {
        return curried_signatures(&args, ret);
    };
    args[0] = DemandSignature::Core(xs);
    curried_signatures(&args, DemandSignature::Core(item))
}

fn close_list_index_range_raw_signature(signature: DemandSignature) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 3 {
        return curried_signatures(&args, ret);
    }
    let item = prefer_closed_core([list_item_arg(&args[0]), list_item_arg(&ret)]);
    let Some(item) = item else {
        return curried_signatures(&args, ret);
    };
    if !item.is_closed() {
        return curried_signatures(&args, ret);
    }
    let Some(xs) = named_core_with_single_arg_like(&args[0], item.clone()) else {
        return curried_signatures(&args, ret);
    };
    let Some(ret) = named_core_with_single_arg_like(&ret, item) else {
        return curried_signatures(&args, ret);
    };
    args[0] = DemandSignature::Core(xs);
    curried_signatures(&args, DemandSignature::Core(ret))
}

fn close_list_binary_signature(signature: DemandSignature) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 2 {
        return curried_signatures(&args, ret);
    }
    let item = prefer_closed_core([
        list_item_arg(&args[0]),
        list_item_arg(&args[1]),
        list_item_arg(&ret),
    ]);
    let Some(item) = item else {
        return curried_signatures(&args, ret);
    };
    if !item.is_closed() {
        return curried_signatures(&args, ret);
    }
    let Some(left) = named_core_with_single_arg_like(&args[0], item.clone()) else {
        return curried_signatures(&args, ret);
    };
    let Some(right) = named_core_with_single_arg_like(&args[1], item.clone()) else {
        return curried_signatures(&args, ret);
    };
    let Some(ret) = named_core_with_single_arg_like(&ret, item) else {
        return curried_signatures(&args, ret);
    };
    args[0] = DemandSignature::Core(left);
    args[1] = DemandSignature::Core(right);
    curried_signatures(&args, DemandSignature::Core(ret))
}

fn list_item_arg(signature: &DemandSignature) -> Option<DemandCoreType> {
    let DemandCoreType::Named { args, .. } = signature_core_value(signature) else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    single_type_arg(&args)
}

fn prefer_closed_core(
    candidates: impl IntoIterator<Item = Option<DemandCoreType>>,
) -> Option<DemandCoreType> {
    let candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
    candidates
        .iter()
        .find(|candidate| candidate.is_closed())
        .cloned()
        .or_else(|| candidates.into_iter().next())
}

fn var_ref_value_arg(signature: &DemandSignature) -> Option<DemandCoreType> {
    let DemandCoreType::Named { args, .. } = signature_core_value(signature) else {
        return None;
    };
    if args.len() < 2 {
        return None;
    }
    match &args[1] {
        DemandTypeArg::Type(value) => Some(value.clone()),
        DemandTypeArg::Bounds {
            lower: Some(value), ..
        }
        | DemandTypeArg::Bounds {
            lower: None,
            upper: Some(value),
        } => Some(value.clone()),
        DemandTypeArg::Bounds {
            lower: None,
            upper: None,
        } => None,
    }
}

fn collection_result_signature(ret: &DemandSignature) -> Option<DemandSignature> {
    match signature_core_value(ret) {
        DemandCoreType::Named { path, args }
            if matches!(args.as_slice(), [DemandTypeArg::Type(_)]) =>
        {
            Some(DemandSignature::Core(DemandCoreType::Named { path, args }))
        }
        _ => None,
    }
}

fn collection_result_item(ret: &DemandSignature) -> Option<DemandSignature> {
    match signature_core_value(ret) {
        DemandCoreType::Named { args, .. } => single_type_arg(&args).map(DemandSignature::Core),
        _ => None,
    }
}

fn close_handler_input_value(input: DemandSignature, item: &DemandSignature) -> DemandSignature {
    match input {
        DemandSignature::Thunk { effect, .. } => DemandSignature::Thunk {
            effect,
            value: Box::new(item.clone()),
        },
        other => other,
    }
}

fn close_for_in_callback(
    callback: DemandSignature,
    item: &DemandSignature,
    result_effect: Option<&DemandEffect>,
) -> DemandSignature {
    match callback {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect,
            value: Box::new(close_for_in_callback(*value, item, result_effect)),
        },
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(close_associated_position(*param, item)),
            ret: Box::new(close_ignored_callback_return(*ret, result_effect)),
        },
        DemandSignature::Core(DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        }) => close_for_in_callback(
            demand_core_fun_signature(*param, *param_effect, *ret_effect, *ret),
            item,
            result_effect,
        ),
        other => other,
    }
}

fn close_ignored_callback_return(
    ret: DemandSignature,
    result_effect: Option<&DemandEffect>,
) -> DemandSignature {
    match ret {
        DemandSignature::Thunk { effect, .. } => DemandSignature::Thunk {
            effect: close_effect_with_preferred_payload(effect, result_effect),
            value: Box::new(DemandSignature::Ignored),
        },
        other => other,
    }
}

fn for_in_result_effect(ret: &DemandSignature) -> Option<DemandEffect> {
    match ret {
        DemandSignature::Thunk { effect, .. } => {
            let effect = drop_open_effect_holes(effect.clone());
            (!effect_is_empty(&effect)).then_some(effect)
        }
        _ => None,
    }
}

fn for_in_callback_residual_effect(
    callback: &DemandSignature,
    loop_effects: &[core_ir::Path],
) -> Option<DemandEffect> {
    match callback {
        DemandSignature::Thunk { value, .. } => {
            for_in_callback_residual_effect(value, loop_effects)
        }
        DemandSignature::Fun { ret, .. } => callback_result_residual_effect(ret, loop_effects),
        _ => None,
    }
}

fn callback_result_residual_effect(
    signature: &DemandSignature,
    loop_effects: &[core_ir::Path],
) -> Option<DemandEffect> {
    match signature {
        DemandSignature::Thunk { effect, value } => {
            let residual = drop_open_effect_holes(remove_effects(effect.clone(), loop_effects));
            if !effect_is_empty(&residual) {
                return Some(residual);
            }
            callback_result_residual_effect(value, loop_effects)
        }
        DemandSignature::Fun { ret, .. } => callback_result_residual_effect(ret, loop_effects),
        _ => None,
    }
}

fn close_for_in_return(
    ret: DemandSignature,
    result_effect: Option<&DemandEffect>,
) -> DemandSignature {
    match ret {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect: close_effect_with_preferred_payload(effect, result_effect),
            value,
        },
        other if result_effect.is_some_and(|effect| !effect_is_empty(effect)) => {
            DemandSignature::Thunk {
                effect: result_effect.cloned().unwrap_or(DemandEffect::Empty),
                value: Box::new(other),
            }
        }
        other => other,
    }
}

fn close_fold_signature(
    semantics: &DemandSemantics,
    signature: DemandSignature,
    thunk_callback: bool,
) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 3 {
        return curried_signatures(&args, ret);
    }
    let Some(item) = fold_item_signature(semantics, &args[0]) else {
        return curried_signatures(&args, ret);
    };
    let acc = signature_value(&args[1]);
    let result_effect = fold_result_effect(&ret)
        .or_else(|| fold_callback_effect(&args[2]))
        .map(|effect| close_fold_result_effect(effect, &acc));
    args[2] = close_fold_callback(args[2].clone(), &acc, &item, result_effect.as_ref());
    if let Some(effect) = result_effect
        .as_ref()
        .filter(|effect| !effect_is_empty(effect))
    {
        args[2] = force_return_thunk_effect(args[2].clone(), effect);
    }
    let ret = close_fold_return(ret, &acc, result_effect.as_ref());
    if thunk_callback {
        args[2] = ensure_empty_thunk_signature(args[2].clone());
    }
    curried_signatures(&args, ret)
}

fn close_find_signature(
    semantics: &DemandSemantics,
    signature: DemandSignature,
) -> DemandSignature {
    let (mut args, ret) = uncurried_signatures(signature);
    if args.len() < 2 {
        return curried_signatures(&args, ret);
    }
    let item = prefer_closed_core([
        fold_item_signature(semantics, &args[0]).map(|item| signature_core_value(&item)),
        opt_result_item(&ret),
    ]);
    let Some(item) = item else {
        return curried_signatures(&args, ret);
    };
    if !item.is_closed() {
        return curried_signatures(&args, ret);
    }
    args[1] = close_find_predicate(args[1].clone(), &item);
    let Some(ret) = named_core_with_single_arg_like(&ret, item) else {
        return curried_signatures(&args, ret);
    };
    let ret = DemandSignature::Core(ret);
    curried_signatures(&args, ret)
}

fn close_find_predicate(predicate: DemandSignature, item: &DemandCoreType) -> DemandSignature {
    match predicate {
        DemandSignature::Thunk { value, .. } => close_find_predicate_value(*value, item),
        other => close_find_predicate_value(other, item),
    }
}

fn close_find_predicate_value(
    predicate: DemandSignature,
    item: &DemandCoreType,
) -> DemandSignature {
    match predicate {
        DemandSignature::Fun { .. } | DemandSignature::Core(DemandCoreType::Fun { .. }) => {
            curried_signatures(
                &[DemandSignature::Core(item.clone())],
                DemandSignature::Core(bool_core()),
            )
        }
        other => other,
    }
}

fn opt_result_item(signature: &DemandSignature) -> Option<DemandCoreType> {
    let DemandCoreType::Named { args, .. } = signature_core_value(signature) else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    single_type_arg(&args)
}

fn bool_core() -> DemandCoreType {
    DemandCoreType::Named {
        path: core_ir::Path::from_name(core_ir::Name("bool".to_string())),
        args: Vec::new(),
    }
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
            DemandSignature::Core(DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            }) => {
                args.push(effected_core_signature(*param, *param_effect));
                current = effected_core_signature(*ret, *ret_effect);
            }
            ret => return (args, ret),
        }
    }
}

fn uncurried_application_signatures(
    signature: DemandSignature,
) -> (Vec<DemandSignature>, DemandSignature) {
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

fn fold_item_signature(
    semantics: &DemandSemantics,
    container: &DemandSignature,
) -> Option<DemandSignature> {
    semantics
        .project_unique_associated_type(
            &core_ir::Name("item".to_string()),
            &[signature_core_value(container)],
        )
        .map(DemandSignature::Core)
}

fn named_core_with_single_arg_like(
    signature: &DemandSignature,
    item: DemandCoreType,
) -> Option<DemandCoreType> {
    named_core_with_single_arg_path_like(signature, None, item)
}

fn named_core_with_single_arg_path_like(
    signature: &DemandSignature,
    fallback_path: Option<core_ir::Path>,
    item: DemandCoreType,
) -> Option<DemandCoreType> {
    let path = named_core_path(signature).or(fallback_path)?;
    Some(DemandCoreType::Named {
        path,
        args: vec![DemandTypeArg::Type(item)],
    })
}

fn named_core_with_args_like(
    signature: &DemandSignature,
    args: Vec<DemandTypeArg>,
) -> Option<DemandCoreType> {
    let path = named_core_path(signature)?;
    Some(DemandCoreType::Named { path, args })
}

fn named_core_path(signature: &DemandSignature) -> Option<core_ir::Path> {
    match signature_core_value(signature) {
        DemandCoreType::Named { path, .. } => Some(path),
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
            param: Box::new(close_associated_position(*param, acc)),
            ret: Box::new(close_fold_callback_item(*ret, acc, item, result_effect)),
        },
        DemandSignature::Core(DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        }) => close_fold_callback(
            demand_core_fun_signature(*param, *param_effect, *ret_effect, *ret),
            acc,
            item,
            result_effect,
        ),
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
            param: Box::new(close_associated_position(*param, item)),
            ret: Box::new(close_fold_callback_return(*ret, acc, result_effect)),
        },
        DemandSignature::Core(DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        }) => close_fold_callback_item(
            demand_core_fun_signature(*param, *param_effect, *ret_effect, *ret),
            acc,
            item,
            result_effect,
        ),
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

fn force_return_thunk_effect(signature: DemandSignature, effect: &DemandEffect) -> DemandSignature {
    match signature {
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param,
            ret: Box::new(force_return_thunk_effect(*ret, effect)),
        },
        DemandSignature::Core(DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        }) => {
            let ret = force_return_thunk_effect(effected_core_signature(*ret, *ret_effect), effect);
            let (ret, ret_effect) = signature_effected_core_value(&ret);
            DemandSignature::Core(DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            })
        }
        DemandSignature::Thunk { value, .. } => DemandSignature::Thunk {
            effect: effect.clone(),
            value: Box::new(force_return_thunk_effect(*value, effect)),
        },
        other => other,
    }
}

fn close_fold_return(
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

fn fold_callback_effect(signature: &DemandSignature) -> Option<DemandEffect> {
    match signature {
        DemandSignature::Thunk { effect, value } => (!effect_is_empty(effect))
            .then(|| effect.clone())
            .or_else(|| fold_callback_effect(value)),
        DemandSignature::Fun { ret, .. } => fold_callback_effect(ret),
        _ => None,
    }
}

fn effect_is_empty(effect: &DemandEffect) -> bool {
    matches!(effect, DemandEffect::Empty)
        || matches!(effect, DemandEffect::Row(items) if items.iter().all(effect_is_empty))
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

fn close_associated_position(
    current: DemandSignature,
    associated: &DemandSignature,
) -> DemandSignature {
    match current {
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect,
            value: Box::new(close_associated_position(*value, associated)),
        },
        _ => associated.clone(),
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

fn close_fold_result_effect(effect: DemandEffect, acc: &DemandSignature) -> DemandEffect {
    let acc = signature_core_value(acc);
    close_sub_effect_payload(effect, &acc)
}

fn close_sub_effect_payload(effect: DemandEffect, payload: &DemandCoreType) -> DemandEffect {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { path, args })
            if args_contain_open_hole(&args) =>
        {
            DemandEffect::Atom(DemandCoreType::Named {
                path,
                args: vec![DemandTypeArg::Type(payload.clone())],
            })
        }
        DemandEffect::Row(items) => normalize_effect_row(
            items
                .into_iter()
                .map(|item| close_sub_effect_payload(item, payload))
                .collect::<Vec<_>>(),
        ),
        other => other,
    }
}

fn demand_core_fun_signature(
    param: DemandCoreType,
    param_effect: DemandEffect,
    ret_effect: DemandEffect,
    ret: DemandCoreType,
) -> DemandSignature {
    DemandSignature::Fun {
        param: Box::new(effected_core_signature(param, param_effect)),
        ret: Box::new(effected_core_signature(ret, ret_effect)),
    }
}

fn prefer_effect(preferred: Option<&DemandEffect>, current: DemandEffect) -> DemandEffect {
    match preferred {
        Some(preferred) if !effect_is_empty(preferred) => preferred.clone(),
        _ => current,
    }
}

fn close_effect_with_preferred_payload(
    effect: DemandEffect,
    preferred: Option<&DemandEffect>,
) -> DemandEffect {
    match effect {
        DemandEffect::Hole(_) => preferred.cloned().unwrap_or(DemandEffect::Empty),
        DemandEffect::Atom(DemandCoreType::Named { path, args })
            if args_contain_open_hole(&args) =>
        {
            preferred
                .and_then(|preferred| matching_named_effect(preferred, &path))
                .cloned()
                .unwrap_or(DemandEffect::Atom(DemandCoreType::Named { path, args }))
        }
        DemandEffect::Row(items) => normalize_effect_row(
            items
                .into_iter()
                .map(|item| close_effect_with_preferred_payload(item, preferred))
                .collect::<Vec<_>>(),
        ),
        other => other,
    }
}

fn remove_effects(effect: DemandEffect, removed: &[core_ir::Path]) -> DemandEffect {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { path, .. })
            if removed
                .iter()
                .any(|removed| effect_path_matches(removed, &path)) =>
        {
            DemandEffect::Empty
        }
        DemandEffect::Row(items) => normalize_effect_row(
            items
                .into_iter()
                .map(|item| remove_effects(item, removed))
                .collect::<Vec<_>>(),
        ),
        other => other,
    }
}

fn drop_open_effect_holes(effect: DemandEffect) -> DemandEffect {
    match effect {
        DemandEffect::Hole(_) => DemandEffect::Empty,
        DemandEffect::Row(items) => normalize_effect_row(
            items
                .into_iter()
                .map(drop_open_effect_holes)
                .collect::<Vec<_>>(),
        ),
        other => other,
    }
}

fn matching_named_effect<'a>(
    effect: &'a DemandEffect,
    path: &core_ir::Path,
) -> Option<&'a DemandEffect> {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named {
            path: candidate, ..
        }) if candidate == path => Some(effect),
        DemandEffect::Row(items) => items
            .iter()
            .find_map(|item| matching_named_effect(item, path)),
        _ => None,
    }
}

fn args_contain_open_hole(args: &[DemandTypeArg]) -> bool {
    args.iter().any(type_arg_contains_open_hole)
}

fn type_arg_contains_open_hole(arg: &DemandTypeArg) -> bool {
    match arg {
        DemandTypeArg::Type(ty) => core_contains_open_hole(ty),
        DemandTypeArg::Bounds { lower, upper } => {
            lower.iter().chain(upper).any(core_contains_open_hole)
        }
    }
}

fn core_contains_open_hole(ty: &DemandCoreType) -> bool {
    match ty {
        DemandCoreType::Hole(_) => true,
        DemandCoreType::Named { args, .. } => args_contain_open_hole(args),
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_contains_open_hole(param)
                || effect_contains_open_hole(param_effect)
                || effect_contains_open_hole(ret_effect)
                || core_contains_open_hole(ret)
        }
        DemandCoreType::Tuple(items)
        | DemandCoreType::Union(items)
        | DemandCoreType::Inter(items) => items.iter().any(core_contains_open_hole),
        DemandCoreType::Record(fields) => fields
            .iter()
            .any(|field| core_contains_open_hole(&field.value)),
        DemandCoreType::Variant(cases) => cases
            .iter()
            .flat_map(|case| &case.payloads)
            .any(core_contains_open_hole),
        DemandCoreType::RowAsValue(items) => items.iter().any(effect_contains_open_hole),
        DemandCoreType::Recursive { body, .. } => core_contains_open_hole(body),
        DemandCoreType::Any | DemandCoreType::Never => false,
    }
}

fn effect_contains_open_hole(effect: &DemandEffect) -> bool {
    match effect {
        DemandEffect::Hole(_) => true,
        DemandEffect::Atom(ty) => core_contains_open_hole(ty),
        DemandEffect::Row(items) => items.iter().any(effect_contains_open_hole),
        DemandEffect::Empty => false,
    }
}

fn normalize_effect_row(items: Vec<DemandEffect>) -> DemandEffect {
    let mut out = Vec::new();
    for item in items {
        push_normalized_effect_item(item, &mut out);
    }
    match out.as_slice() {
        [] => DemandEffect::Empty,
        [item] => item.clone(),
        _ => DemandEffect::Row(out),
    }
}

fn push_normalized_effect_item(item: DemandEffect, out: &mut Vec<DemandEffect>) {
    match item {
        DemandEffect::Empty => {}
        DemandEffect::Row(items) => {
            for item in items {
                push_normalized_effect_item(item, out);
            }
        }
        item if demand_effect_is_impossible(&item) => {}
        item if !out.contains(&item) => out.push(item),
        _ => {}
    }
}

fn effect_path_matches(left: &core_ir::Path, right: &core_ir::Path) -> bool {
    left == right
        || qualified_prefix_effect_paths_match(left, right)
        || qualified_prefix_effect_paths_match(right, left)
}

fn qualified_prefix_effect_paths_match(parent: &core_ir::Path, child: &core_ir::Path) -> bool {
    parent.segments.len() > 1
        && child.segments.len() > parent.segments.len()
        && child.segments.starts_with(parent.segments.as_slice())
}
