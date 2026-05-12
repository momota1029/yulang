use super::*;

pub(super) fn close_known_associated_type_signature_with_semantics(
    _semantics: &DemandSemantics,
    _target: &typed_ir::Path,
    signature: DemandSignature,
) -> DemandSignature {
    signature
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

fn normalize_effect_row(items: Vec<DemandEffect>) -> DemandEffect {
    let mut out = Vec::new();
    for item in items {
        match item {
            DemandEffect::Empty => {}
            DemandEffect::Row(items) => out.extend(items),
            other => out.push(other),
        }
    }
    match out.len() {
        0 => DemandEffect::Empty,
        1 => out.pop().unwrap_or(DemandEffect::Empty),
        _ => DemandEffect::Row(out),
    }
}
