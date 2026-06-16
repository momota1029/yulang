//! Compatibility checks between inferred compact surfaces and declared signatures.
//!
//! These helpers only classify an already-compact type for diagnostics. They do
//! not mutate constraints and must not become a fallback path for inference.

use super::*;

pub(super) fn compact_type_matches_signature(
    actual: &CompactType,
    expected: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    if actual.never {
        return true;
    }
    match expected {
        SignatureType::Var(_) => true,
        SignatureType::Effectful { ret, .. } => {
            compact_type_matches_signature(actual, ret, modules)
        }
        SignatureType::Function { ret, .. } => {
            compact_type_matches_function_signature(actual, ret, modules)
        }
        SignatureType::Tuple(items) => compact_type_matches_tuple_signature(actual, items, modules),
        SignatureType::EffectRow(_) => compact_type_matches_effect_row_signature(actual),
        SignatureType::Builtin(_) | SignatureType::Named(_) | SignatureType::Apply { .. } => {
            let Some(expected) = expected_constructor_signature(expected, modules) else {
                return true;
            };
            compact_type_matches_constructor_signature(actual, &expected, modules)
        }
    }
}

pub(super) fn builtin_annotation_mismatch(
    actual: &CompactType,
    expected: &SignatureType,
) -> Option<(BuiltinType, BuiltinType)> {
    let actual = compact_type_single_builtin(actual)?;
    let expected = signature_single_builtin(expected)?;
    (actual != expected && !builtin_annotation_mismatch_can_be_deferred(actual, expected))
        .then_some((actual, expected))
}

fn compact_type_matches_function_signature(
    actual: &CompactType,
    expected_ret: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    if compact_type_has_concrete_non_function(actual) {
        return false;
    }
    actual
        .funs
        .iter()
        .all(|fun| compact_fun_matches_signature(fun, expected_ret, modules))
}

fn compact_type_matches_tuple_signature(
    actual: &CompactType,
    expected_items: &[SignatureType],
    modules: &ModuleTable,
) -> bool {
    if compact_type_has_concrete_non_tuple(actual) {
        return false;
    }
    actual.tuples.iter().all(|tuple| {
        tuple.items.len() == expected_items.len()
            && tuple
                .items
                .iter()
                .zip(expected_items)
                .all(|(actual, expected)| compact_type_matches_signature(actual, expected, modules))
    })
}

fn compact_fun_matches_signature(
    actual: &CompactFun,
    expected_ret: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    compact_type_matches_signature(&actual.ret, expected_ret, modules)
}

fn compact_type_matches_effect_row_signature(actual: &CompactType) -> bool {
    !actual.never
        && actual.builtins.is_empty()
        && actual.cons.is_empty()
        && actual.funs.is_empty()
        && actual.records.is_empty()
        && actual.record_spreads.is_empty()
        && actual.poly_variants.is_empty()
        && actual.tuples.is_empty()
}

fn compact_type_matches_constructor_signature(
    actual: &CompactType,
    expected: &ExpectedConstructorSignature,
    modules: &ModuleTable,
) -> bool {
    if compact_type_has_concrete_non_constructor(actual) {
        return false;
    }
    let expected_builtin = expected.builtin();
    actual
        .builtins
        .iter()
        .all(|builtin| Some(*builtin) == expected_builtin)
        && actual.cons.iter().all(|(path, args)| {
            path == &expected.path
                && args.len() == expected.args.len()
                && args.iter().zip(&expected.args).all(|(actual, expected)| {
                    compact_bounds_matches_signature(actual, expected, modules)
                })
        })
}

fn compact_type_has_concrete_non_function(actual: &CompactType) -> bool {
    !actual.builtins.is_empty()
        || !actual.cons.is_empty()
        || !actual.records.is_empty()
        || !actual.record_spreads.is_empty()
        || !actual.poly_variants.is_empty()
        || !actual.tuples.is_empty()
        || !actual.rows.is_empty()
}

fn compact_type_has_concrete_non_tuple(actual: &CompactType) -> bool {
    !actual.builtins.is_empty()
        || !actual.cons.is_empty()
        || !actual.funs.is_empty()
        || !actual.records.is_empty()
        || !actual.record_spreads.is_empty()
        || !actual.poly_variants.is_empty()
        || !actual.rows.is_empty()
}

fn compact_type_has_concrete_non_constructor(actual: &CompactType) -> bool {
    !actual.funs.is_empty()
        || !actual.records.is_empty()
        || !actual.record_spreads.is_empty()
        || !actual.poly_variants.is_empty()
        || !actual.tuples.is_empty()
        || !actual.rows.is_empty()
}

fn compact_bounds_matches_signature(
    actual: &CompactBounds,
    expected: &SignatureType,
    modules: &ModuleTable,
) -> bool {
    match actual {
        CompactBounds::Interval { lower, upper, .. } => {
            compact_type_matches_signature(lower, expected, modules)
                && compact_type_matches_signature(upper, expected, modules)
        }
        CompactBounds::Con { path, args } => {
            let Some(expected) = expected_constructor_signature(expected, modules) else {
                return true;
            };
            path == &expected.path
                && args.len() == expected.args.len()
                && args.iter().zip(&expected.args).all(|(actual, expected)| {
                    compact_bounds_matches_signature(actual, expected, modules)
                })
        }
        CompactBounds::Fun { ret, .. } => match expected {
            SignatureType::Function {
                ret: expected_ret, ..
            } => compact_bounds_matches_signature(ret, expected_ret, modules),
            SignatureType::Var(_) => true,
            SignatureType::Effectful { ret: expected, .. } => {
                compact_bounds_matches_signature(actual, expected, modules)
            }
            _ => false,
        },
        CompactBounds::Tuple { items } => match expected {
            SignatureType::Var(_) => true,
            _ => items.is_empty(),
        },
        CompactBounds::Record { .. } | CompactBounds::PolyVariant { .. } => {
            matches!(expected, SignatureType::Var(_))
        }
    }
}

#[derive(Debug, Clone)]
struct ExpectedConstructorSignature {
    path: Vec<String>,
    args: Vec<SignatureType>,
}

impl ExpectedConstructorSignature {
    fn builtin(&self) -> Option<BuiltinType> {
        match self.path.as_slice() {
            [name] if self.args.is_empty() => BuiltinType::from_surface_name(name),
            _ => None,
        }
    }
}

fn expected_constructor_signature(
    expected: &SignatureType,
    modules: &ModuleTable,
) -> Option<ExpectedConstructorSignature> {
    match expected {
        SignatureType::Builtin(builtin) => Some(ExpectedConstructorSignature {
            path: vec![builtin.surface_name().to_string()],
            args: Vec::new(),
        }),
        SignatureType::Named(id) => Some(ExpectedConstructorSignature {
            path: signature_type_decl_path(*id, modules)?,
            args: Vec::new(),
        }),
        SignatureType::Apply { callee, args } => {
            let mut expected = expected_constructor_signature(callee, modules)?;
            expected.args.extend(args.iter().cloned());
            Some(expected)
        }
        SignatureType::Effectful { ret, .. } => expected_constructor_signature(ret, modules),
        SignatureType::Var(_) => None,
        SignatureType::EffectRow(_) | SignatureType::Function { .. } | SignatureType::Tuple(_) => {
            None
        }
    }
}

fn compact_type_single_builtin(ty: &CompactType) -> Option<BuiltinType> {
    if ty.never
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.poly_variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
    {
        return None;
    }
    let [builtin] = ty.builtins.as_slice() else {
        return None;
    };
    Some(*builtin)
}

fn signature_single_builtin(signature: &SignatureType) -> Option<BuiltinType> {
    match signature {
        SignatureType::Effectful { ret, .. } => signature_single_builtin(ret),
        SignatureType::Builtin(builtin) => Some(*builtin),
        _ => None,
    }
}

fn builtin_annotation_mismatch_can_be_deferred(actual: BuiltinType, expected: BuiltinType) -> bool {
    matches!(
        (actual, expected),
        (BuiltinType::Int, BuiltinType::Float) | (BuiltinType::Float, BuiltinType::Int)
    )
}

fn signature_type_decl_path(id: TypeDeclId, modules: &ModuleTable) -> Option<Vec<String>> {
    let decl = modules.type_decl_by_id(id)?;
    Some(
        modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect(),
    )
}
