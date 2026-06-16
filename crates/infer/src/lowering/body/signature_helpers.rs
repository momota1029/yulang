//! Extracted body lowering methods.

use super::super::*;

pub(in crate::lowering) fn ann_type_builder(
    modules: &ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<AnnSelfAlias>,
) -> AnnTypeBuilder<'_> {
    match self_alias {
        Some(self_alias) => AnnTypeBuilder::with_self_alias(modules, module, site, self_alias),
        None => AnnTypeBuilder::new(modules, module, site),
    }
}

pub(in crate::lowering) fn add_type_var_aliases(
    builder: &mut AnnTypeBuilder<'_>,
    aliases: &[(String, String)],
) {
    for (alias, target) in aliases {
        builder.add_bare_type_var_alias(alias.clone(), target.clone());
    }
}

pub(in crate::lowering) fn add_type_name_aliases(
    builder: &mut AnnTypeBuilder<'_>,
    aliases: &[(String, TypeDeclId)],
) {
    for (alias, target) in aliases {
        builder.add_type_name_alias(alias.clone(), *target);
    }
}

pub(in crate::lowering) fn ann_type_builder_with_aliases<'a>(
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    self_alias: Option<AnnSelfAlias>,
    aliases: &[(String, String)],
    type_name_aliases: &[(String, TypeDeclId)],
) -> AnnTypeBuilder<'a> {
    let mut builder = ann_type_builder(modules, module, site, self_alias);
    add_type_var_aliases(&mut builder, aliases);
    add_type_name_aliases(&mut builder, type_name_aliases);
    builder
}

pub(in crate::lowering) fn build_signature_type_expr(
    builder: &mut AnnTypeBuilder,
    type_expr: &Cst,
) -> Result<SignatureType, AnnBuildError> {
    builder
        .build_type_expr(type_expr)
        .map(|ann| signature_from_ann_type(&ann))
}

pub(in crate::lowering) fn role_method_signature_with_receiver(
    receiver: Option<&Name>,
    receiver_type: Option<&String>,
    signature: SignatureType,
) -> SignatureType {
    let (Some(_receiver), Some(receiver_type)) = (receiver, receiver_type) else {
        return signature;
    };
    let param = SignatureType::Var(SignatureVar {
        name: receiver_type.clone(),
    });
    let (ret_eff, ret) = split_effectful_signature(signature);
    SignatureType::Function {
        param: Box::new(param),
        arg_eff: None,
        ret_eff,
        ret: Box::new(ret),
    }
}

pub(in crate::lowering) fn split_effectful_signature(
    signature: SignatureType,
) -> (Option<SignatureEffectRow>, SignatureType) {
    match signature {
        SignatureType::Effectful { eff, ret } => (Some(eff), *ret),
        signature => (None, signature),
    }
}

pub(in crate::lowering) fn role_input_variances_from_requirements(
    role_inputs: &[String],
    methods: &[RoleMethodDecl],
    requirements: &FxHashMap<DefId, RoleMethodRequirement>,
) -> Vec<RoleInputVariance> {
    let input_indices = role_inputs
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect::<FxHashMap<_, _>>();
    let mut variances = vec![RoleInputVariance::Unused; role_inputs.len()];
    for method in methods {
        let Some(requirement) = requirements.get(&method.def) else {
            continue;
        };
        record_role_input_variances_in_signature(
            &requirement.signature,
            &input_indices,
            RoleInputOccurrence::Covariant,
            &mut variances,
        );
    }
    variances
}

pub(in crate::lowering) fn record_role_input_variances_in_signature(
    signature: &SignatureType,
    input_indices: &FxHashMap<String, usize>,
    occurrence: RoleInputOccurrence,
    variances: &mut [RoleInputVariance],
) {
    match signature {
        SignatureType::Builtin(_) | SignatureType::Named(_) => {}
        SignatureType::Var(var) => {
            if let Some(index) = input_indices.get(&var.name).copied()
                && let Some(slot) = variances.get_mut(index)
            {
                *slot = slot.record(occurrence);
            }
        }
        SignatureType::EffectRow(row) => {
            record_role_input_variances_in_effect_row(row, input_indices, variances);
        }
        SignatureType::Effectful { eff, ret } => {
            record_role_input_variances_in_effect_row(eff, input_indices, variances);
            record_role_input_variances_in_signature(ret, input_indices, occurrence, variances);
        }
        SignatureType::Tuple(items) => {
            for item in items {
                record_role_input_variances_in_signature(
                    item,
                    input_indices,
                    occurrence,
                    variances,
                );
            }
        }
        SignatureType::Apply { callee, args } => {
            record_role_input_variances_in_signature(
                callee,
                input_indices,
                RoleInputOccurrence::Invariant,
                variances,
            );
            for arg in args {
                record_role_input_variances_in_signature(
                    arg,
                    input_indices,
                    RoleInputOccurrence::Invariant,
                    variances,
                );
            }
        }
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            record_role_input_variances_in_signature(
                param,
                input_indices,
                occurrence.flipped(),
                variances,
            );
            if let Some(arg_eff) = arg_eff {
                record_role_input_variances_in_effect_row(arg_eff, input_indices, variances);
            }
            if let Some(ret_eff) = ret_eff {
                record_role_input_variances_in_effect_row(ret_eff, input_indices, variances);
            }
            record_role_input_variances_in_signature(ret, input_indices, occurrence, variances);
        }
    }
}

pub(in crate::lowering) fn record_role_input_variances_in_effect_row(
    row: &SignatureEffectRow,
    input_indices: &FxHashMap<String, usize>,
    variances: &mut [RoleInputVariance],
) {
    for item in &row.items {
        match item {
            SignatureEffectAtom::Type(ty) => record_role_input_variances_in_signature(
                ty,
                input_indices,
                RoleInputOccurrence::Invariant,
                variances,
            ),
            SignatureEffectAtom::Wildcard => {}
        }
    }
    if let Some(tail) = &row.tail
        && let Some(index) = input_indices.get(&tail.name).copied()
        && let Some(slot) = variances.get_mut(index)
    {
        *slot = slot.record(RoleInputOccurrence::Invariant);
    }
}

pub(in crate::lowering) fn operation_signature_with_effect(
    signature: SignatureType,
    effect: SignatureType,
) -> Option<SignatureType> {
    let SignatureType::Function {
        param,
        arg_eff,
        ret_eff,
        ret,
    } = signature
    else {
        return None;
    };
    Some(SignatureType::Function {
        param,
        arg_eff,
        ret_eff: Some(operation_return_effect_row(ret_eff, effect)),
        ret,
    })
}

pub(in crate::lowering) fn operation_return_effect_row(
    ret_eff: Option<SignatureEffectRow>,
    effect: SignatureType,
) -> SignatureEffectRow {
    let mut row = ret_eff.unwrap_or(SignatureEffectRow {
        items: Vec::new(),
        tail: None,
    });
    row.items.insert(0, SignatureEffectAtom::Type(effect));
    row
}

pub(in crate::lowering) fn signature_from_ann_type(ann: &AnnType) -> SignatureType {
    match ann {
        AnnType::Builtin(builtin) => SignatureType::Builtin(*builtin),
        AnnType::Named(id) => SignatureType::Named(*id),
        AnnType::Var(var) => SignatureType::Var(SignatureVar {
            name: var.name.clone(),
        }),
        AnnType::Wildcard(var) => SignatureType::Var(SignatureVar {
            name: var.name.clone(),
        }),
        AnnType::EffectRow(row) => SignatureType::EffectRow(signature_effect_row_from_ann(row)),
        AnnType::Effectful { eff, ret } => SignatureType::Effectful {
            eff: signature_effect_row_from_ann(eff),
            ret: Box::new(signature_from_ann_type(ret)),
        },
        AnnType::Tuple(items) => SignatureType::Tuple(
            items
                .iter()
                .map(signature_from_ann_type)
                .collect::<Vec<_>>(),
        ),
        AnnType::Apply { callee, args } => SignatureType::Apply {
            callee: Box::new(signature_from_ann_type(callee)),
            args: args.iter().map(signature_from_ann_type).collect(),
        },
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => SignatureType::Function {
            param: Box::new(signature_from_ann_type(param)),
            arg_eff: arg_eff.as_ref().map(signature_effect_row_from_ann),
            ret_eff: ret_eff.as_ref().map(signature_effect_row_from_ann),
            ret: Box::new(signature_from_ann_type(ret)),
        },
    }
}

pub(in crate::lowering) fn signature_effect_row_from_ann(
    row: &crate::annotation::AnnEffectRow,
) -> SignatureEffectRow {
    SignatureEffectRow {
        items: row
            .items
            .iter()
            .map(|atom| match atom {
                crate::annotation::AnnEffectAtom::Type(ty) => {
                    SignatureEffectAtom::Type(signature_from_ann_type(ty))
                }
                crate::annotation::AnnEffectAtom::Wildcard => SignatureEffectAtom::Wildcard,
            })
            .collect(),
        tail: row.tail.as_ref().map(|tail| SignatureVar {
            name: tail.name.clone(),
        }),
    }
}
