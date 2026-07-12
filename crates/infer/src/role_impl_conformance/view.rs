//! Binder-normalized immutable views used by role-impl conformance.
//!
//! This first slice only translates the declared source contract. Actual method schemes,
//! function/effect structure, recursive bounds, and the comparison relation belong to later
//! Stage 2 slices.

use poly::types::BuiltinType;

use super::{
    AssociatedAssignment, AssociatedInferenceBinderId, ContractTypeRef, DeclaredType,
    ImplUniversalBinderId, RoleImplConformanceContract, RoleRequirementSubstitutionSlot,
    SignatureType,
};
use crate::annotation::AnnType;
use crate::{ModuleTable, TypeDeclId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredRoleImplView {
    pub(crate) inputs: Vec<DeclaredTypeView>,
    pub(crate) associated: Vec<DeclaredAssociatedView>,
    pub(crate) input_substitution: Vec<DeclaredSubstitutionSlotView>,
    pub(crate) associated_substitution: Vec<DeclaredSubstitutionSlotView>,
    pub(crate) methods: Vec<DeclaredMethodRequirementView>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeclaredAssociatedView {
    Explicit {
        name: String,
        value: DeclaredTypeView,
    },
    Inferred {
        name: String,
        binder: ConformanceBinder,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredSubstitutionSlotView {
    pub(crate) name: String,
    pub(crate) value: DeclaredTypeView,
    pub(crate) references: Vec<DeclaredTypeReferenceView>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredMethodRequirementView {
    pub(crate) name: String,
    pub(crate) requirement: DeclaredTypeView,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeclaredTypeView {
    Available(ConformanceTypeView),
    Unavailable(DeclaredViewUnavailable),
    Ambiguous(DeclaredViewAmbiguity),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeclaredViewUnavailable {
    UnannotatedRequirement,
    UnsupportedFunction,
    UnsupportedEffectful,
    UnsupportedEffectRow,
    UnsupportedApplicationCallee,
    MissingCanonicalNominalPath,
    MissingDeclaredInput(u32),
    MissingAssociatedAssignment(u32),
    UnresolvedRequirementVariable(String),
    UnboundSourceBinder,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeclaredViewAmbiguity {
    InputAssociatedNameCollision(String),
    DuplicateSubstitutionName(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ConformanceTypeView {
    Top,
    Bottom,
    Unknown,
    Binder(ConformanceBinder),
    Builtin(BuiltinType),
    Nominal {
        path: Vec<String>,
        args: Vec<ConformanceTypeView>,
    },
    Tuple(Vec<ConformanceTypeView>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ConformanceBinder {
    Universal(ImplUniversalBinderId),
    InferredAssociated(AssociatedInferenceBinderId),
    MethodQuantifier(u32),
    MethodRecursive(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum DeclaredTypeReferenceView {
    DeclaredInput(u32),
    Binder(ConformanceBinder),
}

pub(super) fn build_declared_role_impl_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
) -> DeclaredRoleImplView {
    let inputs = contract
        .inputs
        .iter()
        .map(|input| declared_type_view(contract, modules, input))
        .collect::<Vec<_>>();
    let associated = contract
        .associated
        .iter()
        .map(|assignment| match assignment {
            AssociatedAssignment::Explicit { name, ty, .. } => DeclaredAssociatedView::Explicit {
                name: name.clone(),
                value: declared_type_view(contract, modules, ty),
            },
            AssociatedAssignment::Inferred { name, binder } => DeclaredAssociatedView::Inferred {
                name: name.clone(),
                binder: ConformanceBinder::InferredAssociated(binder.id),
            },
        })
        .collect::<Vec<_>>();
    let input_substitution = contract
        .requirement_substitution
        .inputs
        .iter()
        .enumerate()
        .map(|(index, slot)| DeclaredSubstitutionSlotView {
            name: slot.name.clone(),
            value: input_substitution_value(slot, &inputs).unwrap_or_else(|| {
                DeclaredTypeView::Unavailable(DeclaredViewUnavailable::MissingDeclaredInput(
                    index as u32,
                ))
            }),
            references: normalize_references(slot),
        })
        .collect::<Vec<_>>();
    let associated_substitution = contract
        .requirement_substitution
        .associated
        .iter()
        .enumerate()
        .map(|(index, slot)| DeclaredSubstitutionSlotView {
            name: slot.name.clone(),
            value: associated
                .get(index)
                .map(associated_value)
                .unwrap_or_else(|| {
                    DeclaredTypeView::Unavailable(
                        DeclaredViewUnavailable::MissingAssociatedAssignment(index as u32),
                    )
                }),
            references: normalize_references(slot),
        })
        .collect::<Vec<_>>();
    let methods = contract
        .methods
        .iter()
        .map(|method| DeclaredMethodRequirementView {
            name: method.name.clone(),
            requirement: method
                .declared_requirement
                .as_ref()
                .map(|requirement| {
                    if let Some(name) = requirement.ambiguous_names.first() {
                        return DeclaredTypeView::Ambiguous(
                            DeclaredViewAmbiguity::InputAssociatedNameCollision(name.clone()),
                        );
                    }
                    signature_type_view(
                        contract,
                        modules,
                        &inputs,
                        &associated,
                        &requirement.signature,
                    )
                })
                .unwrap_or(DeclaredTypeView::Unavailable(
                    DeclaredViewUnavailable::UnannotatedRequirement,
                )),
        })
        .collect();

    DeclaredRoleImplView {
        inputs,
        associated,
        input_substitution,
        associated_substitution,
        methods,
    }
}

fn declared_type_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    declared: &DeclaredType,
) -> DeclaredTypeView {
    ann_type_view(contract, modules, &declared.annotation)
}

fn ann_type_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    annotation: &AnnType,
) -> DeclaredTypeView {
    match annotation {
        AnnType::Builtin(BuiltinType::Never) => available(ConformanceTypeView::Bottom),
        AnnType::Builtin(builtin) => available(ConformanceTypeView::Builtin(*builtin)),
        AnnType::Named(id) => nominal_view(modules, *id, Vec::new()),
        AnnType::Var(var) => contract
            .universal_binders
            .iter()
            .find(|binder| binder.annotation_var == var.id)
            .map(|binder| {
                available(ConformanceTypeView::Binder(ConformanceBinder::Universal(
                    binder.id,
                )))
            })
            .unwrap_or(DeclaredTypeView::Unavailable(
                DeclaredViewUnavailable::UnboundSourceBinder,
            )),
        AnnType::Wildcard(_) => available(ConformanceTypeView::Unknown),
        AnnType::Tuple(items) => sequence(
            items
                .iter()
                .map(|item| ann_type_view(contract, modules, item)),
        )
        .map(ConformanceTypeView::Tuple),
        AnnType::Apply { callee, args } => {
            let AnnType::Named(id) = callee.as_ref() else {
                return DeclaredTypeView::Unavailable(
                    DeclaredViewUnavailable::UnsupportedApplicationCallee,
                );
            };
            sequence(args.iter().map(|arg| ann_type_view(contract, modules, arg)))
                .and_then(|args| nominal_type(modules, *id, args))
        }
        AnnType::Function { .. } => {
            DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedFunction)
        }
        AnnType::Effectful { .. } => {
            DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedEffectful)
        }
        AnnType::EffectRow(_) => {
            DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedEffectRow)
        }
    }
}

fn signature_type_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    inputs: &[DeclaredTypeView],
    associated: &[DeclaredAssociatedView],
    signature: &SignatureType,
) -> DeclaredTypeView {
    match signature {
        SignatureType::Builtin(BuiltinType::Never) => available(ConformanceTypeView::Bottom),
        SignatureType::Builtin(builtin) => available(ConformanceTypeView::Builtin(*builtin)),
        SignatureType::Named(id) => nominal_view(modules, *id, Vec::new()),
        SignatureType::Var(var) => substitution_value(contract, inputs, associated, var.name()),
        SignatureType::Tuple(items) => sequence(
            items
                .iter()
                .map(|item| signature_type_view(contract, modules, inputs, associated, item)),
        )
        .map(ConformanceTypeView::Tuple),
        SignatureType::Apply { callee, args } => {
            let SignatureType::Named(id) = callee.as_ref() else {
                return DeclaredTypeView::Unavailable(
                    DeclaredViewUnavailable::UnsupportedApplicationCallee,
                );
            };
            sequence(
                args.iter()
                    .map(|arg| signature_type_view(contract, modules, inputs, associated, arg)),
            )
            .and_then(|args| nominal_type(modules, *id, args))
        }
        SignatureType::Function { .. } => {
            DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedFunction)
        }
        SignatureType::Effectful { .. } => {
            DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedEffectful)
        }
        SignatureType::EffectRow(_) => {
            DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedEffectRow)
        }
    }
}

fn substitution_value(
    contract: &RoleImplConformanceContract,
    inputs: &[DeclaredTypeView],
    associated: &[DeclaredAssociatedView],
    name: &str,
) -> DeclaredTypeView {
    if contract
        .requirement_substitution
        .ambiguous_names
        .iter()
        .any(|candidate| candidate == name)
    {
        return DeclaredTypeView::Ambiguous(DeclaredViewAmbiguity::InputAssociatedNameCollision(
            name.to_string(),
        ));
    }
    let input_matches = contract
        .requirement_substitution
        .inputs
        .iter()
        .enumerate()
        .filter(|(_, slot)| slot.name == name)
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let associated_matches = contract
        .requirement_substitution
        .associated
        .iter()
        .enumerate()
        .filter(|(_, slot)| slot.name == name)
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    if input_matches.len() + associated_matches.len() > 1 {
        return DeclaredTypeView::Ambiguous(DeclaredViewAmbiguity::DuplicateSubstitutionName(
            name.to_string(),
        ));
    }
    if let Some(index) = input_matches.first() {
        return inputs.get(*index).cloned().unwrap_or_else(|| {
            DeclaredTypeView::Unavailable(DeclaredViewUnavailable::MissingDeclaredInput(
                *index as u32,
            ))
        });
    }
    if let Some(index) = associated_matches.first() {
        return associated
            .get(*index)
            .map(associated_value)
            .unwrap_or_else(|| {
                DeclaredTypeView::Unavailable(DeclaredViewUnavailable::MissingAssociatedAssignment(
                    *index as u32,
                ))
            });
    }
    DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnresolvedRequirementVariable(
        name.to_string(),
    ))
}

fn associated_value(associated: &DeclaredAssociatedView) -> DeclaredTypeView {
    match associated {
        DeclaredAssociatedView::Explicit { value, .. } => value.clone(),
        DeclaredAssociatedView::Inferred { binder, .. } => {
            available(ConformanceTypeView::Binder(*binder))
        }
    }
}

fn input_substitution_value(
    slot: &RoleRequirementSubstitutionSlot,
    inputs: &[DeclaredTypeView],
) -> Option<DeclaredTypeView> {
    let [ContractTypeRef::DeclaredInput(index)] = slot.references.as_slice() else {
        return None;
    };
    inputs.get(*index as usize).cloned()
}

fn normalize_references(slot: &RoleRequirementSubstitutionSlot) -> Vec<DeclaredTypeReferenceView> {
    slot.references
        .iter()
        .map(|reference| match reference {
            ContractTypeRef::DeclaredInput(index) => {
                DeclaredTypeReferenceView::DeclaredInput(*index)
            }
            ContractTypeRef::Universal(id) => {
                DeclaredTypeReferenceView::Binder(ConformanceBinder::Universal(*id))
            }
            ContractTypeRef::InferredAssociated(id) => {
                DeclaredTypeReferenceView::Binder(ConformanceBinder::InferredAssociated(*id))
            }
        })
        .collect()
}

fn nominal_view(
    modules: &ModuleTable,
    id: TypeDeclId,
    args: Vec<ConformanceTypeView>,
) -> DeclaredTypeView {
    nominal_type(modules, id, args)
}

fn nominal_type(
    modules: &ModuleTable,
    id: TypeDeclId,
    args: Vec<ConformanceTypeView>,
) -> DeclaredTypeView {
    let Some(decl) = modules.type_decl_by_id(id) else {
        return DeclaredTypeView::Unavailable(DeclaredViewUnavailable::MissingCanonicalNominalPath);
    };
    available(ConformanceTypeView::Nominal {
        path: modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect(),
        args,
    })
}

fn sequence(values: impl IntoIterator<Item = DeclaredTypeView>) -> DeclaredTypeViewSequence {
    let mut available = Vec::new();
    for value in values {
        match value {
            DeclaredTypeView::Available(value) => available.push(value),
            DeclaredTypeView::Unavailable(reason) => {
                return DeclaredTypeViewSequence::Unavailable(reason);
            }
            DeclaredTypeView::Ambiguous(reason) => {
                return DeclaredTypeViewSequence::Ambiguous(reason);
            }
        }
    }
    DeclaredTypeViewSequence::Available(available)
}

enum DeclaredTypeViewSequence {
    Available(Vec<ConformanceTypeView>),
    Unavailable(DeclaredViewUnavailable),
    Ambiguous(DeclaredViewAmbiguity),
}

impl DeclaredTypeViewSequence {
    fn map(
        self,
        map: impl FnOnce(Vec<ConformanceTypeView>) -> ConformanceTypeView,
    ) -> DeclaredTypeView {
        match self {
            Self::Available(values) => available(map(values)),
            Self::Unavailable(reason) => DeclaredTypeView::Unavailable(reason),
            Self::Ambiguous(reason) => DeclaredTypeView::Ambiguous(reason),
        }
    }

    fn and_then(
        self,
        map: impl FnOnce(Vec<ConformanceTypeView>) -> DeclaredTypeView,
    ) -> DeclaredTypeView {
        match self {
            Self::Available(values) => map(values),
            Self::Unavailable(reason) => DeclaredTypeView::Unavailable(reason),
            Self::Ambiguous(reason) => DeclaredTypeView::Ambiguous(reason),
        }
    }
}

fn available(value: ConformanceTypeView) -> DeclaredTypeView {
    DeclaredTypeView::Available(value)
}
