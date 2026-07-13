//! Binder-normalized immutable views used by role-impl conformance.
//!
//! This first slice only translates the declared source contract. Actual method schemes,
//! function/effect structure, recursive bounds, and the comparison relation belong to later
//! Stage 2 slices.

use poly::types::{BuiltinType, TypeVar};

use super::{
    AssociatedAssignment, AssociatedInferenceBinderId, ContractTypeRef, DeclaredType,
    ImplUniversalBinderId, RoleImplConformanceBinderBridge,
    RoleImplConformanceBinderBridgeUnavailable, RoleImplConformanceContract,
    RoleRequirementSubstitutionSlot, SignatureType,
};
use crate::annotation::AnnType;
use crate::compact::{CompactBounds, CompactType, compact_type_var};
use crate::constraints::ConstraintMachine;
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

/// Slice 3's immutable first-order actual-side shadow. It intentionally stops before functions,
/// rows, recursive bounds, and non-exact interval arguments; those shapes remain structured
/// `Unavailable` until the later actual-view handoff slice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ActualMethodConformanceView {
    Available(ConformanceTypeView),
    Unavailable(ActualMethodConformanceViewUnavailable),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ActualMethodConformanceViewUnavailable {
    MissingBinderBridge(RoleImplConformanceBinderBridgeUnavailable),
    OrdinarySccBlocker,
    RecursiveBounds,
    NonAtomicSurface,
    WeightedVariable,
    AmbiguousBinderBridge(TypeVar),
    NonExactInvariantArgument,
    UnsupportedFunction,
    UnsupportedRecord,
    UnsupportedVariant,
    UnsupportedEffectRow,
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

pub(super) fn capture_receiverless_actual_view(
    machine: &ConstraintMachine,
    anchor: TypeVar,
    bridge: &Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
) -> ActualMethodConformanceView {
    let bridge = match bridge {
        Ok(bridge) => bridge,
        Err(reason) => {
            return ActualMethodConformanceView::Unavailable(
                ActualMethodConformanceViewUnavailable::MissingBinderBridge(reason.clone()),
            );
        }
    };
    let compact = compact_type_var(machine, anchor);
    if !compact.rec_vars.is_empty() {
        return ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::RecursiveBounds,
        );
    }
    let mut normalizer = ActualFirstOrderNormalizer::new(bridge, anchor);
    match normalizer.root_view(&compact.root) {
        Ok(view) => ActualMethodConformanceView::Available(view),
        Err(reason) => ActualMethodConformanceView::Unavailable(reason),
    }
}

struct ActualFirstOrderNormalizer<'a> {
    bridge: &'a RoleImplConformanceBinderBridge,
    root_anchor: TypeVar,
    method_quantifiers: rustc_hash::FxHashMap<TypeVar, u32>,
}

impl<'a> ActualFirstOrderNormalizer<'a> {
    fn new(bridge: &'a RoleImplConformanceBinderBridge, root_anchor: TypeVar) -> Self {
        Self {
            bridge,
            root_anchor,
            method_quantifiers: rustc_hash::FxHashMap::default(),
        }
    }

    fn root_view(
        &mut self,
        ty: &CompactType,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        let has_substantive_bound = ty.never
            || !ty.builtins.is_empty()
            || !ty.cons.is_empty()
            || !ty.funs.is_empty()
            || !ty.records.is_empty()
            || !ty.record_spreads.is_empty()
            || !ty.poly_variants.is_empty()
            || !ty.tuples.is_empty()
            || !ty.rows.is_empty()
            || ty.vars.iter().any(|var| var.var != self.root_anchor);
        self.type_view_ignoring(ty, has_substantive_bound.then_some(self.root_anchor))
    }

    fn type_view(
        &mut self,
        ty: &CompactType,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        self.type_view_ignoring(ty, None)
    }

    fn type_view_ignoring(
        &mut self,
        ty: &CompactType,
        ignored_var: Option<TypeVar>,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        if !ty.funs.is_empty() {
            return Err(ActualMethodConformanceViewUnavailable::UnsupportedFunction);
        }
        if !ty.records.is_empty() || !ty.record_spreads.is_empty() {
            return Err(ActualMethodConformanceViewUnavailable::UnsupportedRecord);
        }
        if !ty.poly_variants.is_empty() {
            return Err(ActualMethodConformanceViewUnavailable::UnsupportedVariant);
        }
        if !ty.rows.is_empty() {
            return Err(ActualMethodConformanceViewUnavailable::UnsupportedEffectRow);
        }

        let alternative_count = usize::from(ty.never)
            + ty.vars
                .iter()
                .filter(|var| Some(var.var) != ignored_var)
                .count()
            + ty.builtins.len()
            + ty.cons.len()
            + ty.tuples.len();
        if alternative_count == 0 {
            return Ok(ConformanceTypeView::Top);
        }
        if alternative_count != 1 {
            return Err(ActualMethodConformanceViewUnavailable::NonAtomicSurface);
        }
        if ty.never {
            return Ok(ConformanceTypeView::Bottom);
        }
        if let Some(var) = ty.vars.iter().find(|var| Some(var.var) != ignored_var) {
            if !var.weight.is_empty() {
                return Err(ActualMethodConformanceViewUnavailable::WeightedVariable);
            }
            return self.binder_view(var.var).map(ConformanceTypeView::Binder);
        }
        if let Some(builtin) = ty.builtins.first() {
            return Ok(ConformanceTypeView::Builtin(*builtin));
        }
        if let Some((path, args)) = ty.cons.iter().next() {
            return Ok(ConformanceTypeView::Nominal {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.bounds_view(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            });
        }
        let tuple = ty
            .tuples
            .first()
            .ok_or(ActualMethodConformanceViewUnavailable::NonAtomicSurface)?;
        Ok(ConformanceTypeView::Tuple(
            tuple
                .items
                .iter()
                .map(|item| self.type_view(item))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    fn bounds_view(
        &mut self,
        bounds: &CompactBounds,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        match bounds {
            CompactBounds::Interval { lower, upper } => {
                let lower = self.type_view(lower)?;
                let upper = self.type_view(upper)?;
                if lower == upper {
                    Ok(lower)
                } else {
                    Err(ActualMethodConformanceViewUnavailable::NonExactInvariantArgument)
                }
            }
            CompactBounds::Con { path, args } => Ok(ConformanceTypeView::Nominal {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.bounds_view(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            CompactBounds::Tuple { items } => Ok(ConformanceTypeView::Tuple(
                items
                    .iter()
                    .map(|item| self.bounds_view(item))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            CompactBounds::Fun { .. } => {
                Err(ActualMethodConformanceViewUnavailable::UnsupportedFunction)
            }
            CompactBounds::Record { .. } => {
                Err(ActualMethodConformanceViewUnavailable::UnsupportedRecord)
            }
            CompactBounds::PolyVariant { .. } => {
                Err(ActualMethodConformanceViewUnavailable::UnsupportedVariant)
            }
        }
    }

    fn binder_view(
        &mut self,
        var: TypeVar,
    ) -> Result<ConformanceBinder, ActualMethodConformanceViewUnavailable> {
        let mut mapped = self
            .bridge
            .universals
            .iter()
            .filter_map(|(binder, solver)| {
                (*solver == var).then_some(ConformanceBinder::Universal(*binder))
            })
            .chain(
                self.bridge
                    .inferred_associated
                    .iter()
                    .filter_map(|(binder, solver)| {
                        (*solver == var).then_some(ConformanceBinder::InferredAssociated(*binder))
                    }),
            );
        if let Some(first) = mapped.next() {
            if mapped.next().is_some() {
                return Err(ActualMethodConformanceViewUnavailable::AmbiguousBinderBridge(var));
            }
            return Ok(first);
        }
        let next = self.method_quantifiers.len() as u32;
        let binder = *self.method_quantifiers.entry(var).or_insert(next);
        Ok(ConformanceBinder::MethodQuantifier(binder))
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
