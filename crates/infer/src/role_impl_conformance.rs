//! Immutable source contract and normalized conformance views for source role impls.
//!
//! This module owns source binder identity, associated-assignment provenance, and deterministic
//! method correspondence. Validation belongs to a later stage.

// Stage 2 lands the immutable view before its Stage 3 validation consumer.
#[allow(dead_code)]
pub(crate) mod view;

pub(crate) use view::{
    ActualMethodConformanceView, ActualMethodConformanceViewUnavailable,
    ActualReceiverMethodConformanceView, DeclaredRoleImplView,
};

use poly::expr::{Arena as PolyArena, Def, DefId};
use poly::types::TypeVar;
use sources::SourceRange;

use crate::ModuleTable;
use crate::annotation::{AnnEffectAtom, AnnEffectRow, AnnType, AnnTypeVar, AnnTypeVarId};
use crate::constraints::ConstraintEpoch;
use crate::lowering::{SignatureEffectAtom, SignatureEffectRow, SignatureType};

pub(crate) fn capture_receiverless_actual_view(
    machine: &crate::constraints::ConstraintMachine,
    anchor: TypeVar,
    bridge: &Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
) -> ActualMethodConformanceView {
    view::capture_receiverless_actual_view(machine, anchor, bridge)
}

pub(crate) fn capture_receiver_actual_view(
    machine: &crate::constraints::ConstraintMachine,
    value: TypeVar,
    effect: TypeVar,
    bridge: &Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
) -> ActualReceiverMethodConformanceView {
    view::capture_receiver_actual_view(machine, value, effect, bridge)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplConformanceContract {
    pub(crate) impl_def: DefId,
    pub(crate) role: Vec<String>,
    pub(crate) source: SourceRange,
    pub(crate) universal_binders: Vec<ImplUniversalBinder>,
    pub(crate) inputs: Vec<DeclaredType>,
    pub(crate) associated: Vec<AssociatedAssignment>,
    pub(crate) requirement_substitution: RoleRequirementSubstitution,
    pub(crate) methods: Vec<RoleImplMethodContract>,
    pub(crate) unmatched_implementations: Vec<RoleImplMethodImplementation>,
    actual_methods: Vec<RoleImplMethodActualView>,
    #[allow(
        dead_code,
        reason = "same-session binder transport is consumed by a later conformance slice"
    )]
    pub(crate) binder_bridge:
        Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
    #[cfg(test)]
    annotation_solver_bridge: Vec<(AnnTypeVarId, TypeVar)>,
}

impl RoleImplConformanceContract {
    pub(crate) fn capture(
        impl_def: DefId,
        role: Vec<String>,
        source: SourceRange,
        role_input_names: Vec<String>,
        inputs: Vec<AnnType>,
        associated: Vec<AssociatedAssignment>,
        requirements: Vec<RoleImplMethodRequirementCapture>,
        implementations: Vec<RoleImplMethodImplementation>,
        annotation_solver_vars: &rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Self {
        let inputs = inputs
            .into_iter()
            .map(DeclaredType::new)
            .collect::<Vec<_>>();
        let mut source_binders = Vec::new();
        for input in &inputs {
            input.collect_source_binders(&mut source_binders);
        }
        for assignment in &associated {
            if let AssociatedAssignment::Explicit { ty, .. } = assignment {
                ty.collect_source_binders(&mut source_binders);
            }
        }
        source_binders.sort_by_key(|binder| binder.id.0);
        source_binders.dedup_by_key(|binder| binder.id);
        let universal_binders = source_binders
            .into_iter()
            .enumerate()
            .map(|(index, binder)| ImplUniversalBinder {
                id: ImplUniversalBinderId(index as u32),
                annotation_var: binder.id,
                source_name: binder.name,
            })
            .collect::<Vec<_>>();
        let requirement_substitution =
            RoleRequirementSubstitution::capture(role_input_names, &associated, &universal_binders);
        let (methods, unmatched_implementations) =
            capture_method_correspondence(requirements, implementations, &requirement_substitution);
        let binder_bridge = RoleImplConformanceBinderBridge::capture(
            &universal_binders,
            &associated,
            annotation_solver_vars,
        );

        Self {
            impl_def,
            role,
            source,
            universal_binders,
            inputs,
            associated,
            requirement_substitution,
            methods,
            unmatched_implementations,
            actual_methods: Vec::new(),
            binder_bridge,
            #[cfg(test)]
            annotation_solver_bridge: Vec::new(),
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn declared_view(&self, modules: &ModuleTable) -> DeclaredRoleImplView {
        view::build_declared_role_impl_view(self, modules)
    }

    /// Move one settled pending snapshot into the source contract before the SCC blocker is
    /// released. The snapshot is immutable same-unit output; it is never serialized or read by
    /// the production lowering path in Stage 2.
    pub(crate) fn handoff_actual_method_view(
        &mut self,
        implementation: DefId,
        surface: RoleImplMethodActualSurface,
    ) -> bool {
        let belongs_to_contract = self.methods.iter().any(|method| match &method.provision {
            RoleImplMethodProvision::Explicit { implementations } => implementations
                .iter()
                .any(|candidate| candidate.def == implementation),
            RoleImplMethodProvision::Default { .. } | RoleImplMethodProvision::Missing => false,
        });
        if !belongs_to_contract
            || self
                .actual_methods
                .iter()
                .any(|actual| actual.implementation == implementation)
        {
            return false;
        }
        self.actual_methods.push(RoleImplMethodActualView {
            implementation,
            surface,
        });
        true
    }

    #[cfg(test)]
    pub(crate) fn actual_method_view(
        &self,
        implementation: DefId,
    ) -> Option<&RoleImplMethodActualView> {
        self.actual_methods
            .iter()
            .find(|actual| actual.implementation == implementation)
    }

    #[cfg(test)]
    pub(crate) fn actual_method_views(&self) -> &[RoleImplMethodActualView] {
        &self.actual_methods
    }

    /// Select the explicit-complete source members whose declared requirement is already in the
    /// first-order Stage 2 view. Receiver/receiverless shape is deliberately decided by body
    /// lowering, where the source binder is available.
    pub(crate) fn first_order_shadow_targets(
        &self,
        modules: &ModuleTable,
    ) -> Vec<(
        DefId,
        Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
    )> {
        if self
            .associated
            .iter()
            .any(|assignment| matches!(assignment, AssociatedAssignment::Inferred { .. }))
        {
            return Vec::new();
        }

        let declared_view = self.declared_view(modules);
        self.methods
            .iter()
            .zip(&declared_view.methods)
            .filter(|(method, declared_method)| {
                method
                    .declared_requirement
                    .as_ref()
                    .is_some_and(|requirement| {
                        requirement.ambiguous_names.is_empty()
                            && (matches!(
                                declared_method.requirement,
                                view::DeclaredTypeView::Available(_)
                            ) || view::receiver_result_is_first_order(
                                self,
                                modules,
                                &declared_view.inputs,
                                &declared_view.associated,
                                &requirement.signature,
                            ))
                    })
            })
            .flat_map(|(method, _)| match &method.provision {
                RoleImplMethodProvision::Explicit { implementations } => implementations
                    .iter()
                    .map(|implementation| (implementation.def, self.binder_bridge.clone()))
                    .collect::<Vec<_>>(),
                RoleImplMethodProvision::Default { .. } | RoleImplMethodProvision::Missing => {
                    Vec::new()
                }
            })
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn capture_annotation_solver_bridge(
        &mut self,
        vars: &rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
    ) {
        // Characterization only: `TypeVar` is a same-session transport pointer from source
        // annotation lowering into the finalized scheme. Logical identity remains U/A and this
        // bridge must never be compared across sessions or serialized.
        let mut bridge = vars
            .iter()
            .map(|(ann, var)| (*ann, *var))
            .collect::<Vec<_>>();
        bridge.sort_by_key(|(ann, _)| ann.0);
        self.annotation_solver_bridge = bridge;
    }

    #[cfg(test)]
    pub(crate) fn solver_var_for_annotation(&self, ann: AnnTypeVarId) -> Option<TypeVar> {
        self.annotation_solver_bridge
            .iter()
            .find_map(|(source, target)| (*source == ann).then_some(*target))
    }

    #[cfg(test)]
    pub(crate) fn binder_dump(&self) -> String {
        let universals = self
            .universal_binders
            .iter()
            .map(|binder| format!("U{}", binder.id.0))
            .collect::<Vec<_>>()
            .join(",");
        let inputs = self
            .inputs
            .iter()
            .map(|input| self.declared_type_binder_dump(input))
            .collect::<Vec<_>>()
            .join(",");
        let associated = self
            .associated
            .iter()
            .map(|assignment| match assignment {
                AssociatedAssignment::Explicit { name, ty, .. } => {
                    format!("{name}=explicit{}", self.declared_type_binder_dump(ty))
                }
                AssociatedAssignment::Inferred { name, binder } => {
                    let overlap = self
                        .universal_binder_for(binder.annotation_var)
                        .map(|binder| format!(";annotation-overlap=U{}", binder.0))
                        .unwrap_or_default();
                    format!("{name}=inferred(A{}{overlap})", binder.id.0)
                }
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "role={} universals=[{universals}] inputs=[{inputs}] associated=[{associated}]",
            self.role.join("::"),
        )
    }

    #[cfg(test)]
    fn declared_type_binder_dump(&self, ty: &DeclaredType) -> String {
        let mut binders = Vec::new();
        ty.collect_source_binders(&mut binders);
        let mut binders = binders
            .into_iter()
            .filter_map(|binder| self.universal_binder_for(binder.id))
            .collect::<Vec<_>>();
        binders.sort_by_key(|binder| binder.0);
        binders.dedup();
        format!(
            "{{{}}}",
            binders
                .into_iter()
                .map(|binder| format!("U{}", binder.0))
                .collect::<Vec<_>>()
                .join(",")
        )
    }

    #[cfg(test)]
    fn universal_binder_for(&self, annotation_var: AnnTypeVarId) -> Option<ImplUniversalBinderId> {
        self.universal_binders
            .iter()
            .find_map(|binder| (binder.annotation_var == annotation_var).then_some(binder.id))
    }

    #[cfg(test)]
    pub(crate) fn method_correspondence_dump(&self) -> String {
        let slots = self.requirement_substitution.dump();
        let methods = self
            .methods
            .iter()
            .map(|method| {
                let provision = match &method.provision {
                    RoleImplMethodProvision::Explicit { implementations } => {
                        format!("explicit({})", implementations.len())
                    }
                    RoleImplMethodProvision::Default { .. } => "default".to_string(),
                    RoleImplMethodProvision::Missing => "missing".to_string(),
                };
                let references = method
                    .declared_requirement
                    .as_ref()
                    .map(|requirement| requirement.references.as_slice())
                    .unwrap_or_default()
                    .iter()
                    .map(ContractTypeRef::dump)
                    .collect::<Vec<_>>()
                    .join(",");
                let ambiguous_names = method
                    .declared_requirement
                    .as_ref()
                    .map(|requirement| requirement.ambiguous_names.as_slice())
                    .unwrap_or_default();
                let ambiguous = if ambiguous_names.is_empty() {
                    String::new()
                } else {
                    format!(";ambiguous=[{}]", ambiguous_names.join(","))
                };
                format!("{}={provision};refs=[{references}]{ambiguous}", method.name)
            })
            .collect::<Vec<_>>()
            .join(" | ");
        let unmatched = self
            .unmatched_implementations
            .iter()
            .map(|implementation| implementation.name.as_str())
            .collect::<Vec<_>>()
            .join(",");
        format!("{slots}\nmethods=[{methods}] unmatched=[{unmatched}]")
    }
}

pub(crate) fn role_method_has_default_body(
    modules: &ModuleTable,
    poly: &PolyArena,
    def: DefId,
) -> bool {
    modules.role_method_has_source_default_body(def)
        || matches!(poly.defs.get(def), Some(Def::Let { body: Some(_), .. }))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ImplUniversalBinder {
    pub(crate) id: ImplUniversalBinderId,
    pub(crate) annotation_var: AnnTypeVarId,
    pub(crate) source_name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ImplUniversalBinderId(pub(crate) u32);

/// Same-session transport from logical conformance binders to annotation-lowering solver vars.
///
/// The logical U/A ids remain the identity of each entry. `TypeVar` is only the solver pointer
/// attached to that identity for this inference session; this value must not be serialized.
#[allow(
    dead_code,
    reason = "same-session binder transport is consumed by a later conformance slice"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplConformanceBinderBridge {
    pub(crate) universals: Vec<(ImplUniversalBinderId, TypeVar)>,
    pub(crate) inferred_associated: Vec<(AssociatedInferenceBinderId, TypeVar)>,
}

impl RoleImplConformanceBinderBridge {
    fn capture(
        universal_binders: &[ImplUniversalBinder],
        associated: &[AssociatedAssignment],
        annotation_solver_vars: &rustc_hash::FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<Self, RoleImplConformanceBinderBridgeUnavailable> {
        let mut universals = Vec::with_capacity(universal_binders.len());
        let mut inferred_associated = Vec::new();
        let mut missing = Vec::new();

        for binder in universal_binders {
            if let Some(var) = annotation_solver_vars.get(&binder.annotation_var) {
                universals.push((binder.id, *var));
            } else {
                missing.push(RoleImplConformanceBinderBridgeMissing::Universal {
                    binder: binder.id,
                    annotation_var: binder.annotation_var,
                });
            }
        }
        for assignment in associated {
            let AssociatedAssignment::Inferred { binder, .. } = assignment else {
                continue;
            };
            if let Some(var) = annotation_solver_vars.get(&binder.annotation_var) {
                // Deliberately retain this logical A entry even when its annotation identity and
                // solver var overlap a U entry.
                inferred_associated.push((binder.id, *var));
            } else {
                missing.push(RoleImplConformanceBinderBridgeMissing::InferredAssociated {
                    binder: binder.id,
                    annotation_var: binder.annotation_var,
                });
            }
        }

        if missing.is_empty() {
            Ok(Self {
                universals,
                inferred_associated,
            })
        } else {
            Err(RoleImplConformanceBinderBridgeUnavailable { missing })
        }
    }
}

#[allow(
    dead_code,
    reason = "same-session binder transport is consumed by a later conformance slice"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplConformanceBinderBridgeUnavailable {
    pub(crate) missing: Vec<RoleImplConformanceBinderBridgeMissing>,
}

#[allow(
    dead_code,
    reason = "same-session binder transport is consumed by a later conformance slice"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RoleImplConformanceBinderBridgeMissing {
    Universal {
        binder: ImplUniversalBinderId,
        annotation_var: AnnTypeVarId,
    },
    InferredAssociated {
        binder: AssociatedInferenceBinderId,
        annotation_var: AnnTypeVarId,
    },
}

#[allow(
    dead_code,
    reason = "inactive Slice 1 descriptor metadata is consumed by a later lifecycle slice"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RequirementParameterContextStatus {
    Clean(NonMutatingRequirementClass),
    MutatedBridge(BridgeMutationAudit),
    Unsupported(RequirementParameterContextUnavailable),
}

#[allow(
    dead_code,
    reason = "inactive Slice 1 descriptor metadata is consumed by a later lifecycle slice"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NonMutatingRequirementClass {
    PlainValueParameters { count: usize },
}

#[allow(
    dead_code,
    reason = "inactive Slice 1 descriptor metadata is consumed by a later lifecycle slice"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BridgeMutationAudit {
    pub(crate) epoch_before: ConstraintEpoch,
    pub(crate) epoch_after: ConstraintEpoch,
    pub(crate) affected: Vec<ConformanceBinderMutation>,
    pub(crate) unexplained_epoch_advance: bool,
}

#[allow(
    dead_code,
    reason = "inactive Slice 1 descriptor metadata is consumed by a later lifecycle slice"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ConformanceBinderMutation {
    pub(crate) annotation_var: AnnTypeVarId,
    pub(crate) solver_var: TypeVar,
    pub(crate) bounds_changed: bool,
    pub(crate) subtract_facts_changed: bool,
}

#[allow(
    dead_code,
    reason = "inactive Slice 1 descriptor metadata is consumed by a later lifecycle slice"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RequirementParameterContextUnavailable {
    pub(crate) parameter_index: usize,
    pub(crate) reason: RequirementParameterUnsupportedReason,
}

#[allow(
    dead_code,
    reason = "inactive Slice 1 descriptor metadata is consumed by a later lifecycle slice"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RequirementParameterUnsupportedReason {
    MissingFunctionLayer,
    EffectRow,
    EffectfulLayer,
    EffectFamily { declaration: crate::TypeDeclId },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredType {
    pub(crate) annotation: AnnType,
}

impl DeclaredType {
    pub(crate) fn new(annotation: AnnType) -> Self {
        Self { annotation }
    }

    fn collect_source_binders(&self, out: &mut Vec<AnnTypeVar>) {
        collect_ann_type_vars(&self.annotation, out);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AssociatedAssignment {
    Explicit {
        name: String,
        ty: DeclaredType,
        source: SourceRange,
    },
    Inferred {
        name: String,
        binder: AssociatedInferenceBinder,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AssociatedInferenceBinder {
    pub(crate) id: AssociatedInferenceBinderId,
    pub(crate) annotation_var: AnnTypeVarId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct AssociatedInferenceBinderId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplMethodContract {
    pub(crate) requirement: DefId,
    pub(crate) name: String,
    pub(crate) provision: RoleImplMethodProvision,
    pub(crate) declared_requirement: Option<DeclaredRoleMethodRequirement>,
    pub(crate) source: Option<SourceRange>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredRoleMethodRequirement {
    pub(crate) signature: SignatureType,
    pub(crate) references: Vec<ContractTypeRef>,
    pub(crate) ambiguous_names: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RoleImplMethodProvision {
    Explicit {
        implementations: Vec<RoleImplMethodImplementation>,
    },
    Default {
        implementation: DefId,
        source: Option<SourceRange>,
    },
    Missing,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplMethodImplementation {
    pub(crate) def: DefId,
    pub(crate) name: String,
    pub(crate) source: SourceRange,
    pub(crate) order: u32,
}

/// Immutable actual-side handoff for one explicit source method.
///
/// The implementation id only associates the snapshot with the already-captured method
/// correspondence. An available normalized surface contains no solver identity; an unavailable
/// result may retain same-session failure evidence but is never canonicalized or serialized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplMethodActualView {
    pub(crate) implementation: DefId,
    pub(crate) surface: RoleImplMethodActualSurface,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RoleImplMethodActualSurface {
    Receiverless(ActualMethodConformanceView),
    Receiver(ActualReceiverMethodConformanceView),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplMethodRequirementCapture {
    pub(crate) requirement: DefId,
    pub(crate) name: String,
    pub(crate) signature: Option<SignatureType>,
    pub(crate) has_default_body: bool,
    pub(crate) source: Option<SourceRange>,
    pub(crate) order: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleRequirementSubstitution {
    pub(crate) inputs: Vec<RoleRequirementSubstitutionSlot>,
    pub(crate) associated: Vec<RoleRequirementSubstitutionSlot>,
    pub(crate) ambiguous_names: Vec<String>,
}

impl RoleRequirementSubstitution {
    fn capture(
        role_input_names: Vec<String>,
        associated: &[AssociatedAssignment],
        universal_binders: &[ImplUniversalBinder],
    ) -> Self {
        let inputs = role_input_names
            .into_iter()
            .enumerate()
            .map(|(index, name)| RoleRequirementSubstitutionSlot {
                name,
                references: vec![ContractTypeRef::DeclaredInput(index as u32)],
            })
            .collect::<Vec<_>>();
        let associated = associated
            .iter()
            .map(|assignment| match assignment {
                AssociatedAssignment::Explicit { name, ty, .. } => {
                    let mut source_binders = Vec::new();
                    ty.collect_source_binders(&mut source_binders);
                    let mut references = source_binders
                        .into_iter()
                        .filter_map(|binder| {
                            universal_binders.iter().find_map(|universal| {
                                (universal.annotation_var == binder.id)
                                    .then_some(ContractTypeRef::Universal(universal.id))
                            })
                        })
                        .collect::<Vec<_>>();
                    references.sort();
                    references.dedup();
                    RoleRequirementSubstitutionSlot {
                        name: name.clone(),
                        references,
                    }
                }
                AssociatedAssignment::Inferred { name, binder } => {
                    RoleRequirementSubstitutionSlot {
                        name: name.clone(),
                        references: vec![ContractTypeRef::InferredAssociated(binder.id)],
                    }
                }
            })
            .collect::<Vec<_>>();
        let mut ambiguous_names = inputs
            .iter()
            .filter(|input| {
                associated
                    .iter()
                    .any(|associated| associated.name == input.name)
            })
            .map(|input| input.name.clone())
            .collect::<Vec<_>>();
        ambiguous_names.sort();
        ambiguous_names.dedup();
        Self {
            inputs,
            associated,
            ambiguous_names,
        }
    }

    fn references_for_name(&self, name: &str) -> Result<&[ContractTypeRef], ()> {
        if self
            .ambiguous_names
            .iter()
            .any(|candidate| candidate == name)
        {
            return Err(());
        }
        self.inputs
            .iter()
            .chain(self.associated.iter())
            .find(|slot| slot.name == name)
            .map(|slot| slot.references.as_slice())
            .ok_or(())
    }

    #[cfg(test)]
    fn dump(&self) -> String {
        let dump_slots = |slots: &[RoleRequirementSubstitutionSlot]| {
            slots
                .iter()
                .map(|slot| {
                    format!(
                        "{}->{}",
                        slot.name,
                        slot.references
                            .iter()
                            .map(ContractTypeRef::dump)
                            .collect::<Vec<_>>()
                            .join("+")
                    )
                })
                .collect::<Vec<_>>()
                .join(",")
        };
        format!(
            "substitution=inputs=[{}] associated=[{}] ambiguous=[{}]",
            dump_slots(&self.inputs),
            dump_slots(&self.associated),
            self.ambiguous_names.join(",")
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleRequirementSubstitutionSlot {
    pub(crate) name: String,
    pub(crate) references: Vec<ContractTypeRef>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ContractTypeRef {
    DeclaredInput(u32),
    Universal(ImplUniversalBinderId),
    InferredAssociated(AssociatedInferenceBinderId),
}

impl ContractTypeRef {
    #[cfg(test)]
    fn dump(&self) -> String {
        match self {
            Self::DeclaredInput(index) => format!("input{index}"),
            Self::Universal(id) => format!("U{}", id.0),
            Self::InferredAssociated(id) => format!("A{}", id.0),
        }
    }
}

fn capture_method_correspondence(
    mut requirements: Vec<RoleImplMethodRequirementCapture>,
    mut implementations: Vec<RoleImplMethodImplementation>,
    substitution: &RoleRequirementSubstitution,
) -> (
    Vec<RoleImplMethodContract>,
    Vec<RoleImplMethodImplementation>,
) {
    requirements.sort_by_key(|requirement| (requirement.order, requirement.requirement.0));
    implementations.sort_by_key(|implementation| (implementation.order, implementation.def.0));
    let methods = requirements
        .iter()
        .map(|requirement| {
            let matching = implementations
                .iter()
                .filter(|implementation| implementation.name == requirement.name)
                .cloned()
                .collect::<Vec<_>>();
            let provision = if !matching.is_empty() {
                RoleImplMethodProvision::Explicit {
                    implementations: matching,
                }
            } else if requirement.has_default_body {
                RoleImplMethodProvision::Default {
                    implementation: requirement.requirement,
                    source: requirement.source.clone(),
                }
            } else {
                RoleImplMethodProvision::Missing
            };
            let declared_requirement = requirement.signature.clone().map(|signature| {
                let (references, ambiguous_names) = contract_references(&signature, substitution);
                DeclaredRoleMethodRequirement {
                    signature,
                    references,
                    ambiguous_names,
                }
            });
            RoleImplMethodContract {
                requirement: requirement.requirement,
                name: requirement.name.clone(),
                provision,
                declared_requirement,
                source: requirement.source.clone(),
            }
        })
        .collect();
    let unmatched = implementations
        .into_iter()
        .filter(|implementation| {
            !requirements
                .iter()
                .any(|requirement| requirement.name == implementation.name)
        })
        .collect();
    (methods, unmatched)
}

fn contract_references(
    signature: &SignatureType,
    substitution: &RoleRequirementSubstitution,
) -> (Vec<ContractTypeRef>, Vec<String>) {
    let mut names = Vec::new();
    collect_signature_var_names(signature, &mut names);
    let mut references = Vec::new();
    let mut ambiguous_names = Vec::new();
    for name in names {
        match substitution.references_for_name(&name) {
            Ok(slot) => references.extend_from_slice(slot),
            Err(())
                if substitution
                    .ambiguous_names
                    .iter()
                    .any(|item| item == &name) =>
            {
                ambiguous_names.push(name);
            }
            Err(()) => {}
        }
    }
    ambiguous_names.sort();
    ambiguous_names.dedup();
    (references, ambiguous_names)
}

fn collect_signature_var_names(signature: &SignatureType, out: &mut Vec<String>) {
    match signature {
        SignatureType::Builtin(_) | SignatureType::Named(_) => {}
        SignatureType::Var(var) => out.push(var.name().to_string()),
        SignatureType::EffectRow(row) => collect_signature_effect_row_names(row, out),
        SignatureType::Effectful { eff, ret } => {
            collect_signature_effect_row_names(eff, out);
            collect_signature_var_names(ret, out);
        }
        SignatureType::Tuple(items) => {
            for item in items {
                collect_signature_var_names(item, out);
            }
        }
        SignatureType::Apply { callee, args } => {
            collect_signature_var_names(callee, out);
            for arg in args {
                collect_signature_var_names(arg, out);
            }
        }
        SignatureType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_signature_var_names(param, out);
            if let Some(row) = arg_eff {
                collect_signature_effect_row_names(row, out);
            }
            if let Some(row) = ret_eff {
                collect_signature_effect_row_names(row, out);
            }
            collect_signature_var_names(ret, out);
        }
    }
}

fn collect_signature_effect_row_names(row: &SignatureEffectRow, out: &mut Vec<String>) {
    for item in row.items() {
        if let SignatureEffectAtom::Type(ty) = item {
            collect_signature_var_names(ty, out);
        }
    }
    if let Some(tail) = row.tail() {
        out.push(tail.name().to_string());
    }
}

fn collect_ann_type_vars(ty: &AnnType, out: &mut Vec<AnnTypeVar>) {
    match ty {
        AnnType::Builtin(_) | AnnType::Named(_) => {}
        AnnType::Var(var) => out.push(var.clone()),
        AnnType::Wildcard(_) => {}
        AnnType::EffectRow(row) => collect_effect_row_vars(row, out),
        AnnType::Effectful { eff, ret } => {
            collect_effect_row_vars(eff, out);
            collect_ann_type_vars(ret, out);
        }
        AnnType::Tuple(items) => {
            for item in items {
                collect_ann_type_vars(item, out);
            }
        }
        AnnType::Apply { callee, args } => {
            collect_ann_type_vars(callee, out);
            for arg in args {
                collect_ann_type_vars(arg, out);
            }
        }
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_ann_type_vars(param, out);
            if let Some(arg_eff) = arg_eff {
                collect_effect_row_vars(arg_eff, out);
            }
            if let Some(ret_eff) = ret_eff {
                collect_effect_row_vars(ret_eff, out);
            }
            collect_ann_type_vars(ret, out);
        }
    }
}

fn collect_effect_row_vars(row: &AnnEffectRow, out: &mut Vec<AnnTypeVar>) {
    for item in &row.items {
        if let AnnEffectAtom::Type(ty) = item {
            collect_ann_type_vars(ty, out);
        }
    }
    if let Some(tail) = &row.tail {
        out.push(tail.clone());
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;

    use super::*;

    #[test]
    fn binder_bridge_retains_overlapping_universal_and_associated_identities() {
        let annotation_var = AnnTypeVarId(7);
        let solver_var = TypeVar(42);
        let universal_binders = vec![ImplUniversalBinder {
            id: ImplUniversalBinderId(0),
            annotation_var,
            source_name: "T".to_string(),
        }];
        let associated = vec![AssociatedAssignment::Inferred {
            name: "Item".to_string(),
            binder: AssociatedInferenceBinder {
                id: AssociatedInferenceBinderId(0),
                annotation_var,
            },
        }];
        let annotation_solver_vars = FxHashMap::from_iter([(annotation_var, solver_var)]);

        let bridge = RoleImplConformanceBinderBridge::capture(
            &universal_binders,
            &associated,
            &annotation_solver_vars,
        )
        .expect("overlapping logical identities have a shared solver mapping");

        assert_eq!(
            bridge.universals,
            vec![(ImplUniversalBinderId(0), solver_var)]
        );
        assert_eq!(
            bridge.inferred_associated,
            vec![(AssociatedInferenceBinderId(0), solver_var)]
        );
    }

    #[test]
    fn binder_bridge_reports_every_missing_logical_mapping_as_unavailable() {
        let universal_binders = vec![ImplUniversalBinder {
            id: ImplUniversalBinderId(1),
            annotation_var: AnnTypeVarId(11),
            source_name: "T".to_string(),
        }];
        let associated = vec![AssociatedAssignment::Inferred {
            name: "Item".to_string(),
            binder: AssociatedInferenceBinder {
                id: AssociatedInferenceBinderId(2),
                annotation_var: AnnTypeVarId(12),
            },
        }];

        let unavailable = RoleImplConformanceBinderBridge::capture(
            &universal_binders,
            &associated,
            &FxHashMap::default(),
        )
        .expect_err("missing mappings make the bridge unavailable");

        assert_eq!(
            unavailable.missing,
            vec![
                RoleImplConformanceBinderBridgeMissing::Universal {
                    binder: ImplUniversalBinderId(1),
                    annotation_var: AnnTypeVarId(11),
                },
                RoleImplConformanceBinderBridgeMissing::InferredAssociated {
                    binder: AssociatedInferenceBinderId(2),
                    annotation_var: AnnTypeVarId(12),
                },
            ]
        );
    }
}
