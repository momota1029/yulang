//! Binder-normalized immutable views used by role-impl conformance.
//!
//! Declared contracts and settled actual surfaces meet here as finite first-order shapes. Method
//! recursive bounds are unfolded once and retain Rm back-references; unsupported higher-order
//! structure stays explicit rather than re-entering the solver.

use poly::expr::DefId;
use poly::types::{BuiltinType, TypeVar};
#[cfg(test)]
use poly::types::{Neg, Pos};

use super::{
    AssociatedAssignment, AssociatedInferenceBinderId, ContractTypeRef, DeclaredType,
    ImplUniversalBinderId, RoleImplConformanceBinderBridge,
    RoleImplConformanceBinderBridgeUnavailable, RoleImplConformanceContract,
    RoleRequirementSubstitutionSlot, SignatureType,
};
#[cfg(test)]
use super::{SignatureEffectAtom, SignatureEffectRow};
use crate::annotation::AnnType;
#[cfg(test)]
use crate::casts::CastTable;
use crate::compact::{
    CompactBounds, CompactRecursiveVar, CompactRoleArg, CompactRoleArgPolarity, CompactRoot,
    CompactType, CompactVar, compact_type_var,
};
use crate::constraints::ConstraintMachine;
use crate::{ModuleTable, TypeDeclId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredRoleImplView {
    pub(crate) inputs: Vec<DeclaredTypeView>,
    pub(crate) associated: Vec<DeclaredAssociatedView>,
    pub(crate) advertised_prerequisites: Vec<DeclaredRolePredicateView>,
    pub(crate) input_substitution: Vec<DeclaredSubstitutionSlotView>,
    pub(crate) associated_substitution: Vec<DeclaredSubstitutionSlotView>,
    pub(crate) methods: Vec<DeclaredMethodRequirementView>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct DeclaredRolePredicateView {
    pub(crate) role: Vec<String>,
    pub(crate) inputs: Vec<DeclaredTypeView>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplMethodResidualPrerequisitesView {
    pub(crate) method_name: String,
    pub(crate) implementation: DefId,
    pub(crate) prerequisites: Vec<RoleImplMethodResidualPredicateView>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplMethodResidualPredicateView {
    pub(crate) role: Vec<String>,
    pub(crate) inputs: Vec<ActualMethodConformanceView>,
}

/// Exact normalized comparison of one residual predicate against one advertised predicate.
/// `Unavailable` means their role/arity and every comparable input agree, but at least one input
/// is unavailable or ambiguous in its wrapper.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExactRolePredicateMatch {
    Matches,
    DoesNotMatch,
    Unavailable,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum DeclaredTypeView {
    Available(ConformanceTypeView),
    Unavailable(DeclaredViewUnavailable),
    Ambiguous(DeclaredViewAmbiguity),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum DeclaredViewAmbiguity {
    InputAssociatedNameCollision(String),
    DuplicateSubstitutionName(String),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
    #[cfg(test)]
    EffectSet(Vec<ConformanceTypeView>),
}

/// Pure first-order implementation-to-requirement relation for the Stage 3 shadow kernel.
/// Binder ids are interpreted inside the pair's owning contract; no solver identity participates.
#[cfg(test)]
pub(crate) fn first_order_conforms(
    implementation: &ConformanceTypeView,
    requirement: &ConformanceTypeView,
) -> bool {
    match (implementation, requirement) {
        (ConformanceTypeView::Bottom, _) | (_, ConformanceTypeView::Top) => true,
        (ConformanceTypeView::Binder(left), ConformanceTypeView::Binder(right)) => left == right,
        (ConformanceTypeView::Builtin(left), ConformanceTypeView::Builtin(right)) => left == right,
        (
            ConformanceTypeView::Nominal {
                path: left_path,
                args: left_args,
            },
            ConformanceTypeView::Nominal {
                path: right_path,
                args: right_args,
            },
        ) => {
            left_path == right_path
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| first_order_invariantly_equal(left, right))
        }
        (ConformanceTypeView::Tuple(left), ConformanceTypeView::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| first_order_conforms(left, right))
        }
        (ConformanceTypeView::EffectSet(left), ConformanceTypeView::EffectSet(right)) => {
            first_order_effect_sets_equal(left, right)
        }
        _ => false,
    }
}

#[cfg(test)]
fn first_order_invariantly_equal(left: &ConformanceTypeView, right: &ConformanceTypeView) -> bool {
    match (left, right) {
        (ConformanceTypeView::Top, ConformanceTypeView::Top)
        | (ConformanceTypeView::Bottom, ConformanceTypeView::Bottom) => true,
        (ConformanceTypeView::Binder(left), ConformanceTypeView::Binder(right)) => left == right,
        (ConformanceTypeView::Builtin(left), ConformanceTypeView::Builtin(right)) => left == right,
        (
            ConformanceTypeView::Nominal {
                path: left_path,
                args: left_args,
            },
            ConformanceTypeView::Nominal {
                path: right_path,
                args: right_args,
            },
        ) => {
            left_path == right_path
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| first_order_invariantly_equal(left, right))
        }
        (ConformanceTypeView::Tuple(left), ConformanceTypeView::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| first_order_invariantly_equal(left, right))
        }
        (ConformanceTypeView::EffectSet(left), ConformanceTypeView::EffectSet(right)) => {
            first_order_effect_sets_equal(left, right)
        }
        _ => false,
    }
}

/// Compare one residual predicate with one advertised predicate under exact normalized
/// membership. This deliberately does not use the subtype-flavored `first_order_conforms`.
#[cfg(test)]
pub(crate) fn exact_role_predicate_match(
    residual: &RoleImplMethodResidualPredicateView,
    advertised: &DeclaredRolePredicateView,
) -> ExactRolePredicateMatch {
    if residual.role != advertised.role || residual.inputs.len() != advertised.inputs.len() {
        return ExactRolePredicateMatch::DoesNotMatch;
    }

    let mut unavailable = false;
    for (actual, declared) in residual.inputs.iter().zip(&advertised.inputs) {
        match (actual, declared) {
            (
                ActualMethodConformanceView::Available(actual),
                DeclaredTypeView::Available(declared),
            ) if !first_order_invariantly_equal(actual, declared) => {
                return ExactRolePredicateMatch::DoesNotMatch;
            }
            (ActualMethodConformanceView::Available(_), DeclaredTypeView::Available(_)) => {}
            _ => unavailable = true,
        }
    }

    if unavailable {
        ExactRolePredicateMatch::Unavailable
    } else {
        ExactRolePredicateMatch::Matches
    }
}

#[cfg(test)]
fn first_order_effect_sets_equal(
    left: &[ConformanceTypeView],
    right: &[ConformanceTypeView],
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut matched = vec![false; right.len()];
    left.iter().all(|left_atom| {
        let Some((index, _)) = right.iter().enumerate().find(|(index, right_atom)| {
            !matched[*index] && first_order_invariantly_equal(left_atom, right_atom)
        }) else {
            return false;
        };
        matched[index] = true;
        true
    })
}

/// Slice 3's immutable first-order actual-side shadow. It intentionally stops before functions,
/// rows, and non-exact invariant arguments; unsupported shapes remain structured `Unavailable`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ActualMethodConformanceView {
    Available(ConformanceTypeView),
    Unavailable(ActualMethodConformanceViewUnavailable),
}

/// Receiverless parameterized methods expose their fully inferred inner body separately from the
/// complete curried method value. The effect is retained with the value for a future effect-policy
/// consumer; this slice keeps receiverless comparison behavior value-only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ActualReceiverlessMethodConformanceView {
    pub(crate) value: ActualMethodConformanceView,
    pub(crate) effect: ActualMethodConformanceView,
    #[cfg(test)]
    pub(crate) parameter_count: Option<usize>,
}

/// Receiver methods expose the raw body result and effect anchors separately. Both views are
/// captured in the component-wide read-only batch before either deferred body edge is applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ActualReceiverMethodConformanceView {
    pub(crate) value: ActualMethodConformanceView,
    pub(crate) effect: ActualMethodConformanceView,
    #[cfg(test)]
    pub(crate) tail_parameter_count: Option<usize>,
}

/// The one non-atomic actual shape whose constructor identities are useful to Stage 4's later
/// cast-policy comparison. This remains capture metadata; it is not itself a conformance verdict.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ActualBuiltinNominalPair {
    builtin: BuiltinType,
    nominal_path: Vec<String>,
    nominal_args: Vec<CompactBounds>,
}

#[cfg(test)]
impl ActualBuiltinNominalPair {
    pub(crate) fn builtin(&self) -> BuiltinType {
        self.builtin
    }

    pub(crate) fn nominal_path(&self) -> &[String] {
        &self.nominal_path
    }

    pub(crate) fn nominal_args(&self) -> &[CompactBounds] {
        &self.nominal_args
    }
}

/// Test-only snapshot of one concrete nominal constructor visible from an exact variable class.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ConcreteAnchorNominalWitness {
    pub(crate) path: Vec<String>,
    pub(crate) type_argument_count: usize,
}

/// Test-only evidence retained for one raw compact alternative before its method requirement runs.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConcreteAnchorRawVariableWitness {
    pub(crate) var: TypeVar,
    pub(crate) weight_is_empty: bool,
    pub(crate) exact_class: Vec<TypeVar>,
    pub(crate) empty_weight_lower_nominals: Vec<ConcreteAnchorNominalWitness>,
    pub(crate) empty_weight_upper_nominals: Vec<ConcreteAnchorNominalWitness>,
}

/// Opt-in test capture of the settled actual-value surface at the pre-requirement boundary.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConcreteAnchorActualWitness {
    pub(crate) anchor: TypeVar,
    pub(crate) raw_variables: Vec<ConcreteAnchorRawVariableWitness>,
    pub(crate) nominal_alternatives: Vec<ConcreteAnchorNominalWitness>,
    pub(crate) outward: ActualMethodConformanceView,
    pub(crate) c1a_capture_present: bool,
}

#[cfg(test)]
thread_local! {
    static CONCRETE_ANCHOR_ACTUAL_WITNESSES:
        std::cell::RefCell<Option<Vec<ConcreteAnchorActualWitness>>> = const {
            std::cell::RefCell::new(None)
        };
}

/// Begin one thread-local characterization batch. Ordinary tests pay no capture or traversal cost.
#[cfg(test)]
pub(crate) fn begin_concrete_anchor_actual_witness_capture() {
    CONCRETE_ANCHOR_ACTUAL_WITNESSES.with(|witnesses| {
        *witnesses.borrow_mut() = Some(Vec::new());
    });
}

/// End the current characterization batch and return only snapshots taken before requirement edges.
#[cfg(test)]
pub(crate) fn finish_concrete_anchor_actual_witness_capture() -> Vec<ConcreteAnchorActualWitness> {
    CONCRETE_ANCHOR_ACTUAL_WITNESSES
        .with(|witnesses| witnesses.borrow_mut().take().unwrap_or_default())
}

/// Result of consulting the visible value-cast registry for one constructor pair.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VisibleCastLookup {
    Missing,
    Unique,
    Ambiguous,
}

/// Classify a clean first-order mismatch through the visible cast table. The registry is keyed by
/// constructor paths; argument structure remains part of the captured endpoints but is not
/// re-inferred by this bounded shadow comparison.
#[cfg(test)]
pub(crate) fn visible_cast_lookup(
    casts: &CastTable,
    source: &ConformanceTypeView,
    target: &ConformanceTypeView,
) -> VisibleCastLookup {
    let Some((source_path, _source_arg_count)) = cast_constructor(source) else {
        return VisibleCastLookup::Missing;
    };
    let Some((target_path, _target_arg_count)) = cast_constructor(target) else {
        return VisibleCastLookup::Missing;
    };
    visible_cast_lookup_by_path(casts, &source_path, &target_path)
}

/// Consume C1-a's narrow pre/post-cast surface. The nominal half must identify the declared target
/// before the builtin half may be treated as the actual source of a visible cast.
#[cfg(test)]
pub(crate) fn captured_builtin_nominal_cast_lookup(
    casts: &CastTable,
    captured: &ActualBuiltinNominalPair,
    target: &ConformanceTypeView,
) -> VisibleCastLookup {
    let Some((target_path, target_arg_count)) = cast_constructor(target) else {
        return VisibleCastLookup::Missing;
    };
    if captured.nominal_path() != target_path || captured.nominal_args().len() != target_arg_count {
        return VisibleCastLookup::Missing;
    }
    let source_path = [captured.builtin().surface_name().to_string()];
    visible_cast_lookup_by_path(casts, &source_path, &target_path)
}

#[cfg(test)]
fn cast_constructor(view: &ConformanceTypeView) -> Option<(Vec<String>, usize)> {
    match view {
        ConformanceTypeView::Builtin(builtin) => {
            Some((vec![builtin.surface_name().to_string()], 0))
        }
        ConformanceTypeView::Nominal { path, args } => Some((path.clone(), args.len())),
        _ => None,
    }
}

#[cfg(test)]
fn visible_cast_lookup_by_path(
    casts: &CastTable,
    source_path: &[String],
    target_path: &[String],
) -> VisibleCastLookup {
    match casts.candidates(source_path, target_path).len() {
        0 => VisibleCastLookup::Missing,
        1 => VisibleCastLookup::Unique,
        _ => VisibleCastLookup::Ambiguous,
    }
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredReceiverMethodConformanceView {
    pub(crate) value: DeclaredTypeView,
    pub(crate) effect: DeclaredTypeView,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ActualMethodConformanceViewUnavailable {
    MissingBinderBridge(RoleImplConformanceBinderBridgeUnavailable),
    OrdinarySccBlocker,
    NonAtomicSurface,
    WeightedVariable,
    AmbiguousBinderBridge(TypeVar),
    #[cfg(test)]
    AmbiguousExactClassIdentity(Vec<TypeVar>),
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
    let mut advertised_prerequisites = contract
        .advertised_prerequisites
        .iter()
        .map(|prerequisite| DeclaredRolePredicateView {
            role: prerequisite.role.clone(),
            inputs: prerequisite
                .inputs
                .iter()
                .map(|input| declared_type_view(contract, modules, input))
                .collect(),
        })
        .collect::<Vec<_>>();
    advertised_prerequisites.sort();
    advertised_prerequisites.dedup();
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
        advertised_prerequisites,
        input_substitution,
        associated_substitution,
        methods,
    }
}

pub(super) fn build_role_impl_method_residual_prerequisites_view(
    contract: &RoleImplConformanceContract,
    machine: &ConstraintMachine,
) -> Vec<RoleImplMethodResidualPrerequisitesView> {
    let mut implementations = contract
        .methods
        .iter()
        .flat_map(|method| match &method.provision {
            super::RoleImplMethodProvision::Explicit { implementations } => implementations
                .iter()
                .map(|implementation| (method.name.as_str(), implementation))
                .collect::<Vec<_>>(),
            super::RoleImplMethodProvision::Default { .. }
            | super::RoleImplMethodProvision::Missing => Vec::new(),
        })
        .chain(
            contract
                .unmatched_implementations
                .iter()
                .map(|implementation| (implementation.name.as_str(), implementation)),
        )
        .collect::<Vec<_>>();
    implementations.sort_by_key(|(_, implementation)| (implementation.order, implementation.def.0));
    implementations.dedup_by_key(|(_, implementation)| implementation.def);

    implementations
        .into_iter()
        .filter_map(|(method_name, implementation)| {
            let residual = implementation.residual_prerequisites.as_ref()?;
            Some(RoleImplMethodResidualPrerequisitesView {
                method_name: method_name.to_string(),
                implementation: implementation.def,
                prerequisites: residual_role_predicate_views(contract, machine, residual),
            })
        })
        .collect()
}

fn residual_role_predicate_views(
    contract: &RoleImplConformanceContract,
    machine: &ConstraintMachine,
    residual: &super::RoleImplMethodResidualPrerequisites,
) -> Vec<RoleImplMethodResidualPredicateView> {
    let prerequisites = match &contract.binder_bridge {
        Ok(bridge) => {
            let mut binder_identities = ActualBinderIdentityResolver::new(bridge);
            let mut normalizer =
                ActualFirstOrderNormalizer::new_for_bounds(&mut binder_identities, machine);
            residual
                .compact_prerequisites()
                .iter()
                .map(|prerequisite| RoleImplMethodResidualPredicateView {
                    role: prerequisite.role.clone(),
                    inputs: prerequisite
                        .inputs
                        .iter()
                        .map(|input| match normalizer.role_arg_view(input) {
                            Ok(view) => ActualMethodConformanceView::Available(view),
                            Err(reason) => ActualMethodConformanceView::Unavailable(reason),
                        })
                        .collect(),
                })
                .collect::<Vec<_>>()
        }
        Err(reason) => residual
            .compact_prerequisites()
            .iter()
            .map(|prerequisite| RoleImplMethodResidualPredicateView {
                role: prerequisite.role.clone(),
                inputs: prerequisite
                    .inputs
                    .iter()
                    .map(|_| {
                        ActualMethodConformanceView::Unavailable(
                            ActualMethodConformanceViewUnavailable::MissingBinderBridge(
                                reason.clone(),
                            ),
                        )
                    })
                    .collect(),
            })
            .collect::<Vec<_>>(),
    };
    let mut normalized = Vec::with_capacity(prerequisites.len());
    for prerequisite in prerequisites {
        if !normalized.contains(&prerequisite) {
            normalized.push(prerequisite);
        }
    }
    normalized.sort_by(|left, right| left.role.cmp(&right.role));
    normalized
}

pub(super) fn receiver_result_is_first_order(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    inputs: &[DeclaredTypeView],
    associated: &[DeclaredAssociatedView],
    signature: &SignatureType,
) -> bool {
    let mut result = signature;
    let mut consumed_receiver = false;
    while let SignatureType::Function {
        arg_eff: None, ret, ..
    } = result
    {
        consumed_receiver = true;
        result = ret;
    }
    if !consumed_receiver {
        return false;
    }
    matches!(
        signature_type_view(contract, modules, inputs, associated, result),
        DeclaredTypeView::Available(_)
    )
}

/// Align a receiverless inner-body snapshot with exactly the measured number of declared curried
/// parameter layers. Unlike receiver alignment, there is no leading receiver layer to consume.
#[cfg(test)]
pub(crate) fn declared_receiverless_method_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    inputs: &[DeclaredTypeView],
    associated: &[DeclaredAssociatedView],
    signature: &SignatureType,
    actual_parameter_count: usize,
) -> Option<DeclaredReceiverMethodConformanceView> {
    let mut result = signature;
    let mut result_effect = None;
    for _ in 0..actual_parameter_count {
        let SignatureType::Function {
            arg_eff: None,
            ret_eff,
            ret,
            ..
        } = result
        else {
            return None;
        };
        result_effect = ret_eff.as_ref();
        result = ret;
    }
    if matches!(result, SignatureType::Function { .. }) {
        return None;
    }
    let (result_effect, result) = match (result_effect, result) {
        (None, SignatureType::Effectful { eff, ret }) => (Some(eff), ret.as_ref()),
        _ => (result_effect, result),
    };
    Some(DeclaredReceiverMethodConformanceView {
        value: signature_type_view(contract, modules, inputs, associated, result),
        effect: signature_effect_view(contract, modules, inputs, associated, result_effect),
    })
}

/// Align a receiver requirement with its captured body-value surface. The actual descriptor owns
/// the measured tail arity; the declared signature is accepted only when its complete clean
/// function prefix contains exactly one receiver layer plus that many tail-parameter layers.
#[cfg(test)]
pub(crate) fn declared_receiver_result_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    inputs: &[DeclaredTypeView],
    associated: &[DeclaredAssociatedView],
    signature: &SignatureType,
    actual_tail_parameter_count: usize,
) -> Option<DeclaredTypeView> {
    declared_receiver_method_view(
        contract,
        modules,
        inputs,
        associated,
        signature,
        actual_tail_parameter_count,
    )
    .map(|surface| surface.value)
}

/// Return the receiver body's value/effect requirement after validating the measured tail arity.
/// Effect rows stay deliberately first-order: closed rows are representable, while row tails and
/// wildcards remain structured `Unavailable` values.
#[cfg(test)]
pub(crate) fn declared_receiver_method_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    inputs: &[DeclaredTypeView],
    associated: &[DeclaredAssociatedView],
    signature: &SignatureType,
    actual_tail_parameter_count: usize,
) -> Option<DeclaredReceiverMethodConformanceView> {
    let mut result = signature;
    let mut function_layer_count = 0usize;
    let mut result_effect = None;
    while let SignatureType::Function {
        arg_eff: None,
        ret_eff,
        ret,
        ..
    } = result
    {
        function_layer_count += 1;
        result_effect = ret_eff.as_ref();
        result = ret;
    }

    let declared_tail_parameter_count = function_layer_count.checked_sub(1)?;
    if declared_tail_parameter_count != actual_tail_parameter_count {
        return None;
    }
    let (result_effect, result) = match (result_effect, result) {
        (None, SignatureType::Effectful { eff, ret }) => (Some(eff), ret.as_ref()),
        _ => (result_effect, result),
    };
    Some(DeclaredReceiverMethodConformanceView {
        value: signature_type_view(contract, modules, inputs, associated, result),
        effect: signature_effect_view(contract, modules, inputs, associated, result_effect),
    })
}

#[cfg(test)]
fn signature_effect_view(
    contract: &RoleImplConformanceContract,
    modules: &ModuleTable,
    inputs: &[DeclaredTypeView],
    associated: &[DeclaredAssociatedView],
    row: Option<&SignatureEffectRow>,
) -> DeclaredTypeView {
    let Some(row) = row else {
        return available(ConformanceTypeView::Bottom);
    };
    if row.tail().is_some()
        || row
            .items()
            .iter()
            .any(|atom| matches!(atom, SignatureEffectAtom::Wildcard))
    {
        return DeclaredTypeView::Unavailable(DeclaredViewUnavailable::UnsupportedEffectRow);
    }
    match row.items() {
        [] => available(ConformanceTypeView::Bottom),
        [SignatureEffectAtom::Type(effect)] => {
            signature_type_view(contract, modules, inputs, associated, effect)
        }
        effects => sequence(effects.iter().map(|effect| {
            let SignatureEffectAtom::Type(effect) = effect else {
                unreachable!("wildcard effects return before closed-row projection")
            };
            signature_type_view(contract, modules, inputs, associated, effect)
        }))
        .map(ConformanceTypeView::EffectSet),
    }
}

#[cfg(test)]
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
    let mut binder_identities = ActualBinderIdentityResolver::new(bridge);
    let compact = compact_type_var(machine, anchor);
    binder_identities.register_method_recursive_vars(compact.rec_vars.iter().map(|rec| rec.var));
    capture_receiverless_actual_view_from_compact(machine, anchor, &compact, &mut binder_identities)
}

pub(super) fn capture_receiverless_method_actual_view(
    machine: &ConstraintMachine,
    value: TypeVar,
    effect: TypeVar,
    parameter_count: usize,
    bridge: &Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
) -> ActualReceiverlessMethodConformanceView {
    let bridge = match bridge {
        Ok(bridge) => bridge,
        Err(reason) => {
            return ActualReceiverlessMethodConformanceView {
                value: ActualMethodConformanceView::Unavailable(
                    ActualMethodConformanceViewUnavailable::MissingBinderBridge(reason.clone()),
                ),
                effect: ActualMethodConformanceView::Unavailable(
                    ActualMethodConformanceViewUnavailable::MissingBinderBridge(reason.clone()),
                ),
                #[cfg(test)]
                parameter_count: Some(parameter_count),
            };
        }
    };
    #[cfg(not(test))]
    let _ = parameter_count;
    let mut binder_identities = ActualBinderIdentityResolver::new(bridge);
    let value_compact = compact_type_var(machine, value);
    let effect_compact = compact_type_var(machine, effect);
    binder_identities.register_method_recursive_vars(
        value_compact
            .rec_vars
            .iter()
            .chain(&effect_compact.rec_vars)
            .map(|rec| rec.var),
    );
    let value = capture_receiverless_actual_view_from_compact(
        machine,
        value,
        &value_compact,
        &mut binder_identities,
    );
    #[cfg(not(test))]
    let effect = capture_receiverless_actual_view_from_compact(
        machine,
        effect,
        &effect_compact,
        &mut binder_identities,
    );
    #[cfg(test)]
    let effect = capture_receiver_effect_actual_view(
        machine,
        effect,
        &effect_compact,
        &mut binder_identities,
    );
    ActualReceiverlessMethodConformanceView {
        value,
        effect,
        #[cfg(test)]
        parameter_count: Some(parameter_count),
    }
}

fn capture_receiverless_actual_view_from_compact(
    _machine: &ConstraintMachine,
    anchor: TypeVar,
    compact: &CompactRoot,
    binder_identities: &mut ActualBinderIdentityResolver<'_>,
) -> ActualMethodConformanceView {
    #[cfg(not(test))]
    let mut normalizer =
        ActualFirstOrderNormalizer::new(binder_identities, anchor, &compact.rec_vars);
    #[cfg(test)]
    let mut normalizer =
        ActualFirstOrderNormalizer::new(binder_identities, anchor, _machine, &compact.rec_vars);
    match normalizer.root_view(&compact.root) {
        Ok(view) => ActualMethodConformanceView::Available(view),
        Err(reason) => ActualMethodConformanceView::Unavailable(reason),
    }
}

pub(super) fn capture_receiver_actual_view(
    machine: &ConstraintMachine,
    value: TypeVar,
    effect: TypeVar,
    bridge: &Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
) -> ActualReceiverMethodConformanceView {
    #[cfg(test)]
    let bridge_result = bridge;
    let bridge = match bridge {
        Ok(bridge) => bridge,
        Err(reason) => {
            return ActualReceiverMethodConformanceView {
                value: ActualMethodConformanceView::Unavailable(
                    ActualMethodConformanceViewUnavailable::MissingBinderBridge(reason.clone()),
                ),
                effect: ActualMethodConformanceView::Unavailable(
                    ActualMethodConformanceViewUnavailable::MissingBinderBridge(reason.clone()),
                ),
                #[cfg(test)]
                tail_parameter_count: None,
            };
        }
    };
    let mut binder_identities = ActualBinderIdentityResolver::new(bridge);
    let value_compact = compact_type_var(machine, value);
    let effect_compact = compact_type_var(machine, effect);
    binder_identities.register_method_recursive_vars(
        value_compact
            .rec_vars
            .iter()
            .chain(&effect_compact.rec_vars)
            .map(|rec| rec.var),
    );
    #[cfg(test)]
    let value_anchor = value;
    let value = capture_receiverless_actual_view_from_compact(
        machine,
        value,
        &value_compact,
        &mut binder_identities,
    );
    #[cfg(test)]
    record_concrete_anchor_actual_witness(
        machine,
        value_anchor,
        &value_compact,
        bridge_result,
        value.clone(),
    );
    #[cfg(not(test))]
    let effect = capture_receiverless_actual_view_from_compact(
        machine,
        effect,
        &effect_compact,
        &mut binder_identities,
    );
    #[cfg(test)]
    let effect = capture_receiver_effect_actual_view(
        machine,
        effect,
        &effect_compact,
        &mut binder_identities,
    );
    ActualReceiverMethodConformanceView {
        value,
        effect,
        #[cfg(test)]
        tail_parameter_count: None,
    }
}

/// Read the Stage 4 builtin/nominal capture metadata without consulting cast policy or mutating
/// the settled constraint machine. The ordinary capture result deliberately remains
/// `Unavailable(NonAtomicSurface)` until the comparison-level C1-b slice consumes this shape.
#[cfg(test)]
pub(crate) fn capture_actual_builtin_nominal_pair(
    machine: &ConstraintMachine,
    anchor: TypeVar,
    bridge: &Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
) -> Option<ActualBuiltinNominalPair> {
    let bridge = bridge.as_ref().ok()?;
    let mut binder_identities = ActualBinderIdentityResolver::new(bridge);
    let compact = compact_type_var(machine, anchor);
    binder_identities.register_method_recursive_vars(compact.rec_vars.iter().map(|rec| rec.var));
    let mut normalizer =
        ActualFirstOrderNormalizer::new(&mut binder_identities, anchor, machine, &compact.rec_vars);
    let _ = normalizer.root_view(&compact.root);
    normalizer.builtin_nominal_pair
}

/// Project a settled body-effect lower surface into the first-order relation. Bare unweighted
/// positive aliases carry no effect atom of their own; concrete row items do. This is one finite
/// structural pass over the captured compact tree and never mutates the solver.
#[cfg(test)]
fn capture_receiver_effect_actual_view(
    machine: &ConstraintMachine,
    anchor: TypeVar,
    compact: &CompactRoot,
    binder_identities: &mut ActualBinderIdentityResolver<'_>,
) -> ActualMethodConformanceView {
    if compact.root.vars.iter().any(|var| !var.weight.is_empty()) {
        return ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::WeightedVariable,
        );
    }
    let mut normalizer =
        ActualFirstOrderNormalizer::new(binder_identities, anchor, machine, &compact.rec_vars);
    if !compact.rec_vars.is_empty() {
        return match normalizer.root_view(&compact.root) {
            Ok(view) => ActualMethodConformanceView::Available(view),
            Err(reason) => ActualMethodConformanceView::Unavailable(reason),
        };
    }
    if !compact.root.builtins.is_empty()
        || !compact.root.cons.is_empty()
        || !compact.root.funs.is_empty()
        || !compact.root.records.is_empty()
        || !compact.root.record_spreads.is_empty()
        || !compact.root.poly_variants.is_empty()
        || !compact.root.tuples.is_empty()
    {
        return ActualMethodConformanceView::Unavailable(
            ActualMethodConformanceViewUnavailable::NonAtomicSurface,
        );
    }
    let effect = match compact.root.rows.as_slice() {
        [] => Ok(ConformanceTypeView::Bottom),
        [row] if row.tail.is_empty() => match row.items.len() {
            0 => Ok(ConformanceTypeView::Bottom),
            1 => {
                let (path, args) = row.items.iter().next().expect("one closed effect atom");
                args.iter()
                    .map(|arg| normalizer.bounds_view(arg))
                    .collect::<Result<Vec<_>, _>>()
                    .map(|args| ConformanceTypeView::Nominal {
                        path: path.clone(),
                        args,
                    })
            }
            _ => row
                .items
                .iter()
                .map(|(path, args)| {
                    args.iter()
                        .map(|arg| normalizer.bounds_view(arg))
                        .collect::<Result<Vec<_>, _>>()
                        .map(|args| ConformanceTypeView::Nominal {
                            path: path.clone(),
                            args,
                        })
                })
                .collect::<Result<Vec<_>, _>>()
                .map(ConformanceTypeView::EffectSet),
        },
        _ => Err(ActualMethodConformanceViewUnavailable::UnsupportedEffectRow),
    };
    match effect {
        Ok(effect) => ActualMethodConformanceView::Available(effect),
        Err(reason) => ActualMethodConformanceView::Unavailable(reason),
    }
}

/// Read-only SCC index for the empty-weight variable projection of a constraint machine.
///
/// In test builds this supplies the Stage 3 exact-equivalence collapse. Each reachable variable is
/// visited once by Tarjan's algorithm, and completed classes are memoized for subsequent queries
/// against the same settled machine.
#[cfg(test)]
pub(crate) struct ExactEquivalenceClasses<'a> {
    machine: &'a ConstraintMachine,
    next_index: usize,
    nodes: rustc_hash::FxHashMap<TypeVar, ExactEquivalenceNode>,
    stack: Vec<TypeVar>,
    classes: rustc_hash::FxHashMap<TypeVar, Vec<TypeVar>>,
}

#[cfg(test)]
impl<'a> ExactEquivalenceClasses<'a> {
    pub(crate) fn new(machine: &'a ConstraintMachine) -> Self {
        Self {
            machine,
            next_index: 0,
            nodes: rustc_hash::FxHashMap::default(),
            stack: Vec::new(),
            classes: rustc_hash::FxHashMap::default(),
        }
    }

    pub(crate) fn class(&mut self, start: TypeVar) -> Vec<TypeVar> {
        if !self.classes.contains_key(&start) {
            self.connect(start);
        }
        self.classes
            .get(&start)
            .cloned()
            .unwrap_or_else(|| vec![start])
    }

    fn connect(&mut self, var: TypeVar) {
        let index = self.next_index;
        self.next_index += 1;
        self.nodes.insert(
            var,
            ExactEquivalenceNode {
                index,
                lowlink: index,
                on_stack: true,
            },
        );
        self.stack.push(var);

        for successor in self.exact_successors(var) {
            if self.classes.contains_key(&successor) {
                continue;
            }
            if !self.nodes.contains_key(&successor) {
                self.connect(successor);
                if self.nodes[&successor].on_stack {
                    let successor_lowlink = self.nodes[&successor].lowlink;
                    self.nodes.get_mut(&var).expect("visited node").lowlink =
                        self.nodes[&var].lowlink.min(successor_lowlink);
                }
            } else if self.nodes[&successor].on_stack {
                let successor_index = self.nodes[&successor].index;
                self.nodes.get_mut(&var).expect("visited node").lowlink =
                    self.nodes[&var].lowlink.min(successor_index);
            }
        }

        let node = self.nodes[&var];
        if node.lowlink != node.index {
            return;
        }

        let mut class = Vec::new();
        loop {
            let member = self.stack.pop().expect("SCC root remains on Tarjan stack");
            self.nodes.get_mut(&member).expect("visited node").on_stack = false;
            class.push(member);
            if member == var {
                break;
            }
        }
        class.sort_unstable_by_key(|var| var.0);
        for member in &class {
            self.classes.insert(*member, class.clone());
        }
    }

    fn exact_successors(&self, var: TypeVar) -> Vec<TypeVar> {
        let mut successors = self
            .machine
            .bounds()
            .of(var)
            .into_iter()
            .flat_map(|bounds| bounds.projection_uppers())
            .filter(|upper| upper.weights.is_empty())
            .filter_map(|upper| match self.machine.types().neg(upper.neg) {
                Neg::Var(target) => Some(*target),
                _ => None,
            })
            .collect::<Vec<_>>();
        successors.sort_unstable_by_key(|var| var.0);
        successors.dedup();
        successors
    }
}

#[cfg(test)]
fn record_concrete_anchor_actual_witness(
    machine: &ConstraintMachine,
    anchor: TypeVar,
    compact: &CompactRoot,
    bridge: &Result<RoleImplConformanceBinderBridge, RoleImplConformanceBinderBridgeUnavailable>,
    outward: ActualMethodConformanceView,
) {
    let capture_enabled =
        CONCRETE_ANCHOR_ACTUAL_WITNESSES.with(|witnesses| witnesses.borrow().is_some());
    if !capture_enabled {
        return;
    }

    let raw_candidates = compact
        .root
        .vars
        .iter()
        .filter(|candidate| candidate.var != anchor)
        .collect::<Vec<_>>();
    let nominal_alternatives = compact
        .root
        .cons
        .iter()
        .map(|(path, args)| ConcreteAnchorNominalWitness {
            path: path.clone(),
            type_argument_count: args.len(),
        })
        .collect::<Vec<_>>();
    let mut exact_classes = ExactEquivalenceClasses::new(machine);
    let raw_variables = raw_candidates
        .into_iter()
        .map(|candidate| {
            let exact_class = exact_classes.class(candidate.var);
            ConcreteAnchorRawVariableWitness {
                var: candidate.var,
                weight_is_empty: candidate.weight.is_empty(),
                empty_weight_lower_nominals: empty_weight_class_lower_nominals(
                    machine,
                    &exact_class,
                ),
                empty_weight_upper_nominals: empty_weight_class_upper_nominals(
                    machine,
                    &exact_class,
                ),
                exact_class,
            }
        })
        .collect();
    let c1a_capture_present =
        capture_actual_builtin_nominal_pair(machine, anchor, bridge).is_some();
    let mut witness = ConcreteAnchorActualWitness {
        anchor,
        raw_variables,
        nominal_alternatives,
        outward,
        c1a_capture_present,
    };
    witness.nominal_alternatives.sort();
    CONCRETE_ANCHOR_ACTUAL_WITNESSES.with(|witnesses| {
        if let Some(witnesses) = witnesses.borrow_mut().as_mut() {
            witnesses.push(witness);
        }
    });
}

#[cfg(test)]
fn empty_weight_class_lower_nominals(
    machine: &ConstraintMachine,
    class: &[TypeVar],
) -> Vec<ConcreteAnchorNominalWitness> {
    let mut nominals = class
        .iter()
        .filter_map(|member| machine.bounds().of(*member))
        .flat_map(|bounds| bounds.projection_lowers())
        .filter(|lower| lower.weights.is_empty())
        .filter_map(|lower| match machine.types().pos(lower.pos) {
            Pos::Con(path, args) => Some(ConcreteAnchorNominalWitness {
                path: path.clone(),
                type_argument_count: args.len(),
            }),
            _ => None,
        })
        .collect::<Vec<_>>();
    nominals.sort();
    nominals.dedup();
    nominals
}

#[cfg(test)]
fn empty_weight_class_upper_nominals(
    machine: &ConstraintMachine,
    class: &[TypeVar],
) -> Vec<ConcreteAnchorNominalWitness> {
    let mut nominals = class
        .iter()
        .filter_map(|member| machine.bounds().of(*member))
        .flat_map(|bounds| bounds.projection_uppers())
        .filter(|upper| upper.weights.is_empty())
        .filter_map(|upper| match machine.types().neg(upper.neg) {
            Neg::Con(path, args) => Some(ConcreteAnchorNominalWitness {
                path: path.clone(),
                type_argument_count: args.len(),
            }),
            _ => None,
        })
        .collect::<Vec<_>>();
    nominals.sort();
    nominals.dedup();
    nominals
}

#[cfg(test)]
#[derive(Debug, Clone, Copy)]
struct ExactEquivalenceNode {
    index: usize,
    lowlink: usize,
    on_stack: bool,
}

struct ActualFirstOrderNormalizer<'resolver, 'bridge, 'compact> {
    root_anchor: Option<TypeVar>,
    binder_identities: &'resolver mut ActualBinderIdentityResolver<'bridge>,
    recursive_order: Vec<TypeVar>,
    recursive_bounds: rustc_hash::FxHashMap<TypeVar, &'compact CompactBounds>,
    recursive_views: rustc_hash::FxHashMap<TypeVar, ConformanceTypeView>,
    projecting_recursive_bounds: bool,
    #[cfg(test)]
    exact_equivalence_classes: ExactEquivalenceClasses<'resolver>,
    #[cfg(test)]
    builtin_nominal_pair: Option<ActualBuiltinNominalPair>,
}

enum ActualFirstOrderTypeShape<'a> {
    Top,
    Bottom,
    RawVariableCandidates {
        vars: &'a [CompactVar],
        ignored_var: Option<TypeVar>,
        candidate_count: usize,
    },
    #[cfg(test)]
    BuiltinNominalPair {
        builtin: BuiltinType,
        nominal_path: &'a [String],
        nominal_args: &'a [CompactBounds],
    },
    Builtin(BuiltinType),
    Nominal {
        path: &'a [String],
        args: &'a [CompactBounds],
    },
    Tuple(&'a [CompactType]),
}

enum ActualFirstOrderBoundsShape<'a> {
    Interval {
        lower: &'a CompactType,
        upper: &'a CompactType,
    },
    Nominal {
        path: &'a [String],
        args: &'a [CompactBounds],
    },
    Tuple(&'a [CompactBounds]),
}

struct ActualBinderIdentityResolver<'a> {
    bridge: &'a RoleImplConformanceBinderBridge,
    method_quantifiers: rustc_hash::FxHashMap<TypeVar, u32>,
    method_recursive_vars: rustc_hash::FxHashSet<TypeVar>,
    method_recursive: rustc_hash::FxHashMap<TypeVar, u32>,
    #[cfg(test)]
    exact_class_identities: rustc_hash::FxHashMap<TypeVar, ConformanceBinder>,
}

impl<'resolver, 'bridge, 'compact> ActualFirstOrderNormalizer<'resolver, 'bridge, 'compact> {
    #[cfg(not(test))]
    fn new(
        binder_identities: &'resolver mut ActualBinderIdentityResolver<'bridge>,
        root_anchor: TypeVar,
        recursive_vars: &'compact [CompactRecursiveVar],
    ) -> Self {
        Self {
            root_anchor: Some(root_anchor),
            binder_identities,
            recursive_order: recursive_vars.iter().map(|rec| rec.var).collect(),
            recursive_bounds: recursive_vars
                .iter()
                .map(|rec| (rec.var, &rec.bounds))
                .collect(),
            recursive_views: rustc_hash::FxHashMap::default(),
            projecting_recursive_bounds: false,
        }
    }

    #[cfg(test)]
    fn new(
        binder_identities: &'resolver mut ActualBinderIdentityResolver<'bridge>,
        root_anchor: TypeVar,
        machine: &'resolver ConstraintMachine,
        recursive_vars: &'compact [CompactRecursiveVar],
    ) -> Self {
        Self {
            root_anchor: Some(root_anchor),
            binder_identities,
            recursive_order: recursive_vars.iter().map(|rec| rec.var).collect(),
            recursive_bounds: recursive_vars
                .iter()
                .map(|rec| (rec.var, &rec.bounds))
                .collect(),
            recursive_views: rustc_hash::FxHashMap::default(),
            projecting_recursive_bounds: false,
            exact_equivalence_classes: ExactEquivalenceClasses::new(machine),
            builtin_nominal_pair: None,
        }
    }

    #[cfg(not(test))]
    fn new_for_bounds(
        binder_identities: &'resolver mut ActualBinderIdentityResolver<'bridge>,
        _machine: &'resolver ConstraintMachine,
    ) -> Self {
        Self {
            root_anchor: None,
            binder_identities,
            recursive_order: Vec::new(),
            recursive_bounds: rustc_hash::FxHashMap::default(),
            recursive_views: rustc_hash::FxHashMap::default(),
            projecting_recursive_bounds: false,
        }
    }

    #[cfg(test)]
    fn new_for_bounds(
        binder_identities: &'resolver mut ActualBinderIdentityResolver<'bridge>,
        machine: &'resolver ConstraintMachine,
    ) -> Self {
        Self {
            root_anchor: None,
            binder_identities,
            recursive_order: Vec::new(),
            recursive_bounds: rustc_hash::FxHashMap::default(),
            recursive_views: rustc_hash::FxHashMap::default(),
            projecting_recursive_bounds: false,
            exact_equivalence_classes: ExactEquivalenceClasses::new(machine),
            builtin_nominal_pair: None,
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
            || ty.vars.iter().any(|var| Some(var.var) != self.root_anchor);
        let view = self.type_view_ignoring(
            ty,
            has_substantive_bound.then_some(self.root_anchor).flatten(),
        )?;
        self.project_recursive_bounds_once()?;
        Ok(view)
    }

    /// Compact collection stores a recursive positive surface as a raw root variable plus one
    /// unfolded lower side in `rec_vars`. Project every entry once while recursive references are
    /// represented by their root-walk-assigned Rm identity; this keeps capture finite without
    /// losing the shape immediately below the root or depending on raw `TypeVar` order.
    fn project_recursive_bounds_once(
        &mut self,
    ) -> Result<(), ActualMethodConformanceViewUnavailable> {
        for var in self.recursive_order.clone() {
            if self.recursive_views.contains_key(&var) {
                continue;
            }
            self.project_recursive_bound(var)?;
        }
        Ok(())
    }

    fn project_recursive_bound(
        &mut self,
        var: TypeVar,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        if let Some(view) = self.recursive_views.get(&var) {
            return Ok(view.clone());
        }
        self.binder_identities
            .resolve_method_recursive_binder(var)
            .expect("compact recursive bounds are registered before normalization");
        let bounds = self.recursive_bounds[&var];
        let was_projecting = self.projecting_recursive_bounds;
        self.projecting_recursive_bounds = true;
        let view = match bounds {
            CompactBounds::Interval { lower, .. } => self.type_view_ignoring(lower, Some(var)),
            bounds => self.bounds_view(bounds),
        };
        self.projecting_recursive_bounds = was_projecting;
        let view = view?;
        self.recursive_views.insert(var, view.clone());
        Ok(view)
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
        let shape = project_actual_first_order_type_shape(ty, ignored_var)?;
        self.resolve_type_shape(shape)
    }

    fn resolve_type_shape(
        &mut self,
        shape: ActualFirstOrderTypeShape<'_>,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        match shape {
            ActualFirstOrderTypeShape::Top => Ok(ConformanceTypeView::Top),
            ActualFirstOrderTypeShape::Bottom => Ok(ConformanceTypeView::Bottom),
            ActualFirstOrderTypeShape::RawVariableCandidates {
                vars,
                ignored_var,
                candidate_count,
            } => self.resolve_raw_variable_candidates(vars, ignored_var, candidate_count),
            #[cfg(test)]
            ActualFirstOrderTypeShape::BuiltinNominalPair {
                builtin,
                nominal_path,
                nominal_args,
            } => {
                self.builtin_nominal_pair = Some(ActualBuiltinNominalPair {
                    builtin,
                    nominal_path: nominal_path.to_vec(),
                    nominal_args: nominal_args.to_vec(),
                });
                Err(ActualMethodConformanceViewUnavailable::NonAtomicSurface)
            }
            ActualFirstOrderTypeShape::Builtin(builtin) => {
                Ok(ConformanceTypeView::Builtin(builtin))
            }
            ActualFirstOrderTypeShape::Nominal { path, args } => Ok(ConformanceTypeView::Nominal {
                path: path.to_vec(),
                args: args
                    .iter()
                    .map(|arg| self.bounds_view(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            ActualFirstOrderTypeShape::Tuple(items) => Ok(ConformanceTypeView::Tuple(
                items
                    .iter()
                    .map(|item| self.type_view(item))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
        }
    }

    fn resolve_raw_variable_candidates(
        &mut self,
        vars: &[CompactVar],
        ignored_var: Option<TypeVar>,
        candidate_count: usize,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        if candidate_count != 1 {
            #[cfg(not(test))]
            return Err(ActualMethodConformanceViewUnavailable::NonAtomicSurface);
            #[cfg(test)]
            return self.resolve_exact_variable_class(vars, ignored_var);
        }
        let var = vars
            .iter()
            .find(|var| Some(var.var) != ignored_var)
            .expect("one projected raw variable candidate");
        if !var.weight.is_empty() {
            return Err(ActualMethodConformanceViewUnavailable::WeightedVariable);
        }
        if let Some(binder) = self
            .binder_identities
            .resolve_method_recursive_binder(var.var)
        {
            if self.projecting_recursive_bounds {
                return Ok(ConformanceTypeView::Binder(binder));
            }
            return if self.recursive_bounds.contains_key(&var.var) {
                self.project_recursive_bound(var.var)
            } else {
                Ok(ConformanceTypeView::Binder(binder))
            };
        }
        self.binder_identities
            .resolve(var.var)
            .map(ConformanceTypeView::Binder)
    }

    #[cfg(test)]
    fn resolve_exact_variable_class(
        &mut self,
        vars: &[CompactVar],
        ignored_var: Option<TypeVar>,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        let candidates = vars
            .iter()
            .filter(|candidate| Some(candidate.var) != ignored_var)
            .collect::<Vec<_>>();
        if candidates
            .iter()
            .any(|candidate| !candidate.weight.is_empty())
        {
            return Err(ActualMethodConformanceViewUnavailable::WeightedVariable);
        }
        let first = candidates
            .first()
            .expect("multiple projected raw variable candidates");
        let class = self.exact_equivalence_classes.class(first.var);
        if !candidates
            .iter()
            .all(|candidate| class.contains(&candidate.var))
        {
            return Err(ActualMethodConformanceViewUnavailable::NonAtomicSurface);
        }
        self.binder_identities
            .resolve_class(&class)
            .map(ConformanceTypeView::Binder)
    }

    fn bounds_view(
        &mut self,
        bounds: &CompactBounds,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        let shape = project_actual_first_order_bounds_shape(bounds)?;
        self.resolve_bounds_shape(shape)
    }

    fn role_arg_view(
        &mut self,
        arg: &CompactRoleArg,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        match (&arg.polarity, &arg.bounds) {
            (CompactRoleArgPolarity::Covariant, CompactBounds::Interval { lower, upper: _ }) => {
                self.type_view(lower)
            }
            (
                CompactRoleArgPolarity::Contravariant,
                CompactBounds::Interval { lower: _, upper },
            ) => self.type_view(upper),
            (CompactRoleArgPolarity::Invariant, bounds)
            | (CompactRoleArgPolarity::Covariant | CompactRoleArgPolarity::Contravariant, bounds) => {
                self.bounds_view(bounds)
            }
        }
    }

    fn resolve_bounds_shape(
        &mut self,
        shape: ActualFirstOrderBoundsShape<'_>,
    ) -> Result<ConformanceTypeView, ActualMethodConformanceViewUnavailable> {
        match shape {
            ActualFirstOrderBoundsShape::Interval { lower, upper } => {
                let lower = self.type_view(lower)?;
                let upper = self.type_view(upper)?;
                if lower == upper {
                    Ok(lower)
                } else {
                    Err(ActualMethodConformanceViewUnavailable::NonExactInvariantArgument)
                }
            }
            ActualFirstOrderBoundsShape::Nominal { path, args } => {
                Ok(ConformanceTypeView::Nominal {
                    path: path.to_vec(),
                    args: args
                        .iter()
                        .map(|arg| self.bounds_view(arg))
                        .collect::<Result<Vec<_>, _>>()?,
                })
            }
            ActualFirstOrderBoundsShape::Tuple(items) => Ok(ConformanceTypeView::Tuple(
                items
                    .iter()
                    .map(|item| self.bounds_view(item))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
        }
    }
}

fn project_actual_first_order_type_shape<'a>(
    ty: &'a CompactType,
    ignored_var: Option<TypeVar>,
) -> Result<ActualFirstOrderTypeShape<'a>, ActualMethodConformanceViewUnavailable> {
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

    let raw_variable_count = ty
        .vars
        .iter()
        .filter(|var| Some(var.var) != ignored_var)
        .count();
    let alternative_count = usize::from(ty.never)
        + raw_variable_count
        + ty.builtins.len()
        + ty.cons.len()
        + ty.tuples.len();
    if alternative_count == 0 {
        return Ok(ActualFirstOrderTypeShape::Top);
    }
    if raw_variable_count == alternative_count {
        return Ok(ActualFirstOrderTypeShape::RawVariableCandidates {
            vars: &ty.vars,
            ignored_var,
            candidate_count: raw_variable_count,
        });
    }
    #[cfg(test)]
    if alternative_count == 2
        && raw_variable_count == 0
        && !ty.never
        && ty.builtins.len() == 1
        && ty.cons.len() == 1
        && ty.tuples.is_empty()
    {
        let (nominal_path, nominal_args) = ty.cons.iter().next().expect("one nominal alternative");
        return Ok(ActualFirstOrderTypeShape::BuiltinNominalPair {
            builtin: ty.builtins[0],
            nominal_path,
            nominal_args,
        });
    }
    if alternative_count != 1 {
        return Err(ActualMethodConformanceViewUnavailable::NonAtomicSurface);
    }
    if ty.never {
        return Ok(ActualFirstOrderTypeShape::Bottom);
    }
    if let Some(builtin) = ty.builtins.first() {
        return Ok(ActualFirstOrderTypeShape::Builtin(*builtin));
    }
    if let Some((path, args)) = ty.cons.iter().next() {
        return Ok(ActualFirstOrderTypeShape::Nominal { path, args });
    }
    let tuple = ty
        .tuples
        .first()
        .ok_or(ActualMethodConformanceViewUnavailable::NonAtomicSurface)?;
    Ok(ActualFirstOrderTypeShape::Tuple(&tuple.items))
}

fn project_actual_first_order_bounds_shape(
    bounds: &CompactBounds,
) -> Result<ActualFirstOrderBoundsShape<'_>, ActualMethodConformanceViewUnavailable> {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            Ok(ActualFirstOrderBoundsShape::Interval { lower, upper })
        }
        CompactBounds::Con { path, args } => {
            Ok(ActualFirstOrderBoundsShape::Nominal { path, args })
        }
        CompactBounds::Tuple { items } => Ok(ActualFirstOrderBoundsShape::Tuple(items)),
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

impl<'a> ActualBinderIdentityResolver<'a> {
    fn new(bridge: &'a RoleImplConformanceBinderBridge) -> Self {
        Self {
            bridge,
            method_quantifiers: rustc_hash::FxHashMap::default(),
            method_recursive_vars: rustc_hash::FxHashSet::default(),
            method_recursive: rustc_hash::FxHashMap::default(),
            #[cfg(test)]
            exact_class_identities: rustc_hash::FxHashMap::default(),
        }
    }

    fn register_method_recursive_vars(&mut self, vars: impl IntoIterator<Item = TypeVar>) {
        for var in vars {
            self.method_recursive_vars.insert(var);
        }
    }

    fn resolve_method_recursive_binder(&mut self, var: TypeVar) -> Option<ConformanceBinder> {
        if !self.method_recursive_vars.contains(&var) {
            return None;
        }
        let next = self.method_recursive.len() as u32;
        let binder = *self.method_recursive.entry(var).or_insert(next);
        Some(ConformanceBinder::MethodRecursive(binder))
    }

    fn resolve(
        &mut self,
        var: TypeVar,
    ) -> Result<ConformanceBinder, ActualMethodConformanceViewUnavailable> {
        if let Some(binder) = self.resolve_method_recursive_binder(var) {
            return Ok(binder);
        }
        #[cfg(test)]
        if let Some(binder) = self.exact_class_identities.get(&var) {
            return Ok(*binder);
        }
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
            #[cfg(test)]
            self.exact_class_identities.insert(var, first);
            return Ok(first);
        }
        let next = self.method_quantifiers.len() as u32;
        let binder = *self.method_quantifiers.entry(var).or_insert(next);
        #[cfg(not(test))]
        return Ok(ConformanceBinder::MethodQuantifier(binder));
        #[cfg(test)]
        let binder = ConformanceBinder::MethodQuantifier(binder);
        #[cfg(test)]
        {
            self.exact_class_identities.insert(var, binder);
            Ok(binder)
        }
    }

    #[cfg(test)]
    fn resolve_class(
        &mut self,
        class: &[TypeVar],
    ) -> Result<ConformanceBinder, ActualMethodConformanceViewUnavailable> {
        let mut recursive_identities = class
            .iter()
            .filter_map(|var| self.resolve_method_recursive_binder(*var))
            .collect::<Vec<_>>();
        recursive_identities.sort();
        recursive_identities.dedup();
        if recursive_identities.len() > 1 {
            return Err(
                ActualMethodConformanceViewUnavailable::AmbiguousExactClassIdentity(class.to_vec()),
            );
        }
        if let Some(recursive) = recursive_identities.first() {
            for member in class {
                self.exact_class_identities.insert(*member, *recursive);
            }
            return Ok(*recursive);
        }

        let mut bridge_identities = self
            .bridge
            .universals
            .iter()
            .filter_map(|(binder, var)| {
                class
                    .contains(var)
                    .then_some(ConformanceBinder::Universal(*binder))
            })
            .chain(
                self.bridge
                    .inferred_associated
                    .iter()
                    .filter_map(|(binder, var)| {
                        class
                            .contains(var)
                            .then_some(ConformanceBinder::InferredAssociated(*binder))
                    }),
            )
            .collect::<Vec<_>>();
        bridge_identities.sort();
        bridge_identities.dedup();
        if bridge_identities.len() > 1 {
            return Err(
                ActualMethodConformanceViewUnavailable::AmbiguousExactClassIdentity(class.to_vec()),
            );
        }

        let mut registered_identities = class
            .iter()
            .filter_map(|var| self.exact_class_identities.get(var).copied())
            .collect::<Vec<_>>();
        registered_identities.sort();
        registered_identities.dedup();
        let binder = match (bridge_identities.first(), registered_identities.as_slice()) {
            (Some(bridge), []) => *bridge,
            (Some(bridge), [registered]) if bridge == registered => *bridge,
            (None, [registered]) => *registered,
            (None, []) => {
                let representative = *class.first().expect("non-empty exact-equivalence class");
                let next = self.method_quantifiers.len() as u32;
                let quantifier = *self
                    .method_quantifiers
                    .entry(representative)
                    .or_insert(next);
                ConformanceBinder::MethodQuantifier(quantifier)
            }
            _ => {
                return Err(
                    ActualMethodConformanceViewUnavailable::AmbiguousExactClassIdentity(
                        class.to_vec(),
                    ),
                );
            }
        };
        for member in class {
            self.exact_class_identities.insert(*member, binder);
        }
        Ok(binder)
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

#[cfg(test)]
mod tests {
    use super::*;
    use poly::types::Pos;

    struct FirstOrderRelationFixture {
        name: &'static str,
        implementation: ConformanceTypeView,
        requirement: ConformanceTypeView,
        conforms: bool,
    }

    #[test]
    fn exact_equivalence_classes_memoize_strong_components_of_exact_var_edges() {
        let mut machine = ConstraintMachine::new();
        let a = TypeVar(0);
        let b = TypeVar(1);
        let downstream = TypeVar(2);
        for (lower, upper) in [(a, b), (b, a), (b, downstream)] {
            let lower = machine.alloc_pos(Pos::Var(lower));
            let upper = machine.alloc_neg(Neg::Var(upper));
            machine.subtype(lower, upper);
        }

        let mut classes = ExactEquivalenceClasses::new(&machine);
        assert_eq!(classes.class(a), vec![a, b]);
        assert_eq!(classes.class(b), vec![a, b]);
        assert_eq!(classes.class(downstream), vec![downstream]);
    }

    #[test]
    fn exact_class_identity_resolver_registers_one_qm_for_every_member() {
        let bridge = RoleImplConformanceBinderBridge {
            universals: Vec::new(),
            inferred_associated: Vec::new(),
        };
        let mut resolver = ActualBinderIdentityResolver::new(&bridge);
        let a = TypeVar(0);
        let b = TypeVar(1);
        let unrelated = TypeVar(2);
        let q0 = ConformanceBinder::MethodQuantifier(0);

        assert_eq!(resolver.resolve_class(&[a, b]), Ok(q0));
        assert_eq!(resolver.resolve(a), Ok(q0));
        assert_eq!(resolver.resolve(b), Ok(q0));
        assert_eq!(
            resolver.resolve(unrelated),
            Ok(ConformanceBinder::MethodQuantifier(1)),
        );
    }

    #[test]
    fn slice3b_first_order_relation_covers_lattice_binders_builtins_nominals_and_tuples() {
        let builtin = ConformanceTypeView::Builtin;
        let binder = ConformanceTypeView::Binder;
        let u0 = binder(ConformanceBinder::Universal(ImplUniversalBinderId(0)));
        let u1 = binder(ConformanceBinder::Universal(ImplUniversalBinderId(1)));
        let a0 = binder(ConformanceBinder::InferredAssociated(
            AssociatedInferenceBinderId(0),
        ));
        let a1 = binder(ConformanceBinder::InferredAssociated(
            AssociatedInferenceBinderId(1),
        ));
        let q0 = binder(ConformanceBinder::MethodQuantifier(0));
        let q1 = binder(ConformanceBinder::MethodQuantifier(1));
        let r0 = binder(ConformanceBinder::MethodRecursive(0));
        let r1 = binder(ConformanceBinder::MethodRecursive(1));
        let list = |arg| ConformanceTypeView::Nominal {
            path: vec!["std".into(), "list".into()],
            args: vec![arg],
        };
        let option = |arg| ConformanceTypeView::Nominal {
            path: vec!["std".into(), "option".into()],
            args: vec![arg],
        };
        let fixtures = vec![
            FirstOrderRelationFixture {
                name: "bottom-conforms-to-every-requirement",
                implementation: ConformanceTypeView::Bottom,
                requirement: builtin(BuiltinType::Bool),
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "every-implementation-conforms-to-top",
                implementation: builtin(BuiltinType::Int),
                requirement: ConformanceTypeView::Top,
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "top-does-not-conform-to-concrete-requirement",
                implementation: ConformanceTypeView::Top,
                requirement: builtin(BuiltinType::Int),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "same-builtin",
                implementation: builtin(BuiltinType::Int),
                requirement: builtin(BuiltinType::Int),
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "different-builtin",
                implementation: builtin(BuiltinType::Int),
                requirement: builtin(BuiltinType::Bool),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "same-explicit-associated-universal",
                implementation: u0.clone(),
                requirement: u0.clone(),
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "different-universal-id",
                implementation: u0.clone(),
                requirement: u1,
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "different-inferred-associated-id",
                implementation: a0.clone(),
                requirement: a1,
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "universal-does-not-match-inferred-associated",
                implementation: u0.clone(),
                requirement: a0.clone(),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "same-method-quantifier",
                implementation: q0.clone(),
                requirement: q0.clone(),
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "different-method-quantifier-id",
                implementation: q0.clone(),
                requirement: q1,
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "same-method-recursive-binder",
                implementation: r0.clone(),
                requirement: r0.clone(),
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "different-method-recursive-id",
                implementation: r0,
                requirement: r1,
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "universal-does-not-match-method-quantifier",
                implementation: u0,
                requirement: q0,
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "inferred-associated-does-not-match-method-recursive",
                implementation: a0,
                requirement: binder(ConformanceBinder::MethodRecursive(0)),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "same-nominal-and-invariant-argument",
                implementation: list(builtin(BuiltinType::Int)),
                requirement: list(builtin(BuiltinType::Int)),
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "nominal-invariant-argument-differs",
                implementation: list(builtin(BuiltinType::Int)),
                requirement: list(builtin(BuiltinType::Bool)),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "nominal-canonical-path-differs",
                implementation: list(builtin(BuiltinType::Int)),
                requirement: option(builtin(BuiltinType::Int)),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "nominal-arity-differs",
                implementation: list(builtin(BuiltinType::Int)),
                requirement: ConformanceTypeView::Nominal {
                    path: vec!["std".into(), "list".into()],
                    args: vec![builtin(BuiltinType::Int), builtin(BuiltinType::Bool)],
                },
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "nominal-argument-does-not-become-covariant",
                implementation: list(ConformanceTypeView::Bottom),
                requirement: list(ConformanceTypeView::Top),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "tuple-arity-differs",
                implementation: ConformanceTypeView::Tuple(vec![builtin(BuiltinType::Int)]),
                requirement: ConformanceTypeView::Tuple(vec![
                    builtin(BuiltinType::Int),
                    builtin(BuiltinType::Bool),
                ]),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "tuple-elements-compare-covariantly",
                implementation: ConformanceTypeView::Tuple(vec![ConformanceTypeView::Bottom]),
                requirement: ConformanceTypeView::Tuple(vec![builtin(BuiltinType::Int)]),
                conforms: true,
            },
            FirstOrderRelationFixture {
                name: "tuple-element-differs",
                implementation: ConformanceTypeView::Tuple(vec![builtin(BuiltinType::Int)]),
                requirement: ConformanceTypeView::Tuple(vec![builtin(BuiltinType::Bool)]),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "different-structural-shapes",
                implementation: builtin(BuiltinType::Int),
                requirement: ConformanceTypeView::Tuple(vec![builtin(BuiltinType::Int)]),
                conforms: false,
            },
            FirstOrderRelationFixture {
                name: "unknown-is-not-a-conformance-witness",
                implementation: ConformanceTypeView::Unknown,
                requirement: ConformanceTypeView::Unknown,
                conforms: false,
            },
        ];

        for fixture in fixtures {
            assert_eq!(
                first_order_conforms(&fixture.implementation, &fixture.requirement),
                fixture.conforms,
                "fixture: {}",
                fixture.name,
            );
        }
    }
}
