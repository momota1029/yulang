//! Test-only proof that a method-blocked wrapper component can select role methods early.
//!
//! The classifier predicts the role demands that ordinary scheme instantiation would expose, but
//! never freshens a scheme or updates the constraint/SCC machines. Every unsupported projection,
//! unapplied compact merge, or potentially resolvable demand rejects the complete component.

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CandidateIndependentFallbackClassification {
    Eligible {
        selections: Vec<CandidateIndependentFallbackSelection>,
    },
    Ineligible(CandidateIndependentFallbackRejection),
}

impl CandidateIndependentFallbackClassification {
    pub(crate) fn is_eligible(&self) -> bool {
        matches!(self, Self::Eligible { .. })
    }

    pub(crate) fn selections(&self) -> &[CandidateIndependentFallbackSelection] {
        match self {
            Self::Eligible { selections } => selections,
            Self::Ineligible(_) => &[],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CandidateIndependentFallbackSelection {
    pub(crate) select_id: SelectId,
    pub(crate) role: Vec<String>,
    pub(crate) target: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CandidateIndependentFallbackRejection {
    SelectionCountMismatch {
        unresolved_selections: usize,
        method_dependencies: usize,
    },
    SelectionNoLongerUnresolved {
        select_id: SelectId,
    },
    UnprobedReceiverUpper {
        select_id: SelectId,
    },
    LocalRoleCandidates {
        select_id: SelectId,
        count: usize,
    },
    GlobalRoleCandidateCount {
        select_id: SelectId,
        count: usize,
    },
    RecordFieldFallback {
        select_id: SelectId,
    },
    EmptyRolePath {
        select_id: SelectId,
    },
    ImportedTarget {
        select_id: SelectId,
        target: DefId,
    },
    TargetNotLocallyQuantified {
        select_id: SelectId,
        target: DefId,
    },
    MissingTargetScheme {
        select_id: SelectId,
        target: DefId,
    },
    RolePredicateCount {
        select_id: SelectId,
        count: usize,
    },
    CandidateRoleMismatch {
        select_id: SelectId,
    },
    MissingSubjectInput {
        select_id: SelectId,
    },
    UnsupportedRoleCarrier {
        select_id: SelectId,
    },
    RoleBinderNotQuantified {
        select_id: SelectId,
        binder: TypeVar,
    },
    RecursiveRoleBinder {
        select_id: SelectId,
        binder: TypeVar,
    },
    UnsupportedSchemeShape {
        select_id: SelectId,
    },
    SubjectReceiverMismatch {
        select_id: SelectId,
    },
    MissingBinderOccurrence {
        select_id: SelectId,
        binder: TypeVar,
    },
    UnsupportedProjection {
        select_id: SelectId,
    },
    ProjectionMergeRequired {
        select_id: SelectId,
    },
    RecursiveSelectionProjection {
        select_id: SelectId,
    },
    ReceiverProjectionMismatch {
        select_id: SelectId,
    },
    ExistingDemandMergeRequired {
        member: DefId,
    },
    CoalescingMergeRequired,
    ResolvableRoleDemand,
}

impl AnalysisSession {
    pub(crate) fn classify_candidate_independent_fallback_component(
        &self,
        component: &crate::scc::CandidateIndependentFallbackComponent,
    ) -> CandidateIndependentFallbackClassification {
        let members = component.members.iter().copied().collect::<FxHashSet<_>>();
        let mut selections = self
            .selections
            .iter()
            .filter(|(_, use_site)| members.contains(&use_site.parent))
            .map(|(select_id, use_site)| (select_id, *use_site))
            .collect::<Vec<_>>();
        selections.sort_by_key(|(select_id, _)| select_id.0);
        if selections.len() != component.method_dependencies {
            return CandidateIndependentFallbackClassification::Ineligible(
                CandidateIndependentFallbackRejection::SelectionCountMismatch {
                    unresolved_selections: selections.len(),
                    method_dependencies: component.method_dependencies,
                },
            );
        }

        let mut predicted = Vec::with_capacity(selections.len());
        let mut eligible = Vec::with_capacity(selections.len());
        for (select_id, use_site) in selections {
            match self.predict_selection_role_demand(select_id, use_site) {
                Ok((selection, demand)) => {
                    eligible.push(selection);
                    predicted.push(demand);
                }
                Err(reason) => {
                    return CandidateIndependentFallbackClassification::Ineligible(reason);
                }
            }
        }

        let mut demands = Vec::new();
        for member in &component.members {
            for role in self.roles.for_owner(*member) {
                let (compact, merge_constraints) =
                    compact_role_constraint_recording_merge_constraints(
                        self.infer.constraints(),
                        role,
                    );
                if merge_constraints_require_application(&merge_constraints) {
                    return CandidateIndependentFallbackClassification::Ineligible(
                        CandidateIndependentFallbackRejection::ExistingDemandMergeRequired {
                            member: *member,
                        },
                    );
                }
                demands.push(compact);
            }
        }
        demands.extend(predicted);
        if let Err(reason) = prove_role_demands_cannot_resolve(demands) {
            return CandidateIndependentFallbackClassification::Ineligible(reason);
        }

        CandidateIndependentFallbackClassification::Eligible {
            selections: eligible,
        }
    }

    fn predict_selection_role_demand(
        &self,
        select_id: SelectId,
        use_site: SelectionUse,
    ) -> Result<
        (CandidateIndependentFallbackSelection, CompactRoleConstraint),
        CandidateIndependentFallbackRejection,
    > {
        if self.selections.get(select_id).is_none()
            || self.poly.select(select_id).resolution.is_some()
        {
            return Err(
                CandidateIndependentFallbackRejection::SelectionNoLongerUnresolved { select_id },
            );
        }
        if self.selections.has_unprobed_receiver_upper(select_id) {
            return Err(CandidateIndependentFallbackRejection::UnprobedReceiverUpper { select_id });
        }

        let name = self.poly.select(select_id).name.as_str();
        if let Some(scope) = use_site.local_method_scope {
            let local = self.local_methods.role_candidates(scope, name);
            if !local.is_empty() {
                return Err(CandidateIndependentFallbackRejection::LocalRoleCandidates {
                    select_id,
                    count: local.len(),
                });
            }
        }
        let global = self.role_methods.candidates(name);
        let [candidate] = global else {
            if global.is_empty() {
                return Err(CandidateIndependentFallbackRejection::RecordFieldFallback {
                    select_id,
                });
            }
            return Err(
                CandidateIndependentFallbackRejection::GlobalRoleCandidateCount {
                    select_id,
                    count: global.len(),
                },
            );
        };
        if candidate.role.is_empty() {
            return Err(CandidateIndependentFallbackRejection::EmptyRolePath { select_id });
        }

        let target = candidate.def;
        if self.imported_scheme_defs.contains(&target) {
            return Err(CandidateIndependentFallbackRejection::ImportedTarget {
                select_id,
                target,
            });
        }
        // Quantified definitions have been removed from the open SCC graph. Consequently this
        // check also proves that the target cannot belong to a pending conformance component.
        if !self.scc.is_quantified(target) {
            return Err(
                CandidateIndependentFallbackRejection::TargetNotLocallyQuantified {
                    select_id,
                    target,
                },
            );
        }
        let Some(Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.poly.defs.get(target)
        else {
            return Err(CandidateIndependentFallbackRejection::MissingTargetScheme {
                select_id,
                target,
            });
        };

        let prediction = predict_scheme_demand(
            &self.poly.typ,
            scheme,
            &candidate.role,
            self.infer.constraints(),
            use_site.method_value,
            use_site.receiver_value,
        )
        .map_err(|reason| reason.with_select(select_id))?;

        Ok((
            CandidateIndependentFallbackSelection {
                select_id,
                role: candidate.role.clone(),
                target,
            },
            prediction,
        ))
    }
}

fn prove_role_demands_cannot_resolve(
    demands: Vec<CompactRoleConstraint>,
) -> Result<(), CandidateIndependentFallbackRejection> {
    if demands.iter().any(role_constraint_could_resolve) {
        return Err(CandidateIndependentFallbackRejection::ResolvableRoleDemand);
    }
    let (coalesced, merge_constraints) =
        coalesce_role_constraints_recording_merge_constraints(demands);
    if merge_constraints_require_application(&merge_constraints) {
        return Err(CandidateIndependentFallbackRejection::CoalescingMergeRequired);
    }
    if coalesced.iter().any(role_constraint_could_resolve) {
        return Err(CandidateIndependentFallbackRejection::ResolvableRoleDemand);
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SchemePredictionRejection {
    RolePredicateCount(usize),
    CandidateRoleMismatch,
    MissingSubjectInput,
    UnsupportedRoleCarrier,
    RoleBinderNotQuantified(TypeVar),
    RecursiveRoleBinder(TypeVar),
    UnsupportedSchemeShape,
    SubjectReceiverMismatch,
    MissingBinderOccurrence(TypeVar),
    UnsupportedProjection,
    ProjectionMergeRequired,
    RecursiveSelectionProjection,
    ReceiverProjectionMismatch,
}

impl SchemePredictionRejection {
    fn with_select(self, select_id: SelectId) -> CandidateIndependentFallbackRejection {
        match self {
            Self::RolePredicateCount(count) => {
                CandidateIndependentFallbackRejection::RolePredicateCount { select_id, count }
            }
            Self::CandidateRoleMismatch => {
                CandidateIndependentFallbackRejection::CandidateRoleMismatch { select_id }
            }
            Self::MissingSubjectInput => {
                CandidateIndependentFallbackRejection::MissingSubjectInput { select_id }
            }
            Self::UnsupportedRoleCarrier => {
                CandidateIndependentFallbackRejection::UnsupportedRoleCarrier { select_id }
            }
            Self::RoleBinderNotQuantified(binder) => {
                CandidateIndependentFallbackRejection::RoleBinderNotQuantified { select_id, binder }
            }
            Self::RecursiveRoleBinder(binder) => {
                CandidateIndependentFallbackRejection::RecursiveRoleBinder { select_id, binder }
            }
            Self::UnsupportedSchemeShape => {
                CandidateIndependentFallbackRejection::UnsupportedSchemeShape { select_id }
            }
            Self::SubjectReceiverMismatch => {
                CandidateIndependentFallbackRejection::SubjectReceiverMismatch { select_id }
            }
            Self::MissingBinderOccurrence(binder) => {
                CandidateIndependentFallbackRejection::MissingBinderOccurrence { select_id, binder }
            }
            Self::UnsupportedProjection => {
                CandidateIndependentFallbackRejection::UnsupportedProjection { select_id }
            }
            Self::ProjectionMergeRequired => {
                CandidateIndependentFallbackRejection::ProjectionMergeRequired { select_id }
            }
            Self::RecursiveSelectionProjection => {
                CandidateIndependentFallbackRejection::RecursiveSelectionProjection { select_id }
            }
            Self::ReceiverProjectionMismatch => {
                CandidateIndependentFallbackRejection::ReceiverProjectionMismatch { select_id }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct RoleCarrier {
    binder: TypeVar,
    polarity: crate::compact::CompactRoleArgPolarity,
}

#[derive(Debug, Clone, Default)]
struct BinderDemand {
    lowers: Vec<CompactType>,
    uppers: Vec<CompactType>,
    invariant: Vec<CompactBounds>,
    occurrences: usize,
}

impl BinderDemand {
    fn add_lower(&mut self, value: CompactType) {
        self.lowers.push(value);
        self.occurrences += 1;
    }

    fn add_upper(&mut self, value: CompactType) {
        self.uppers.push(value);
        self.occurrences += 1;
    }

    fn add_invariant(&mut self, value: CompactBounds) {
        self.invariant.push(value);
        self.occurrences += 1;
    }

    fn bounds(
        &self,
        polarity: crate::compact::CompactRoleArgPolarity,
    ) -> Result<CompactBounds, SchemePredictionRejection> {
        let lower = merge_projected_types(true, &self.lowers)?;
        let upper = merge_projected_types(false, &self.uppers)?;
        if polarity != crate::compact::CompactRoleArgPolarity::Invariant
            && !self.invariant.is_empty()
        {
            return Err(SchemePredictionRejection::UnsupportedProjection);
        }
        let mut bounds = match polarity {
            crate::compact::CompactRoleArgPolarity::Covariant if !lower.is_empty() => {
                Some(CompactBounds::Interval {
                    lower,
                    upper: CompactType::default(),
                })
            }
            crate::compact::CompactRoleArgPolarity::Contravariant if !upper.is_empty() => {
                Some(CompactBounds::Interval {
                    lower: CompactType::default(),
                    upper,
                })
            }
            crate::compact::CompactRoleArgPolarity::Invariant
                if !lower.is_empty() || !upper.is_empty() =>
            {
                Some(CompactBounds::Interval { lower, upper })
            }
            _ => None,
        };
        for projected in &self.invariant {
            let Some(current) = bounds else {
                bounds = Some(projected.clone());
                continue;
            };
            let (merged, merge_constraints) =
                crate::compact::merge_compact_bounds_recording_merge_constraints(
                    true,
                    current,
                    projected.clone(),
                );
            if merge_constraints_require_application(&merge_constraints) {
                return Err(SchemePredictionRejection::ProjectionMergeRequired);
            }
            bounds = Some(merged);
        }
        Ok(bounds.unwrap_or(CompactBounds::Interval {
            lower: CompactType::default(),
            upper: CompactType::default(),
        }))
    }
}

fn merge_projected_types(
    positive: bool,
    projected: &[CompactType],
) -> Result<CompactType, SchemePredictionRejection> {
    let mut merged = CompactType::default();
    for value in projected {
        let (next, merge_constraints) =
            crate::compact::merge_compact_types_recording_merge_constraints(
                positive,
                merged,
                value.clone(),
            );
        if merge_constraints_require_application(&merge_constraints) {
            return Err(SchemePredictionRejection::ProjectionMergeRequired);
        }
        merged = next;
    }
    Ok(merged)
}

fn predict_scheme_demand(
    arena: &TypeArena,
    scheme: &Scheme,
    candidate_role: &[String],
    machine: &crate::constraints::ConstraintMachine,
    method_value: TypeVar,
    receiver_value: TypeVar,
) -> Result<CompactRoleConstraint, SchemePredictionRejection> {
    let [predicate] = scheme.role_predicates.as_slice() else {
        return Err(SchemePredictionRejection::RolePredicateCount(
            scheme.role_predicates.len(),
        ));
    };
    if predicate.role != candidate_role {
        return Err(SchemePredictionRejection::CandidateRoleMismatch);
    }
    let Some(subject_input) = predicate.inputs.first().copied() else {
        return Err(SchemePredictionRejection::MissingSubjectInput);
    };
    let subject = direct_role_carrier(arena, subject_input)
        .ok_or(SchemePredictionRejection::UnsupportedRoleCarrier)?;

    let mut carriers = Vec::with_capacity(predicate.inputs.len() + predicate.associated.len());
    for input in &predicate.inputs {
        carriers.push(
            direct_role_carrier(arena, *input)
                .ok_or(SchemePredictionRejection::UnsupportedRoleCarrier)?,
        );
    }
    let mut associated_carriers = Vec::with_capacity(predicate.associated.len());
    for associated in &predicate.associated {
        let binder = direct_invariant_binder(arena, associated.value)
            .ok_or(SchemePredictionRejection::UnsupportedRoleCarrier)?;
        associated_carriers.push(RoleCarrier {
            binder,
            polarity: crate::compact::CompactRoleArgPolarity::Invariant,
        });
    }

    let quantifiers = scheme.quantifiers.iter().copied().collect::<FxHashSet<_>>();
    let relevant = carriers
        .iter()
        .chain(&associated_carriers)
        .map(|carrier| carrier.binder)
        .collect::<FxHashSet<_>>();
    for binder in &relevant {
        if !quantifiers.contains(binder) {
            return Err(SchemePredictionRejection::RoleBinderNotQuantified(*binder));
        }
        if scheme
            .recursive_bounds
            .iter()
            .any(|bound| bound.var == *binder)
        {
            return Err(SchemePredictionRejection::RecursiveRoleBinder(*binder));
        }
    }
    if !scheme.recursive_bounds.is_empty() || !scheme.stack_quantifiers.is_empty() {
        return Err(SchemePredictionRejection::UnsupportedSchemeShape);
    }

    let Pos::Fun { arg, .. } = arena.pos(scheme.predicate) else {
        return Err(SchemePredictionRejection::SubjectReceiverMismatch);
    };
    if !matches!(arena.neg(*arg), Neg::Var(binder) if *binder == subject.binder) {
        return Err(SchemePredictionRejection::SubjectReceiverMismatch);
    }

    let (method_compact, method_merge_constraints) =
        crate::compact::compact_negative_type_var_recording_merge_constraints(
            machine,
            method_value,
        );
    if merge_constraints_require_application(&method_merge_constraints) {
        return Err(SchemePredictionRejection::ProjectionMergeRequired);
    }
    if !method_compact.rec_vars.is_empty() {
        return Err(SchemePredictionRejection::RecursiveSelectionProjection);
    }
    let outer_fun = single_fun_projection(&method_compact.root)?;

    let mut demands = relevant
        .iter()
        .copied()
        .map(|binder| (binder, BinderDemand::default()))
        .collect::<FxHashMap<_, _>>();
    project_pos_occurrences(
        arena,
        scheme.predicate,
        &method_compact.root,
        &relevant,
        &mut demands,
    )?;

    let (receiver_compact, receiver_merge_constraints) =
        compact_type_var_recording_merge_constraints(machine, receiver_value);
    if merge_constraints_require_application(&receiver_merge_constraints) {
        return Err(SchemePredictionRejection::ProjectionMergeRequired);
    }
    if !receiver_compact.rec_vars.is_empty() {
        return Err(SchemePredictionRejection::RecursiveSelectionProjection);
    }
    validate_compact_leaf(&receiver_compact.root)?;
    if receiver_compact.root != outer_fun.arg {
        return Err(SchemePredictionRejection::ReceiverProjectionMismatch);
    }
    demands
        .get_mut(&subject.binder)
        .expect("subject binder is relevant")
        .add_lower(receiver_compact.root);

    for (binder, demand) in &demands {
        if demand.occurrences == 0 {
            return Err(SchemePredictionRejection::MissingBinderOccurrence(*binder));
        }
    }

    let inputs = carriers
        .iter()
        .map(|carrier| {
            let bounds = demands[&carrier.binder].bounds(carrier.polarity)?;
            Ok(CompactRoleArg::invariant(bounds).with_polarity(carrier.polarity))
        })
        .collect::<Result<Vec<_>, SchemePredictionRejection>>()?;
    let associated = predicate
        .associated
        .iter()
        .zip(&associated_carriers)
        .map(|(associated, carrier)| {
            let bounds = demands[&carrier.binder].bounds(carrier.polarity)?;
            Ok(crate::compact::CompactRoleAssociatedType {
                name: associated.name.clone(),
                value: CompactRoleArg::invariant(bounds).with_polarity(carrier.polarity),
            })
        })
        .collect::<Result<Vec<_>, SchemePredictionRejection>>()?;

    Ok(CompactRoleConstraint {
        role: predicate.role.clone(),
        inputs,
        associated,
    })
}

fn direct_role_carrier(arena: &TypeArena, input: RolePredicateArg) -> Option<RoleCarrier> {
    match input {
        RolePredicateArg::Covariant(pos) => match arena.pos(pos) {
            Pos::Var(binder) => Some(RoleCarrier {
                binder: *binder,
                polarity: crate::compact::CompactRoleArgPolarity::Covariant,
            }),
            _ => None,
        },
        RolePredicateArg::Contravariant(neg) => match arena.neg(neg) {
            Neg::Var(binder) => Some(RoleCarrier {
                binder: *binder,
                polarity: crate::compact::CompactRoleArgPolarity::Contravariant,
            }),
            _ => None,
        },
        RolePredicateArg::Invariant(neu) => {
            direct_invariant_binder(arena, neu).map(|binder| RoleCarrier {
                binder,
                polarity: crate::compact::CompactRoleArgPolarity::Invariant,
            })
        }
    }
}

fn direct_invariant_binder(arena: &TypeArena, neu: NeuId) -> Option<TypeVar> {
    let Neu::Bounds(lower, upper) = arena.neu(neu) else {
        return None;
    };
    match (arena.pos(*lower), arena.neg(*upper)) {
        (Pos::Var(lower), Neg::Var(upper)) if lower == upper => Some(*lower),
        _ => None,
    }
}

fn project_pos_occurrences(
    arena: &TypeArena,
    id: PosId,
    actual: &CompactType,
    relevant: &FxHashSet<TypeVar>,
    demands: &mut FxHashMap<TypeVar, BinderDemand>,
) -> Result<(), SchemePredictionRejection> {
    if !pos_contains_relevant(arena, id, relevant) {
        return Ok(());
    }
    match arena.pos(id) {
        Pos::Var(binder) => {
            validate_compact_leaf(actual)?;
            demands
                .get_mut(binder)
                .expect("relevant positive binder has demand slot")
                .add_upper(actual.clone());
            Ok(())
        }
        Pos::Con(path, args) => {
            let projected = single_con_projection(actual, path, args.len())?;
            for (arg, projected) in args.iter().zip(projected) {
                project_neu_occurrences(arena, *arg, projected, relevant, demands)?;
            }
            Ok(())
        }
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let projected = single_fun_projection(actual)?;
            project_neg_occurrences(arena, *arg, &projected.arg, relevant, demands)?;
            project_neg_occurrences(arena, *arg_eff, &projected.arg_eff, relevant, demands)?;
            project_pos_occurrences(arena, *ret_eff, &projected.ret_eff, relevant, demands)?;
            project_pos_occurrences(arena, *ret, &projected.ret, relevant, demands)
        }
        Pos::Record(fields) => {
            let projected = single_record_projection(actual)?;
            for field in fields {
                if !pos_contains_relevant(arena, field.value, relevant) {
                    continue;
                }
                let value = projected
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name && actual.optional == field.optional)
                    .ok_or(SchemePredictionRejection::UnsupportedProjection)?;
                project_pos_occurrences(arena, field.value, &value.value, relevant, demands)?;
            }
            Ok(())
        }
        Pos::PolyVariant(items) => {
            let projected = single_variant_projection(actual)?;
            for (name, payloads) in items {
                let Some((_, actual_payloads)) =
                    projected.items.iter().find(|(actual, _)| actual == name)
                else {
                    return Err(SchemePredictionRejection::UnsupportedProjection);
                };
                if payloads.len() != actual_payloads.len() {
                    return Err(SchemePredictionRejection::UnsupportedProjection);
                }
                for (payload, actual) in payloads.iter().zip(actual_payloads) {
                    project_pos_occurrences(arena, *payload, actual, relevant, demands)?;
                }
            }
            Ok(())
        }
        Pos::Tuple(items) => {
            let projected = single_tuple_projection(actual)?;
            if items.len() != projected.items.len() {
                return Err(SchemePredictionRejection::UnsupportedProjection);
            }
            for (item, actual) in items.iter().zip(&projected.items) {
                project_pos_occurrences(arena, *item, actual, relevant, demands)?;
            }
            Ok(())
        }
        Pos::Bot => Ok(()),
        Pos::RecordTailSpread { .. }
        | Pos::RecordHeadSpread { .. }
        | Pos::Row(_)
        | Pos::Stack { .. }
        | Pos::NonSubtract(_, _)
        | Pos::Union(_, _) => Err(SchemePredictionRejection::UnsupportedSchemeShape),
    }
}

fn project_neg_occurrences(
    arena: &TypeArena,
    id: NegId,
    actual: &CompactType,
    relevant: &FxHashSet<TypeVar>,
    demands: &mut FxHashMap<TypeVar, BinderDemand>,
) -> Result<(), SchemePredictionRejection> {
    if !neg_contains_relevant(arena, id, relevant) {
        return Ok(());
    }
    match arena.neg(id) {
        Neg::Var(binder) => {
            validate_compact_leaf(actual)?;
            demands
                .get_mut(binder)
                .expect("relevant negative binder has demand slot")
                .add_lower(actual.clone());
            Ok(())
        }
        Neg::Con(path, args) => {
            let projected = single_con_projection(actual, path, args.len())?;
            for (arg, projected) in args.iter().zip(projected) {
                project_neu_occurrences(arena, *arg, projected, relevant, demands)?;
            }
            Ok(())
        }
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let projected = single_fun_projection(actual)?;
            project_pos_occurrences(arena, *arg, &projected.arg, relevant, demands)?;
            project_pos_occurrences(arena, *arg_eff, &projected.arg_eff, relevant, demands)?;
            project_neg_occurrences(arena, *ret_eff, &projected.ret_eff, relevant, demands)?;
            project_neg_occurrences(arena, *ret, &projected.ret, relevant, demands)
        }
        Neg::Record(fields) => {
            let projected = single_record_projection(actual)?;
            for field in fields {
                if !neg_contains_relevant(arena, field.value, relevant) {
                    continue;
                }
                let value = projected
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name && actual.optional == field.optional)
                    .ok_or(SchemePredictionRejection::UnsupportedProjection)?;
                project_neg_occurrences(arena, field.value, &value.value, relevant, demands)?;
            }
            Ok(())
        }
        Neg::PolyVariant(items) => {
            let projected = single_variant_projection(actual)?;
            for (name, payloads) in items {
                let Some((_, actual_payloads)) =
                    projected.items.iter().find(|(actual, _)| actual == name)
                else {
                    return Err(SchemePredictionRejection::UnsupportedProjection);
                };
                if payloads.len() != actual_payloads.len() {
                    return Err(SchemePredictionRejection::UnsupportedProjection);
                }
                for (payload, actual) in payloads.iter().zip(actual_payloads) {
                    project_neg_occurrences(arena, *payload, actual, relevant, demands)?;
                }
            }
            Ok(())
        }
        Neg::Tuple(items) => {
            let projected = single_tuple_projection(actual)?;
            if items.len() != projected.items.len() {
                return Err(SchemePredictionRejection::UnsupportedProjection);
            }
            for (item, actual) in items.iter().zip(&projected.items) {
                project_neg_occurrences(arena, *item, actual, relevant, demands)?;
            }
            Ok(())
        }
        Neg::Top | Neg::Bot => Ok(()),
        Neg::Row(_, _) | Neg::Stack { .. } | Neg::Intersection(_, _) => {
            Err(SchemePredictionRejection::UnsupportedSchemeShape)
        }
    }
}

fn project_neu_occurrences(
    arena: &TypeArena,
    id: NeuId,
    actual: &CompactBounds,
    relevant: &FxHashSet<TypeVar>,
    demands: &mut FxHashMap<TypeVar, BinderDemand>,
) -> Result<(), SchemePredictionRejection> {
    if !neu_contains_relevant(arena, id, relevant) {
        return Ok(());
    }
    if let Some(binder) = direct_invariant_binder(arena, id)
        && relevant.contains(&binder)
    {
        validate_compact_bounds_leaf(actual)?;
        demands
            .get_mut(&binder)
            .expect("relevant invariant binder has demand slot")
            .add_invariant(actual.clone());
        return Ok(());
    }

    match (arena.neu(id), actual) {
        (
            Neu::Con(path, args),
            CompactBounds::Con {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (arg, actual) in args.iter().zip(actual_args) {
                project_neu_occurrences(arena, *arg, actual, relevant, demands)?;
            }
            Ok(())
        }
        (
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
            CompactBounds::Fun {
                arg: actual_arg,
                arg_eff: actual_arg_eff,
                ret_eff: actual_ret_eff,
                ret: actual_ret,
            },
        ) => {
            project_neu_occurrences(arena, *arg, actual_arg, relevant, demands)?;
            project_neu_occurrences(arena, *arg_eff, actual_arg_eff, relevant, demands)?;
            project_neu_occurrences(arena, *ret_eff, actual_ret_eff, relevant, demands)?;
            project_neu_occurrences(arena, *ret, actual_ret, relevant, demands)
        }
        (Neu::Record(fields), CompactBounds::Record { fields: actual }) => {
            for field in fields {
                if !neu_contains_relevant(arena, field.value, relevant) {
                    continue;
                }
                let value = actual
                    .iter()
                    .find(|actual| actual.name == field.name && actual.optional == field.optional)
                    .ok_or(SchemePredictionRejection::UnsupportedProjection)?;
                project_neu_occurrences(arena, field.value, &value.value, relevant, demands)?;
            }
            Ok(())
        }
        (Neu::PolyVariant(items), CompactBounds::PolyVariant { items: actual }) => {
            for (name, payloads) in items {
                let Some((_, actual_payloads)) = actual.iter().find(|(actual, _)| actual == name)
                else {
                    return Err(SchemePredictionRejection::UnsupportedProjection);
                };
                if payloads.len() != actual_payloads.len() {
                    return Err(SchemePredictionRejection::UnsupportedProjection);
                }
                for (payload, actual) in payloads.iter().zip(actual_payloads) {
                    project_neu_occurrences(arena, *payload, actual, relevant, demands)?;
                }
            }
            Ok(())
        }
        (Neu::Tuple(items), CompactBounds::Tuple { items: actual })
            if items.len() == actual.len() =>
        {
            for (item, actual) in items.iter().zip(actual) {
                project_neu_occurrences(arena, *item, actual, relevant, demands)?;
            }
            Ok(())
        }
        (Neu::Bounds(_, _), _) => Err(SchemePredictionRejection::UnsupportedProjection),
        _ => Err(SchemePredictionRejection::UnsupportedProjection),
    }
}

fn pos_contains_relevant(arena: &TypeArena, id: PosId, relevant: &FxHashSet<TypeVar>) -> bool {
    match arena.pos(id) {
        Pos::Bot => false,
        Pos::Var(var) => relevant.contains(var),
        Pos::Con(_, args) => args
            .iter()
            .any(|arg| neu_contains_relevant(arena, *arg, relevant)),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            neg_contains_relevant(arena, *arg, relevant)
                || neg_contains_relevant(arena, *arg_eff, relevant)
                || pos_contains_relevant(arena, *ret_eff, relevant)
                || pos_contains_relevant(arena, *ret, relevant)
        }
        Pos::Record(fields) => fields
            .iter()
            .any(|field| pos_contains_relevant(arena, field.value, relevant)),
        Pos::RecordTailSpread { fields, tail } => {
            fields
                .iter()
                .any(|field| pos_contains_relevant(arena, field.value, relevant))
                || pos_contains_relevant(arena, *tail, relevant)
        }
        Pos::RecordHeadSpread { tail, fields } => {
            pos_contains_relevant(arena, *tail, relevant)
                || fields
                    .iter()
                    .any(|field| pos_contains_relevant(arena, field.value, relevant))
        }
        Pos::PolyVariant(items) => items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| pos_contains_relevant(arena, *payload, relevant))
        }),
        Pos::Tuple(items) | Pos::Row(items) => items
            .iter()
            .any(|item| pos_contains_relevant(arena, *item, relevant)),
        Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
            pos_contains_relevant(arena, *inner, relevant)
        }
        Pos::Union(left, right) => {
            pos_contains_relevant(arena, *left, relevant)
                || pos_contains_relevant(arena, *right, relevant)
        }
    }
}

fn neg_contains_relevant(arena: &TypeArena, id: NegId, relevant: &FxHashSet<TypeVar>) -> bool {
    match arena.neg(id) {
        Neg::Top | Neg::Bot => false,
        Neg::Var(var) => relevant.contains(var),
        Neg::Con(_, args) => args
            .iter()
            .any(|arg| neu_contains_relevant(arena, *arg, relevant)),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            pos_contains_relevant(arena, *arg, relevant)
                || pos_contains_relevant(arena, *arg_eff, relevant)
                || neg_contains_relevant(arena, *ret_eff, relevant)
                || neg_contains_relevant(arena, *ret, relevant)
        }
        Neg::Record(fields) => fields
            .iter()
            .any(|field| neg_contains_relevant(arena, field.value, relevant)),
        Neg::PolyVariant(items) => items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| neg_contains_relevant(arena, *payload, relevant))
        }),
        Neg::Tuple(items) => items
            .iter()
            .any(|item| neg_contains_relevant(arena, *item, relevant)),
        Neg::Row(items, tail) => {
            items
                .iter()
                .any(|item| neg_contains_relevant(arena, *item, relevant))
                || neg_contains_relevant(arena, *tail, relevant)
        }
        Neg::Stack { inner, .. } => neg_contains_relevant(arena, *inner, relevant),
        Neg::Intersection(left, right) => {
            neg_contains_relevant(arena, *left, relevant)
                || neg_contains_relevant(arena, *right, relevant)
        }
    }
}

fn neu_contains_relevant(arena: &TypeArena, id: NeuId, relevant: &FxHashSet<TypeVar>) -> bool {
    match arena.neu(id) {
        Neu::Bounds(lower, upper) => {
            pos_contains_relevant(arena, *lower, relevant)
                || neg_contains_relevant(arena, *upper, relevant)
        }
        Neu::Con(_, args) => args
            .iter()
            .any(|arg| neu_contains_relevant(arena, *arg, relevant)),
        Neu::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            neu_contains_relevant(arena, *arg, relevant)
                || neu_contains_relevant(arena, *arg_eff, relevant)
                || neu_contains_relevant(arena, *ret_eff, relevant)
                || neu_contains_relevant(arena, *ret, relevant)
        }
        Neu::Record(fields) => fields
            .iter()
            .any(|field| neu_contains_relevant(arena, field.value, relevant)),
        Neu::PolyVariant(items) => items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| neu_contains_relevant(arena, *payload, relevant))
        }),
        Neu::Tuple(items) => items
            .iter()
            .any(|item| neu_contains_relevant(arena, *item, relevant)),
    }
}

fn single_fun_projection(
    ty: &CompactType,
) -> Result<&crate::compact::CompactFun, SchemePredictionRejection> {
    if structural_alternative_count(ty) != 1 || ty.funs.len() != 1 {
        return Err(SchemePredictionRejection::UnsupportedProjection);
    }
    Ok(&ty.funs[0])
}

fn single_con_projection<'a>(
    ty: &'a CompactType,
    path: &[String],
    arity: usize,
) -> Result<&'a [CompactBounds], SchemePredictionRejection> {
    if structural_alternative_count(ty) != 1 || ty.cons.len() != 1 {
        return Err(SchemePredictionRejection::UnsupportedProjection);
    }
    let args = ty
        .cons
        .get(path)
        .ok_or(SchemePredictionRejection::UnsupportedProjection)?;
    if args.len() != arity {
        return Err(SchemePredictionRejection::UnsupportedProjection);
    }
    Ok(args)
}

fn single_record_projection(
    ty: &CompactType,
) -> Result<&crate::compact::CompactRecord, SchemePredictionRejection> {
    if structural_alternative_count(ty) != 1 || ty.records.len() != 1 {
        return Err(SchemePredictionRejection::UnsupportedProjection);
    }
    Ok(&ty.records[0])
}

fn single_variant_projection(
    ty: &CompactType,
) -> Result<&crate::compact::CompactPolyVariant, SchemePredictionRejection> {
    if structural_alternative_count(ty) != 1 || ty.poly_variants.len() != 1 {
        return Err(SchemePredictionRejection::UnsupportedProjection);
    }
    Ok(&ty.poly_variants[0])
}

fn single_tuple_projection(
    ty: &CompactType,
) -> Result<&crate::compact::CompactTuple, SchemePredictionRejection> {
    if structural_alternative_count(ty) != 1 || ty.tuples.len() != 1 {
        return Err(SchemePredictionRejection::UnsupportedProjection);
    }
    Ok(&ty.tuples[0])
}

fn validate_compact_leaf(ty: &CompactType) -> Result<(), SchemePredictionRejection> {
    if structural_alternative_count(ty) > 1
        || !ty.record_spreads.is_empty()
        || !ty.rows.is_empty()
        || ty.vars.iter().any(|var| !var.weight.is_empty())
    {
        return Err(SchemePredictionRejection::UnsupportedProjection);
    }
    Ok(())
}

fn validate_compact_bounds_leaf(bounds: &CompactBounds) -> Result<(), SchemePredictionRejection> {
    if let CompactBounds::Interval { lower, upper } = bounds {
        validate_compact_leaf(lower)?;
        validate_compact_leaf(upper)?;
    }
    Ok(())
}

fn structural_alternative_count(ty: &CompactType) -> usize {
    usize::from(ty.never)
        + ty.builtins.len()
        + ty.cons.len()
        + ty.funs.len()
        + ty.records.len()
        + ty.record_spreads.len()
        + ty.poly_variants.len()
        + ty.tuples.len()
        + ty.rows.len()
}

fn merge_constraints_require_application(constraints: &[CompactMergeConstraint]) -> bool {
    unapplied_compact_merge_constraint_count(constraints, &FxHashSet::default()) != 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn projected_occurrence_merge_that_needs_application_is_rejected() {
        let first_arg = CompactBounds::Interval {
            lower: CompactType::from_var(crate::compact::CompactVar::plain(TypeVar(1))),
            upper: CompactType::from_var(crate::compact::CompactVar::plain(TypeVar(1))),
        };
        let second_arg = CompactBounds::Interval {
            lower: CompactType::from_var(crate::compact::CompactVar::plain(TypeVar(2))),
            upper: CompactType::from_var(crate::compact::CompactVar::plain(TypeVar(2))),
        };
        let first = CompactType::from_con(crate::compact::CompactCon {
            path: vec!["Box".into()],
            args: vec![first_arg],
        });
        let second = CompactType::from_con(crate::compact::CompactCon {
            path: vec!["Box".into()],
            args: vec![second_arg],
        });

        assert_eq!(
            merge_projected_types(true, &[first, second]),
            Err(SchemePredictionRejection::ProjectionMergeRequired),
        );
    }

    #[test]
    fn coalescing_that_requires_a_merge_is_not_candidate_independent() {
        let shared = CompactType::from_var(crate::compact::CompactVar::plain(TypeVar(1)));
        let other = CompactType::from_var(crate::compact::CompactVar::plain(TypeVar(2)));
        let first = CompactRoleConstraint {
            role: vec!["R".into()],
            inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
                lower: shared.clone(),
                upper: shared.clone(),
            })],
            associated: Vec::new(),
        };
        let second = CompactRoleConstraint {
            role: vec!["R".into()],
            inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
                lower: shared,
                upper: other,
            })],
            associated: Vec::new(),
        };
        assert!(!role_constraint_could_resolve(&first));
        assert!(!role_constraint_could_resolve(&second));

        assert_eq!(
            prove_role_demands_cannot_resolve(vec![first, second]),
            Err(CandidateIndependentFallbackRejection::CoalescingMergeRequired),
        );
    }
}
