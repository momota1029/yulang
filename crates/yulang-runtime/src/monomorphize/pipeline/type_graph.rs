use std::collections::BTreeMap;
use std::time::Instant;

use super::*;
use crate::diagnostic::display_type;
use crate::types::{
    BoundsChoice, choose_bounds_type, close_type_substitution_map_recursively, collect_type_vars,
    effect_is_empty, hir_type_has_vars, infer_type_substitutions,
    retain_acyclic_type_substitutions, same_effect_head, substitute_bounds, substitute_type,
    type_compatible,
};

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraph {
    slots: Vec<TypeGraphSlot>,
    edges: Vec<TypeGraphEdge>,
    bounds_evidence: Vec<TypeGraphBoundsEvidence>,
    type_var_lower_evidence: Vec<TypeGraphTypeVarLowerEvidence>,
    role_bounds_evidence: Vec<TypeGraphRoleBoundsEvidence>,
    role_associated_resolutions: Vec<TypeGraphRoleAssociatedResolutionEvidence>,
    next_type_var_scope: usize,
    conflicts: Vec<TypeGraphConflict>,
}

impl TypeGraph {
    pub(super) fn conflicts(&self) -> &[TypeGraphConflict] {
        &self.conflicts
    }

    pub(super) fn slot_at(&self, index: usize) -> Option<&TypeGraphSlot> {
        self.slots.get(index)
    }

    pub(super) fn solve_lower_snapshot(&self) -> TypeGraphLowerSolution {
        let mut union = TypeGraphUnionFind::new(self.slots.len());
        for edge in &self.edges {
            if edge_kind_propagates_lower(edge.kind) {
                union.union(edge.source.0, edge.target.0);
            }
        }

        let mut groups = vec![TypeGraphLowerGroup::default(); self.slots.len()];
        for slot in &self.slots {
            let group = union.find(slot.id.0);
            groups[group].slots.push(slot.id);
            if !slot.upper_requirements.is_empty() {
                groups[group].has_upper_requirements = true;
            }
            for evidence in &slot.lower_evidence {
                let Some(candidate) = self.bounds_evidence[evidence.0]
                    .projection
                    .lower_runtime_type()
                else {
                    continue;
                };
                push_runtime_lower_candidate(&mut groups[group].lower_candidates, candidate);
            }
        }

        let mut slot_candidates = vec![None; self.slots.len()];
        let mut report = TypeGraphLowerSnapshotReport::default();
        for group in groups.into_iter().filter(|group| !group.slots.is_empty()) {
            match group.lower_candidates.as_slice() {
                [] => {
                    if group.has_upper_requirements {
                        report.upper_only_groups += 1;
                        report.upper_only_slots += group.slots.len();
                    } else {
                        report.groups_without_bounds += 1;
                        report.slots_without_bounds += group.slots.len();
                    }
                }
                [candidate] => {
                    report.solved_groups += 1;
                    report.solved_slots += group.slots.len();
                    if runtime_type_is_closed(candidate) {
                        report.closed_solved_slots += group.slots.len();
                    } else {
                        report.open_solved_slots += group.slots.len();
                    }
                    for slot in group.slots {
                        slot_candidates[slot.0] = Some(candidate.clone());
                    }
                }
                candidates => {
                    report.conflicting_lower_groups += 1;
                    report.conflicting_lower_slots += group.slots.len();
                    if candidates.iter().all(runtime_type_is_closed) {
                        report.closed_conflicting_lower_slots += group.slots.len();
                    }
                }
            }
        }

        for edge in &self.edges {
            if !edge_kind_checks_direct_mismatch(edge.kind) {
                continue;
            }
            match (
                slot_candidates[edge.source.0].as_ref(),
                slot_candidates[edge.target.0].as_ref(),
            ) {
                (Some(left), Some(right)) => {
                    report.lower_solution_checked_edges += 1;
                    if left != right {
                        report.lower_solution_mismatched_edges += 1;
                    }
                }
                _ => {
                    report.lower_solution_unresolved_edges += 1;
                }
            }
        }

        TypeGraphLowerSolution {
            slot_candidates,
            report,
        }
    }

    pub(super) fn solve_upper_supplements(
        &self,
        lower_solution: &TypeGraphLowerSolution,
    ) -> TypeGraphUpperSupplementSolution {
        let mut slot_candidates = vec![None; self.slots.len()];
        let mut report = TypeGraphUpperSupplementReport::default();
        for slot in &self.slots {
            let lower_candidate = lower_solution.slot_candidates[slot.id.0].as_ref();
            let mut supplement_candidates = Vec::new();
            for evidence in &slot.upper_requirements {
                let Some(upper) = self.bounds_evidence[evidence.0]
                    .projection
                    .upper_runtime_type()
                else {
                    continue;
                };
                report.upper_requirements += 1;
                if let Some(lower) = lower_candidate {
                    report.checked_against_lower += 1;
                    if runtime_lower_satisfies_upper(lower, &upper) {
                        report.satisfied_by_lower += 1;
                    } else {
                        report.mismatched_with_lower += 1;
                    }
                } else {
                    push_runtime_upper_supplement_candidate(&mut supplement_candidates, upper);
                }
            }
            if lower_candidate.is_some() {
                continue;
            }
            match supplement_candidates.as_slice() {
                [] => {}
                [candidate] => {
                    report.supplemented_slots += 1;
                    if runtime_type_is_closed(candidate) {
                        report.closed_supplemented_slots += 1;
                    } else {
                        report.open_supplemented_slots += 1;
                    }
                    slot_candidates[slot.id.0] = Some(candidate.clone());
                }
                _ => {
                    report.ambiguous_supplement_slots += 1;
                }
            }
        }

        TypeGraphUpperSupplementSolution {
            slot_candidates,
            report,
        }
    }

    pub(super) fn solve_final_defaults(
        &self,
        lower_solution: &TypeGraphLowerSolution,
        upper_solution: &TypeGraphUpperSupplementSolution,
    ) -> FillHolesReport {
        let mut report = FillHolesReport::default();
        for slot in &self.slots {
            if lower_solution.slot_candidates[slot.id.0].is_some()
                || upper_solution.slot_candidates[slot.id.0].is_some()
            {
                continue;
            }
            collect_final_default_holes(&slot.ty, &mut report);
        }
        report
    }

    pub(super) fn solve_type_var_lowers(&self) -> TypeGraphTypeVarLowerSolution {
        let mut report = TypeGraphTypeVarLowerReport {
            evidence: self.type_var_lower_evidence.len(),
            ..TypeGraphTypeVarLowerReport::default()
        };
        let mut by_scoped_var: BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>> =
            BTreeMap::new();
        for evidence in &self.type_var_lower_evidence {
            if core_type_is_bottom_like_lower(&evidence.ty) {
                report.bottom_like_exclusions += 1;
                continue;
            }
            if core_type_is_identity_lower_for_var(&evidence.var, &evidence.ty) {
                report.identity_lower_exclusions += 1;
                continue;
            }
            let candidates = by_scoped_var
                .entry(TypeGraphScopedTypeVar {
                    scope: evidence.scope,
                    var: evidence.var.clone(),
                })
                .or_default();
            push_type_var_lower_candidate(candidates, evidence);
        }
        solve_structural_type_var_lowers(&mut report, &mut by_scoped_var);
        let vars = type_var_lower_vars_by_name(&by_scoped_var);
        report.vars = vars.len();
        report.scoped_vars = by_scoped_var.len();
        report.vars_used_in_multiple_scopes = vars.values().filter(|count| **count > 1).count();
        let mut solved_by_scope =
            BTreeMap::<TypeGraphTypeVarScope, BTreeMap<typed_ir::TypeVar, typed_ir::Type>>::new();
        for (scoped_var, candidates) in &by_scoped_var {
            match candidates.as_slice() {
                [] => {}
                [candidate] => {
                    report.solved_vars += 1;
                    solved_by_scope
                        .entry(scoped_var.scope)
                        .or_default()
                        .insert(scoped_var.var.clone(), candidate.ty.clone());
                    if !core_type_has_vars(&candidate.ty) {
                        report.closed_solved_vars += 1;
                    }
                }
                _ => {
                    report.conflicting_vars += 1;
                    let sources = candidates.iter().fold(
                        TypeGraphTypeVarEvidenceSources::default(),
                        |mut sources, candidate| {
                            sources.merge(candidate.sources);
                            sources
                        },
                    );
                    if candidates
                        .iter()
                        .all(|candidate| !core_type_has_vars(&candidate.ty))
                    {
                        report.closed_conflicting_vars += 1;
                    }
                    if sources.apply_evidence_substitution {
                        report.conflicting_vars_with_apply_substitution += 1;
                    }
                    if sources.principal_substitution_candidate {
                        report.conflicting_vars_with_principal_candidate += 1;
                    }
                    if sources.principal_elaboration_substitution {
                        report.conflicting_vars_with_principal_elaboration += 1;
                    }
                    if sources.type_instantiation {
                        report.conflicting_vars_with_type_instantiation += 1;
                    }
                    if sources.role_associated_resolution {
                        report.conflicting_vars_with_role_associated_resolution += 1;
                    }
                    if sources.structural_lower_decomposition {
                        report.conflicting_vars_with_structural_decomposition += 1;
                    }
                    if sources.kind_count() > 1 {
                        report.conflicting_vars_with_mixed_sources += 1;
                    }
                }
            }
        }
        let mut recursive_substitutions_by_scope = solved_by_scope;
        for substitutions in recursive_substitutions_by_scope.values_mut() {
            retain_acyclic_type_substitutions(substitutions);
            close_type_substitution_map_recursively(substitutions);
        }
        report_recursive_type_var_substitutions(
            &mut report,
            &by_scoped_var,
            &recursive_substitutions_by_scope,
        );
        TypeGraphTypeVarLowerSolution {
            substitutions_by_scope: recursive_substitutions_by_scope,
            report,
        }
    }

    #[cfg(test)]
    pub(super) fn type_var_lower_report(&self) -> TypeGraphTypeVarLowerReport {
        self.solve_type_var_lowers().report
    }

    fn push_slot(&mut self, kind: TypeGraphSlotKind, ty: RuntimeType) -> TypeGraphSlotId {
        let id = TypeGraphSlotId(self.slots.len());
        self.slots.push(TypeGraphSlot {
            id,
            kind,
            ty,
            lower_evidence: Vec::new(),
            upper_requirements: Vec::new(),
        });
        id
    }

    fn push_edge(
        &mut self,
        kind: TypeGraphEdgeKind,
        source: TypeGraphSlotId,
        target: TypeGraphSlotId,
        provenance: TypeGraphEdgeProvenance,
    ) {
        let id = TypeGraphEdgeId(self.edges.len());
        self.edges.push(TypeGraphEdge {
            id,
            kind,
            source,
            target,
            provenance,
        });
        if edge_kind_checks_direct_mismatch(kind) {
            let left = &self.slots[source.0].ty;
            let right = &self.slots[target.0].ty;
            if runtime_type_is_closed(left) && runtime_type_is_closed(right) && left != right {
                self.conflicts.push(TypeGraphConflict {
                    kind: TypeGraphConflictKind::DirectMismatch,
                    edge: id,
                    left: source,
                    right: target,
                });
            }
        }
    }

    fn push_bounds_evidence(
        &mut self,
        role: TypeGraphBoundsEvidenceRole,
        target: TypeGraphSlotId,
        bounds: &typed_ir::TypeBounds,
    ) {
        let projection = classify_bounds_projection(bounds);
        let has_lower = projection.has_lower_candidate();
        let has_upper = projection.has_upper_requirement();
        let id = TypeGraphBoundsEvidenceId(self.bounds_evidence.len());
        self.bounds_evidence.push(TypeGraphBoundsEvidence {
            role,
            target,
            projection,
        });
        if has_lower {
            self.slots[target.0].lower_evidence.push(id);
        }
        if has_upper {
            self.slots[target.0].upper_requirements.push(id);
        }
    }

    fn push_runtime_lower_evidence(
        &mut self,
        role: TypeGraphBoundsEvidenceRole,
        target: TypeGraphSlotId,
        ty: RuntimeType,
    ) {
        if runtime_type_is_bottom_like_lower(&ty) {
            return;
        }
        let id = TypeGraphBoundsEvidenceId(self.bounds_evidence.len());
        self.bounds_evidence.push(TypeGraphBoundsEvidence {
            role,
            target,
            projection: TypeGraphBoundsProjection::RuntimeLower { ty },
        });
        self.slots[target.0].lower_evidence.push(id);
    }

    #[cfg(test)]
    fn push_type_substitution_lower_evidence(
        &mut self,
        scope: TypeGraphTypeVarScope,
        source: TypeGraphTypeVarEvidenceSource,
        substitution: &typed_ir::TypeSubstitution,
    ) {
        self.push_type_substitution_lower_evidence_with_origin(scope, source, substitution, None);
    }

    fn push_type_substitution_lower_evidence_with_origin(
        &mut self,
        scope: TypeGraphTypeVarScope,
        source: TypeGraphTypeVarEvidenceSource,
        substitution: &typed_ir::TypeSubstitution,
        origin: Option<String>,
    ) {
        self.type_var_lower_evidence
            .push(TypeGraphTypeVarLowerEvidence {
                scope,
                source,
                origin,
                var: substitution.var.clone(),
                ty: substitution.ty.clone(),
            });
    }

    fn push_principal_candidate_lower_evidence(
        &mut self,
        scope: TypeGraphTypeVarScope,
        candidate: &typed_ir::PrincipalSubstitutionCandidate,
        origin: Option<String>,
    ) {
        if !matches!(
            candidate.relation,
            typed_ir::PrincipalCandidateRelation::Lower
                | typed_ir::PrincipalCandidateRelation::Exact
        ) {
            return;
        }
        self.type_var_lower_evidence
            .push(TypeGraphTypeVarLowerEvidence {
                scope,
                source: TypeGraphTypeVarEvidenceSource::PrincipalSubstitutionCandidate,
                origin,
                var: candidate.var.clone(),
                ty: candidate.ty.clone(),
            });
    }

    fn fresh_type_var_scope(&mut self) -> TypeGraphTypeVarScope {
        let scope = TypeGraphTypeVarScope(self.next_type_var_scope);
        self.next_type_var_scope += 1;
        scope
    }

    fn push_role_bounds_evidence(
        &mut self,
        source: TypeGraphRoleBoundsEvidenceSource,
        bounds: &typed_ir::TypeBounds,
    ) {
        self.role_bounds_evidence.push(TypeGraphRoleBoundsEvidence {
            source,
            projection: classify_bounds_projection(bounds),
        });
    }

    fn push_role_associated_resolution_evidence(
        &mut self,
        status: TypeGraphRoleAssociatedResolutionStatus,
        projected_type_vars: usize,
    ) {
        self.role_associated_resolutions
            .push(TypeGraphRoleAssociatedResolutionEvidence {
                status,
                projected_type_vars,
            });
    }

    fn push_role_associated_type_var_lower_evidence(
        &mut self,
        scope: TypeGraphTypeVarScope,
        bounds: &typed_ir::TypeBounds,
        resolved: &typed_ir::Type,
        origin: String,
    ) -> usize {
        let Some(template) = lower_core_candidate_from_bounds(bounds) else {
            return 0;
        };
        let mut params = BTreeSet::new();
        collect_type_vars(&template, &mut params);
        if params.is_empty() {
            return 0;
        }
        let mut substitutions = BTreeMap::new();
        infer_type_substitutions(&template, resolved, &params, &mut substitutions);
        if substitute_type(&template, &substitutions) != *resolved {
            return 0;
        }
        let mut projected = 0;
        for (var, ty) in substitutions {
            self.type_var_lower_evidence
                .push(TypeGraphTypeVarLowerEvidence {
                    scope,
                    source: TypeGraphTypeVarEvidenceSource::RoleAssociatedResolution,
                    origin: Some(origin.clone()),
                    var,
                    ty,
                });
            projected += 1;
        }
        projected
    }

    fn push_role_associated_impl_substitutions(
        &mut self,
        scope: TypeGraphTypeVarScope,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
        origin: String,
    ) -> usize {
        let mut projected = 0;
        for (var, ty) in substitutions {
            if core_type_is_bottom_like_lower(ty) || core_type_is_identity_lower_for_var(var, ty) {
                continue;
            }
            self.type_var_lower_evidence
                .push(TypeGraphTypeVarLowerEvidence {
                    scope,
                    source: TypeGraphTypeVarEvidenceSource::RoleAssociatedResolution,
                    origin: Some(origin.clone()),
                    var: var.clone(),
                    ty: ty.clone(),
                });
            projected += 1;
        }
        projected
    }

    fn report(&self) -> TypeGraphBuildReport {
        let mut binding_slots = 0;
        let mut apply_edges = 0;
        let mut local_name_bytes = 0;
        let mut root_index_sum = 0;
        let mut self_edges = 0;
        let mut direct_mismatches = 0;
        let mut direct_mismatch_equal_edges = 0;
        let mut direct_mismatch_apply_edges = 0;
        let mut direct_mismatch_let_edges = 0;
        let mut slots_with_lower_evidence = 0;
        let mut slots_with_closed_lower_evidence = 0;
        let mut slots_with_multiple_lower_evidence = 0;
        let mut slots_with_upper_requirements = 0;
        let mut slots_with_only_upper_requirements = 0;
        for slot in &self.slots {
            let _id = slot.id;
            if !slot.lower_evidence.is_empty() {
                slots_with_lower_evidence += 1;
                if slot.lower_evidence.len() > 1 {
                    slots_with_multiple_lower_evidence += 1;
                }
                if slot.lower_evidence.iter().any(|evidence| {
                    self.bounds_evidence[evidence.0]
                        .projection
                        .lower_runtime_type()
                        .is_some_and(|ty| runtime_type_is_closed(&ty))
                }) {
                    slots_with_closed_lower_evidence += 1;
                }
            }
            if !slot.upper_requirements.is_empty() {
                slots_with_upper_requirements += 1;
                if slot.lower_evidence.is_empty() {
                    slots_with_only_upper_requirements += 1;
                }
            }
            match &slot.kind {
                TypeGraphSlotKind::BindingScheme { binding }
                | TypeGraphSlotKind::BindingBody { binding } => {
                    binding_slots += 1;
                    local_name_bytes += binding.segments.len();
                }
                TypeGraphSlotKind::RootExpr { index } => {
                    root_index_sum += index;
                }
                TypeGraphSlotKind::LambdaParam { name }
                | TypeGraphSlotKind::LambdaResult { name } => {
                    local_name_bytes += name.0.len();
                }
                TypeGraphSlotKind::Expr
                | TypeGraphSlotKind::Pattern
                | TypeGraphSlotKind::ApplyCallee
                | TypeGraphSlotKind::ApplyArg
                | TypeGraphSlotKind::ApplyResult
                | TypeGraphSlotKind::ApplyEvidenceCallee
                | TypeGraphSlotKind::ApplyEvidenceArg
                | TypeGraphSlotKind::ApplyEvidenceResult
                | TypeGraphSlotKind::FunctionParam
                | TypeGraphSlotKind::FunctionResult
                | TypeGraphSlotKind::LetValue
                | TypeGraphSlotKind::LetPattern => {}
            }
        }
        for edge in &self.edges {
            let _id = edge.id;
            if matches!(
                edge.kind,
                TypeGraphEdgeKind::ApplyCallee
                    | TypeGraphEdgeKind::ApplyArg
                    | TypeGraphEdgeKind::ApplyResult
                    | TypeGraphEdgeKind::ApplyEvidence
            ) {
                apply_edges += 1;
            }
            if edge.source == edge.target {
                self_edges += 1;
            }
        }
        for conflict in &self.conflicts {
            if matches!(conflict.kind, TypeGraphConflictKind::DirectMismatch) {
                direct_mismatches += 1;
                let edge = &self.edges[conflict.edge.0];
                match edge.provenance {
                    TypeGraphEdgeProvenance::ApplyCallee
                    | TypeGraphEdgeProvenance::ApplyArg
                    | TypeGraphEdgeProvenance::ApplyResult
                    | TypeGraphEdgeProvenance::ApplyFunctionParam
                    | TypeGraphEdgeProvenance::ApplyFunctionResult
                    | TypeGraphEdgeProvenance::ApplyEvidence { .. } => {
                        direct_mismatch_apply_edges += 1;
                    }
                    TypeGraphEdgeProvenance::LetValue
                    | TypeGraphEdgeProvenance::LetPattern
                    | TypeGraphEdgeProvenance::LetValuePattern => {
                        direct_mismatch_let_edges += 1;
                    }
                    TypeGraphEdgeProvenance::BindingSchemeBody
                    | TypeGraphEdgeProvenance::BindingBodyExpr
                    | TypeGraphEdgeProvenance::RootExpr { .. }
                    | TypeGraphEdgeProvenance::LambdaParam
                    | TypeGraphEdgeProvenance::LambdaResult
                    | TypeGraphEdgeProvenance::IfBranch
                    | TypeGraphEdgeProvenance::MatchArmBody
                    | TypeGraphEdgeProvenance::BlockTail
                    | TypeGraphEdgeProvenance::WrapperExpr
                    | TypeGraphEdgeProvenance::RecordPatternField
                    | TypeGraphEdgeProvenance::OrPattern
                    | TypeGraphEdgeProvenance::AsPattern => {
                        direct_mismatch_equal_edges += 1;
                    }
                }
            }
            if conflict.left == conflict.right {
                self_edges += 1;
            }
        }
        let mut bounds_evidence = 0;
        let mut bounds_lower_candidates = 0;
        let mut bounds_exact_candidates = 0;
        let mut bounds_upper_requirements = 0;
        let mut bounds_upper_only_dependencies = 0;
        let mut bounds_bottom_like_exclusions = 0;
        let mut bounds_empty = 0;
        let mut bounds_lower_upper_diverged = 0;
        let mut bounds_lower_visible_diverged = 0;
        let mut apply_callee_bounds = 0;
        let mut apply_arg_bounds = 0;
        let mut apply_result_bounds = 0;
        let mut handler_result_bounds = 0;
        let mut role_bounds_evidence = 0;
        let mut role_input_lower_candidates = 0;
        let mut role_associated_lower_candidates = 0;
        let mut role_upper_only_dependencies = 0;
        let mut role_bottom_like_exclusions = 0;
        let mut role_associated_resolution_attempts = 0;
        let mut role_associated_resolution_missing_inputs = 0;
        let mut role_associated_resolution_missing_impls = 0;
        let mut role_associated_resolution_ambiguous_impls = 0;
        let mut role_associated_resolution_resolved = 0;
        let mut role_associated_resolution_projected_type_vars = 0;
        for evidence in &self.bounds_evidence {
            let _target = evidence.target;
            bounds_evidence += 1;
            match evidence.role {
                TypeGraphBoundsEvidenceRole::ApplyCallee => apply_callee_bounds += 1,
                TypeGraphBoundsEvidenceRole::ApplyArg => apply_arg_bounds += 1,
                TypeGraphBoundsEvidenceRole::ApplyResult => apply_result_bounds += 1,
                TypeGraphBoundsEvidenceRole::HandlerResult => handler_result_bounds += 1,
            }
            match &evidence.projection {
                TypeGraphBoundsProjection::Empty => {
                    bounds_empty += 1;
                }
                TypeGraphBoundsProjection::LowerOnly { .. } => {
                    bounds_lower_candidates += 1;
                }
                TypeGraphBoundsProjection::Exact { .. } => {
                    bounds_lower_candidates += 1;
                    bounds_exact_candidates += 1;
                    bounds_upper_requirements += 1;
                }
                TypeGraphBoundsProjection::LowerAndUpper {
                    lower,
                    upper,
                    visible,
                } => {
                    bounds_lower_candidates += 1;
                    bounds_upper_requirements += 1;
                    if lower != upper {
                        bounds_lower_upper_diverged += 1;
                    }
                    if visible.as_ref().is_some_and(|visible| visible != lower) {
                        bounds_lower_visible_diverged += 1;
                    }
                }
                TypeGraphBoundsProjection::UpperOnly { .. } => {
                    bounds_upper_requirements += 1;
                    bounds_upper_only_dependencies += 1;
                }
                TypeGraphBoundsProjection::RuntimeLower { .. } => {
                    bounds_lower_candidates += 1;
                }
                TypeGraphBoundsProjection::BottomLikeLower { upper, .. } => {
                    bounds_bottom_like_exclusions += 1;
                    if upper.is_some() {
                        bounds_upper_requirements += 1;
                    }
                }
            }
        }
        for evidence in &self.role_bounds_evidence {
            role_bounds_evidence += 1;
            if evidence.projection.has_lower_candidate() {
                match evidence.source {
                    TypeGraphRoleBoundsEvidenceSource::RequirementInput => {
                        role_input_lower_candidates += 1;
                    }
                    TypeGraphRoleBoundsEvidenceSource::RequirementAssociated => {
                        role_associated_lower_candidates += 1;
                    }
                }
            }
            if matches!(
                evidence.projection,
                TypeGraphBoundsProjection::UpperOnly { .. }
            ) {
                role_upper_only_dependencies += 1;
            }
            if matches!(
                evidence.projection,
                TypeGraphBoundsProjection::BottomLikeLower { .. }
            ) {
                role_bottom_like_exclusions += 1;
            }
        }
        for evidence in &self.role_associated_resolutions {
            role_associated_resolution_attempts += 1;
            role_associated_resolution_projected_type_vars += evidence.projected_type_vars;
            match evidence.status {
                TypeGraphRoleAssociatedResolutionStatus::MissingInputLower => {
                    role_associated_resolution_missing_inputs += 1;
                }
                TypeGraphRoleAssociatedResolutionStatus::MissingImpl => {
                    role_associated_resolution_missing_impls += 1;
                }
                TypeGraphRoleAssociatedResolutionStatus::AmbiguousImpl => {
                    role_associated_resolution_ambiguous_impls += 1;
                }
                TypeGraphRoleAssociatedResolutionStatus::Resolved => {
                    role_associated_resolution_resolved += 1;
                }
            }
        }
        TypeGraphBuildReport {
            slots: self.slots.len(),
            edges: self.edges.len(),
            conflicts: self.conflicts.len(),
            binding_slots,
            apply_edges,
            direct_mismatches,
            direct_mismatch_equal_edges,
            direct_mismatch_apply_edges,
            direct_mismatch_let_edges,
            root_index_sum,
            local_name_bytes,
            self_edges,
            bounds_evidence,
            bounds_lower_candidates,
            bounds_exact_candidates,
            bounds_upper_requirements,
            bounds_upper_only_dependencies,
            bounds_bottom_like_exclusions,
            bounds_empty,
            bounds_lower_upper_diverged,
            bounds_lower_visible_diverged,
            apply_callee_bounds,
            apply_arg_bounds,
            apply_result_bounds,
            handler_result_bounds,
            slots_with_lower_evidence,
            slots_with_closed_lower_evidence,
            slots_with_multiple_lower_evidence,
            slots_with_upper_requirements,
            slots_with_only_upper_requirements,
            role_bounds_evidence,
            role_input_lower_candidates,
            role_associated_lower_candidates,
            role_upper_only_dependencies,
            role_bottom_like_exclusions,
            role_associated_resolution_attempts,
            role_associated_resolution_missing_inputs,
            role_associated_resolution_missing_impls,
            role_associated_resolution_ambiguous_impls,
            role_associated_resolution_resolved,
            role_associated_resolution_projected_type_vars,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct TypeGraphSlotId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct TypeGraphEdgeId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct TypeGraphBoundsEvidenceId(usize);

#[derive(Debug, Clone)]
pub(super) struct TypeGraphSlot {
    pub(super) id: TypeGraphSlotId,
    pub(super) kind: TypeGraphSlotKind,
    pub(super) ty: RuntimeType,
    lower_evidence: Vec<TypeGraphBoundsEvidenceId>,
    upper_requirements: Vec<TypeGraphBoundsEvidenceId>,
}

#[derive(Debug, Clone)]
pub(super) enum TypeGraphSlotKind {
    BindingScheme { binding: typed_ir::Path },
    BindingBody { binding: typed_ir::Path },
    RootExpr { index: usize },
    Expr,
    Pattern,
    ApplyCallee,
    ApplyArg,
    ApplyResult,
    ApplyEvidenceCallee,
    ApplyEvidenceArg,
    ApplyEvidenceResult,
    FunctionParam,
    FunctionResult,
    LambdaParam { name: typed_ir::Name },
    LambdaResult { name: typed_ir::Name },
    LetValue,
    LetPattern,
}

#[derive(Debug, Clone)]
pub(super) struct TypeGraphEdge {
    id: TypeGraphEdgeId,
    pub(super) kind: TypeGraphEdgeKind,
    pub(super) source: TypeGraphSlotId,
    pub(super) target: TypeGraphSlotId,
    provenance: TypeGraphEdgeProvenance,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeGraphEdgeKind {
    Equal,
    ApplyCallee,
    ApplyArg,
    ApplyResult,
    ApplyEvidence,
    LambdaParam,
    LambdaResult,
    LetValuePattern,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeGraphEdgeProvenance {
    BindingSchemeBody,
    BindingBodyExpr,
    RootExpr { index: usize },
    LambdaParam,
    LambdaResult,
    ApplyCallee,
    ApplyArg,
    ApplyResult,
    ApplyFunctionParam,
    ApplyFunctionResult,
    ApplyEvidence { role: TypeGraphBoundsEvidenceRole },
    IfBranch,
    MatchArmBody,
    BlockTail,
    WrapperExpr,
    LetValue,
    LetPattern,
    LetValuePattern,
    RecordPatternField,
    OrPattern,
    AsPattern,
}

#[derive(Debug, Clone)]
pub(super) struct TypeGraphConflict {
    pub(super) kind: TypeGraphConflictKind,
    edge: TypeGraphEdgeId,
    pub(super) left: TypeGraphSlotId,
    pub(super) right: TypeGraphSlotId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeGraphConflictKind {
    DirectMismatch,
}

#[derive(Debug, Clone)]
struct TypeGraphBoundsEvidence {
    role: TypeGraphBoundsEvidenceRole,
    target: TypeGraphSlotId,
    projection: TypeGraphBoundsProjection,
}

#[derive(Debug, Clone)]
struct TypeGraphTypeVarLowerEvidence {
    scope: TypeGraphTypeVarScope,
    source: TypeGraphTypeVarEvidenceSource,
    origin: Option<String>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct TypeGraphTypeVarScope(usize);

impl TypeGraphTypeVarScope {
    pub(super) fn from_index(index: usize) -> Self {
        Self(index)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct TypeGraphScopedTypeVar {
    scope: TypeGraphTypeVarScope,
    var: typed_ir::TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeGraphTypeVarCandidate {
    ty: typed_ir::Type,
    sources: TypeGraphTypeVarEvidenceSources,
    origins: Vec<String>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct TypeGraphTypeVarEvidenceSources {
    apply_evidence_substitution: bool,
    principal_substitution_candidate: bool,
    principal_elaboration_substitution: bool,
    type_instantiation: bool,
    role_associated_resolution: bool,
    structural_lower_decomposition: bool,
}

impl TypeGraphTypeVarEvidenceSources {
    fn from_source(source: TypeGraphTypeVarEvidenceSource) -> Self {
        let mut sources = Self::default();
        sources.insert(source);
        sources
    }

    fn insert(&mut self, source: TypeGraphTypeVarEvidenceSource) {
        match source {
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution => {
                self.apply_evidence_substitution = true;
            }
            TypeGraphTypeVarEvidenceSource::PrincipalSubstitutionCandidate => {
                self.principal_substitution_candidate = true;
            }
            TypeGraphTypeVarEvidenceSource::PrincipalElaborationSubstitution => {
                self.principal_elaboration_substitution = true;
            }
            TypeGraphTypeVarEvidenceSource::TypeInstantiation => {
                self.type_instantiation = true;
            }
            TypeGraphTypeVarEvidenceSource::RoleAssociatedResolution => {
                self.role_associated_resolution = true;
            }
            TypeGraphTypeVarEvidenceSource::StructuralLowerDecomposition => {
                self.structural_lower_decomposition = true;
            }
        }
    }

    fn merge(&mut self, other: Self) {
        self.apply_evidence_substitution |= other.apply_evidence_substitution;
        self.principal_substitution_candidate |= other.principal_substitution_candidate;
        self.principal_elaboration_substitution |= other.principal_elaboration_substitution;
        self.type_instantiation |= other.type_instantiation;
        self.role_associated_resolution |= other.role_associated_resolution;
        self.structural_lower_decomposition |= other.structural_lower_decomposition;
    }

    fn kind_count(self) -> usize {
        self.apply_evidence_substitution as usize
            + self.principal_substitution_candidate as usize
            + self.principal_elaboration_substitution as usize
            + self.type_instantiation as usize
            + self.role_associated_resolution as usize
            + self.structural_lower_decomposition as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeGraphTypeVarEvidenceSource {
    ApplyEvidenceSubstitution,
    PrincipalSubstitutionCandidate,
    PrincipalElaborationSubstitution,
    TypeInstantiation,
    RoleAssociatedResolution,
    StructuralLowerDecomposition,
}

#[derive(Debug, Clone)]
struct TypeGraphRoleBoundsEvidence {
    source: TypeGraphRoleBoundsEvidenceSource,
    projection: TypeGraphBoundsProjection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeGraphRoleBoundsEvidenceSource {
    RequirementInput,
    RequirementAssociated,
}

#[derive(Debug, Clone)]
struct TypeGraphRoleAssociatedResolutionEvidence {
    status: TypeGraphRoleAssociatedResolutionStatus,
    projected_type_vars: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeGraphRoleAssociatedResolutionStatus {
    MissingInputLower,
    MissingImpl,
    AmbiguousImpl,
    Resolved,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeGraphBoundsEvidenceRole {
    ApplyCallee,
    ApplyArg,
    ApplyResult,
    HandlerResult,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TypeGraphBoundsProjection {
    Empty,
    LowerOnly {
        lower: typed_ir::Type,
    },
    Exact {
        ty: typed_ir::Type,
    },
    LowerAndUpper {
        lower: typed_ir::Type,
        upper: typed_ir::Type,
        visible: Option<typed_ir::Type>,
    },
    UpperOnly {
        upper: typed_ir::Type,
    },
    RuntimeLower {
        ty: RuntimeType,
    },
    BottomLikeLower {
        lower: typed_ir::Type,
        upper: Option<typed_ir::Type>,
    },
}

impl TypeGraphBoundsProjection {
    fn has_lower_candidate(&self) -> bool {
        matches!(
            self,
            TypeGraphBoundsProjection::LowerOnly { .. }
                | TypeGraphBoundsProjection::Exact { .. }
                | TypeGraphBoundsProjection::LowerAndUpper { .. }
                | TypeGraphBoundsProjection::RuntimeLower { .. }
        )
    }

    fn has_upper_requirement(&self) -> bool {
        matches!(
            self,
            TypeGraphBoundsProjection::Exact { .. }
                | TypeGraphBoundsProjection::LowerAndUpper { .. }
                | TypeGraphBoundsProjection::UpperOnly { .. }
                | TypeGraphBoundsProjection::BottomLikeLower { upper: Some(_), .. }
        )
    }

    fn lower_runtime_type(&self) -> Option<RuntimeType> {
        match self {
            TypeGraphBoundsProjection::LowerOnly { lower }
            | TypeGraphBoundsProjection::LowerAndUpper { lower, .. } => {
                Some(RuntimeType::core(lower.clone()))
            }
            TypeGraphBoundsProjection::Exact { ty } => Some(RuntimeType::core(ty.clone())),
            TypeGraphBoundsProjection::RuntimeLower { ty } => Some(ty.clone()),
            TypeGraphBoundsProjection::Empty
            | TypeGraphBoundsProjection::UpperOnly { .. }
            | TypeGraphBoundsProjection::BottomLikeLower { .. } => None,
        }
    }

    fn upper_runtime_type(&self) -> Option<RuntimeType> {
        match self {
            TypeGraphBoundsProjection::Exact { ty } => Some(RuntimeType::core(ty.clone())),
            TypeGraphBoundsProjection::LowerAndUpper { upper, .. }
            | TypeGraphBoundsProjection::UpperOnly { upper } => {
                Some(RuntimeType::core(upper.clone()))
            }
            TypeGraphBoundsProjection::BottomLikeLower {
                upper: Some(upper), ..
            } => Some(RuntimeType::core(upper.clone())),
            TypeGraphBoundsProjection::Empty
            | TypeGraphBoundsProjection::LowerOnly { .. }
            | TypeGraphBoundsProjection::RuntimeLower { .. }
            | TypeGraphBoundsProjection::BottomLikeLower { upper: None, .. } => None,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraphBuildReport {
    pub(super) slots: usize,
    pub(super) edges: usize,
    pub(super) conflicts: usize,
    pub(super) binding_slots: usize,
    pub(super) apply_edges: usize,
    pub(super) direct_mismatches: usize,
    pub(super) direct_mismatch_equal_edges: usize,
    pub(super) direct_mismatch_apply_edges: usize,
    pub(super) direct_mismatch_let_edges: usize,
    pub(super) root_index_sum: usize,
    pub(super) local_name_bytes: usize,
    pub(super) self_edges: usize,
    pub(super) bounds_evidence: usize,
    pub(super) bounds_lower_candidates: usize,
    pub(super) bounds_exact_candidates: usize,
    pub(super) bounds_upper_requirements: usize,
    pub(super) bounds_upper_only_dependencies: usize,
    pub(super) bounds_bottom_like_exclusions: usize,
    pub(super) bounds_empty: usize,
    pub(super) bounds_lower_upper_diverged: usize,
    pub(super) bounds_lower_visible_diverged: usize,
    pub(super) apply_callee_bounds: usize,
    pub(super) apply_arg_bounds: usize,
    pub(super) apply_result_bounds: usize,
    pub(super) handler_result_bounds: usize,
    pub(super) slots_with_lower_evidence: usize,
    pub(super) slots_with_closed_lower_evidence: usize,
    pub(super) slots_with_multiple_lower_evidence: usize,
    pub(super) slots_with_upper_requirements: usize,
    pub(super) slots_with_only_upper_requirements: usize,
    pub(super) role_bounds_evidence: usize,
    pub(super) role_input_lower_candidates: usize,
    pub(super) role_associated_lower_candidates: usize,
    pub(super) role_upper_only_dependencies: usize,
    pub(super) role_bottom_like_exclusions: usize,
    pub(super) role_associated_resolution_attempts: usize,
    pub(super) role_associated_resolution_missing_inputs: usize,
    pub(super) role_associated_resolution_missing_impls: usize,
    pub(super) role_associated_resolution_ambiguous_impls: usize,
    pub(super) role_associated_resolution_resolved: usize,
    pub(super) role_associated_resolution_projected_type_vars: usize,
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraphLowerSnapshotReport {
    pub(super) solved_slots: usize,
    pub(super) closed_solved_slots: usize,
    pub(super) open_solved_slots: usize,
    pub(super) conflicting_lower_slots: usize,
    pub(super) closed_conflicting_lower_slots: usize,
    pub(super) upper_only_slots: usize,
    pub(super) slots_without_bounds: usize,
    pub(super) solved_groups: usize,
    pub(super) conflicting_lower_groups: usize,
    pub(super) upper_only_groups: usize,
    pub(super) groups_without_bounds: usize,
    pub(super) lower_solution_checked_edges: usize,
    pub(super) lower_solution_mismatched_edges: usize,
    pub(super) lower_solution_unresolved_edges: usize,
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraphUpperSupplementReport {
    pub(super) upper_requirements: usize,
    pub(super) checked_against_lower: usize,
    pub(super) satisfied_by_lower: usize,
    pub(super) mismatched_with_lower: usize,
    pub(super) supplemented_slots: usize,
    pub(super) closed_supplemented_slots: usize,
    pub(super) open_supplemented_slots: usize,
    pub(super) ambiguous_supplement_slots: usize,
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraphTypeVarLowerReport {
    pub(super) evidence: usize,
    pub(super) derived_structural_lower_evidence: usize,
    pub(super) vars: usize,
    pub(super) scoped_vars: usize,
    pub(super) vars_used_in_multiple_scopes: usize,
    pub(super) solved_vars: usize,
    pub(super) closed_solved_vars: usize,
    pub(super) recursive_substitution_vars: usize,
    pub(super) closed_after_recursive_substitution_vars: usize,
    pub(super) residual_open_vars_after_recursive_substitution: usize,
    pub(super) residual_open_recursive_cycle_vars_after_substitution: usize,
    pub(super) residual_open_missing_substitution_vars_after_substitution: usize,
    pub(super) residual_open_after_recursive_substitution_with_apply_substitution: usize,
    pub(super) residual_open_after_recursive_substitution_with_principal_candidate: usize,
    pub(super) residual_open_after_recursive_substitution_with_principal_elaboration: usize,
    pub(super) residual_open_after_recursive_substitution_with_type_instantiation: usize,
    pub(super) residual_open_after_recursive_substitution_with_role_associated_resolution: usize,
    pub(super) residual_open_after_recursive_substitution_with_structural_decomposition: usize,
    pub(super) residual_open_after_recursive_substitution_with_mixed_sources: usize,
    pub(super) residual_open_samples: Vec<String>,
    pub(super) structural_decomposition_iterations: usize,
    pub(super) structural_decomposition_candidate_visits: usize,
    pub(super) structural_decomposition_addition_attempts: usize,
    pub(super) conflicting_vars: usize,
    pub(super) closed_conflicting_vars: usize,
    pub(super) conflicting_vars_with_apply_substitution: usize,
    pub(super) conflicting_vars_with_principal_candidate: usize,
    pub(super) conflicting_vars_with_principal_elaboration: usize,
    pub(super) conflicting_vars_with_type_instantiation: usize,
    pub(super) conflicting_vars_with_role_associated_resolution: usize,
    pub(super) conflicting_vars_with_structural_decomposition: usize,
    pub(super) conflicting_vars_with_mixed_sources: usize,
    pub(super) bottom_like_exclusions: usize,
    pub(super) identity_lower_exclusions: usize,
}

impl TypeGraphTypeVarLowerReport {
    fn record_residual_open_after_recursive_substitution(
        &mut self,
        sources: TypeGraphTypeVarEvidenceSources,
    ) {
        if sources.apply_evidence_substitution {
            self.residual_open_after_recursive_substitution_with_apply_substitution += 1;
        }
        if sources.principal_substitution_candidate {
            self.residual_open_after_recursive_substitution_with_principal_candidate += 1;
        }
        if sources.principal_elaboration_substitution {
            self.residual_open_after_recursive_substitution_with_principal_elaboration += 1;
        }
        if sources.type_instantiation {
            self.residual_open_after_recursive_substitution_with_type_instantiation += 1;
        }
        if sources.role_associated_resolution {
            self.residual_open_after_recursive_substitution_with_role_associated_resolution += 1;
        }
        if sources.structural_lower_decomposition {
            self.residual_open_after_recursive_substitution_with_structural_decomposition += 1;
        }
        if sources.kind_count() > 1 {
            self.residual_open_after_recursive_substitution_with_mixed_sources += 1;
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraphLowerSolution {
    slot_candidates: Vec<Option<RuntimeType>>,
    pub(super) report: TypeGraphLowerSnapshotReport,
}

impl TypeGraphLowerSolution {
    pub(super) fn candidate_count(&self) -> usize {
        self.slot_candidates
            .iter()
            .filter(|candidate| candidate.is_some())
            .count()
    }

    pub(super) fn candidate(&self, slot: TypeGraphSlotId) -> Option<&RuntimeType> {
        self.slot_candidates.get(slot.0).and_then(Option::as_ref)
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraphUpperSupplementSolution {
    slot_candidates: Vec<Option<RuntimeType>>,
    pub(super) report: TypeGraphUpperSupplementReport,
}

impl TypeGraphUpperSupplementSolution {
    pub(super) fn candidate_count(&self) -> usize {
        self.slot_candidates
            .iter()
            .filter(|candidate| candidate.is_some())
            .count()
    }

    #[cfg(test)]
    pub(super) fn candidate(&self, slot: TypeGraphSlotId) -> Option<&RuntimeType> {
        self.slot_candidates.get(slot.0).and_then(Option::as_ref)
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct TypeGraphTypeVarLowerSolution {
    substitutions_by_scope:
        BTreeMap<TypeGraphTypeVarScope, BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
    pub(super) report: TypeGraphTypeVarLowerReport,
}

impl TypeGraphTypeVarLowerSolution {
    pub(super) fn substitution_count(&self) -> usize {
        self.substitutions_by_scope
            .values()
            .map(BTreeMap::len)
            .sum()
    }

    pub(super) fn substitutions_for_scope(
        &self,
        scope: TypeGraphTypeVarScope,
    ) -> Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
        self.substitutions_by_scope.get(&scope)
    }

    #[cfg(test)]
    fn candidate(
        &self,
        scope: TypeGraphTypeVarScope,
        var: &typed_ir::TypeVar,
    ) -> Option<&typed_ir::Type> {
        self.substitutions_by_scope.get(&scope)?.get(var)
    }
}

#[derive(Debug, Clone, Default)]
struct TypeGraphLowerGroup {
    slots: Vec<TypeGraphSlotId>,
    lower_candidates: Vec<RuntimeType>,
    has_upper_requirements: bool,
}

fn push_runtime_lower_candidate(candidates: &mut Vec<RuntimeType>, candidate: RuntimeType) {
    for existing in candidates.iter_mut() {
        let Some(joined) = join_runtime_lower_candidate(existing, &candidate) else {
            continue;
        };
        *existing = joined;
        return;
    }
    candidates.push(candidate);
}

fn push_runtime_upper_supplement_candidate(
    candidates: &mut Vec<RuntimeType>,
    candidate: RuntimeType,
) {
    if candidates.iter().any(|existing| existing == &candidate) {
        return;
    }
    candidates.push(candidate);
}

fn runtime_lower_satisfies_upper(lower: &RuntimeType, upper: &RuntimeType) -> bool {
    lower == upper || {
        let lower = runtime_core_type(lower);
        let upper = runtime_core_type(upper);
        lower == upper || type_compatible(&lower, &upper)
    }
}

fn collect_final_default_holes(ty: &RuntimeType, report: &mut FillHolesReport) {
    match ty {
        RuntimeType::Unknown => {
            report.filled_value_holes += 1;
        }
        RuntimeType::Core(ty) => collect_final_default_core_value_holes(ty, report),
        RuntimeType::Fun { param, ret } => {
            collect_final_default_holes(param, report);
            collect_final_default_holes(ret, report);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_final_default_effect_holes(effect, report);
            collect_final_default_holes(value, report);
        }
    }
}

fn collect_final_default_core_value_holes(ty: &typed_ir::Type, report: &mut FillHolesReport) {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => {
            report.filled_value_holes += 1;
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_final_default_core_value_holes(param, report);
            collect_final_default_effect_holes(param_effect, report);
            collect_final_default_effect_holes(ret_effect, report);
            collect_final_default_core_value_holes(ret, report);
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_final_default_type_arg_holes(arg, report);
            }
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_final_default_core_value_holes(item, report);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_final_default_core_value_holes(&field.value, report);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_final_default_core_value_holes(ty, report);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_final_default_core_value_holes(payload, report);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_final_default_core_value_holes(tail, report);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_final_default_effect_holes(item, report);
            }
            collect_final_default_effect_holes(tail, report);
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_final_default_core_value_holes(body, report);
        }
        typed_ir::Type::Never => {}
    }
}

fn collect_final_default_effect_holes(ty: &typed_ir::Type, report: &mut FillHolesReport) {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => {
            report.filled_effect_holes += 1;
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_final_default_effect_holes(item, report);
            }
            collect_final_default_effect_holes(tail, report);
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_final_default_type_arg_holes(arg, report);
            }
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_final_default_effect_holes(item, report);
            }
        }
        typed_ir::Type::Recursive { body, .. } => collect_final_default_effect_holes(body, report),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_final_default_core_value_holes(param, report);
            collect_final_default_effect_holes(param_effect, report);
            collect_final_default_effect_holes(ret_effect, report);
            collect_final_default_core_value_holes(ret, report);
        }
        typed_ir::Type::Tuple(items) => {
            for item in items {
                collect_final_default_core_value_holes(item, report);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_final_default_core_value_holes(&field.value, report);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_final_default_core_value_holes(payload, report);
                }
            }
        }
        typed_ir::Type::Never => {}
    }
}

fn collect_final_default_type_arg_holes(arg: &typed_ir::TypeArg, report: &mut FillHolesReport) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_final_default_core_value_holes(ty, report),
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_final_default_core_value_holes(lower, report);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_final_default_core_value_holes(upper, report);
            }
        }
    }
}

fn join_runtime_lower_candidate(left: &RuntimeType, right: &RuntimeType) -> Option<RuntimeType> {
    if left == right {
        return Some(left.clone());
    }
    match (left, right) {
        (RuntimeType::Unknown, ty) | (ty, RuntimeType::Unknown) => Some(ty.clone()),
        (RuntimeType::Core(left), RuntimeType::Core(right)) => {
            join_core_lower_candidate(left, right).map(RuntimeType::core)
        }
        _ => None,
    }
}

fn push_type_var_lower_candidate(
    candidates: &mut Vec<TypeGraphTypeVarCandidate>,
    evidence: &TypeGraphTypeVarLowerEvidence,
) -> bool {
    push_type_var_lower_candidate_parts(
        candidates,
        evidence.ty.clone(),
        TypeGraphTypeVarEvidenceSources::from_source(evidence.source),
        evidence.origin.iter().cloned().collect(),
    )
}

fn push_type_var_lower_candidate_parts(
    candidates: &mut Vec<TypeGraphTypeVarCandidate>,
    ty: typed_ir::Type,
    sources: TypeGraphTypeVarEvidenceSources,
    origins: Vec<String>,
) -> bool {
    let mut origins = origins;
    origins.sort();
    origins.dedup();
    let mut sources = sources;
    for candidate in candidates.iter_mut() {
        if candidate.ty != ty && (core_type_has_vars(&candidate.ty) || core_type_has_vars(&ty)) {
            continue;
        }
        let Some(joined) = join_core_lower_candidate(&candidate.ty, &ty) else {
            continue;
        };
        let before = candidate.clone();
        candidate.ty = joined;
        sources.merge(candidate.sources);
        candidate.sources = sources;
        for origin in &origins {
            if !candidate.origins.contains(origin) {
                candidate.origins.push(origin.clone());
            }
        }
        candidate.origins.sort();
        candidate.origins.dedup();
        return before != *candidate;
    }
    candidates.push(TypeGraphTypeVarCandidate {
        ty,
        sources,
        origins,
    });
    true
}

fn solve_structural_type_var_lowers(
    report: &mut TypeGraphTypeVarLowerReport,
    by_scoped_var: &mut BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
) {
    if std::env::var_os("YULANG_DISABLE_TYPE_GRAPH_STRUCTURAL_LOWER").is_some() {
        return;
    }
    let profile = TypeGraphSolverProfile::from_env();
    for iteration in 0..32 {
        report.structural_decomposition_iterations += 1;
        profile.round_start(iteration, by_scoped_var);
        let started_at = Instant::now();
        let mut changed = false;
        let additions = structural_type_var_lower_additions(report, by_scoped_var, profile);
        profile.round_additions(iteration, additions.len(), started_at.elapsed());
        for addition in additions {
            report.structural_decomposition_addition_attempts += 1;
            let candidates = by_scoped_var
                .entry(TypeGraphScopedTypeVar {
                    scope: addition.scope,
                    var: addition.var,
                })
                .or_default();
            if push_type_var_lower_candidate_parts(
                candidates,
                addition.ty,
                TypeGraphTypeVarEvidenceSources::from_source(
                    TypeGraphTypeVarEvidenceSource::StructuralLowerDecomposition,
                ),
                vec![addition.origin],
            ) {
                report.derived_structural_lower_evidence += 1;
                changed = true;
            }
        }
        let started_at = Instant::now();
        if normalize_type_var_lower_candidates(by_scoped_var) {
            changed = true;
        }
        profile.round_normalized(iteration, changed, started_at.elapsed(), by_scoped_var);
        if !changed {
            break;
        }
    }
}

#[derive(Debug, Clone)]
struct TypeGraphStructuralTypeVarLowerAddition {
    scope: TypeGraphTypeVarScope,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
    origin: String,
}

fn structural_type_var_lower_additions(
    report: &mut TypeGraphTypeVarLowerReport,
    by_scoped_var: &BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
    profile: TypeGraphSolverProfile,
) -> Vec<TypeGraphStructuralTypeVarLowerAddition> {
    let mut additions = Vec::new();
    for (scoped_var, candidates) in by_scoped_var {
        profile.scope_candidates(scoped_var, candidates);
        for (left_index, left) in candidates.iter().enumerate() {
            for (right_index, right) in candidates.iter().enumerate() {
                report.structural_decomposition_candidate_visits += 1;
                if left_index == right_index {
                    continue;
                }
                profile.candidate_pair(scoped_var, left_index, right_index, &left.ty, &right.ty);
                collect_structural_type_var_lower_additions(
                    scoped_var,
                    &left.ty,
                    &right.ty,
                    &mut additions,
                );
            }
        }
    }
    additions
}

#[derive(Debug, Clone, Copy)]
struct TypeGraphSolverProfile {
    enabled: bool,
}

impl TypeGraphSolverProfile {
    fn from_env() -> Self {
        Self {
            enabled: std::env::var_os("YULANG_DEBUG_TYPE_GRAPH_SOLVER_PROFILE").is_some(),
        }
    }

    fn round_start(
        self,
        iteration: usize,
        by_scoped_var: &BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
    ) {
        if !self.enabled {
            return;
        }
        let scoped_vars = by_scoped_var.len();
        let candidates = by_scoped_var.values().map(Vec::len).sum::<usize>();
        let scopes_with_multiple_candidates = by_scoped_var
            .values()
            .filter(|candidates| candidates.len() > 1)
            .count();
        let max_candidates_per_var = by_scoped_var
            .values()
            .map(Vec::len)
            .max()
            .unwrap_or_default();
        let mut max_nodes = 0;
        let mut max_depth = 0;
        for candidate in by_scoped_var
            .values()
            .flat_map(|candidates| candidates.iter())
        {
            let metrics = type_profile_metrics(&candidate.ty);
            max_nodes = max_nodes.max(metrics.nodes);
            max_depth = max_depth.max(metrics.max_depth);
        }
        eprintln!(
            "type graph solver profile: structural round={iteration} start scoped_vars={scoped_vars} candidates={candidates} multi_candidate_vars={scopes_with_multiple_candidates} max_candidates_per_var={max_candidates_per_var} max_type_nodes={max_nodes} max_type_depth={max_depth}",
        );
    }

    fn round_additions(self, iteration: usize, additions: usize, elapsed: std::time::Duration) {
        if !self.enabled {
            return;
        }
        eprintln!(
            "type graph solver profile: structural round={iteration} additions={additions} collect_elapsed={elapsed:?}",
        );
    }

    fn round_normalized(
        self,
        iteration: usize,
        changed: bool,
        elapsed: std::time::Duration,
        by_scoped_var: &BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
    ) {
        if !self.enabled {
            return;
        }
        let candidates = by_scoped_var.values().map(Vec::len).sum::<usize>();
        eprintln!(
            "type graph solver profile: structural round={iteration} normalized changed={changed} candidates={candidates} normalize_elapsed={elapsed:?}",
        );
    }

    fn scope_candidates(
        self,
        scoped_var: &TypeGraphScopedTypeVar,
        candidates: &[TypeGraphTypeVarCandidate],
    ) {
        if !self.enabled || candidates.len() <= 1 {
            return;
        }
        let mut max_nodes = 0;
        let mut max_depth = 0;
        for candidate in candidates {
            let metrics = type_profile_metrics(&candidate.ty);
            max_nodes = max_nodes.max(metrics.nodes);
            max_depth = max_depth.max(metrics.max_depth);
        }
        eprintln!(
            "type graph solver profile: structural scope={} var={} candidates={} max_type_nodes={} max_type_depth={}",
            scoped_var.scope.0,
            scoped_var.var.0,
            candidates.len(),
            max_nodes,
            max_depth,
        );
    }

    fn candidate_pair(
        self,
        scoped_var: &TypeGraphScopedTypeVar,
        left_index: usize,
        right_index: usize,
        left: &typed_ir::Type,
        right: &typed_ir::Type,
    ) {
        if !self.enabled {
            return;
        }
        let left_metrics = type_profile_metrics(left);
        let right_metrics = type_profile_metrics(right);
        if left_metrics.nodes < 512
            && right_metrics.nodes < 512
            && left_metrics.max_depth < 64
            && right_metrics.max_depth < 64
        {
            return;
        }
        eprintln!(
            "type graph solver profile: structural large_pair scope={} var={} left_index={} right_index={} left_nodes={} left_depth={} right_nodes={} right_depth={}",
            scoped_var.scope.0,
            scoped_var.var.0,
            left_index,
            right_index,
            left_metrics.nodes,
            left_metrics.max_depth,
            right_metrics.nodes,
            right_metrics.max_depth,
        );
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct TypeProfileMetrics {
    nodes: usize,
    max_depth: usize,
}

fn type_profile_metrics(ty: &typed_ir::Type) -> TypeProfileMetrics {
    let mut metrics = TypeProfileMetrics::default();
    let mut stack = vec![(ty, 1usize)];
    while let Some((ty, depth)) = stack.pop() {
        metrics.nodes += 1;
        metrics.max_depth = metrics.max_depth.max(depth);
        match ty {
            typed_ir::Type::Named { args, .. } => {
                for arg in args {
                    match arg {
                        typed_ir::TypeArg::Type(ty) => stack.push((ty, depth + 1)),
                        typed_ir::TypeArg::Bounds(bounds) => {
                            if let Some(lower) = bounds.lower.as_deref() {
                                stack.push((lower, depth + 1));
                            }
                            if let Some(upper) = bounds.upper.as_deref() {
                                stack.push((upper, depth + 1));
                            }
                        }
                    }
                }
            }
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                stack.push((param, depth + 1));
                stack.push((param_effect, depth + 1));
                stack.push((ret_effect, depth + 1));
                stack.push((ret, depth + 1));
            }
            typed_ir::Type::Tuple(items)
            | typed_ir::Type::Union(items)
            | typed_ir::Type::Inter(items) => {
                for item in items {
                    stack.push((item, depth + 1));
                }
            }
            typed_ir::Type::Record(record) => {
                for field in &record.fields {
                    stack.push((&field.value, depth + 1));
                }
                if let Some(spread) = record.spread.as_ref() {
                    match spread {
                        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                            stack.push((ty, depth + 1))
                        }
                    }
                }
            }
            typed_ir::Type::Variant(variant) => {
                for payload in variant.cases.iter().flat_map(|case| &case.payloads) {
                    stack.push((payload, depth + 1));
                }
                if let Some(tail) = variant.tail.as_deref() {
                    stack.push((tail, depth + 1));
                }
            }
            typed_ir::Type::Row { items, tail } => {
                for item in items {
                    stack.push((item, depth + 1));
                }
                stack.push((tail, depth + 1));
            }
            typed_ir::Type::Recursive { body, .. } => stack.push((body, depth + 1)),
            typed_ir::Type::Unknown
            | typed_ir::Type::Never
            | typed_ir::Type::Any
            | typed_ir::Type::Var(_) => {}
        }
    }
    metrics
}

fn collect_structural_type_var_lower_additions(
    scoped_var: &TypeGraphScopedTypeVar,
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    additions: &mut Vec<TypeGraphStructuralTypeVarLowerAddition>,
) {
    if template == actual {
        return;
    }
    if !structural_lower_decomposition_allowed(template, actual) {
        return;
    }
    let mut params = BTreeSet::new();
    collect_type_vars(template, &mut params);
    if params.is_empty() {
        return;
    }
    let mut substitutions = BTreeMap::new();
    infer_type_substitutions(template, actual, &params, &mut substitutions);
    let structural_vars = structural_type_var_lower_vars(template, actual);
    substitutions.retain(|var, _| structural_vars.contains(var));
    if substitutions.is_empty() {
        return;
    }
    retain_acyclic_type_substitutions(&mut substitutions);
    close_type_substitution_map_recursively(&mut substitutions);
    if !substituted_type_matches_actual(template, actual, &substitutions) {
        return;
    }
    for (var, ty) in substitutions {
        if core_type_is_bottom_like_lower(&ty) || core_type_is_identity_lower_for_var(&var, &ty) {
            continue;
        }
        if free_type_vars(&ty).contains(&var) {
            continue;
        }
        additions.push(TypeGraphStructuralTypeVarLowerAddition {
            scope: scoped_var.scope,
            var,
            ty,
            origin: format!("structural_lower parent={}", scoped_var.var.0),
        });
    }
}

fn structural_lower_decomposition_allowed(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> bool {
    match (template, actual) {
        (typed_ir::Type::Var(_), _) => true,
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => items
            .iter()
            .any(|item| structural_lower_decomposition_allowed(item, actual)),
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) => path == actual_path && args.len() == actual_args.len(),
        (typed_ir::Type::Fun { .. }, typed_ir::Type::Fun { .. }) => true,
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items)) => {
            items.len() == actual_items.len()
        }
        (typed_ir::Type::Record(_), typed_ir::Type::Record(_)) => true,
        (typed_ir::Type::Variant(_), typed_ir::Type::Variant(_)) => true,
        (typed_ir::Type::Row { .. }, typed_ir::Type::Row { .. }) => true,
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            structural_lower_decomposition_allowed(body, actual)
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            structural_lower_decomposition_allowed(template, body)
        }
        _ => false,
    }
}

fn structural_type_var_lower_vars(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_structural_type_var_lower_vars(template, actual, &mut vars, 128);
    vars
}

fn collect_structural_type_var_lower_vars(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), _) => {
            vars.insert(var.clone());
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => {
            for item in items {
                if structural_lower_decomposition_allowed(item, actual) {
                    collect_structural_type_var_lower_vars(item, actual, vars, depth - 1);
                }
            }
        }
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template, actual) in args.iter().zip(actual_args) {
                collect_structural_type_arg_lower_vars(template, actual, vars, depth - 1);
            }
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => {
            collect_structural_type_var_lower_vars(param, actual_param, vars, depth - 1);
            collect_structural_type_var_lower_vars(
                param_effect,
                actual_param_effect,
                vars,
                depth - 1,
            );
            collect_structural_type_var_lower_vars(ret_effect, actual_ret_effect, vars, depth - 1);
            collect_structural_type_var_lower_vars(ret, actual_ret, vars, depth - 1);
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (template, actual) in items.iter().zip(actual_items) {
                collect_structural_type_var_lower_vars(template, actual, vars, depth - 1);
            }
        }
        (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
            for field in &record.fields {
                let Some(actual_field) = actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                else {
                    continue;
                };
                collect_structural_type_var_lower_vars(
                    &field.value,
                    &actual_field.value,
                    vars,
                    depth - 1,
                );
            }
        }
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
            for case in &variant.cases {
                let Some(actual_case) = actual_variant
                    .cases
                    .iter()
                    .find(|actual| actual.name == case.name)
                else {
                    continue;
                };
                if case.payloads.len() != actual_case.payloads.len() {
                    continue;
                }
                for (template, actual) in case.payloads.iter().zip(&actual_case.payloads) {
                    collect_structural_type_var_lower_vars(template, actual, vars, depth - 1);
                }
            }
        }
        (
            typed_ir::Type::Row { items, .. },
            typed_ir::Type::Row {
                items: actual_items,
                ..
            },
        ) => {
            collect_effect_row_structural_type_var_lower_vars(items, actual_items, vars, depth - 1);
        }
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            collect_structural_type_var_lower_vars(body, actual, vars, depth - 1);
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            collect_structural_type_var_lower_vars(template, body, vars, depth - 1);
        }
        _ => {}
    }
}

fn collect_structural_type_arg_lower_vars(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            collect_structural_type_var_lower_vars(template, actual, vars, depth);
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            if let (Some(template), Some(actual)) =
                (template.lower.as_deref(), actual.lower.as_deref())
            {
                collect_structural_type_var_lower_vars(template, actual, vars, depth);
            }
            if let (Some(template), Some(actual)) =
                (template.upper.as_deref(), actual.upper.as_deref())
            {
                collect_structural_type_var_lower_vars(template, actual, vars, depth);
            }
        }
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
            if let Some(actual) = actual.lower.as_deref() {
                collect_structural_type_var_lower_vars(template, actual, vars, depth);
            }
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
            if let Some(template) = template.lower.as_deref() {
                collect_structural_type_var_lower_vars(template, actual, vars, depth);
            }
        }
    }
}

fn collect_effect_row_structural_type_var_lower_vars(
    template_items: &[typed_ir::Type],
    actual_items: &[typed_ir::Type],
    vars: &mut BTreeSet<typed_ir::TypeVar>,
    depth: usize,
) {
    let mut matched_actual = vec![false; actual_items.len()];
    for template in template_items {
        let Some((index, actual)) = actual_items
            .iter()
            .enumerate()
            .find(|(index, actual)| !matched_actual[*index] && same_effect_head(template, actual))
        else {
            continue;
        };
        matched_actual[index] = true;
        collect_structural_type_var_lower_vars(template, actual, vars, depth);
    }
}

fn substituted_type_matches_actual(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> bool {
    substituted_type_matches_actual_inner(
        template,
        actual,
        substitutions,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
        128,
    )
}

fn substituted_type_matches_actual_inner(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    active_vars: &mut BTreeSet<typed_ir::TypeVar>,
    visited_pairs: &mut BTreeSet<(usize, usize)>,
    depth: usize,
) -> bool {
    if depth == 0 {
        return false;
    }
    if template == actual {
        return true;
    }
    let pair = (
        template as *const typed_ir::Type as usize,
        actual as *const typed_ir::Type as usize,
    );
    if !visited_pairs.insert(pair) {
        return true;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) => {
            let Some(replacement) = substitutions.get(var) else {
                return template == actual;
            };
            if !active_vars.insert(var.clone()) {
                return template == actual;
            }
            let matches = substituted_type_matches_actual_inner(
                replacement,
                actual,
                substitutions,
                active_vars,
                visited_pairs,
                depth - 1,
            );
            active_vars.remove(var);
            matches
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => {
            items.iter().any(|item| {
                substituted_type_matches_actual_inner(
                    item,
                    actual,
                    substitutions,
                    active_vars,
                    visited_pairs,
                    depth - 1,
                )
            })
        }
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            args.iter().zip(actual_args).all(|(template, actual)| {
                substituted_type_arg_matches_actual(
                    template,
                    actual,
                    substitutions,
                    active_vars,
                    visited_pairs,
                    depth - 1,
                )
            })
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => {
            substituted_type_matches_actual_inner(
                param,
                actual_param,
                substitutions,
                active_vars,
                visited_pairs,
                depth - 1,
            ) && substituted_type_matches_actual_inner(
                param_effect,
                actual_param_effect,
                substitutions,
                active_vars,
                visited_pairs,
                depth - 1,
            ) && substituted_type_matches_actual_inner(
                ret_effect,
                actual_ret_effect,
                substitutions,
                active_vars,
                visited_pairs,
                depth - 1,
            ) && substituted_type_matches_actual_inner(
                ret,
                actual_ret,
                substitutions,
                active_vars,
                visited_pairs,
                depth - 1,
            )
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            items.iter().zip(actual_items).all(|(template, actual)| {
                substituted_type_matches_actual_inner(
                    template,
                    actual,
                    substitutions,
                    active_vars,
                    visited_pairs,
                    depth - 1,
                )
            })
        }
        (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
            record.fields.iter().all(|field| {
                let Some(actual_field) = actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                else {
                    return field.optional;
                };
                substituted_type_matches_actual_inner(
                    &field.value,
                    &actual_field.value,
                    substitutions,
                    active_vars,
                    visited_pairs,
                    depth - 1,
                )
            })
        }
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
            actual_variant.cases.iter().all(|actual_case| {
                let Some(case) = variant
                    .cases
                    .iter()
                    .find(|case| case.name == actual_case.name)
                else {
                    return false;
                };
                case.payloads.len() == actual_case.payloads.len()
                    && case
                        .payloads
                        .iter()
                        .zip(&actual_case.payloads)
                        .all(|(template, actual)| {
                            substituted_type_matches_actual_inner(
                                template,
                                actual,
                                substitutions,
                                active_vars,
                                visited_pairs,
                                depth - 1,
                            )
                        })
            })
        }
        (
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) => {
            substituted_effect_row_items_match_actual(
                items,
                actual_items,
                substitutions,
                active_vars,
                visited_pairs,
                depth - 1,
            ) && (effect_is_empty(tail) || effect_is_empty(actual_tail) || {
                substituted_type_matches_actual_inner(
                    tail,
                    actual_tail,
                    substitutions,
                    active_vars,
                    visited_pairs,
                    depth - 1,
                )
            })
        }
        (typed_ir::Type::Recursive { body, .. }, actual) => substituted_type_matches_actual_inner(
            body,
            actual,
            substitutions,
            active_vars,
            visited_pairs,
            depth - 1,
        ),
        (template, typed_ir::Type::Recursive { body, .. }) => {
            substituted_type_matches_actual_inner(
                template,
                body,
                substitutions,
                active_vars,
                visited_pairs,
                depth - 1,
            )
        }
        _ => false,
    }
}

fn substituted_type_arg_matches_actual(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    active_vars: &mut BTreeSet<typed_ir::TypeVar>,
    visited_pairs: &mut BTreeSet<(usize, usize)>,
    depth: usize,
) -> bool {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            substituted_type_matches_actual_inner(
                template,
                actual,
                substitutions,
                active_vars,
                visited_pairs,
                depth,
            )
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            substituted_type_bounds_matches_actual(
                template,
                actual,
                substitutions,
                active_vars,
                visited_pairs,
                depth,
            )
        }
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
            actual.lower.as_deref().is_some_and(|actual| {
                substituted_type_matches_actual_inner(
                    template,
                    actual,
                    substitutions,
                    active_vars,
                    visited_pairs,
                    depth,
                )
            })
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
            template.lower.as_deref().is_some_and(|template| {
                substituted_type_matches_actual_inner(
                    template,
                    actual,
                    substitutions,
                    active_vars,
                    visited_pairs,
                    depth,
                )
            })
        }
    }
}

fn substituted_effect_row_items_match_actual(
    template_items: &[typed_ir::Type],
    actual_items: &[typed_ir::Type],
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    active_vars: &mut BTreeSet<typed_ir::TypeVar>,
    visited_pairs: &mut BTreeSet<(usize, usize)>,
    depth: usize,
) -> bool {
    let mut matched_actual = vec![false; actual_items.len()];
    for template in template_items {
        let Some((index, actual)) = actual_items
            .iter()
            .enumerate()
            .find(|(index, actual)| !matched_actual[*index] && same_effect_head(template, actual))
        else {
            continue;
        };
        matched_actual[index] = true;
        if !substituted_type_matches_actual_inner(
            template,
            actual,
            substitutions,
            active_vars,
            visited_pairs,
            depth,
        ) {
            return false;
        }
    }
    true
}

fn substituted_type_bounds_matches_actual(
    template: &typed_ir::TypeBounds,
    actual: &typed_ir::TypeBounds,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    active_vars: &mut BTreeSet<typed_ir::TypeVar>,
    visited_pairs: &mut BTreeSet<(usize, usize)>,
    depth: usize,
) -> bool {
    let lower_matches = match (template.lower.as_deref(), actual.lower.as_deref()) {
        (Some(template), Some(actual)) => substituted_type_matches_actual_inner(
            template,
            actual,
            substitutions,
            active_vars,
            visited_pairs,
            depth,
        ),
        (None, None) => true,
        _ => false,
    };
    let upper_matches = match (template.upper.as_deref(), actual.upper.as_deref()) {
        (Some(template), Some(actual)) => substituted_type_matches_actual_inner(
            template,
            actual,
            substitutions,
            active_vars,
            visited_pairs,
            depth,
        ),
        (None, None) => true,
        _ => false,
    };
    lower_matches && upper_matches
}

fn normalize_type_var_lower_candidates(
    by_scoped_var: &mut BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
) -> bool {
    let substitutions_by_scope = single_candidate_substitutions_by_scope(by_scoped_var);
    let mut normalized = BTreeMap::<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>::new();
    let mut changed = false;
    for (scoped_var, candidates) in by_scoped_var.iter() {
        let substitutions = substitutions_by_scope.get(&scoped_var.scope);
        for candidate in candidates {
            let ty = substitutions
                .map(|substitutions| substitute_type(&candidate.ty, substitutions))
                .unwrap_or_else(|| candidate.ty.clone());
            if ty != candidate.ty {
                changed = true;
            }
            let target = normalized.entry(scoped_var.clone()).or_default();
            push_type_var_lower_candidate_parts(
                target,
                ty,
                candidate.sources,
                candidate.origins.clone(),
            );
        }
    }
    if *by_scoped_var != normalized {
        *by_scoped_var = normalized;
        changed = true;
    }
    changed
}

fn single_candidate_substitutions_by_scope(
    by_scoped_var: &BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
) -> BTreeMap<TypeGraphTypeVarScope, BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
    let mut substitutions_by_scope =
        BTreeMap::<TypeGraphTypeVarScope, BTreeMap<typed_ir::TypeVar, typed_ir::Type>>::new();
    for (scoped_var, candidates) in by_scoped_var {
        let [candidate] = candidates.as_slice() else {
            continue;
        };
        substitutions_by_scope
            .entry(scoped_var.scope)
            .or_default()
            .insert(scoped_var.var.clone(), candidate.ty.clone());
    }
    for substitutions in substitutions_by_scope.values_mut() {
        retain_acyclic_type_substitutions(substitutions);
        close_type_substitution_map_recursively(substitutions);
    }
    substitutions_by_scope
}

fn type_var_lower_vars_by_name(
    by_scoped_var: &BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
) -> BTreeMap<typed_ir::TypeVar, usize> {
    let mut vars = BTreeMap::<typed_ir::TypeVar, usize>::new();
    for scoped_var in by_scoped_var.keys() {
        vars.entry(scoped_var.var.clone())
            .and_modify(|count| *count += 1)
            .or_insert(1);
    }
    vars
}

fn report_recursive_type_var_substitutions(
    report: &mut TypeGraphTypeVarLowerReport,
    by_scoped_var: &BTreeMap<TypeGraphScopedTypeVar, Vec<TypeGraphTypeVarCandidate>>,
    solved_by_scope: &BTreeMap<TypeGraphTypeVarScope, BTreeMap<typed_ir::TypeVar, typed_ir::Type>>,
) {
    for (scoped_var, candidates) in by_scoped_var {
        let [candidate] = candidates.as_slice() else {
            continue;
        };
        let Some(substitutions) = solved_by_scope.get(&scoped_var.scope) else {
            continue;
        };
        let substituted = substitute_type(&candidate.ty, substitutions);
        if substituted != candidate.ty {
            report.recursive_substitution_vars += 1;
        }
        if core_type_has_vars(&candidate.ty) && !core_type_has_vars(&substituted) {
            report.closed_after_recursive_substitution_vars += 1;
        }
        if core_type_has_vars(&substituted) {
            report.residual_open_vars_after_recursive_substitution += 1;
            let residual_vars = free_type_vars(&substituted);
            if residual_vars
                .iter()
                .any(|var| substitutions.contains_key(var))
            {
                report.residual_open_recursive_cycle_vars_after_substitution += 1;
            }
            if residual_vars
                .iter()
                .any(|var| !substitutions.contains_key(var))
            {
                report.residual_open_missing_substitution_vars_after_substitution += 1;
            }
            report.record_residual_open_after_recursive_substitution(candidate.sources);
            if report.residual_open_samples.len() < 24 {
                report.residual_open_samples.push(format!(
                    "scope={} var={} candidate={} substituted={} candidate_debug={:?} substituted_debug={:?} sources={:?} origins={:?}",
                    scoped_var.scope.0,
                    scoped_var.var.0,
                    display_type(&candidate.ty),
                    display_type(&substituted),
                    candidate.ty,
                    substituted,
                    candidate.sources,
                    candidate.origins
                ));
            }
        }
    }
}

fn free_type_vars(ty: &typed_ir::Type) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars
}

fn format_path(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn join_core_lower_candidate(
    left: &typed_ir::Type,
    right: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if left == right {
        return Some(left.clone());
    }
    if core_type_is_bottom_like_lower(left) {
        return Some(right.clone());
    }
    if core_type_is_bottom_like_lower(right) {
        return Some(left.clone());
    }
    match (type_compatible(left, right), type_compatible(right, left)) {
        (true, true) => Some(left.clone()),
        (true, false) => Some(left.clone()),
        (false, true) => Some(right.clone()),
        (false, false) => None,
    }
}

fn lower_core_candidate_from_bounds(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    let lower = bounds.lower.as_deref()?.clone();
    (!core_type_is_bottom_like_lower(&lower)).then_some(lower)
}

fn core_type_is_identity_lower_for_var(var: &typed_ir::TypeVar, ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Var(candidate) if candidate == var)
}

fn resolve_role_associated_lower(
    requirement: &typed_ir::RoleRequirement,
    name: &typed_ir::Name,
    inputs: &[typed_ir::Type],
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> (
    TypeGraphRoleAssociatedResolutionStatus,
    Option<TypeGraphResolvedAssociatedLower>,
) {
    let mut resolved: Option<TypeGraphResolvedAssociatedLower> = None;
    let mut saw_candidate = false;
    for role_impl in role_impls.iter().filter(|role_impl| {
        role_impl.role == requirement.role && role_impl.inputs.len() == inputs.len()
    }) {
        let Some(associated) = role_impl
            .associated_types
            .iter()
            .find(|associated| associated.name == *name)
        else {
            continue;
        };
        let Some(candidate) =
            project_role_impl_associated_lower(&role_impl.inputs, inputs, &associated.value)
        else {
            continue;
        };
        saw_candidate = true;
        match &resolved {
            Some(existing) if existing.associated != candidate.associated => {
                return (TypeGraphRoleAssociatedResolutionStatus::AmbiguousImpl, None);
            }
            Some(_) => {}
            None => resolved = Some(candidate),
        }
    }
    match resolved {
        Some(resolved) => (
            TypeGraphRoleAssociatedResolutionStatus::Resolved,
            Some(resolved),
        ),
        None if saw_candidate => (TypeGraphRoleAssociatedResolutionStatus::AmbiguousImpl, None),
        None => (TypeGraphRoleAssociatedResolutionStatus::MissingImpl, None),
    }
}

fn project_role_impl_associated_lower(
    impl_inputs: &[typed_ir::TypeBounds],
    actual_inputs: &[typed_ir::Type],
    associated: &typed_ir::TypeBounds,
) -> Option<TypeGraphResolvedAssociatedLower> {
    let mut impl_vars = BTreeSet::new();
    let templates = impl_inputs
        .iter()
        .map(|bounds| {
            let template = lower_core_candidate_from_bounds(bounds)?;
            collect_type_vars(&template, &mut impl_vars);
            Some(template)
        })
        .collect::<Option<Vec<_>>>()?;
    collect_type_bounds_vars(associated, &mut impl_vars);
    let mut substitutions = BTreeMap::new();
    for (template, actual) in templates.iter().zip(actual_inputs) {
        infer_type_substitutions(template, actual, &impl_vars, &mut substitutions);
    }
    if templates
        .iter()
        .zip(actual_inputs)
        .any(|(template, actual)| substitute_type(template, &substitutions) != *actual)
    {
        return None;
    }
    let associated = substitute_bounds(associated.clone(), &substitutions);
    Some(TypeGraphResolvedAssociatedLower {
        associated: lower_core_candidate_from_bounds(&associated)?,
        impl_substitutions: substitutions,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeGraphResolvedAssociatedLower {
    associated: typed_ir::Type,
    impl_substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
}

fn collect_type_bounds_vars(bounds: &typed_ir::TypeBounds, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_type_vars(upper, vars);
    }
}

pub(super) fn build_type_graph(module: &Module) -> (TypeGraph, TypeGraphBuildReport) {
    let mut builder = TypeGraphBuilder {
        graph: TypeGraph::default(),
    };
    builder.module(module);
    let report = builder.graph.report();
    (builder.graph, report)
}

struct TypeGraphBuilder {
    graph: TypeGraph,
}

impl TypeGraphBuilder {
    fn module(&mut self, module: &Module) {
        for binding in &module.bindings {
            self.binding(binding, &module.role_impls);
        }
        for (index, expr) in module.root_exprs.iter().enumerate() {
            let slot = self.expr(expr);
            let root = self
                .graph
                .push_slot(TypeGraphSlotKind::RootExpr { index }, expr.ty.clone());
            self.graph.push_edge(
                TypeGraphEdgeKind::Equal,
                root,
                slot,
                TypeGraphEdgeProvenance::RootExpr { index },
            );
        }
    }

    fn binding(&mut self, binding: &Binding, role_impls: &[typed_ir::RoleImplGraphNode]) {
        self.scheme_requirements(&binding.scheme, role_impls);
        let scheme = self.graph.push_slot(
            TypeGraphSlotKind::BindingScheme {
                binding: binding.name.clone(),
            },
            RuntimeType::core(binding.scheme.body.clone()),
        );
        let body = self.graph.push_slot(
            TypeGraphSlotKind::BindingBody {
                binding: binding.name.clone(),
            },
            binding.body.ty.clone(),
        );
        self.graph.push_edge(
            TypeGraphEdgeKind::Equal,
            scheme,
            body,
            TypeGraphEdgeProvenance::BindingSchemeBody,
        );
        let expr = self.expr(&binding.body);
        self.graph.push_edge(
            TypeGraphEdgeKind::Equal,
            body,
            expr,
            TypeGraphEdgeProvenance::BindingBodyExpr,
        );
    }

    fn scheme_requirements(
        &mut self,
        scheme: &typed_ir::Scheme,
        role_impls: &[typed_ir::RoleImplGraphNode],
    ) {
        for requirement in &scheme.requirements {
            for arg in &requirement.args {
                match arg {
                    typed_ir::RoleRequirementArg::Input(bounds) => {
                        self.graph.push_role_bounds_evidence(
                            TypeGraphRoleBoundsEvidenceSource::RequirementInput,
                            bounds,
                        )
                    }
                    typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                        self.graph.push_role_bounds_evidence(
                            TypeGraphRoleBoundsEvidenceSource::RequirementAssociated,
                            bounds,
                        );
                    }
                }
            }
            self.role_associated_requirements(requirement, role_impls);
        }
    }

    fn role_associated_requirements(
        &mut self,
        requirement: &typed_ir::RoleRequirement,
        role_impls: &[typed_ir::RoleImplGraphNode],
    ) {
        let missing_input_lower = requirement.args.iter().any(|arg| {
            matches!(arg, typed_ir::RoleRequirementArg::Input(bounds) if lower_core_candidate_from_bounds(bounds).is_none())
        });
        let inputs = requirement
            .args
            .iter()
            .filter_map(|arg| match arg {
                typed_ir::RoleRequirementArg::Input(bounds) => {
                    lower_core_candidate_from_bounds(bounds)
                }
                typed_ir::RoleRequirementArg::Associated { .. } => None,
            })
            .collect::<Vec<_>>();
        let scope = self.graph.fresh_type_var_scope();
        for arg in &requirement.args {
            let typed_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            if missing_input_lower {
                self.graph.push_role_associated_resolution_evidence(
                    TypeGraphRoleAssociatedResolutionStatus::MissingInputLower,
                    0,
                );
                continue;
            }
            let (status, resolved) =
                resolve_role_associated_lower(requirement, name, &inputs, role_impls);
            let projected_type_vars = resolved
                .as_ref()
                .map(|resolved| {
                    let origin = format!(
                        "role_associated role={} name={}",
                        format_path(&requirement.role),
                        name.0
                    );
                    let mut projected = self.graph.push_role_associated_impl_substitutions(
                        scope,
                        &resolved.impl_substitutions,
                        origin.clone(),
                    );
                    projected += self.graph.push_role_associated_type_var_lower_evidence(
                        scope,
                        bounds,
                        &resolved.associated,
                        origin,
                    );
                    projected
                })
                .unwrap_or(0);
            self.graph
                .push_role_associated_resolution_evidence(status, projected_type_vars);
        }
    }

    fn expr(&mut self, expr: &Expr) -> TypeGraphSlotId {
        let expr_slot = self
            .graph
            .push_slot(TypeGraphSlotKind::Expr, expr.ty.clone());
        match &expr.kind {
            ExprKind::Lambda { param, body, .. } => {
                if let Some((param_ty, ret_ty)) = runtime_function_parts(&expr.ty) {
                    let param_slot = self.graph.push_slot(
                        TypeGraphSlotKind::LambdaParam {
                            name: param.clone(),
                        },
                        param_ty,
                    );
                    let ret_slot = self.graph.push_slot(
                        TypeGraphSlotKind::LambdaResult {
                            name: param.clone(),
                        },
                        ret_ty,
                    );
                    let body_slot = self.expr(body);
                    self.graph.push_edge(
                        TypeGraphEdgeKind::LambdaResult,
                        ret_slot,
                        body_slot,
                        TypeGraphEdgeProvenance::LambdaResult,
                    );
                    self.graph.push_edge(
                        TypeGraphEdgeKind::LambdaParam,
                        expr_slot,
                        param_slot,
                        TypeGraphEdgeProvenance::LambdaParam,
                    );
                } else {
                    self.expr(body);
                }
            }
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
                ..
            } => {
                let callee_slot = self.expr(callee);
                let arg_slot = self.expr(arg);
                let apply_callee = self
                    .graph
                    .push_slot(TypeGraphSlotKind::ApplyCallee, callee.ty.clone());
                let apply_arg = self
                    .graph
                    .push_slot(TypeGraphSlotKind::ApplyArg, arg.ty.clone());
                let apply_result = self
                    .graph
                    .push_slot(TypeGraphSlotKind::ApplyResult, expr.ty.clone());
                self.graph.push_edge(
                    TypeGraphEdgeKind::ApplyCallee,
                    apply_callee,
                    callee_slot,
                    TypeGraphEdgeProvenance::ApplyCallee,
                );
                self.graph.push_edge(
                    TypeGraphEdgeKind::ApplyArg,
                    apply_arg,
                    arg_slot,
                    TypeGraphEdgeProvenance::ApplyArg,
                );
                self.graph.push_edge(
                    TypeGraphEdgeKind::ApplyResult,
                    expr_slot,
                    apply_result,
                    TypeGraphEdgeProvenance::ApplyResult,
                );
                self.apply_function_shape(callee, arg_slot, expr_slot);
                if let Some(evidence) = evidence {
                    self.apply_evidence(evidence, apply_callee, apply_arg, apply_result);
                }
                if let Some(instantiation) = instantiation {
                    self.type_instantiation(instantiation);
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.expr(cond);
                let then_slot = self.expr(then_branch);
                let else_slot = self.expr(else_branch);
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    expr_slot,
                    then_slot,
                    TypeGraphEdgeProvenance::IfBranch,
                );
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    expr_slot,
                    else_slot,
                    TypeGraphEdgeProvenance::IfBranch,
                );
            }
            ExprKind::Tuple(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            ExprKind::Record { fields, spread } => {
                for field in fields {
                    self.expr(&field.value);
                }
                if let Some(spread) = spread {
                    self.record_spread_expr(spread);
                }
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            ExprKind::Select { base, .. } => {
                self.expr(base);
            }
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                self.expr(scrutinee);
                for arm in arms {
                    self.pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    let body = self.expr(&arm.body);
                    self.graph.push_edge(
                        TypeGraphEdgeKind::Equal,
                        expr_slot,
                        body,
                        TypeGraphEdgeProvenance::MatchArmBody,
                    );
                }
            }
            ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    self.stmt(stmt);
                }
                if let Some(tail) = tail {
                    let tail_slot = self.expr(tail);
                    self.graph.push_edge(
                        TypeGraphEdgeKind::Equal,
                        expr_slot,
                        tail_slot,
                        TypeGraphEdgeProvenance::BlockTail,
                    );
                }
            }
            ExprKind::Handle {
                body,
                arms,
                handler,
                ..
            } => {
                self.expr(body);
                if let Some(output) = handler_output_lower_type(&body.ty, handler) {
                    self.graph.push_runtime_lower_evidence(
                        TypeGraphBoundsEvidenceRole::HandlerResult,
                        expr_slot,
                        output,
                    );
                }
                for arm in arms {
                    self.pattern(&arm.payload);
                    if let Some(resume) = &arm.resume {
                        self.graph
                            .push_slot(TypeGraphSlotKind::Pattern, resume.ty.clone());
                    }
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    let body = self.expr(&arm.body);
                    self.graph.push_edge(
                        TypeGraphEdgeKind::Equal,
                        expr_slot,
                        body,
                        TypeGraphEdgeProvenance::MatchArmBody,
                    );
                }
            }
            ExprKind::BindHere { expr }
            | ExprKind::Thunk { expr, .. }
            | ExprKind::LocalPushId { body: expr, .. }
            | ExprKind::AddId { thunk: expr, .. }
            | ExprKind::Coerce { expr, .. }
            | ExprKind::Pack { expr, .. } => {
                let inner = self.expr(expr);
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    expr_slot,
                    inner,
                    TypeGraphEdgeProvenance::WrapperExpr,
                );
            }
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => {}
        }
        expr_slot
    }

    fn stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { pattern, value } => {
                let value_slot = self.expr(value);
                let pattern_slot = self.pattern(pattern);
                let let_value = self
                    .graph
                    .push_slot(TypeGraphSlotKind::LetValue, value.ty.clone());
                let let_pattern = self
                    .graph
                    .push_slot(TypeGraphSlotKind::LetPattern, pattern_runtime_type(pattern));
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    let_value,
                    value_slot,
                    TypeGraphEdgeProvenance::LetValue,
                );
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    let_pattern,
                    pattern_slot,
                    TypeGraphEdgeProvenance::LetPattern,
                );
                self.graph.push_edge(
                    TypeGraphEdgeKind::LetValuePattern,
                    let_value,
                    let_pattern,
                    TypeGraphEdgeProvenance::LetValuePattern,
                );
            }
            Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => {
                self.expr(expr);
            }
        }
    }

    fn pattern(&mut self, pattern: &Pattern) -> TypeGraphSlotId {
        let slot = self
            .graph
            .push_slot(TypeGraphSlotKind::Pattern, pattern_runtime_type(pattern));
        match pattern {
            Pattern::Tuple { items, .. } => {
                for item in items {
                    self.pattern(item);
                }
            }
            Pattern::List {
                prefix,
                spread,
                suffix,
                ..
            } => {
                for item in prefix {
                    self.pattern(item);
                }
                if let Some(spread) = spread {
                    self.pattern(spread);
                }
                for item in suffix {
                    self.pattern(item);
                }
            }
            Pattern::Record { fields, spread, .. } => {
                for field in fields {
                    let field_slot = self.pattern(&field.pattern);
                    self.graph.push_edge(
                        TypeGraphEdgeKind::Equal,
                        slot,
                        field_slot,
                        TypeGraphEdgeProvenance::RecordPatternField,
                    );
                    if let Some(default) = &field.default {
                        self.expr(default);
                    }
                }
                if let Some(spread) = spread {
                    self.record_spread_pattern(spread);
                }
            }
            Pattern::Variant { value, .. } => {
                if let Some(value) = value {
                    self.pattern(value);
                }
            }
            Pattern::Or { left, right, .. } => {
                let left = self.pattern(left);
                let right = self.pattern(right);
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    slot,
                    left,
                    TypeGraphEdgeProvenance::OrPattern,
                );
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    slot,
                    right,
                    TypeGraphEdgeProvenance::OrPattern,
                );
            }
            Pattern::As { pattern, .. } => {
                let inner = self.pattern(pattern);
                self.graph.push_edge(
                    TypeGraphEdgeKind::Equal,
                    slot,
                    inner,
                    TypeGraphEdgeProvenance::AsPattern,
                );
            }
            Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
        }
        slot
    }

    fn apply_function_shape(
        &mut self,
        callee: &Expr,
        arg: TypeGraphSlotId,
        result: TypeGraphSlotId,
    ) {
        let Some((param_ty, ret_ty)) = runtime_function_parts(&callee.ty) else {
            return;
        };
        let param = self
            .graph
            .push_slot(TypeGraphSlotKind::FunctionParam, param_ty);
        let ret = self
            .graph
            .push_slot(TypeGraphSlotKind::FunctionResult, ret_ty);
        self.graph.push_edge(
            TypeGraphEdgeKind::ApplyArg,
            param,
            arg,
            TypeGraphEdgeProvenance::ApplyFunctionParam,
        );
        self.graph.push_edge(
            TypeGraphEdgeKind::ApplyResult,
            result,
            ret,
            TypeGraphEdgeProvenance::ApplyFunctionResult,
        );
    }

    fn apply_evidence(
        &mut self,
        evidence: &typed_ir::ApplyEvidence,
        callee: TypeGraphSlotId,
        arg: TypeGraphSlotId,
        result: TypeGraphSlotId,
    ) {
        let scope = self.graph.fresh_type_var_scope();
        let apply_origin = evidence
            .principal_callee
            .as_ref()
            .map(|ty| format!("apply principal={}", display_type(ty)));
        for substitution in &evidence.substitutions {
            self.graph
                .push_type_substitution_lower_evidence_with_origin(
                    scope,
                    TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
                    substitution,
                    apply_origin.clone(),
                );
        }
        for candidate in &evidence.substitution_candidates {
            self.graph.push_principal_candidate_lower_evidence(
                scope,
                candidate,
                apply_origin.clone(),
            );
        }
        if let Some(plan) = &evidence.principal_elaboration {
            let origin = plan.target.as_ref().map(|target| {
                format!(
                    "principal_elaboration target={} principal={}",
                    format_path(target),
                    display_type(&plan.principal_callee)
                )
            });
            for substitution in &plan.substitutions {
                self.graph
                    .push_type_substitution_lower_evidence_with_origin(
                        scope,
                        TypeGraphTypeVarEvidenceSource::PrincipalElaborationSubstitution,
                        substitution,
                        origin.clone(),
                    );
            }
        }
        self.graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyCallee,
            callee,
            &evidence.callee,
        );
        if let Some(ty) = choose_bounds_runtime_type(&evidence.callee) {
            let slot = self
                .graph
                .push_slot(TypeGraphSlotKind::ApplyEvidenceCallee, ty);
            self.graph.push_edge(
                TypeGraphEdgeKind::ApplyEvidence,
                slot,
                callee,
                TypeGraphEdgeProvenance::ApplyEvidence {
                    role: TypeGraphBoundsEvidenceRole::ApplyCallee,
                },
            );
        }
        let arg_bounds = evidence.expected_arg.as_ref().unwrap_or(&evidence.arg);
        self.graph
            .push_bounds_evidence(TypeGraphBoundsEvidenceRole::ApplyArg, arg, arg_bounds);
        if let Some(ty) = choose_bounds_runtime_type(arg_bounds) {
            let slot = self
                .graph
                .push_slot(TypeGraphSlotKind::ApplyEvidenceArg, ty);
            self.graph.push_edge(
                TypeGraphEdgeKind::ApplyEvidence,
                slot,
                arg,
                TypeGraphEdgeProvenance::ApplyEvidence {
                    role: TypeGraphBoundsEvidenceRole::ApplyArg,
                },
            );
        }
        self.graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyResult,
            result,
            &evidence.result,
        );
        if let Some(ty) = choose_bounds_runtime_type(&evidence.result) {
            let slot = self
                .graph
                .push_slot(TypeGraphSlotKind::ApplyEvidenceResult, ty);
            self.graph.push_edge(
                TypeGraphEdgeKind::ApplyEvidence,
                slot,
                result,
                TypeGraphEdgeProvenance::ApplyEvidence {
                    role: TypeGraphBoundsEvidenceRole::ApplyResult,
                },
            );
        }
    }

    fn type_instantiation(&mut self, instantiation: &TypeInstantiation) {
        let scope = self.graph.fresh_type_var_scope();
        let origin = Some(format!(
            "type_instantiation target={}",
            format_path(&instantiation.target)
        ));
        for substitution in &instantiation.args {
            self.graph
                .push_type_substitution_lower_evidence_with_origin(
                    scope,
                    TypeGraphTypeVarEvidenceSource::TypeInstantiation,
                    &typed_ir::TypeSubstitution {
                        var: substitution.var.clone(),
                        ty: substitution.ty.clone(),
                    },
                    origin.clone(),
                );
        }
    }

    fn record_spread_expr(&mut self, spread: &RecordSpreadExpr) {
        match spread {
            RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                self.expr(expr);
            }
        }
    }

    fn record_spread_pattern(&mut self, spread: &RecordSpreadPattern) {
        match spread {
            RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                self.pattern(pattern);
            }
        }
    }
}

fn classify_bounds_projection(bounds: &typed_ir::TypeBounds) -> TypeGraphBoundsProjection {
    let lower = bounds.lower.as_deref().cloned();
    let upper = bounds.upper.as_deref().cloned();
    match (lower, upper) {
        (None, None) => TypeGraphBoundsProjection::Empty,
        (Some(lower), None) if core_type_is_bottom_like_lower(&lower) => {
            TypeGraphBoundsProjection::BottomLikeLower { lower, upper: None }
        }
        (Some(lower), None) => TypeGraphBoundsProjection::LowerOnly { lower },
        (None, Some(upper)) => TypeGraphBoundsProjection::UpperOnly { upper },
        (Some(lower), Some(upper)) if core_type_is_bottom_like_lower(&lower) => {
            TypeGraphBoundsProjection::BottomLikeLower {
                lower,
                upper: Some(upper),
            }
        }
        (Some(lower), Some(upper)) if lower == upper => {
            TypeGraphBoundsProjection::Exact { ty: lower }
        }
        (Some(lower), Some(upper)) => TypeGraphBoundsProjection::LowerAndUpper {
            lower,
            upper,
            visible: choose_bounds_type(bounds, BoundsChoice::VisiblePrincipal),
        },
    }
}

fn core_type_is_bottom_like_lower(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any
    )
}

fn edge_kind_checks_direct_mismatch(kind: TypeGraphEdgeKind) -> bool {
    matches!(
        kind,
        TypeGraphEdgeKind::Equal
            | TypeGraphEdgeKind::ApplyCallee
            | TypeGraphEdgeKind::ApplyArg
            | TypeGraphEdgeKind::ApplyResult
            | TypeGraphEdgeKind::ApplyEvidence
            | TypeGraphEdgeKind::LambdaResult
            | TypeGraphEdgeKind::LetValuePattern
    )
}

fn edge_kind_propagates_lower(kind: TypeGraphEdgeKind) -> bool {
    edge_kind_checks_direct_mismatch(kind)
}

fn choose_bounds_runtime_type(bounds: &typed_ir::TypeBounds) -> Option<RuntimeType> {
    choose_bounds_type(bounds, BoundsChoice::VisiblePrincipal).map(RuntimeType::core)
}

fn runtime_function_parts(ty: &RuntimeType) -> Option<(RuntimeType, RuntimeType)> {
    match ty {
        RuntimeType::Fun { param, ret } => Some((param.as_ref().clone(), ret.as_ref().clone())),
        RuntimeType::Core(typed_ir::Type::Fun { param, ret, .. }) => Some((
            RuntimeType::core(param.as_ref().clone()),
            RuntimeType::core(ret.as_ref().clone()),
        )),
        RuntimeType::Unknown | RuntimeType::Core(_) | RuntimeType::Thunk { .. } => None,
    }
}

fn runtime_type_is_closed(ty: &RuntimeType) -> bool {
    !matches!(ty, RuntimeType::Unknown) && !hir_type_has_vars(ty)
}

fn runtime_type_is_bottom_like_lower(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_is_bottom_like_lower(ty),
        RuntimeType::Fun { .. } => false,
        RuntimeType::Thunk { value, .. } => runtime_type_is_bottom_like_lower(value),
    }
}

fn handler_output_lower_type(body_ty: &RuntimeType, handler: &HandleEffect) -> Option<RuntimeType> {
    let residual = handler.residual_after.as_ref()?;
    let value = runtime_value_type(body_ty);
    let effect = project_runtime_effect(residual);
    if should_thunk_effect(&effect) {
        Some(RuntimeType::thunk(effect, value))
    } else {
        Some(value)
    }
}

fn runtime_value_type(ty: &RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
        ty => ty.clone(),
    }
}

fn pattern_runtime_type(pattern: &Pattern) -> RuntimeType {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty.clone(),
    }
}

#[derive(Debug, Clone)]
struct TypeGraphUnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl TypeGraphUnionFind {
    fn new(len: usize) -> Self {
        Self {
            parent: (0..len).collect(),
            rank: vec![0; len],
        }
    }

    fn find(&mut self, value: usize) -> usize {
        let parent = self.parent[value];
        if parent == value {
            return value;
        }
        let root = self.find(parent);
        self.parent[value] = root;
        root
    }

    fn union(&mut self, left: usize, right: usize) {
        let left = self.find(left);
        let right = self.find(right);
        if left == right {
            return;
        }
        match self.rank[left].cmp(&self.rank[right]) {
            std::cmp::Ordering::Less => {
                self.parent[left] = right;
            }
            std::cmp::Ordering::Greater => {
                self.parent[right] = left;
            }
            std::cmp::Ordering::Equal => {
                self.parent[right] = left;
                self.rank[left] += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unit() -> typed_ir::Type {
        typed_ir::Type::Tuple(Vec::new())
    }

    fn named(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_owned())),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> typed_ir::Path {
        typed_ir::Path::from_name(typed_ir::Name(name.to_owned()))
    }

    fn effect_row(names: &[&str]) -> typed_ir::Type {
        typed_ir::Type::Row {
            items: names.iter().map(|name| named(name)).collect(),
            tail: Box::new(typed_ir::Type::Never),
        }
    }

    fn list_of(item: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_owned())),
            args: vec![typed_ir::TypeArg::Type(item)],
        }
    }

    fn named_with_args(name: &str, args: Vec<typed_ir::TypeArg>) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_owned())),
            args,
        }
    }

    fn var(name: &str) -> typed_ir::TypeVar {
        typed_ir::TypeVar(name.to_owned())
    }

    fn var_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Var(var(name))
    }

    #[test]
    fn bounds_projection_excludes_bottom_like_lower_with_upper() {
        let bounds = typed_ir::TypeBounds {
            lower: Some(Box::new(typed_ir::Type::Never)),
            upper: Some(Box::new(unit())),
        };

        assert_eq!(
            classify_bounds_projection(&bounds),
            TypeGraphBoundsProjection::BottomLikeLower {
                lower: typed_ir::Type::Never,
                upper: Some(unit()),
            }
        );
    }

    #[test]
    fn bounds_projection_marks_upper_only_dependency() {
        let bounds = typed_ir::TypeBounds::upper(unit());

        assert_eq!(
            classify_bounds_projection(&bounds),
            TypeGraphBoundsProjection::UpperOnly { upper: unit() }
        );
    }

    #[test]
    fn bounds_projection_keeps_inhabited_lower_candidate() {
        let bounds = typed_ir::TypeBounds::lower(unit());

        assert_eq!(
            classify_bounds_projection(&bounds),
            TypeGraphBoundsProjection::LowerOnly { lower: unit() }
        );
    }

    #[test]
    fn lower_snapshot_reports_conflicting_lower_candidates() {
        let mut graph = TypeGraph::default();
        let slot = graph.push_slot(TypeGraphSlotKind::Expr, RuntimeType::Unknown);
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyArg,
            slot,
            &typed_ir::TypeBounds::lower(unit()),
        );
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyArg,
            slot,
            &typed_ir::TypeBounds::lower(named("int")),
        );

        let report = graph.solve_lower_snapshot().report;

        assert_eq!(report.solved_slots, 0);
        assert_eq!(report.conflicting_lower_slots, 1);
        assert_eq!(report.closed_conflicting_lower_slots, 1);
        assert_eq!(report.conflicting_lower_groups, 1);
    }

    #[test]
    fn lower_snapshot_joins_compatible_numeric_lower_candidates() {
        let mut graph = TypeGraph::default();
        let slot = graph.push_slot(TypeGraphSlotKind::Expr, RuntimeType::Unknown);
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyArg,
            slot,
            &typed_ir::TypeBounds::lower(named("int")),
        );
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyArg,
            slot,
            &typed_ir::TypeBounds::lower(named("float")),
        );

        let solution = graph.solve_lower_snapshot();

        assert_eq!(
            solution.candidate(slot),
            Some(&RuntimeType::core(named("float")))
        );
        assert_eq!(solution.report.solved_slots, 1);
        assert_eq!(solution.report.conflicting_lower_slots, 0);
        assert_eq!(solution.report.conflicting_lower_groups, 0);
    }

    #[test]
    fn lower_snapshot_propagates_candidate_across_equal_edge() {
        let mut graph = TypeGraph::default();
        let source = graph.push_slot(TypeGraphSlotKind::ApplyArg, RuntimeType::Unknown);
        let target = graph.push_slot(TypeGraphSlotKind::Expr, RuntimeType::Unknown);
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyArg,
            source,
            &typed_ir::TypeBounds::lower(unit()),
        );
        graph.push_edge(
            TypeGraphEdgeKind::Equal,
            source,
            target,
            TypeGraphEdgeProvenance::ApplyArg,
        );

        let solution = graph.solve_lower_snapshot();

        assert_eq!(solution.candidate(source), Some(&RuntimeType::core(unit())));
        assert_eq!(solution.candidate(target), Some(&RuntimeType::core(unit())));
        assert_eq!(solution.report.solved_groups, 1);
        assert_eq!(solution.report.solved_slots, 2);
        assert_eq!(solution.report.lower_solution_checked_edges, 1);
        assert_eq!(solution.report.lower_solution_mismatched_edges, 0);
    }

    #[test]
    fn lower_snapshot_adds_handler_residual_output_lower_candidate() {
        let body_effect = effect_row(&["io", "log"]);
        let residual_after = effect_row(&["log"]);
        let int_ty = RuntimeType::core(named("int"));
        let body = Expr::typed(
            ExprKind::Thunk {
                effect: body_effect.clone(),
                value: int_ty.clone(),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".to_owned())),
                    int_ty.clone(),
                )),
            },
            RuntimeType::thunk(body_effect.clone(), int_ty.clone()),
        );
        let handle = Expr::typed(
            ExprKind::Handle {
                body: Box::new(body),
                arms: Vec::new(),
                evidence: JoinEvidence {
                    result: named("int"),
                },
                handler: HandleEffect {
                    consumes: vec![path("io")],
                    residual_before: Some(body_effect),
                    residual_after: Some(residual_after.clone()),
                },
            },
            RuntimeType::Unknown,
        );
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![handle],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let (graph, report) = build_type_graph(&module);
        let solution = graph.solve_lower_snapshot();
        let root = graph
            .slots
            .iter()
            .find(|slot| matches!(slot.kind, TypeGraphSlotKind::RootExpr { index: 0 }))
            .map(|slot| slot.id)
            .expect("root slot");

        assert_eq!(report.handler_result_bounds, 1);
        assert_eq!(
            solution.candidate(root),
            Some(&RuntimeType::thunk(residual_after, int_ty))
        );
    }

    #[test]
    fn upper_supplement_uses_upper_only_when_lower_is_missing() {
        let mut graph = TypeGraph::default();
        let slot = graph.push_slot(TypeGraphSlotKind::Expr, RuntimeType::Unknown);
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyResult,
            slot,
            &typed_ir::TypeBounds::upper(unit()),
        );

        let lower = graph.solve_lower_snapshot();
        let upper = graph.solve_upper_supplements(&lower);

        assert_eq!(lower.candidate(slot), None);
        assert_eq!(upper.candidate(slot), Some(&RuntimeType::core(unit())));
        assert_eq!(upper.report.upper_requirements, 1);
        assert_eq!(upper.report.supplemented_slots, 1);
        assert_eq!(upper.report.checked_against_lower, 0);
    }

    #[test]
    fn upper_supplement_checks_existing_lower_without_overwriting_it() {
        let mut graph = TypeGraph::default();
        let slot = graph.push_slot(TypeGraphSlotKind::Expr, RuntimeType::Unknown);
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyResult,
            slot,
            &typed_ir::TypeBounds {
                lower: Some(Box::new(named("int"))),
                upper: Some(Box::new(named("bool"))),
            },
        );

        let lower = graph.solve_lower_snapshot();
        let upper = graph.solve_upper_supplements(&lower);

        assert_eq!(
            lower.candidate(slot),
            Some(&RuntimeType::core(named("int")))
        );
        assert_eq!(upper.candidate(slot), None);
        assert_eq!(upper.report.checked_against_lower, 1);
        assert_eq!(upper.report.mismatched_with_lower, 1);
        assert_eq!(upper.report.supplemented_slots, 0);
    }

    #[test]
    fn final_defaults_fill_unresolved_value_and_effect_holes() {
        let mut graph = TypeGraph::default();
        graph.push_slot(TypeGraphSlotKind::Expr, RuntimeType::Unknown);
        graph.push_slot(
            TypeGraphSlotKind::Expr,
            RuntimeType::thunk(var_type("effect"), RuntimeType::core(var_type("value"))),
        );

        let lower = graph.solve_lower_snapshot();
        let upper = graph.solve_upper_supplements(&lower);
        let defaults = graph.solve_final_defaults(&lower, &upper);

        assert_eq!(defaults.filled_value_holes, 2);
        assert_eq!(defaults.filled_effect_holes, 1);
    }

    #[test]
    fn final_defaults_do_not_touch_upper_supplemented_slots() {
        let mut graph = TypeGraph::default();
        let slot = graph.push_slot(TypeGraphSlotKind::Expr, RuntimeType::Unknown);
        graph.push_bounds_evidence(
            TypeGraphBoundsEvidenceRole::ApplyResult,
            slot,
            &typed_ir::TypeBounds::upper(unit()),
        );

        let lower = graph.solve_lower_snapshot();
        let upper = graph.solve_upper_supplements(&lower);
        let defaults = graph.solve_final_defaults(&lower, &upper);

        assert_eq!(upper.candidate(slot), Some(&RuntimeType::core(unit())));
        assert_eq!(defaults.filled_value_holes, 0);
        assert_eq!(defaults.filled_effect_holes, 0);
    }

    #[test]
    fn direct_mismatch_report_keeps_apply_provenance() {
        let mut graph = TypeGraph::default();
        let evidence = graph.push_slot(
            TypeGraphSlotKind::ApplyEvidenceArg,
            RuntimeType::core(unit()),
        );
        let arg = graph.push_slot(TypeGraphSlotKind::ApplyArg, RuntimeType::core(named("int")));

        graph.push_edge(
            TypeGraphEdgeKind::ApplyEvidence,
            evidence,
            arg,
            TypeGraphEdgeProvenance::ApplyEvidence {
                role: TypeGraphBoundsEvidenceRole::ApplyArg,
            },
        );

        let report = graph.report();

        assert_eq!(report.direct_mismatches, 1);
        assert_eq!(report.direct_mismatch_apply_edges, 1);
        assert_eq!(report.direct_mismatch_equal_edges, 0);
        assert_eq!(report.direct_mismatch_let_edges, 0);
    }

    #[test]
    fn type_var_lower_report_solves_instantiation_var_from_lower() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: named("int"),
            },
        );

        let report = graph.type_var_lower_report();

        assert_eq!(report.evidence, 1);
        assert_eq!(report.vars, 1);
        assert_eq!(report.scoped_vars, 1);
        assert_eq!(report.solved_vars, 1);
        assert_eq!(report.closed_solved_vars, 1);
        assert_eq!(report.conflicting_vars, 0);
    }

    #[test]
    fn type_var_lower_report_joins_compatible_numeric_lower_candidates() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: named("int"),
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: named("float"),
            },
        );

        let report = graph.type_var_lower_report();

        assert_eq!(report.vars, 1);
        assert_eq!(report.scoped_vars, 1);
        assert_eq!(report.solved_vars, 1);
        assert_eq!(report.closed_solved_vars, 1);
        assert_eq!(report.conflicting_vars, 0);
    }

    #[test]
    fn type_var_lower_report_recursively_substitutes_scoped_candidates() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: var_type("b"),
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("b"),
                ty: named("int"),
            },
        );

        let solution = graph.solve_type_var_lowers();
        let report = &solution.report;

        assert_eq!(report.scoped_vars, 2);
        assert_eq!(report.solved_vars, 2);
        assert_eq!(report.closed_solved_vars, 2);
        assert_eq!(report.recursive_substitution_vars, 0);
        assert_eq!(report.closed_after_recursive_substitution_vars, 0);
        assert_eq!(report.residual_open_vars_after_recursive_substitution, 0);
        assert_eq!(
            report.residual_open_recursive_cycle_vars_after_substitution,
            0
        );
        assert_eq!(
            report.residual_open_missing_substitution_vars_after_substitution,
            0
        );
        assert_eq!(report.conflicting_vars, 0);
        assert_eq!(solution.substitution_count(), 2);
        assert_eq!(solution.candidate(scope, &var("a")), Some(&named("int")));
        assert_eq!(solution.candidate(scope, &var("b")), Some(&named("int")));
    }

    #[test]
    fn type_var_lower_solution_keeps_structural_cycles_unresolved() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: list_of(var_type("b")),
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("b"),
                ty: list_of(var_type("a")),
            },
        );

        let solution = graph.solve_type_var_lowers();
        let report = &solution.report;

        assert_eq!(report.scoped_vars, 2);
        assert_eq!(report.solved_vars, 2);
        assert_eq!(report.recursive_substitution_vars, 0);
        assert_eq!(report.residual_open_vars_after_recursive_substitution, 2);
        assert_eq!(
            report.residual_open_missing_substitution_vars_after_substitution,
            2
        );
        assert_eq!(solution.substitution_count(), 0);
    }

    #[test]
    fn type_var_lower_solution_decomposes_structural_candidates() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("xs"),
                ty: list_of(var_type("a")),
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("xs"),
                ty: list_of(named("int")),
            },
        );

        let solution = graph.solve_type_var_lowers();
        let report = &solution.report;

        assert_eq!(report.derived_structural_lower_evidence, 1);
        assert_eq!(report.scoped_vars, 2);
        assert_eq!(report.solved_vars, 2);
        assert_eq!(report.conflicting_vars, 0);
        assert_eq!(solution.candidate(scope, &var("a")), Some(&named("int")));
        assert_eq!(
            solution.candidate(scope, &var("xs")),
            Some(&list_of(named("int")))
        );
    }

    #[test]
    fn type_var_lower_solution_decomposes_structured_choice_candidate() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("xs"),
                ty: typed_ir::Type::Union(vec![list_of(var_type("a")), named("int")]),
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("xs"),
                ty: list_of(named("bool")),
            },
        );

        let solution = graph.solve_type_var_lowers();
        let report = &solution.report;

        assert_eq!(report.derived_structural_lower_evidence, 1);
        assert_eq!(report.conflicting_vars, 0);
        assert_eq!(solution.candidate(scope, &var("a")), Some(&named("bool")));
    }

    #[test]
    fn type_var_lower_solution_does_not_decompose_bare_var_choice_candidate() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("x"),
                ty: typed_ir::Type::Union(vec![var_type("a"), named("int")]),
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("x"),
                ty: named("bool"),
            },
        );

        let solution = graph.solve_type_var_lowers();
        let report = &solution.report;

        assert_eq!(report.derived_structural_lower_evidence, 0);
        assert_eq!(solution.candidate(scope, &var("a")), None);
    }

    #[test]
    fn type_var_lower_solution_decomposes_matching_effect_item() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        let template_effects = typed_ir::Type::Row {
            items: vec![named_with_args(
                "state",
                vec![typed_ir::TypeArg::Type(var_type("a"))],
            )],
            tail: Box::new(typed_ir::Type::Never),
        };
        let actual_effects = typed_ir::Type::Row {
            items: vec![
                named_with_args("io", vec![typed_ir::TypeArg::Type(named("unit"))]),
                named_with_args("state", vec![typed_ir::TypeArg::Type(named("int"))]),
            ],
            tail: Box::new(typed_ir::Type::Never),
        };
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("e"),
                ty: template_effects,
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("e"),
                ty: actual_effects,
            },
        );

        let solution = graph.solve_type_var_lowers();
        let report = &solution.report;

        assert_eq!(report.derived_structural_lower_evidence, 1);
        assert_eq!(solution.candidate(scope, &var("a")), Some(&named("int")));
    }

    #[test]
    fn type_var_lower_solution_ignores_different_effect_items() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        let template_effects = typed_ir::Type::Row {
            items: Vec::new(),
            tail: Box::new(var_type("rest")),
        };
        let actual_effects = typed_ir::Type::Row {
            items: vec![named_with_args(
                "io",
                vec![typed_ir::TypeArg::Type(named("unit"))],
            )],
            tail: Box::new(typed_ir::Type::Never),
        };
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("e"),
                ty: template_effects,
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("e"),
                ty: actual_effects,
            },
        );

        let solution = graph.solve_type_var_lowers();
        let report = &solution.report;

        assert_eq!(report.derived_structural_lower_evidence, 0);
        assert_eq!(solution.candidate(scope, &var("rest")), None);
    }

    #[test]
    fn type_var_lower_report_excludes_bottom_like_substitution() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: typed_ir::Type::Never,
            },
        );

        let report = graph.type_var_lower_report();

        assert_eq!(report.evidence, 1);
        assert_eq!(report.vars, 0);
        assert_eq!(report.bottom_like_exclusions, 1);
    }

    #[test]
    fn type_var_lower_report_excludes_identity_substitution() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::TypeInstantiation,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: var_type("a"),
            },
        );

        let report = graph.type_var_lower_report();

        assert_eq!(report.evidence, 1);
        assert_eq!(report.vars, 0);
        assert_eq!(report.identity_lower_exclusions, 1);
    }

    #[test]
    fn type_var_lower_report_keeps_call_site_scopes_separate() {
        let mut graph = TypeGraph::default();
        let first_call = graph.fresh_type_var_scope();
        let second_call = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            first_call,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: named("int"),
            },
        );
        graph.push_type_substitution_lower_evidence(
            second_call,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: named("bool"),
            },
        );

        let report = graph.type_var_lower_report();

        assert_eq!(report.vars, 1);
        assert_eq!(report.scoped_vars, 2);
        assert_eq!(report.vars_used_in_multiple_scopes, 1);
        assert_eq!(report.solved_vars, 2);
        assert_eq!(report.conflicting_vars, 0);
    }

    #[test]
    fn type_var_lower_report_classifies_conflict_sources() {
        let mut graph = TypeGraph::default();
        let scope = graph.fresh_type_var_scope();
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::ApplyEvidenceSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: named("int"),
            },
        );
        graph.push_type_substitution_lower_evidence(
            scope,
            TypeGraphTypeVarEvidenceSource::PrincipalElaborationSubstitution,
            &typed_ir::TypeSubstitution {
                var: var("a"),
                ty: named("bool"),
            },
        );

        let report = graph.type_var_lower_report();

        assert_eq!(report.conflicting_vars, 1);
        assert_eq!(report.conflicting_vars_with_apply_substitution, 1);
        assert_eq!(report.conflicting_vars_with_principal_elaboration, 1);
        assert_eq!(report.conflicting_vars_with_mixed_sources, 1);
    }

    #[test]
    fn role_bounds_report_separates_input_and_associated_lower() {
        let mut graph = TypeGraph::default();
        graph.push_role_bounds_evidence(
            TypeGraphRoleBoundsEvidenceSource::RequirementInput,
            &typed_ir::TypeBounds::lower(named("int")),
        );
        graph.push_role_bounds_evidence(
            TypeGraphRoleBoundsEvidenceSource::RequirementAssociated,
            &typed_ir::TypeBounds::lower(named("str")),
        );

        let report = graph.report();

        assert_eq!(report.role_bounds_evidence, 2);
        assert_eq!(report.role_input_lower_candidates, 1);
        assert_eq!(report.role_associated_lower_candidates, 1);
        assert_eq!(report.role_upper_only_dependencies, 0);
    }

    #[test]
    fn role_associated_resolution_adds_type_var_lower_from_input_lower() {
        let role = typed_ir::Path::from_name(typed_ir::Name("Fold".to_owned()));
        let item = typed_ir::Name("item".to_owned());
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: vec![Binding {
                name: typed_ir::Path::from_name(typed_ir::Name("uses_fold".to_owned())),
                type_params: Vec::new(),
                scheme: typed_ir::Scheme {
                    requirements: vec![typed_ir::RoleRequirement {
                        role: role.clone(),
                        args: vec![
                            typed_ir::RoleRequirementArg::Input(typed_ir::TypeBounds::exact(
                                list_of(named("int")),
                            )),
                            typed_ir::RoleRequirementArg::Associated {
                                name: item.clone(),
                                bounds: typed_ir::TypeBounds::exact(var_type("item")),
                            },
                        ],
                    }],
                    body: unit(),
                },
                body: Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::core(unit()),
                ),
            }],
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: vec![typed_ir::RoleImplGraphNode {
                role,
                inputs: vec![typed_ir::TypeBounds::exact(list_of(var_type("a")))],
                associated_types: vec![typed_ir::RecordField {
                    name: item,
                    value: typed_ir::TypeBounds::exact(var_type("a")),
                    optional: false,
                }],
                members: Vec::new(),
            }],
        };

        let (graph, report) = build_type_graph(&module);
        let type_vars = graph.type_var_lower_report();

        assert_eq!(report.role_associated_resolution_attempts, 1);
        assert_eq!(report.role_associated_resolution_resolved, 1);
        assert_eq!(report.role_associated_resolution_projected_type_vars, 2);
        assert_eq!(type_vars.evidence, 2);
        assert_eq!(type_vars.solved_vars, 2);
        assert_eq!(type_vars.closed_solved_vars, 2);
        assert_eq!(type_vars.conflicting_vars, 0);
    }
}
