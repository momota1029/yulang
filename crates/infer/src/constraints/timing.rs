//! Aggregate timing counters for the subtype constraint machine.
//!
//! The machine owns propagation semantics; this module only records how work
//! enters and drains through that machine so performance probes do not obscure
//! the main constraint data structures.

use crate::time::Duration;

use super::{
    BodyRequirementKind, BoundDirection, ConstraintOriginKind, RowDerivationRule,
    StructuralDerivationRule,
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConstraintOriginCoverage {
    pub application_argument: usize,
    pub annotation: usize,
    pub return_: usize,
    pub field: usize,
    pub assignment: usize,
    pub body_requirement: usize,
    pub internal: usize,
    pub unknown_internal: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BodyRequirementOriginCoverage {
    pub boolean_condition: usize,
    pub operator_operand: usize,
    pub pattern_guard: usize,
    pub callee_argument: usize,
    pub roots_lacking_location: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StructuralDerivationCoverage {
    pub full_unary: usize,
    pub normalization: usize,
    pub union_intersection: usize,
    pub function: usize,
    pub constructor: usize,
    pub tuple: usize,
    pub record: usize,
    pub variant: usize,
    pub row: usize,
    pub deferred_multi_parent: usize,
    pub unknown_rule: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RowDerivationCoverage {
    pub residual_created: usize,
    pub residual_reused: usize,
    pub unweighted_multi_parent: usize,
    pub row_item_match: usize,
    pub filter_invariant: usize,
    pub payload_invariant: usize,
    pub subtract_fact_transformation: usize,
    pub store_without_replay: usize,
    pub edges_inserted: usize,
    pub edges_deduplicated: usize,
    pub unexplained_propagation_paths: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BoundDispositionCoverage {
    pub inserted: usize,
    pub equivalent: usize,
    pub subsumed: usize,
    pub trivial: usize,
    pub tombstones: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StableRecordCoverage {
    pub ordinary_lower_created: usize,
    pub ordinary_upper_created: usize,
    pub evidence_lower_created: usize,
    pub evidence_upper_created: usize,
    pub lower_duplicate_provenance_merges: usize,
    pub upper_duplicate_provenance_merges: usize,
    pub promotions_identity_preserved: usize,
    pub subtract_fact_records_created: usize,
    pub subtract_fact_duplicate_provenance_merges: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReplayDerivationCoverage {
    pub considered: usize,
    pub inserted: usize,
    pub deduplicated: usize,
    pub budget_dropped: usize,
    pub semantic_duplicate_results: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReplayDerivationStorageMetrics {
    pub bytes_proxy: usize,
    pub max_incoming_per_record: usize,
    pub incomplete_records: usize,
    pub session_incomplete: bool,
}

impl ConstraintOriginCoverage {
    pub fn total(self) -> usize {
        self.application_argument
            + self.annotation
            + self.return_
            + self.field
            + self.assignment
            + self.body_requirement
            + self.internal
            + self.unknown_internal
    }

    fn record(&mut self, kind: ConstraintOriginKind) {
        let counter = match kind {
            ConstraintOriginKind::ApplicationArgument => &mut self.application_argument,
            ConstraintOriginKind::Annotation => &mut self.annotation,
            ConstraintOriginKind::Return => &mut self.return_,
            ConstraintOriginKind::Field => &mut self.field,
            ConstraintOriginKind::Assignment => &mut self.assignment,
            ConstraintOriginKind::BodyRequirement(_) => &mut self.body_requirement,
            ConstraintOriginKind::Internal => &mut self.internal,
            ConstraintOriginKind::UnknownInternal => &mut self.unknown_internal,
        };
        *counter += 1;
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConstraintTiming {
    pub drain: Duration,
    pub epoch: u64,
    pub provenance_epoch: u64,
    pub type_var_count: usize,
    pub row_tail_var_count: usize,
    pub pos_node_count: usize,
    pub neg_node_count: usize,
    pub neu_node_count: usize,
    pub type_node_count: usize,
    pub drains: usize,
    pub empty_drains: usize,
    pub initial_queue_items: usize,
    pub work_items: usize,
    pub subtype_work_items: usize,
    pub subtract_work_items: usize,
    pub max_initial_queue: usize,
    pub max_work_items: usize,
    pub subtype_calls: usize,
    pub subtype_many_calls: usize,
    pub subtype_many_items: usize,
    pub weighted_subtype_calls: usize,
    pub constrain_subtype_calls: usize,
    pub constrain_invariant_neu_calls: usize,
    pub constrain_var_var_direct_calls: usize,
    pub constrain_var_var_direct_pairs: usize,
    pub constrain_pos_var_direct_calls: usize,
    pub subtract_fact_calls: usize,
    pub canonical_subtype_constraints: usize,
    pub subtype_duplicate_admissions: usize,
    pub subtype_trivial_admissions: usize,
    pub root_origins: ConstraintOriginCoverage,
    pub body_requirement_origins: BodyRequirementOriginCoverage,
    pub structural_derivations: StructuralDerivationCoverage,
    pub row_derivations: RowDerivationCoverage,
    pub bound_dispositions: BoundDispositionCoverage,
    pub stable_records: StableRecordCoverage,
    pub replay_derivations: ReplayDerivationCoverage,
    pub replay_derivation_storage: ReplayDerivationStorageMetrics,
    pub lower_bounds_added: usize,
    pub upper_bounds_added: usize,
    pub row_upper_bounds_added_without_replay: usize,
    pub evidence_lower_bounds_added: usize,
    pub evidence_upper_bounds_added: usize,
    pub subtract_facts_added: usize,
    pub row_residuals_created: usize,
    pub row_residuals_reused: usize,
    pub nominal_cast_events: usize,
    pub lower_replay_inputs: usize,
    pub upper_replay_inputs: usize,
    pub lower_replay_enqueued: usize,
    pub upper_replay_enqueued: usize,
    pub lower_replay_var_var: usize,
    pub upper_replay_var_var: usize,
    pub lower_replay_accepted: usize,
    pub upper_replay_accepted: usize,
    pub lower_replay_evidence_only: usize,
    pub upper_replay_evidence_only: usize,
    pub lower_replay_duplicate: usize,
    pub upper_replay_duplicate: usize,
    pub lower_replay_trivial: usize,
    pub upper_replay_trivial: usize,
    pub lower_replay_prefiltered: usize,
    pub upper_replay_prefiltered: usize,
    pub lower_replay_prefilter_duplicate: ReplayDuplicateProfile,
    pub upper_replay_prefilter_duplicate: ReplayDuplicateProfile,
    pub replay_frontier_shadow_lower_var_var: ReplayFrontierShadowMetrics,
    pub replay_frontier_shadow_upper_var_var: ReplayFrontierShadowMetrics,
    pub replay_routing_shadow_var_var: ReplayRoutingShadowMetrics,
    pub replay_weighted_routing_shadow_var_var: ReplayWeightedRoutingShadowMetrics,
    pub max_lower_replay_inputs: usize,
    pub max_upper_replay_inputs: usize,
    pub max_lower_replay_enqueued: usize,
    pub max_upper_replay_enqueued: usize,
    pub max_lower_replay_var_var: usize,
    pub max_upper_replay_var_var: usize,
    pub max_lower_replay_accepted: usize,
    pub max_upper_replay_accepted: usize,
    pub max_lower_replay_evidence_only: usize,
    pub max_upper_replay_evidence_only: usize,
    pub max_lower_replay_duplicate: usize,
    pub max_upper_replay_duplicate: usize,
    pub max_lower_replay_trivial: usize,
    pub max_upper_replay_trivial: usize,
    pub max_lower_replay_prefiltered: usize,
    pub max_upper_replay_prefiltered: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReplayWeightedRoutingShadowMetrics {
    pub accepted_edges: usize,
    pub reachable_before_edges: usize,
    pub capped_searches: usize,
    pub search_states: usize,
    pub max_search_states: usize,
    pub frontier_inserted_edges: usize,
    pub frontier_skipped_edges: usize,
    pub frontier_capped_searches: usize,
    pub frontier_search_states: usize,
    pub frontier_max_search_states: usize,
    pub consequence_queries: usize,
    pub consequence_known: usize,
    pub consequence_known_unseen: usize,
    pub consequence_unknown: usize,
    pub consequence_unknown_seen: usize,
    pub consequence_capped_searches: usize,
    pub consequence_search_states: usize,
    pub consequence_max_search_states: usize,
    pub consequence_frontier_known: usize,
    pub consequence_frontier_known_unseen: usize,
    pub consequence_frontier_unknown: usize,
    pub consequence_frontier_unknown_seen: usize,
    pub consequence_frontier_capped_searches: usize,
    pub consequence_frontier_search_states: usize,
    pub consequence_frontier_max_search_states: usize,
    pub graph_nodes: usize,
    pub graph_edges: usize,
    pub frontier_graph_nodes: usize,
    pub frontier_graph_edges: usize,
    pub route_cache_hits: usize,
    pub frontier_route_cache_hits: usize,
    pub route_cache_entries: usize,
    pub frontier_route_cache_entries: usize,
    pub summary_observed_edges: usize,
    pub summary_known_edges: usize,
    pub summary_new_edges: usize,
    pub summary_inserted_paths: usize,
    pub summary_duplicate_paths: usize,
    pub summary_capped_insertions: usize,
    pub summary_max_queue: usize,
    pub summary_paths: usize,
    pub summary_outgoing_nodes: usize,
    pub summary_incoming_nodes: usize,
    pub weight_count: usize,
    pub compose_cache_hits: usize,
    pub compose_cache_misses: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReplayRoutingShadowMetrics {
    pub accepted_edges: usize,
    pub repeated_endpoint_edges: usize,
    pub reachable_before_edges: usize,
    pub graph_nodes: usize,
    pub graph_edges: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReplayFrontierShadowMetrics {
    pub candidates: usize,
    pub hits: usize,
    pub safe_hits: usize,
    pub unsafe_hits: usize,
    pub unsafe_accepted: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReplayDuplicateProfile {
    pub exact_key: usize,
    pub var_var_key: usize,
    pub terminal_weight_erased: usize,
    pub row_tail: usize,
}

impl ReplayDuplicateProfile {
    pub(super) fn absorb(&mut self, other: Self) {
        self.exact_key += other.exact_key;
        self.var_var_key += other.var_var_key;
        self.terminal_weight_erased += other.terminal_weight_erased;
        self.row_tail += other.row_tail;
    }
}

impl ConstraintTiming {
    pub(super) fn record_root_origin(&mut self, kind: ConstraintOriginKind) {
        self.root_origins.record(kind);
    }

    pub(super) fn record_body_requirement_origin(&mut self, kind: BodyRequirementKind) {
        let coverage = &mut self.body_requirement_origins;
        let counter = match kind {
            BodyRequirementKind::BooleanCondition => &mut coverage.boolean_condition,
            BodyRequirementKind::OperatorOperand { .. } => &mut coverage.operator_operand,
            BodyRequirementKind::PatternGuard => &mut coverage.pattern_guard,
            BodyRequirementKind::CalleeArgument { .. } => &mut coverage.callee_argument,
        };
        *counter += 1;
        coverage.roots_lacking_location += 1;
    }

    pub(super) fn record_body_requirement_location(&mut self) {
        self.body_requirement_origins.roots_lacking_location = self
            .body_requirement_origins
            .roots_lacking_location
            .checked_sub(1)
            .expect("a body-requirement location follows an allocated root");
    }

    pub(super) fn record_structural_derivation(&mut self, rule: StructuralDerivationRule) {
        let coverage = &mut self.structural_derivations;
        coverage.full_unary += 1;
        let counter = match rule {
            StructuralDerivationRule::LowerStackNormalization
            | StructuralDerivationRule::LowerNonSubtractNormalization
            | StructuralDerivationRule::UpperStackNormalization => &mut coverage.normalization,
            StructuralDerivationRule::UnionBranch { .. }
            | StructuralDerivationRule::IntersectionBranch { .. } => {
                &mut coverage.union_intersection
            }
            StructuralDerivationRule::FunctionArgument
            | StructuralDerivationRule::FunctionArgumentEffect { .. }
            | StructuralDerivationRule::FunctionReturnEffect
            | StructuralDerivationRule::FunctionReturn => &mut coverage.function,
            StructuralDerivationRule::ConstructorArgument { .. } => &mut coverage.constructor,
            StructuralDerivationRule::TupleElement { .. } => &mut coverage.tuple,
            StructuralDerivationRule::RecordField { .. }
            | StructuralDerivationRule::RecordSpreadField { .. }
            | StructuralDerivationRule::RecordSpreadTail { .. } => &mut coverage.record,
            StructuralDerivationRule::VariantPayload { .. } => &mut coverage.variant,
            StructuralDerivationRule::RowItem { .. }
            | StructuralDerivationRule::RowItemArgument { .. } => &mut coverage.row,
        };
        *counter += 1;
    }

    pub(super) fn record_structural_deferred_multi_parent(&mut self) {
        self.structural_derivations.deferred_multi_parent += 1;
    }

    pub(super) fn record_row_derivation(&mut self, rule: RowDerivationRule, inserted: bool) {
        let coverage = &mut self.row_derivations;
        if inserted {
            coverage.edges_inserted += 1;
        } else {
            coverage.edges_deduplicated += 1;
        }
        match rule {
            RowDerivationRule::WeightedResidual => {}
            RowDerivationRule::UnweightedReduction => coverage.unweighted_multi_parent += 1,
            RowDerivationRule::RowItemMatch => coverage.row_item_match += 1,
            RowDerivationRule::FilterInvariant => coverage.filter_invariant += 1,
            RowDerivationRule::PayloadInvariant => coverage.payload_invariant += 1,
            RowDerivationRule::SubtractFactTransformation => {
                coverage.subtract_fact_transformation += 1
            }
            RowDerivationRule::StoreUpperWithoutReplay => coverage.store_without_replay += 1,
        }
    }

    pub(super) fn record_row_residual_derivation(&mut self, reused: bool) {
        if reused {
            self.row_derivations.residual_reused += 1;
        } else {
            self.row_derivations.residual_created += 1;
        }
    }

    pub(super) fn record_bound_disposition(
        &mut self,
        disposition: super::BoundDisposition,
        tombstone: bool,
    ) {
        let coverage = &mut self.bound_dispositions;
        match disposition {
            super::BoundDisposition::Inserted(_) => coverage.inserted += 1,
            super::BoundDisposition::EquivalentTo(_) => coverage.equivalent += 1,
            super::BoundDisposition::SubsumedBy(_) => coverage.subsumed += 1,
            super::BoundDisposition::Trivial(_) => coverage.trivial += 1,
        }
        coverage.tombstones += usize::from(tombstone);
    }

    pub(super) fn record_bound_record(
        &mut self,
        direction: BoundDirection,
        evidence: bool,
        created: bool,
        duplicate_provenance_merge: bool,
        promoted: bool,
    ) {
        let coverage = &mut self.stable_records;
        if created {
            match (direction, evidence) {
                (BoundDirection::Lower, false) => coverage.ordinary_lower_created += 1,
                (BoundDirection::Upper, false) => coverage.ordinary_upper_created += 1,
                (BoundDirection::Lower, true) => coverage.evidence_lower_created += 1,
                (BoundDirection::Upper, true) => coverage.evidence_upper_created += 1,
            }
        }
        if duplicate_provenance_merge {
            match direction {
                BoundDirection::Lower => coverage.lower_duplicate_provenance_merges += 1,
                BoundDirection::Upper => coverage.upper_duplicate_provenance_merges += 1,
            }
        }
        if promoted {
            coverage.promotions_identity_preserved += 1;
        }
    }

    pub(super) fn record_subtract_fact_record(
        &mut self,
        created: bool,
        duplicate_provenance_merge: bool,
    ) {
        if created {
            self.stable_records.subtract_fact_records_created += 1;
        }
        if duplicate_provenance_merge {
            self.stable_records
                .subtract_fact_duplicate_provenance_merges += 1;
        }
    }

    pub(super) fn record_replay_derivation_edge(
        &mut self,
        inserted: bool,
        deduplicated: bool,
        budget_dropped: bool,
        semantic_duplicate_result: bool,
    ) {
        let coverage = &mut self.replay_derivations;
        coverage.considered += 1;
        coverage.inserted += usize::from(inserted);
        coverage.deduplicated += usize::from(deduplicated);
        coverage.budget_dropped += usize::from(budget_dropped);
        coverage.semantic_duplicate_results += usize::from(semantic_duplicate_result);
    }

    pub(super) fn record_subtype_call(&mut self) {
        self.subtype_calls += 1;
    }

    pub(super) fn record_subtype_many_call(&mut self, item_count: usize) {
        self.subtype_many_calls += 1;
        self.subtype_many_items += item_count;
    }

    pub(super) fn record_weighted_subtype_call(&mut self) {
        self.weighted_subtype_calls += 1;
    }

    pub(super) fn record_constrain_subtype_call(&mut self) {
        self.constrain_subtype_calls += 1;
    }

    pub(super) fn record_constrain_invariant_neu_call(&mut self) {
        self.constrain_invariant_neu_calls += 1;
    }

    pub(super) fn record_constrain_var_var_direct_call(&mut self, pair_count: usize) {
        self.constrain_var_var_direct_calls += 1;
        self.constrain_var_var_direct_pairs += pair_count;
    }

    pub(super) fn record_constrain_pos_var_direct_call(&mut self) {
        self.constrain_pos_var_direct_calls += 1;
    }

    pub(super) fn record_subtract_fact_call(&mut self) {
        self.subtract_fact_calls += 1;
    }

    pub(super) fn record_subtype_duplicate_admission(&mut self) {
        self.subtype_duplicate_admissions += 1;
    }

    pub(super) fn record_subtype_trivial_admission(&mut self) {
        self.subtype_trivial_admissions += 1;
    }

    pub(super) fn record_row_upper_bound_added_without_replay(&mut self) {
        self.row_upper_bounds_added_without_replay += 1;
    }

    pub(super) fn record_evidence_lower_bound_added(&mut self) {
        self.evidence_lower_bounds_added += 1;
    }

    pub(super) fn record_evidence_upper_bound_added(&mut self) {
        self.evidence_upper_bounds_added += 1;
    }

    pub(super) fn record_subtract_fact_added(&mut self) {
        self.subtract_facts_added += 1;
    }

    pub(super) fn record_row_residual_created(&mut self) {
        self.row_residuals_created += 1;
    }

    pub(super) fn record_row_residual_reused(&mut self) {
        self.row_residuals_reused += 1;
    }

    pub(super) fn record_nominal_cast_event(&mut self, _source: &[String], _target: &[String]) {
        self.nominal_cast_events += 1;
        #[cfg(test)]
        observe_nominal_cast_pair(_source, _target);
    }

    pub(super) fn record_lower_bound_added(
        &mut self,
        replay_inputs: usize,
        replay_enqueued: usize,
        replay_var_var: usize,
        replay_accepted: usize,
        replay_evidence_only: usize,
        replay_duplicate: usize,
        replay_trivial: usize,
        replay_prefiltered: usize,
        replay_prefilter_duplicate: ReplayDuplicateProfile,
    ) {
        self.lower_bounds_added += 1;
        self.lower_replay_inputs += replay_inputs;
        self.lower_replay_enqueued += replay_enqueued;
        self.lower_replay_var_var += replay_var_var;
        self.lower_replay_accepted += replay_accepted;
        self.lower_replay_evidence_only += replay_evidence_only;
        self.lower_replay_duplicate += replay_duplicate;
        self.lower_replay_trivial += replay_trivial;
        self.lower_replay_prefiltered += replay_prefiltered;
        self.lower_replay_prefilter_duplicate
            .absorb(replay_prefilter_duplicate);
        self.max_lower_replay_inputs = self.max_lower_replay_inputs.max(replay_inputs);
        self.max_lower_replay_enqueued = self.max_lower_replay_enqueued.max(replay_enqueued);
        self.max_lower_replay_var_var = self.max_lower_replay_var_var.max(replay_var_var);
        self.max_lower_replay_accepted = self.max_lower_replay_accepted.max(replay_accepted);
        self.max_lower_replay_evidence_only = self
            .max_lower_replay_evidence_only
            .max(replay_evidence_only);
        self.max_lower_replay_duplicate = self.max_lower_replay_duplicate.max(replay_duplicate);
        self.max_lower_replay_trivial = self.max_lower_replay_trivial.max(replay_trivial);
        self.max_lower_replay_prefiltered =
            self.max_lower_replay_prefiltered.max(replay_prefiltered);
    }

    pub(super) fn record_upper_bound_added(
        &mut self,
        replay_inputs: usize,
        replay_enqueued: usize,
        replay_var_var: usize,
        replay_accepted: usize,
        replay_evidence_only: usize,
        replay_duplicate: usize,
        replay_trivial: usize,
        replay_prefiltered: usize,
        replay_prefilter_duplicate: ReplayDuplicateProfile,
    ) {
        self.upper_bounds_added += 1;
        self.upper_replay_inputs += replay_inputs;
        self.upper_replay_enqueued += replay_enqueued;
        self.upper_replay_var_var += replay_var_var;
        self.upper_replay_accepted += replay_accepted;
        self.upper_replay_evidence_only += replay_evidence_only;
        self.upper_replay_duplicate += replay_duplicate;
        self.upper_replay_trivial += replay_trivial;
        self.upper_replay_prefiltered += replay_prefiltered;
        self.upper_replay_prefilter_duplicate
            .absorb(replay_prefilter_duplicate);
        self.max_upper_replay_inputs = self.max_upper_replay_inputs.max(replay_inputs);
        self.max_upper_replay_enqueued = self.max_upper_replay_enqueued.max(replay_enqueued);
        self.max_upper_replay_var_var = self.max_upper_replay_var_var.max(replay_var_var);
        self.max_upper_replay_accepted = self.max_upper_replay_accepted.max(replay_accepted);
        self.max_upper_replay_evidence_only = self
            .max_upper_replay_evidence_only
            .max(replay_evidence_only);
        self.max_upper_replay_duplicate = self.max_upper_replay_duplicate.max(replay_duplicate);
        self.max_upper_replay_trivial = self.max_upper_replay_trivial.max(replay_trivial);
        self.max_upper_replay_prefiltered =
            self.max_upper_replay_prefiltered.max(replay_prefiltered);
    }

    pub(super) fn record_drain(
        &mut self,
        elapsed: Duration,
        initial_queue: usize,
        work_items: usize,
        subtype_work_items: usize,
        subtract_work_items: usize,
    ) {
        self.drain += elapsed;
        self.drains += 1;
        if work_items == 0 {
            self.empty_drains += 1;
        }
        self.initial_queue_items += initial_queue;
        self.work_items += work_items;
        self.subtype_work_items += subtype_work_items;
        self.subtract_work_items += subtract_work_items;
        self.max_initial_queue = self.max_initial_queue.max(initial_queue);
        self.max_work_items = self.max_work_items.max(work_items);
    }
}

#[cfg(test)]
thread_local! {
    static NOMINAL_CAST_PAIR_CAPTURE:
        std::cell::RefCell<Option<Vec<(Vec<String>, Vec<String>)>>> = const {
            std::cell::RefCell::new(None)
        };
}

#[cfg(test)]
pub(super) fn begin_nominal_cast_pair_capture() {
    NOMINAL_CAST_PAIR_CAPTURE.with(|capture| {
        let previous = capture.borrow_mut().replace(Vec::new());
        assert!(
            previous.is_none(),
            "nominal-cast pair capture cannot be nested"
        );
    });
}

#[cfg(test)]
pub(super) fn finish_nominal_cast_pair_capture() -> Vec<(Vec<String>, Vec<String>)> {
    NOMINAL_CAST_PAIR_CAPTURE.with(|capture| capture.borrow_mut().take().unwrap_or_default())
}

#[cfg(test)]
fn observe_nominal_cast_pair(source: &[String], target: &[String]) {
    NOMINAL_CAST_PAIR_CAPTURE.with(|capture| {
        let mut capture = capture.borrow_mut();
        if let Some(pairs) = capture.as_mut() {
            pairs.push((source.to_vec(), target.to_vec()));
        }
    });
}
