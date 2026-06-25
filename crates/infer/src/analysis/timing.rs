//! Aggregate timing counters for the analysis coordinator.
//!
//! These counters are intentionally separate from environment-gated tracing.
//! They are cheap, always-collected phase metrics used by CLI timing output and
//! benchmark scripts.

use crate::time::Duration;

use super::{AnalysisWork, GeneralizeRootMetrics, SelectionTarget};
use crate::role_solve::RoleResolveStats;
use crate::scc::SccStats;
use poly::expr::DefId;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AnalysisTiming {
    pub route_constraints: Duration,
    pub route_scc_events: Duration,
    pub route_scc_open_use: Duration,
    pub route_scc_quantify: Duration,
    pub route_scc_instantiate: Duration,
    pub route_scc_other: Duration,
    pub scc_apply: Duration,
    pub work_total: Duration,
    pub work_resolve_ref: Duration,
    pub work_probe_select: Duration,
    pub work_apply_ref: Duration,
    pub work_apply_select: Duration,
    pub work_apply_select_record_field: Duration,
    pub work_apply_select_method: Duration,
    pub work_apply_select_effect_method: Duration,
    pub work_apply_select_typeclass_method: Duration,
    pub work_scc: Duration,
    pub work_resolve_ref_items: usize,
    pub work_probe_select_items: usize,
    pub work_apply_ref_items: usize,
    pub work_apply_select_items: usize,
    pub work_apply_select_record_field_items: usize,
    pub work_apply_select_method_items: usize,
    pub work_apply_select_effect_method_items: usize,
    pub work_apply_select_typeclass_method_items: usize,
    pub work_scc_items: usize,
    pub role_pass: Duration,
    pub method_taint: Duration,
    pub method_role_solve: Duration,
    pub unready_role_dependency_scan: Duration,
    pub enqueue_selection_probes: Duration,
    pub quantify: Duration,
    pub quantify_generalize: Duration,
    pub quantify_prerequisites: Duration,
    pub quantify_finalize: Duration,
    pub generalize_compact: Duration,
    pub generalize_collect_roles: Duration,
    pub generalize_apply_merge: Duration,
    pub generalize_collect_dominance: Duration,
    pub generalize_apply_subtype: Duration,
    pub generalize_cast: Duration,
    pub generalize_resolve_roles: Duration,
    pub generalize_final_roles: Duration,
    pub generalize_final_cleanup: Duration,
    pub generalize_filter_roles: Duration,
    pub generalize_prepared: Duration,
    pub instantiate: Duration,
    pub instantiate_clone_scheme: Duration,
    pub instantiate_subtype_predicate: Duration,
    pub instantiate_insert_roles: Duration,
    pub record_field_fallback: Duration,
    pub constraint_event_batches: usize,
    pub constraint_events: usize,
    pub scc_event_batches: usize,
    pub scc_events: usize,
    pub scc_open_use_events: usize,
    pub scc_quantify_events: usize,
    pub scc_instantiate_events: usize,
    pub scc_other_events: usize,
    pub scc_reachability_calls: usize,
    pub scc_reachability_nodes_visited: usize,
    pub scc_reachability_edges_visited: usize,
    pub scc_merge_count: usize,
    pub scc_merged_component_count: usize,
    pub scc_rebuilt_edges: usize,
    pub scc_rebuilt_edge_payloads: usize,
    pub scc_duplicate_dependency_payloads: usize,
    pub scc_payload_sorts: usize,
    pub scc_payload_sort_total_len: usize,
    pub scc_pending_use_scans: usize,
    pub scc_pending_use_scan_count: usize,
    pub scc_ready_component_checks: usize,
    pub scc_ready_member_checks: usize,
    pub work_items: usize,
    pub max_queue: usize,
    pub role_passes: usize,
    pub progressed_role_passes: usize,
    pub unready_role_dependency_scans: usize,
    pub unready_role_dependency_inputs: usize,
    pub unready_role_dependency_edges: usize,
    pub quantified_components: usize,
    pub quantified_defs: usize,
    pub quantify_single_def_components: usize,
    pub quantify_multi_def_components: usize,
    pub quantify_max_component_defs: usize,
    pub generalize_iterations: usize,
    pub generalize_merge_restarts: usize,
    pub generalize_subtype_restarts: usize,
    pub generalize_cast_restarts: usize,
    pub generalize_role_restarts: usize,
    pub quantify_generalize_roots_with_restarts: usize,
    pub quantify_generalize_max_iterations_per_root: usize,
    pub quantify_generalize_max_restarts_per_root: usize,
    pub generalize_top_restart_root: Option<DefId>,
    pub generalize_top_restart_iterations: usize,
    pub generalize_top_restart_constraint_epoch_start: u64,
    pub generalize_top_restart_constraint_epoch_end: u64,
    pub generalize_top_restart_constraint_epoch_delta: u64,
    pub generalize_top_restart_role_epoch_start: u64,
    pub generalize_top_restart_role_epoch_end: u64,
    pub generalize_top_restart_role_epoch_delta: u64,
    pub generalize_top_restart_total_restarts: usize,
    pub generalize_top_restart_merge_restarts: usize,
    pub generalize_top_restart_subtype_restarts: usize,
    pub generalize_top_restart_cast_restarts: usize,
    pub generalize_top_restart_role_restarts: usize,
    pub generalize_top_restart_first_compact_nodes: usize,
    pub generalize_top_restart_first_compact_vars: usize,
    pub generalize_top_restart_compact_iteration_nodes: usize,
    pub generalize_top_restart_compact_iteration_vars: usize,
    pub generalize_top_restart_role_input_constraints: usize,
    pub generalize_top_restart_reachable_role_constraints: usize,
    pub generalize_top_restart_coalesced_role_constraints: usize,
    pub generalize_top_restart_dominance_role_constraints: usize,
    pub generalize_top_restart_dominance_subtype_constraints: usize,
    pub generalize_top_restart_role_resolve_inputs: usize,
    pub generalize_top_restart_role_resolutions: usize,
    pub generalize_compact_shadow_requests: usize,
    pub generalize_compact_shadow_hits: usize,
    pub generalize_compact_shadow_misses: usize,
    pub generalize_role_input_constraints: usize,
    pub generalize_reachable_role_constraints: usize,
    pub generalize_coalesced_role_constraints: usize,
    pub generalize_dominance_role_constraints: usize,
    pub generalize_role_resolve_inputs: usize,
    pub role_resolve_demands: usize,
    pub role_resolve_candidate_scans: usize,
    pub role_resolve_candidate_matches: usize,
    pub role_resolve_ambiguous_demands: usize,
    pub role_resolve_already_applied: usize,
    pub role_resolve_prerequisite_demands: usize,
    pub role_resolve_prerequisite_candidate_scans: usize,
    pub role_resolve_prerequisite_candidate_matches: usize,
    pub role_resolve_candidate_cache_hits: usize,
    pub role_resolve_candidate_cache_misses: usize,
    pub generalize_merge_constraints: usize,
    pub generalize_subtype_constraints: usize,
    pub generalize_cast_batches: usize,
    pub generalize_cast_applications: usize,
    pub generalize_role_resolutions: usize,
    pub generalize_root_compact_nodes: usize,
    pub generalize_root_compact_vars: usize,
    pub generalize_component_unique_compact_vars: usize,
    pub generalize_compact_iteration_nodes: usize,
    pub generalize_compact_iteration_vars: usize,
    pub instantiated_uses: usize,
    pub instantiate_predicate_var: usize,
    pub instantiate_predicate_stack: usize,
    pub instantiate_predicate_non_subtract: usize,
    pub instantiate_predicate_fun: usize,
    pub instantiate_predicate_con: usize,
    pub instantiate_predicate_other: usize,
    pub instantiate_direct_lower_predicates: usize,
    pub instantiate_event_runs: usize,
    pub instantiate_max_event_run: usize,
    pub instantiate_unique_targets: usize,
    pub instantiate_reused_target_events: usize,
    pub record_field_batches: usize,
    pub record_field_selections: usize,
    pub record_field_constraints: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AnalysisWorkTimingKind {
    ResolveRef,
    ProbeSelect,
    ApplyRef,
    ApplySelect(AnalysisSelectionTargetTimingKind),
    Scc,
}

impl AnalysisWorkTimingKind {
    pub(super) fn from_work(work: &AnalysisWork) -> Self {
        match work {
            AnalysisWork::ResolveRef(_) => Self::ResolveRef,
            AnalysisWork::ProbeSelect(_) => Self::ProbeSelect,
            AnalysisWork::ApplyRefResolution { .. } => Self::ApplyRef,
            AnalysisWork::ApplySelectionResolution { target, .. } => {
                Self::ApplySelect(AnalysisSelectionTargetTimingKind::from_target(target))
            }
            AnalysisWork::Scc(_) => Self::Scc,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AnalysisSelectionTargetTimingKind {
    RecordField,
    Method,
    EffectMethod,
    TypeclassMethod,
}

impl AnalysisSelectionTargetTimingKind {
    fn from_target(target: &SelectionTarget) -> Self {
        match target {
            SelectionTarget::RecordField => Self::RecordField,
            SelectionTarget::Method { .. } => Self::Method,
            SelectionTarget::EffectMethod { .. } => Self::EffectMethod,
            SelectionTarget::TypeclassMethod { .. } => Self::TypeclassMethod,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AnalysisSccEventTimingKind {
    OpenUse,
    Quantify,
    Instantiate,
    Other,
}

impl AnalysisTiming {
    pub(super) fn record_route_constraints(&mut self, elapsed: Duration, event_count: usize) {
        self.route_constraints += elapsed;
        self.constraint_event_batches += 1;
        self.constraint_events += event_count;
    }

    pub(super) fn record_route_scc_events(&mut self, elapsed: Duration, event_count: usize) {
        self.route_scc_events += elapsed;
        self.scc_event_batches += 1;
        self.scc_events += event_count;
    }

    pub(super) fn record_scc_apply(&mut self, elapsed: Duration) {
        self.scc_apply += elapsed;
    }

    pub(super) fn record_scc_stats(&mut self, stats: SccStats) {
        self.scc_reachability_calls = stats.reachability_calls;
        self.scc_reachability_nodes_visited = stats.reachability_nodes_visited;
        self.scc_reachability_edges_visited = stats.reachability_edges_visited;
        self.scc_merge_count = stats.merge_count;
        self.scc_merged_component_count = stats.merged_component_count;
        self.scc_rebuilt_edges = stats.rebuilt_edges;
        self.scc_rebuilt_edge_payloads = stats.rebuilt_edge_payloads;
        self.scc_duplicate_dependency_payloads = stats.duplicate_dependency_payloads;
        self.scc_payload_sorts = stats.payload_sorts;
        self.scc_payload_sort_total_len = stats.payload_sort_total_len;
        self.scc_pending_use_scans = stats.pending_use_scans;
        self.scc_pending_use_scan_count = stats.pending_use_scan_count;
        self.scc_ready_component_checks = stats.ready_component_checks;
        self.scc_ready_member_checks = stats.ready_member_checks;
    }

    pub(super) fn record_route_scc_event(
        &mut self,
        kind: AnalysisSccEventTimingKind,
        elapsed: Duration,
    ) {
        self.record_route_scc_event_batch(kind, elapsed, 1);
    }

    pub(super) fn record_route_scc_event_batch(
        &mut self,
        kind: AnalysisSccEventTimingKind,
        elapsed: Duration,
        event_count: usize,
    ) {
        match kind {
            AnalysisSccEventTimingKind::OpenUse => {
                self.route_scc_open_use += elapsed;
                self.scc_open_use_events += event_count;
            }
            AnalysisSccEventTimingKind::Quantify => {
                self.route_scc_quantify += elapsed;
                self.scc_quantify_events += event_count;
            }
            AnalysisSccEventTimingKind::Instantiate => {
                self.route_scc_instantiate += elapsed;
                self.scc_instantiate_events += event_count;
            }
            AnalysisSccEventTimingKind::Other => {
                self.route_scc_other += elapsed;
                self.scc_other_events += event_count;
            }
        }
    }

    pub(super) fn record_work(
        &mut self,
        kind: AnalysisWorkTimingKind,
        elapsed: Duration,
        queue_len: usize,
    ) {
        self.work_total += elapsed;
        self.work_items += 1;
        self.max_queue = self.max_queue.max(queue_len);
        match kind {
            AnalysisWorkTimingKind::ResolveRef => {
                self.work_resolve_ref += elapsed;
                self.work_resolve_ref_items += 1;
            }
            AnalysisWorkTimingKind::ProbeSelect => {
                self.work_probe_select += elapsed;
                self.work_probe_select_items += 1;
            }
            AnalysisWorkTimingKind::ApplyRef => {
                self.work_apply_ref += elapsed;
                self.work_apply_ref_items += 1;
            }
            AnalysisWorkTimingKind::ApplySelect(target) => {
                self.work_apply_select += elapsed;
                self.work_apply_select_items += 1;
                match target {
                    AnalysisSelectionTargetTimingKind::RecordField => {
                        self.work_apply_select_record_field += elapsed;
                        self.work_apply_select_record_field_items += 1;
                    }
                    AnalysisSelectionTargetTimingKind::Method => {
                        self.work_apply_select_method += elapsed;
                        self.work_apply_select_method_items += 1;
                    }
                    AnalysisSelectionTargetTimingKind::EffectMethod => {
                        self.work_apply_select_effect_method += elapsed;
                        self.work_apply_select_effect_method_items += 1;
                    }
                    AnalysisSelectionTargetTimingKind::TypeclassMethod => {
                        self.work_apply_select_typeclass_method += elapsed;
                        self.work_apply_select_typeclass_method_items += 1;
                    }
                }
            }
            AnalysisWorkTimingKind::Scc => {
                self.work_scc += elapsed;
                self.work_scc_items += 1;
            }
        }
    }

    pub(super) fn record_role_pass(&mut self, elapsed: Duration, progressed: bool) {
        self.role_pass += elapsed;
        self.role_passes += 1;
        if progressed {
            self.progressed_role_passes += 1;
        }
    }

    pub(super) fn record_method_taint(&mut self, elapsed: Duration) {
        self.method_taint += elapsed;
    }

    pub(super) fn record_method_role_solve(&mut self, elapsed: Duration) {
        self.method_role_solve += elapsed;
    }

    pub(super) fn record_unready_role_dependency_scan(
        &mut self,
        elapsed: Duration,
        input_count: usize,
        edge_count: usize,
    ) {
        self.unready_role_dependency_scan += elapsed;
        self.unready_role_dependency_scans += 1;
        self.unready_role_dependency_inputs += input_count;
        self.unready_role_dependency_edges += edge_count;
    }

    pub(super) fn record_enqueue_selection_probes(&mut self, elapsed: Duration) {
        self.enqueue_selection_probes += elapsed;
    }

    pub(super) fn record_quantify(&mut self, elapsed: Duration, def_count: usize) {
        self.quantify += elapsed;
        self.quantified_components += 1;
        self.quantified_defs += def_count;
        if def_count <= 1 {
            self.quantify_single_def_components += 1;
        } else {
            self.quantify_multi_def_components += 1;
        }
        self.quantify_max_component_defs = self.quantify_max_component_defs.max(def_count);
    }

    pub(super) fn record_quantify_generalize(&mut self, elapsed: Duration) {
        self.quantify_generalize += elapsed;
    }

    pub(super) fn record_quantify_prerequisites(&mut self, elapsed: Duration) {
        self.quantify_prerequisites += elapsed;
    }

    pub(super) fn record_quantify_finalize(&mut self, elapsed: Duration) {
        self.quantify_finalize += elapsed;
    }

    pub(super) fn record_generalize_iteration(&mut self) {
        self.generalize_iterations += 1;
    }

    pub(super) fn record_generalize_merge_restart(&mut self) {
        self.generalize_merge_restarts += 1;
    }

    pub(super) fn record_generalize_subtype_restart(&mut self) {
        self.generalize_subtype_restarts += 1;
    }

    pub(super) fn record_generalize_cast_restart(&mut self) {
        self.generalize_cast_restarts += 1;
    }

    pub(super) fn record_generalize_role_restart(&mut self) {
        self.generalize_role_restarts += 1;
    }

    pub(super) fn record_generalize_compact_shadow(&mut self, hit: bool) {
        self.generalize_compact_shadow_requests += 1;
        if hit {
            self.generalize_compact_shadow_hits += 1;
        } else {
            self.generalize_compact_shadow_misses += 1;
        }
    }

    pub(super) fn record_generalize_root_summary(
        &mut self,
        def: DefId,
        metrics: &GeneralizeRootMetrics,
    ) {
        let restart_count = metrics.restart_count();
        if restart_count == 0 {
            return;
        }

        let new_score = (
            restart_count,
            metrics.iterations,
            metrics.first_compact_nodes,
            metrics.first_compact_vars.len(),
            def.0,
        );
        let current_score = (
            self.generalize_top_restart_total_restarts,
            self.generalize_top_restart_iterations,
            self.generalize_top_restart_first_compact_nodes,
            self.generalize_top_restart_first_compact_vars,
            self.generalize_top_restart_root
                .map(|root| root.0)
                .unwrap_or(0),
        );
        if self.generalize_top_restart_root.is_some() && new_score <= current_score {
            return;
        }

        self.generalize_top_restart_root = Some(def);
        self.generalize_top_restart_iterations = metrics.iterations;
        self.generalize_top_restart_constraint_epoch_start =
            metrics.constraint_epoch_start.as_u64();
        self.generalize_top_restart_constraint_epoch_end = metrics.constraint_epoch_end.as_u64();
        self.generalize_top_restart_constraint_epoch_delta = metrics.constraint_epoch_delta();
        self.generalize_top_restart_role_epoch_start = metrics.role_epoch_start.as_u64();
        self.generalize_top_restart_role_epoch_end = metrics.role_epoch_end.as_u64();
        self.generalize_top_restart_role_epoch_delta = metrics.role_epoch_delta();
        self.generalize_top_restart_total_restarts = restart_count;
        self.generalize_top_restart_merge_restarts = metrics.merge_restarts;
        self.generalize_top_restart_subtype_restarts = metrics.subtype_restarts;
        self.generalize_top_restart_cast_restarts = metrics.cast_restarts;
        self.generalize_top_restart_role_restarts = metrics.role_restarts;
        self.generalize_top_restart_first_compact_nodes = metrics.first_compact_nodes;
        self.generalize_top_restart_first_compact_vars = metrics.first_compact_vars.len();
        self.generalize_top_restart_compact_iteration_nodes = metrics.compact_iteration_nodes;
        self.generalize_top_restart_compact_iteration_vars = metrics.compact_iteration_vars;
        self.generalize_top_restart_role_input_constraints = metrics.role_input_constraints;
        self.generalize_top_restart_reachable_role_constraints = metrics.reachable_role_constraints;
        self.generalize_top_restart_coalesced_role_constraints = metrics.coalesced_role_constraints;
        self.generalize_top_restart_dominance_role_constraints = metrics.dominance_role_constraints;
        self.generalize_top_restart_dominance_subtype_constraints =
            metrics.dominance_subtype_constraints;
        self.generalize_top_restart_role_resolve_inputs = metrics.role_resolve_inputs;
        self.generalize_top_restart_role_resolutions = metrics.role_resolutions;
    }

    pub(super) fn record_generalize_role_constraints(
        &mut self,
        input_count: usize,
        reachable_count: usize,
        coalesced_count: usize,
    ) {
        self.generalize_role_input_constraints += input_count;
        self.generalize_reachable_role_constraints += reachable_count;
        self.generalize_coalesced_role_constraints += coalesced_count;
    }

    pub(super) fn record_generalize_dominance_roles(&mut self, count: usize) {
        self.generalize_dominance_role_constraints += count;
    }

    pub(super) fn record_generalize_role_resolve_inputs(&mut self, count: usize) {
        self.generalize_role_resolve_inputs += count;
    }

    pub(super) fn record_role_resolve_stats(&mut self, stats: RoleResolveStats) {
        self.role_resolve_demands += stats.demands;
        self.role_resolve_candidate_scans += stats.candidate_scans;
        self.role_resolve_candidate_matches += stats.candidate_matches;
        self.role_resolve_ambiguous_demands += stats.ambiguous_demands;
        self.role_resolve_already_applied += stats.already_applied;
        self.role_resolve_prerequisite_demands += stats.prerequisite_demands;
        self.role_resolve_prerequisite_candidate_scans += stats.prerequisite_candidate_scans;
        self.role_resolve_prerequisite_candidate_matches += stats.prerequisite_candidate_matches;
        self.role_resolve_candidate_cache_hits += stats.candidate_cache_hits;
        self.role_resolve_candidate_cache_misses += stats.candidate_cache_misses;
    }

    pub(super) fn record_generalize_component_shape(
        &mut self,
        root_compact_nodes: usize,
        root_compact_vars: usize,
        component_unique_compact_vars: usize,
        compact_iteration_nodes: usize,
        compact_iteration_vars: usize,
        roots_with_restarts: usize,
        max_iterations_per_root: usize,
        max_restarts_per_root: usize,
    ) {
        self.generalize_root_compact_nodes += root_compact_nodes;
        self.generalize_root_compact_vars += root_compact_vars;
        self.generalize_component_unique_compact_vars += component_unique_compact_vars;
        self.generalize_compact_iteration_nodes += compact_iteration_nodes;
        self.generalize_compact_iteration_vars += compact_iteration_vars;
        self.quantify_generalize_roots_with_restarts += roots_with_restarts;
        self.quantify_generalize_max_iterations_per_root = self
            .quantify_generalize_max_iterations_per_root
            .max(max_iterations_per_root);
        self.quantify_generalize_max_restarts_per_root = self
            .quantify_generalize_max_restarts_per_root
            .max(max_restarts_per_root);
    }

    pub(super) fn record_generalize_compact(&mut self, elapsed: Duration) {
        self.generalize_compact += elapsed;
    }

    pub(super) fn record_generalize_collect_roles(&mut self, elapsed: Duration) {
        self.generalize_collect_roles += elapsed;
    }

    pub(super) fn record_generalize_apply_merge(
        &mut self,
        elapsed: Duration,
        constraint_count: usize,
    ) {
        self.generalize_apply_merge += elapsed;
        self.generalize_merge_constraints += constraint_count;
    }

    pub(super) fn record_generalize_collect_dominance(&mut self, elapsed: Duration) {
        self.generalize_collect_dominance += elapsed;
    }

    pub(super) fn record_generalize_apply_subtype(
        &mut self,
        elapsed: Duration,
        constraint_count: usize,
    ) {
        self.generalize_apply_subtype += elapsed;
        self.generalize_subtype_constraints += constraint_count;
    }

    pub(super) fn record_generalize_cast(
        &mut self,
        elapsed: Duration,
        batch_count: usize,
        application_count: usize,
    ) {
        self.generalize_cast += elapsed;
        self.generalize_cast_batches += batch_count;
        self.generalize_cast_applications += application_count;
    }

    pub(super) fn record_generalize_resolve_roles(
        &mut self,
        elapsed: Duration,
        resolution_count: usize,
    ) {
        self.generalize_resolve_roles += elapsed;
        self.generalize_role_resolutions += resolution_count;
    }

    pub(super) fn record_generalize_final_roles(&mut self, elapsed: Duration) {
        self.generalize_final_roles += elapsed;
    }

    pub(super) fn record_generalize_final_cleanup(&mut self, elapsed: Duration) {
        self.generalize_final_cleanup += elapsed;
    }

    pub(super) fn record_generalize_filter_roles(&mut self, elapsed: Duration) {
        self.generalize_filter_roles += elapsed;
    }

    pub(super) fn record_generalize_prepared(&mut self, elapsed: Duration) {
        self.generalize_prepared += elapsed;
    }

    pub(super) fn record_instantiate_batch(&mut self, elapsed: Duration, use_count: usize) {
        self.instantiate += elapsed;
        self.instantiated_uses += use_count;
    }

    pub(super) fn record_instantiate_predicate_shape(&mut self, shape: InstantiatePredicateShape) {
        match shape {
            InstantiatePredicateShape::Var => self.instantiate_predicate_var += 1,
            InstantiatePredicateShape::Stack => self.instantiate_predicate_stack += 1,
            InstantiatePredicateShape::NonSubtract => self.instantiate_predicate_non_subtract += 1,
            InstantiatePredicateShape::Fun => self.instantiate_predicate_fun += 1,
            InstantiatePredicateShape::Con => self.instantiate_predicate_con += 1,
            InstantiatePredicateShape::Other => self.instantiate_predicate_other += 1,
        }
    }

    pub(super) fn record_instantiate_direct_lower_predicate(&mut self) {
        self.instantiate_direct_lower_predicates += 1;
    }

    pub(super) fn record_instantiate_event_run(&mut self, run_len: usize) {
        if run_len == 0 {
            return;
        }
        self.instantiate_event_runs += 1;
        self.instantiate_max_event_run = self.instantiate_max_event_run.max(run_len);
    }

    pub(super) fn record_instantiate_target(&mut self, was_new: bool) {
        if was_new {
            self.instantiate_unique_targets += 1;
        } else {
            self.instantiate_reused_target_events += 1;
        }
    }

    pub(super) fn record_instantiate_clone_scheme(&mut self, elapsed: Duration) {
        self.instantiate_clone_scheme += elapsed;
    }

    pub(super) fn record_instantiate_subtype_predicate(&mut self, elapsed: Duration) {
        self.instantiate_subtype_predicate += elapsed;
    }

    pub(super) fn record_instantiate_insert_roles(&mut self, elapsed: Duration) {
        self.instantiate_insert_roles += elapsed;
    }

    pub(super) fn record_field_fallback(
        &mut self,
        elapsed: Duration,
        selections: usize,
        constraints: usize,
    ) {
        self.record_field_fallback += elapsed;
        self.record_field_batches += 1;
        self.record_field_selections += selections;
        self.record_field_constraints += constraints;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum InstantiatePredicateShape {
    Var,
    Stack,
    NonSubtract,
    Fun,
    Con,
    Other,
}
