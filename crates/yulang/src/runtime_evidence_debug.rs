//! Debug output for `debug runtime-evidence-run` / `debug evidence-vm-run`.
//!
//! The runtime owns the counters; this module only decides how the CLI prints them.

use crate::{
    RuntimeEvidenceBenchSummary, RuntimeEvidenceRunTimings, RuntimePhaseTimings, format_duration,
};

pub(crate) fn print_run_report(
    summary: &RuntimeEvidenceBenchSummary,
    output: &evidence_vm::RuntimeEvidenceRunOutput,
    timings: &RuntimeEvidenceRunTimings,
    build_timings: &RuntimePhaseTimings,
) {
    println!("runtime evidence run:");
    println!("  evidence.tasks: {}", summary.tasks);
    println!("  evidence.nodes: {}", summary.nodes);
    println!(
        "  evidence.node_evidence_refs: {}",
        summary.node_evidence_refs
    );
    println!(
        "  evidence.plan_provider_slots: {}",
        output.evidence_stats.plan_provider_slots
    );
    println!(
        "  evidence.plan_provider_candidates: {}",
        output.evidence_stats.plan_provider_candidates
    );
    println!(
        "  evidence.plan_env_provider_slots: {}",
        output.evidence_stats.plan_env_provider_slots
    );
    println!(
        "  evidence.plan_env_provider_candidates: {}",
        output.evidence_stats.plan_env_provider_candidates
    );
    println!(
        "  evidence.plan_direct_candidates: {}",
        output.evidence_stats.plan_direct_candidates
    );
    println!(
        "  evidence.plan_effect_routes: {}",
        output.evidence_stats.plan_effect_routes
    );
    println!(
        "  evidence.plan_direct_effect_routes: {}",
        output.evidence_stats.plan_direct_effect_routes
    );
    println!(
        "  evidence.plan_direct_abortive_effect_routes: {}",
        output.evidence_stats.plan_direct_abortive_effect_routes
    );
    println!(
        "  evidence.plan_direct_tail_resumptive_effect_routes: {}",
        output
            .evidence_stats
            .plan_direct_tail_resumptive_effect_routes
    );
    println!(
        "  runtime_evidence.provider_env_values: {}",
        output.evidence_stats.runtime_provider_env_values
    );
    println!(
        "  runtime_evidence.provider_env_slots: {}",
        output.evidence_stats.runtime_provider_env_slots
    );
    println!(
        "  runtime_evidence.provider_env_candidates: {}",
        output.evidence_stats.runtime_provider_env_candidates
    );
    println!(
        "  runtime_evidence.provider_env_reads: {}",
        output.evidence_stats.runtime_provider_env_reads
    );
    println!(
        "  runtime_evidence.provider_env_read_slots: {}",
        output.evidence_stats.runtime_provider_env_read_slots
    );
    println!(
        "  runtime_evidence.provider_env_read_candidates: {}",
        output.evidence_stats.runtime_provider_env_read_candidates
    );
    println!(
        "  runtime_evidence.provider_env_route_lookups: {}",
        output.evidence_stats.runtime_provider_env_route_lookups
    );
    println!(
        "  runtime_evidence.provider_env_route_hits: {}",
        output.evidence_stats.runtime_provider_env_route_hits
    );
    println!(
        "  runtime_evidence.provider_env_route_hit_direct_abortive: {}",
        output
            .evidence_stats
            .runtime_provider_env_route_hit_direct_abortive
    );
    println!(
        "  runtime_evidence.provider_env_route_hit_direct_tail_resumptive: {}",
        output
            .evidence_stats
            .runtime_provider_env_route_hit_direct_tail_resumptive
    );
    println!(
        "  runtime_evidence.provider_env_route_hit_yield_fallback: {}",
        output
            .evidence_stats
            .runtime_provider_env_route_hit_yield_fallback
    );
    println!(
        "  runtime_evidence.provider_env_route_hit_blocked_fallback: {}",
        output
            .evidence_stats
            .runtime_provider_env_route_hit_blocked_fallback
    );
    println!(
        "  runtime_evidence.provider_env_route_hit_generic_fallback: {}",
        output
            .evidence_stats
            .runtime_provider_env_route_hit_generic_fallback
    );
    println!(
        "  runtime_evidence.provider_env_route_hit_unhandled: {}",
        output
            .evidence_stats
            .runtime_provider_env_route_hit_unhandled
    );
    println!(
        "  runtime_evidence.route_cert_none: {}",
        output.evidence_stats.route_cert_none
    );
    println!(
        "  runtime_evidence.route_cert_static_direct: {}",
        output.evidence_stats.route_cert_static_direct
    );
    println!(
        "  runtime_evidence.route_cert_provider_grant: {}",
        output.evidence_stats.route_cert_provider_grant
    );
    println!(
        "  runtime_evidence.route_cert_provider_grant_clean: {}",
        output.evidence_stats.route_cert_provider_grant_clean
    );
    println!(
        "  runtime_evidence.route_cert_provider_grant_dirty_scope: {}",
        output.evidence_stats.route_cert_provider_grant_dirty_scope
    );
    println!(
        "  runtime_evidence.route_cert_provider_grant_dirty_add_id: {}",
        output.evidence_stats.route_cert_provider_grant_dirty_add_id
    );
    println!(
        "  runtime_evidence.route_cert_provider_grant_dirty_handler: {}",
        output
            .evidence_stats
            .route_cert_provider_grant_dirty_handler
    );
    println!(
        "  runtime_evidence.route_cert_provider_grant_dirty_missing: {}",
        output
            .evidence_stats
            .route_cert_provider_grant_dirty_missing
    );
    println!(
        "  runtime_evidence.route_cert_request_free: {}",
        output.evidence_stats.route_cert_request_free
    );
    println!(
        "  runtime_evidence.route_cert_legacy_request_fallbacks: {}",
        output.evidence_stats.route_cert_legacy_request_fallbacks
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_no_grant: {}",
        output.evidence_stats.direct_tail_gate_fail_no_grant
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_missing_grant: {}",
        output.evidence_stats.direct_tail_gate_fail_missing_grant
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_scope_missing: {}",
        output.evidence_stats.direct_tail_gate_fail_scope_missing
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_add_id_shadowed: {}",
        output.evidence_stats.direct_tail_gate_fail_add_id_shadowed
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_add_id_all_path: {}",
        output.evidence_stats.direct_tail_gate_fail_add_id_all_path
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_add_id_own_path: {}",
        output.evidence_stats.direct_tail_gate_fail_add_id_own_path
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_add_id_foreign_path: {}",
        output
            .evidence_stats
            .direct_tail_gate_fail_add_id_foreign_path
    );
    println!(
        "  runtime_evidence.direct_tail_gate_fail_handler_shadowed: {}",
        output.evidence_stats.direct_tail_gate_fail_handler_shadowed
    );
    println!(
        "  runtime_evidence.direct_tail_guarded_add_id_shadowed: {}",
        output.evidence_stats.direct_tail_guarded_add_id_shadowed
    );
    println!(
        "  runtime_evidence.direct_tail_guarded_add_id_all_path: {}",
        output.evidence_stats.direct_tail_guarded_add_id_all_path
    );
    println!(
        "  runtime_evidence.direct_tail_guarded_add_id_own_path: {}",
        output.evidence_stats.direct_tail_guarded_add_id_own_path
    );
    println!(
        "  runtime_evidence.direct_tail_guarded_add_id_foreign_path: {}",
        output
            .evidence_stats
            .direct_tail_guarded_add_id_foreign_path
    );
    println!(
        "  runtime_evidence.permission_visibility_signals: {}",
        output.evidence_stats.permission_visibility_signals
    );
    println!(
        "  runtime_evidence.permission_visibility_identity: {}",
        output.evidence_stats.permission_visibility_identity
    );
    println!(
        "  runtime_evidence.permission_visibility_legacy_bridge: {}",
        output.evidence_stats.permission_visibility_legacy_bridge
    );
    println!(
        "  runtime_evidence.permission_visibility_guard_mask: {}",
        output.evidence_stats.permission_visibility_guard_mask
    );
    println!(
        "  runtime_evidence.permission_visibility_resume_delta: {}",
        output.evidence_stats.permission_visibility_resume_delta
    );
    println!(
        "  runtime_evidence.permission_visibility_handler_boundary_mask: {}",
        output
            .evidence_stats
            .permission_visibility_handler_boundary_mask
    );
    println!(
        "  runtime_evidence.permission_visibility_guard_and_boundary_mask: {}",
        output
            .evidence_stats
            .permission_visibility_guard_and_boundary_mask
    );
    println!(
        "  runtime_evidence.permission_visibility_guard_without_boundary: {}",
        output
            .evidence_stats
            .permission_visibility_guard_without_boundary
    );
    println!(
        "  runtime_evidence.permission_visibility_boundary_without_guard: {}",
        output
            .evidence_stats
            .permission_visibility_boundary_without_guard
    );
    println!(
        "  runtime_evidence.permission_shadow_provider_boundary_pair: {}",
        output
            .evidence_stats
            .permission_shadow_provider_boundary_pair
    );
    println!(
        "  runtime_evidence.permission_shadow_provider_boundary_pair_legacy_visible: {}",
        output
            .evidence_stats
            .permission_shadow_provider_boundary_pair_legacy_visible
    );
    println!(
        "  runtime_evidence.permission_shadow_provider_boundary_pair_permission_visible: {}",
        output
            .evidence_stats
            .permission_shadow_provider_boundary_pair_permission_visible
    );
    println!(
        "  runtime_evidence.permission_shadow_provider_boundary_pair_match: {}",
        output
            .evidence_stats
            .permission_shadow_provider_boundary_pair_match
    );
    println!(
        "  runtime_evidence.permission_shadow_provider_boundary_pair_mismatch: {}",
        output
            .evidence_stats
            .permission_shadow_provider_boundary_pair_mismatch
    );
    println!(
        "  runtime_evidence.permission_shadow_provider_boundary_pair_no_allowed_handler: {}",
        output
            .evidence_stats
            .permission_shadow_provider_boundary_pair_no_allowed_handler
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_fast_paths: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_fast_paths
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_fast_path_visible: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_fast_path_visible
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_fast_path_invisible: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_fast_path_invisible
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_fast_path_no_allowed_handler: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_fast_path_no_allowed_handler
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_native_shadow: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_native_shadow
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_native_shadow_legacy_visible: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_native_shadow_legacy_visible
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_native_shadow_native_visible: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_native_shadow_native_visible
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_native_shadow_match: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_native_shadow_match
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_native_shadow_mismatch: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_native_shadow_mismatch
    );
    println!(
        "  runtime_evidence.permission_provider_boundary_pair_native_shadow_no_allowed_handler: {}",
        output
            .evidence_stats
            .permission_provider_boundary_pair_native_shadow_no_allowed_handler
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_attempts: {}",
        output.evidence_stats.provider_add_id_shortcut_attempts
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_used: {}",
        output.evidence_stats.provider_add_id_shortcut_used
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_fallback_carry_after_frame: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_fallback_carry_after_frame
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_fallback_no_provider_permission: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_fallback_no_provider_permission
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_full_scan_guard_visible_match: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_full_scan_guard_visible_match
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_full_scan_guard_visible_mismatch: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_full_scan_guard_visible_mismatch
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_full_scan_extra_guards: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_full_scan_extra_guards
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_full_scan_extra_carried_guards: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_full_scan_extra_carried_guards
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_visible_verify: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_visible_verify
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_visible_match: {}",
        output.evidence_stats.provider_add_id_shortcut_visible_match
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_visible_mismatch: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_visible_mismatch
    );
    println!(
        "  runtime_evidence.provider_add_id_shortcut_full_scan_visible: {}",
        output
            .evidence_stats
            .provider_add_id_shortcut_full_scan_visible
    );
    println!(
        "  control_evidence.effect_calls: {}",
        output.evidence_stats.effect_calls
    );
    println!(
        "  control_evidence.direct_effect_calls: {}",
        output.evidence_stats.direct_effect_calls
    );
    println!(
        "  runtime_evidence.expr_evals: {}",
        output.evidence_stats.expr_evals
    );
    println!(
        "  runtime_evidence.env_clones: {}",
        output.evidence_stats.env_clones
    );
    println!(
        "  runtime_evidence.env_entries_cloned: {}",
        output.evidence_stats.env_entries_cloned
    );
    println!(
        "  runtime_evidence.apply_value_calls: {}",
        output.evidence_stats.apply_value_calls
    );
    println!(
        "  runtime_evidence.apply_adapter_calls: {}",
        output.evidence_stats.apply_adapter_calls
    );
    println!(
        "  runtime_evidence.adapt_value_calls: {}",
        output.evidence_stats.adapt_value_calls
    );
    println!(
        "  runtime_evidence.primitive_apply_calls: {}",
        output.evidence_stats.primitive_apply_calls
    );
    println!(
        "  runtime_evidence.forced_effect_call_fusions: {}",
        output.evidence_stats.forced_effect_call_fusions
    );
    println!(
        "  runtime_evidence.thunk_forces: {}",
        output.evidence_stats.thunk_forces
    );
    println!(
        "  runtime_evidence.thunk_force_expr: {}",
        output.evidence_stats.thunk_force_expr
    );
    println!(
        "  runtime_evidence.thunk_force_effect: {}",
        output.evidence_stats.thunk_force_effect
    );
    println!(
        "  runtime_evidence.thunk_force_continuation: {}",
        output.evidence_stats.thunk_force_continuation
    );
    println!(
        "  runtime_evidence.thunk_force_value: {}",
        output.evidence_stats.thunk_force_value
    );
    println!(
        "  runtime_evidence.thunk_force_adapter: {}",
        output.evidence_stats.thunk_force_adapter
    );
    println!(
        "  runtime_evidence.continuation_appends: {}",
        output.evidence_stats.continuation_appends
    );
    println!(
        "  runtime_evidence.continuation_owned_tail_appends: {}",
        output.evidence_stats.continuation_owned_tail_appends
    );
    println!(
        "  runtime_evidence.continuation_append_steps: {}",
        output.evidence_stats.continuation_append_steps
    );
    println!(
        "  runtime_evidence.request_continuation_appends: {}",
        output.evidence_stats.request_continuation_appends
    );
    println!(
        "  runtime_evidence.request_continuation_owned_tail_appends: {}",
        output
            .evidence_stats
            .request_continuation_owned_tail_appends
    );
    println!(
        "  runtime_evidence.request_continuation_then_appends: {}",
        output.evidence_stats.request_continuation_then_appends
    );
    println!(
        "  runtime_evidence.direct_tail_continuation_appends: {}",
        output.evidence_stats.direct_tail_continuation_appends
    );
    println!(
        "  runtime_evidence.direct_tail_continuation_owned_tail_appends: {}",
        output
            .evidence_stats
            .direct_tail_continuation_owned_tail_appends
    );
    println!(
        "  runtime_evidence.direct_tail_continuation_then_appends: {}",
        output.evidence_stats.direct_tail_continuation_then_appends
    );
    println!(
        "  runtime_evidence.continuation_append_blocked_by_marker_frame: {}",
        output
            .evidence_stats
            .continuation_append_blocked_by_marker_frame
    );
    println!(
        "  runtime_evidence.continuation_append_blocked_by_provider_env: {}",
        output
            .evidence_stats
            .continuation_append_blocked_by_provider_env
    );
    println!(
        "  runtime_evidence.continuation_append_blocked_by_rc_shared: {}",
        output
            .evidence_stats
            .continuation_append_blocked_by_rc_shared
    );
    println!(
        "  runtime_evidence.request_continuation_append_blocked_by_marker_frame: {}",
        output
            .evidence_stats
            .request_continuation_append_blocked_by_marker_frame
    );
    println!(
        "  runtime_evidence.request_continuation_append_blocked_by_provider_env: {}",
        output
            .evidence_stats
            .request_continuation_append_blocked_by_provider_env
    );
    println!(
        "  runtime_evidence.request_continuation_append_blocked_by_rc_shared: {}",
        output
            .evidence_stats
            .request_continuation_append_blocked_by_rc_shared
    );
    println!(
        "  runtime_evidence.direct_tail_continuation_append_blocked_by_marker_frame: {}",
        output
            .evidence_stats
            .direct_tail_continuation_append_blocked_by_marker_frame
    );
    println!(
        "  runtime_evidence.direct_tail_continuation_append_blocked_by_provider_env: {}",
        output
            .evidence_stats
            .direct_tail_continuation_append_blocked_by_provider_env
    );
    println!(
        "  runtime_evidence.direct_tail_continuation_append_blocked_by_rc_shared: {}",
        output
            .evidence_stats
            .direct_tail_continuation_append_blocked_by_rc_shared
    );
    println!(
        "  runtime_evidence.direct_tail_permission_boundary_append_candidates: {}",
        output
            .evidence_stats
            .direct_tail_permission_boundary_append_candidates
    );
    println!(
        "  runtime_evidence.direct_tail_permission_boundary_append_provider_pair: {}",
        output
            .evidence_stats
            .direct_tail_permission_boundary_append_provider_pair
    );
    println!(
        "  runtime_evidence.direct_tail_permission_boundary_append_reject_no_provider_permission: {}",
        output
            .evidence_stats
            .direct_tail_permission_boundary_append_reject_no_provider_permission
    );
    println!(
        "  runtime_evidence.direct_tail_permission_boundary_append_reject_resume_delta: {}",
        output
            .evidence_stats
            .direct_tail_permission_boundary_append_reject_resume_delta
    );
    println!(
        "  runtime_evidence.direct_tail_permission_boundary_append_reject_handler_path: {}",
        output
            .evidence_stats
            .direct_tail_permission_boundary_append_reject_handler_path
    );
    println!(
        "  runtime_evidence.direct_tail_permission_boundary_append_reject_legacy_bridge: {}",
        output
            .evidence_stats
            .direct_tail_permission_boundary_append_reject_legacy_bridge
    );
    println!(
        "  runtime_evidence.direct_tail_permission_boundary_append_reject_other_transform: {}",
        output
            .evidence_stats
            .direct_tail_permission_boundary_append_reject_other_transform
    );
    println!(
        "  runtime_evidence.direct_tail_segment_candidates: {}",
        output.evidence_stats.direct_tail_segment_candidates
    );
    println!(
        "  runtime_evidence.direct_tail_segment_materialized_continuations: {}",
        output
            .evidence_stats
            .direct_tail_segment_materialized_continuations
    );
    println!(
        "  runtime_evidence.direct_tail_segment_created: {}",
        output.evidence_stats.direct_tail_segment_created
    );
    println!(
        "  runtime_evidence.direct_tail_segment_to_tree_fallbacks: {}",
        output.evidence_stats.direct_tail_segment_to_tree_fallbacks
    );
    println!(
        "  runtime_evidence.direct_tail_segment_identity: {}",
        output.evidence_stats.direct_tail_segment_identity
    );
    println!(
        "  runtime_evidence.direct_tail_segment_eval_only: {}",
        output.evidence_stats.direct_tail_segment_eval_only
    );
    println!(
        "  runtime_evidence.direct_tail_segment_eval_frames: {}",
        output.evidence_stats.direct_tail_segment_eval_frames
    );
    println!(
        "  runtime_evidence.direct_tail_segment_then_frames: {}",
        output.evidence_stats.direct_tail_segment_then_frames
    );
    println!(
        "  runtime_evidence.direct_tail_segment_scope_marker_frames: {}",
        output
            .evidence_stats
            .direct_tail_segment_scope_marker_frames
    );
    println!(
        "  runtime_evidence.direct_tail_segment_scope_marker_dynamic: {}",
        output
            .evidence_stats
            .direct_tail_segment_scope_marker_dynamic
    );
    println!(
        "  runtime_evidence.direct_tail_segment_scope_marker_empty: {}",
        output.evidence_stats.direct_tail_segment_scope_marker_empty
    );
    println!(
        "  runtime_evidence.direct_tail_segment_scope_provider_env_frames: {}",
        output
            .evidence_stats
            .direct_tail_segment_scope_provider_env_frames
    );
    println!(
        "  runtime_evidence.direct_tail_segment_request_boundary_rejected: {}",
        output
            .evidence_stats
            .direct_tail_segment_request_boundary_rejected
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_candidates: {}",
        output.evidence_stats.resume_plan_shadow_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_direct_tail_candidates: {}",
        output
            .evidence_stats
            .resume_plan_shadow_direct_tail_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_resume_pack_candidates: {}",
        output
            .evidence_stats
            .resume_plan_shadow_resume_pack_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_eval_frames: {}",
        output.evidence_stats.resume_plan_shadow_eval_frames
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_then_frames: {}",
        output.evidence_stats.resume_plan_shadow_then_frames
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_catch_boundaries: {}",
        output.evidence_stats.resume_plan_shadow_catch_boundaries
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_catch_same_handler: {}",
        output.evidence_stats.resume_plan_shadow_catch_same_handler
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_catch_no_routed_handler: {}",
        output
            .evidence_stats
            .resume_plan_shadow_catch_no_routed_handler
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_catch_foreign_handler: {}",
        output
            .evidence_stats
            .resume_plan_shadow_catch_foreign_handler
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_ref_set_boundaries: {}",
        output.evidence_stats.resume_plan_shadow_ref_set_boundaries
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_marker_frames: {}",
        output.evidence_stats.resume_plan_shadow_marker_frames
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_marker_dynamic_frames: {}",
        output
            .evidence_stats
            .resume_plan_shadow_marker_dynamic_frames
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_marker_empty_frames: {}",
        output.evidence_stats.resume_plan_shadow_marker_empty_frames
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_marker_active_add_id_ops: {}",
        output
            .evidence_stats
            .resume_plan_shadow_marker_active_add_id_ops
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_marker_handler_boundary_ops: {}",
        output
            .evidence_stats
            .resume_plan_shadow_marker_handler_boundary_ops
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_provider_env_deltas: {}",
        output.evidence_stats.resume_plan_shadow_provider_env_deltas
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_provider_grant_dirty_add_id: {}",
        output
            .evidence_stats
            .resume_plan_shadow_provider_grant_dirty_add_id
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_multi_shot: {}",
        output.evidence_stats.resume_plan_shadow_multi_shot
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_eval_only: {}",
        output.evidence_stats.resume_plan_shadow_eval_only
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_with_catch_boundary: {}",
        output.evidence_stats.resume_plan_shadow_with_catch_boundary
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_with_dynamic_marker: {}",
        output.evidence_stats.resume_plan_shadow_with_dynamic_marker
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_with_provider_delta: {}",
        output.evidence_stats.resume_plan_shadow_with_provider_delta
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_candidates: {}",
        output.evidence_stats.resume_plan_candidate_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_direct_tail_candidates: {}",
        output
            .evidence_stats
            .resume_plan_candidate_direct_tail_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_resume_pack_candidates: {}",
        output
            .evidence_stats
            .resume_plan_candidate_resume_pack_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_planned: {}",
        output.evidence_stats.resume_plan_candidate_planned
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_rejected: {}",
        output.evidence_stats.resume_plan_candidate_rejected
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_reject_ref_set: {}",
        output.evidence_stats.resume_plan_candidate_reject_ref_set
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_multi_shot: {}",
        output.evidence_stats.resume_plan_candidate_multi_shot
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_eval_frames: {}",
        output.evidence_stats.resume_plan_candidate_eval_frames
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_estimated_resume_steps: {}",
        output
            .evidence_stats
            .resume_plan_candidate_estimated_resume_steps
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_with_trace: {}",
        output.evidence_stats.resume_plan_candidate_with_trace
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_with_eval_delta: {}",
        output.evidence_stats.resume_plan_candidate_with_eval_delta
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_request_delta_none: {}",
        output
            .evidence_stats
            .resume_plan_candidate_request_delta_none
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_request_delta_catch_same: {}",
        output
            .evidence_stats
            .resume_plan_candidate_request_delta_catch_same
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_request_delta_catch_no_routed: {}",
        output
            .evidence_stats
            .resume_plan_candidate_request_delta_catch_no_routed
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_request_delta_catch_foreign: {}",
        output
            .evidence_stats
            .resume_plan_candidate_request_delta_catch_foreign
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_with_request_delta: {}",
        output
            .evidence_stats
            .resume_plan_candidate_with_request_delta
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_with_marker_delta: {}",
        output
            .evidence_stats
            .resume_plan_candidate_with_marker_delta
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_with_provider_delta: {}",
        output
            .evidence_stats
            .resume_plan_candidate_with_provider_delta
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_with_both_scope_deltas: {}",
        output
            .evidence_stats
            .resume_plan_candidate_with_both_scope_deltas
    );
    println!(
        "  runtime_evidence.resume_plan_candidate_provider_dirty_add_id: {}",
        output
            .evidence_stats
            .resume_plan_candidate_provider_dirty_add_id
    );
    println!(
        "  runtime_evidence.resume_plan_cert_candidates: {}",
        output.evidence_stats.resume_plan_cert_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_cert_provider_dirty_foreign_scope: {}",
        output
            .evidence_stats
            .resume_plan_cert_provider_dirty_foreign_scope
    );
    println!(
        "  runtime_evidence.resume_plan_cert_direct_tail_provider_dirty_foreign_scope: {}",
        output
            .evidence_stats
            .resume_plan_cert_direct_tail_provider_dirty_foreign_scope
    );
    println!(
        "  runtime_evidence.resume_plan_cert_resume_pack_provider_dirty_foreign_scope: {}",
        output
            .evidence_stats
            .resume_plan_cert_resume_pack_provider_dirty_foreign_scope
    );
    println!(
        "  runtime_evidence.resume_plan_cert_provider_dirty_foreign_scope_handlers: {}",
        output
            .evidence_stats
            .resume_plan_cert_provider_dirty_foreign_scope_handlers
    );
    println!(
        "  runtime_evidence.resume_plan_cert_provider_dirty_foreign_scope_estimated_resume_steps: {}",
        output
            .evidence_stats
            .resume_plan_cert_provider_dirty_foreign_scope_estimated_resume_steps
    );
    println!(
        "  runtime_evidence.resume_plan_cert_rejected: {}",
        output.evidence_stats.resume_plan_cert_rejected
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_not_planned: {}",
        output.evidence_stats.resume_plan_cert_reject_not_planned
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_missing_trace: {}",
        output.evidence_stats.resume_plan_cert_reject_missing_trace
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_missing_eval_delta: {}",
        output
            .evidence_stats
            .resume_plan_cert_reject_missing_eval_delta
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_missing_request_delta: {}",
        output
            .evidence_stats
            .resume_plan_cert_reject_missing_request_delta
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_missing_marker_delta: {}",
        output
            .evidence_stats
            .resume_plan_cert_reject_missing_marker_delta
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_missing_provider_delta: {}",
        output
            .evidence_stats
            .resume_plan_cert_reject_missing_provider_delta
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_route_not_provider_dirty_add_id: {}",
        output
            .evidence_stats
            .resume_plan_cert_reject_route_not_provider_dirty_add_id
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_multi_shot: {}",
        output.evidence_stats.resume_plan_cert_reject_multi_shot
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_request_none: {}",
        output.evidence_stats.resume_plan_cert_reject_request_none
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_request_catch_same_or_no_routed: {}",
        output
            .evidence_stats
            .resume_plan_cert_reject_request_catch_same_or_no_routed
    );
    println!(
        "  runtime_evidence.resume_plan_cert_reject_request_no_foreign_catch: {}",
        output
            .evidence_stats
            .resume_plan_cert_reject_request_no_foreign_catch
    );
    println!(
        "  runtime_evidence.resume_plan_plans: {}",
        output.evidence_stats.resume_plan_plans
    );
    println!(
        "  runtime_evidence.resume_plan_direct_tail_plans: {}",
        output.evidence_stats.resume_plan_direct_tail_plans
    );
    println!(
        "  runtime_evidence.resume_plan_resume_pack_plans: {}",
        output.evidence_stats.resume_plan_resume_pack_plans
    );
    println!(
        "  runtime_evidence.resume_plan_provider_dirty_foreign_scope_plans: {}",
        output
            .evidence_stats
            .resume_plan_provider_dirty_foreign_scope_plans
    );
    println!(
        "  runtime_evidence.resume_plan_trace_plans: {}",
        output.evidence_stats.resume_plan_trace_plans
    );
    println!(
        "  runtime_evidence.resume_plan_trace_direct_tail_plans: {}",
        output.evidence_stats.resume_plan_trace_direct_tail_plans
    );
    println!(
        "  runtime_evidence.resume_plan_trace_resume_pack_plans: {}",
        output.evidence_stats.resume_plan_trace_resume_pack_plans
    );
    println!(
        "  runtime_evidence.resume_plan_trace_steps: {}",
        output.evidence_stats.resume_plan_trace_steps
    );
    println!(
        "  runtime_evidence.resume_plan_trace_eval_steps: {}",
        output.evidence_stats.resume_plan_trace_eval_steps
    );
    println!(
        "  runtime_evidence.resume_plan_trace_request_steps: {}",
        output.evidence_stats.resume_plan_trace_request_steps
    );
    println!(
        "  runtime_evidence.resume_plan_trace_marker_steps: {}",
        output.evidence_stats.resume_plan_trace_marker_steps
    );
    println!(
        "  runtime_evidence.resume_plan_trace_provider_steps: {}",
        output.evidence_stats.resume_plan_trace_provider_steps
    );
    println!(
        "  runtime_evidence.resume_plan_trace_max_steps: {}",
        output.evidence_stats.resume_plan_trace_max_steps
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_plans: {}",
        output.evidence_stats.resume_plan_scoped_trace_plans
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_scopes: {}",
        output.evidence_stats.resume_plan_scoped_trace_scopes
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_provider_child_scopes: {}",
        output
            .evidence_stats
            .resume_plan_scoped_trace_provider_child_scopes
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_steps: {}",
        output.evidence_stats.resume_plan_scoped_trace_steps
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_root_marker_steps: {}",
        output
            .evidence_stats
            .resume_plan_scoped_trace_root_marker_steps
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_child_marker_steps: {}",
        output
            .evidence_stats
            .resume_plan_scoped_trace_child_marker_steps
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_root_marker_matches_marker_delta: {}",
        output
            .evidence_stats
            .resume_plan_scoped_trace_root_marker_matches_marker_delta
    );
    println!(
        "  runtime_evidence.resume_plan_scoped_trace_root_marker_mismatches_marker_delta: {}",
        output
            .evidence_stats
            .resume_plan_scoped_trace_root_marker_mismatches_marker_delta
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_checks: {}",
        output.evidence_stats.resume_plan_exec_shadow_checks
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_ready: {}",
        output.evidence_stats.resume_plan_exec_shadow_ready
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_direct_tail_ready: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_direct_tail_ready
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_resume_pack_ready: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_resume_pack_ready
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_steps: {}",
        output.evidence_stats.resume_plan_exec_shadow_steps
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_estimated_saved_steps: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_estimated_saved_steps
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_missing_trace: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_missing_trace
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_missing_eval_delta: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_missing_eval_delta
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_missing_request_delta: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_missing_request_delta
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_missing_marker_delta: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_missing_marker_delta
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_missing_provider_delta: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_missing_provider_delta
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_trace_eval_bounds: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_trace_eval_bounds
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_trace_request_bounds: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_trace_request_bounds
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_trace_marker_bounds: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_trace_marker_bounds
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_trace_provider_bounds: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_trace_provider_bounds
    );
    println!(
        "  runtime_evidence.resume_plan_exec_shadow_reject_trace_unused_payload: {}",
        output
            .evidence_stats
            .resume_plan_exec_shadow_reject_trace_unused_payload
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_candidates: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_direct_tail_candidates: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_direct_tail_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_resume_pack_candidates: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_resume_pack_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_reject_no_catch_boundary: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_reject_no_catch_boundary
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_reject_ref_set_boundary: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_reject_ref_set_boundary
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_requires_marker_delta: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_requires_marker_delta
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_requires_provider_delta: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_requires_provider_delta
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_requires_both_scope_deltas: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_requires_both_scope_deltas
    );
    println!(
        "  runtime_evidence.resume_plan_shadow_request_delta_provider_dirty_add_id: {}",
        output
            .evidence_stats
            .resume_plan_shadow_request_delta_provider_dirty_add_id
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_plans: {}",
        output.evidence_stats.resume_plan_eval_delta_plans
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_direct_tail_plans: {}",
        output
            .evidence_stats
            .resume_plan_eval_delta_direct_tail_plans
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_resume_pack_plans: {}",
        output
            .evidence_stats
            .resume_plan_eval_delta_resume_pack_plans
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_force_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_force_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_apply_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_apply_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_adapter_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_adapter_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_case_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_case_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_aggregate_frames: {}",
        output
            .evidence_stats
            .resume_plan_eval_delta_aggregate_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_select_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_select_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_block_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_block_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_ref_set_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_ref_set_frames
    );
    println!(
        "  runtime_evidence.resume_plan_eval_delta_max_frames: {}",
        output.evidence_stats.resume_plan_eval_delta_max_frames
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_plans: {}",
        output.evidence_stats.resume_plan_request_delta_plans
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_direct_tail_plans: {}",
        output
            .evidence_stats
            .resume_plan_request_delta_direct_tail_plans
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_resume_pack_plans: {}",
        output
            .evidence_stats
            .resume_plan_request_delta_resume_pack_plans
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_frames: {}",
        output.evidence_stats.resume_plan_request_delta_frames
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_same_handler_frames: {}",
        output
            .evidence_stats
            .resume_plan_request_delta_same_handler_frames
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_no_routed_handler_frames: {}",
        output
            .evidence_stats
            .resume_plan_request_delta_no_routed_handler_frames
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_foreign_handler_frames: {}",
        output
            .evidence_stats
            .resume_plan_request_delta_foreign_handler_frames
    );
    println!(
        "  runtime_evidence.resume_plan_request_delta_max_frames: {}",
        output.evidence_stats.resume_plan_request_delta_max_frames
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_candidates: {}",
        output.evidence_stats.resume_plan_marker_delta_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_direct_tail_candidates: {}",
        output
            .evidence_stats
            .resume_plan_marker_delta_direct_tail_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_resume_pack_candidates: {}",
        output
            .evidence_stats
            .resume_plan_marker_delta_resume_pack_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_unique: {}",
        output.evidence_stats.resume_plan_marker_delta_unique
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_reused: {}",
        output.evidence_stats.resume_plan_marker_delta_reused
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_frames: {}",
        output.evidence_stats.resume_plan_marker_delta_frames
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_active_add_id_ops: {}",
        output
            .evidence_stats
            .resume_plan_marker_delta_active_add_id_ops
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_handler_boundary_ops: {}",
        output
            .evidence_stats
            .resume_plan_marker_delta_handler_boundary_ops
    );
    println!(
        "  runtime_evidence.resume_plan_marker_delta_max_frames: {}",
        output.evidence_stats.resume_plan_marker_delta_max_frames
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_candidates: {}",
        output.evidence_stats.resume_plan_provider_delta_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_direct_tail_candidates: {}",
        output
            .evidence_stats
            .resume_plan_provider_delta_direct_tail_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_resume_pack_candidates: {}",
        output
            .evidence_stats
            .resume_plan_provider_delta_resume_pack_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_unique: {}",
        output.evidence_stats.resume_plan_provider_delta_unique
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_reused: {}",
        output.evidence_stats.resume_plan_provider_delta_reused
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_frames: {}",
        output.evidence_stats.resume_plan_provider_delta_frames
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_slots: {}",
        output.evidence_stats.resume_plan_provider_delta_slots
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_handler_candidates: {}",
        output
            .evidence_stats
            .resume_plan_provider_delta_handler_candidates
    );
    println!(
        "  runtime_evidence.resume_plan_provider_delta_max_frames: {}",
        output.evidence_stats.resume_plan_provider_delta_max_frames
    );
    println!(
        "  runtime_evidence.resume_pack_candidates: {}",
        output.evidence_stats.resume_pack_candidates
    );
    println!(
        "  runtime_evidence.resume_pack_thunks_forced: {}",
        output.evidence_stats.resume_pack_thunks_forced
    );
    println!(
        "  runtime_evidence.resume_pack_multi_shot_required: {}",
        output.evidence_stats.resume_pack_multi_shot_required
    );
    println!(
        "  runtime_evidence.resume_pack_can_share_segment: {}",
        output.evidence_stats.resume_pack_can_share_segment
    );
    println!(
        "  runtime_evidence.resume_pack_to_tree_fallbacks: {}",
        output.evidence_stats.resume_pack_to_tree_fallbacks
    );
    println!(
        "  runtime_evidence.resume_pack_identity: {}",
        output.evidence_stats.resume_pack_identity
    );
    println!(
        "  runtime_evidence.resume_pack_eval_frames: {}",
        output.evidence_stats.resume_pack_eval_frames
    );
    println!(
        "  runtime_evidence.resume_pack_then_frames: {}",
        output.evidence_stats.resume_pack_then_frames
    );
    println!(
        "  runtime_evidence.resume_pack_scope_marker_frames: {}",
        output.evidence_stats.resume_pack_scope_marker_frames
    );
    println!(
        "  runtime_evidence.resume_pack_scope_provider_env_frames: {}",
        output.evidence_stats.resume_pack_scope_provider_env_frames
    );
    println!(
        "  runtime_evidence.resume_pack_request_boundary_rejected: {}",
        output.evidence_stats.resume_pack_request_boundary_rejected
    );
    println!(
        "  runtime_evidence.continuation_resume_steps: {}",
        output.evidence_stats.continuation_resume_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_then_steps: {}",
        output.evidence_stats.continuation_resume_then_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_then_first_marker_frame: {}",
        output
            .evidence_stats
            .continuation_resume_then_first_marker_frame
    );
    println!(
        "  runtime_evidence.continuation_resume_then_first_provider_env: {}",
        output
            .evidence_stats
            .continuation_resume_then_first_provider_env
    );
    println!(
        "  runtime_evidence.continuation_resume_then_first_other: {}",
        output.evidence_stats.continuation_resume_then_first_other
    );
    println!(
        "  runtime_evidence.continuation_resume_then_second_marker_frame: {}",
        output
            .evidence_stats
            .continuation_resume_then_second_marker_frame
    );
    println!(
        "  runtime_evidence.continuation_resume_then_second_provider_env: {}",
        output
            .evidence_stats
            .continuation_resume_then_second_provider_env
    );
    println!(
        "  runtime_evidence.continuation_resume_then_second_other: {}",
        output.evidence_stats.continuation_resume_then_second_other
    );
    println!(
        "  runtime_evidence.continuation_resume_then_plain: {}",
        output.evidence_stats.continuation_resume_then_plain
    );
    println!(
        "  runtime_evidence.continuation_resume_force_steps: {}",
        output.evidence_stats.continuation_resume_force_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_apply_steps: {}",
        output.evidence_stats.continuation_resume_apply_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_adapter_steps: {}",
        output.evidence_stats.continuation_resume_adapter_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_case_steps: {}",
        output.evidence_stats.continuation_resume_case_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_catch_steps: {}",
        output.evidence_stats.continuation_resume_catch_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_steps: {}",
        output.evidence_stats.continuation_resume_marker_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_identity_fast_paths: {}",
        output
            .evidence_stats
            .continuation_resume_marker_identity_fast_paths
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_empty_markers: {}",
        output
            .evidence_stats
            .continuation_resume_marker_empty_markers
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_with_active_add_id: {}",
        output
            .evidence_stats
            .continuation_resume_marker_with_active_add_id
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_with_handler_path: {}",
        output
            .evidence_stats
            .continuation_resume_marker_with_handler_path
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_result_value: {}",
        output
            .evidence_stats
            .continuation_resume_marker_result_value
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_result_direct_tail: {}",
        output
            .evidence_stats
            .continuation_resume_marker_result_direct_tail
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_result_direct_tail_provider_permission: {}",
        output
            .evidence_stats
            .continuation_resume_marker_result_direct_tail_provider_permission
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_result_direct_tail_provider_boundary_pair: {}",
        output
            .evidence_stats
            .continuation_resume_marker_result_direct_tail_provider_boundary_pair
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_result_legacy_signal: {}",
        output
            .evidence_stats
            .continuation_resume_marker_result_legacy_signal
    );
    println!(
        "  runtime_evidence.continuation_resume_marker_result_error: {}",
        output
            .evidence_stats
            .continuation_resume_marker_result_error
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_candidates: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_candidates
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_provider_pair: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_provider_pair
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_no_provider_permission: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_no_provider_permission
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_resume_delta: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_resume_delta
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_handler_path: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_handler_path
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_value_result: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_value_result
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_legacy_signal: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_legacy_signal
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_legacy_bridge: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_legacy_bridge
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_other_transform: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_other_transform
    );
    println!(
        "  runtime_evidence.resume_marker_permission_native_reject_error_result: {}",
        output
            .evidence_stats
            .resume_marker_permission_native_reject_error_result
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_candidates: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_candidates
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_shadow: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_shadow
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_shadow_match: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_shadow_match
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_shadow_mismatch: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_shadow_mismatch
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_shadow_legacy_visible: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_shadow_legacy_visible
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_shadow_permission_visible: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_shadow_permission_visible
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_no_provider_permission: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_no_provider_permission
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_resume_delta: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_resume_delta
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_blocked: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_blocked
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_unblocked: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_unblocked
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_no_boundary: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_no_boundary
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_same_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_same_family
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_foreign_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_foreign_family
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_matches_call_boundary: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_matches_call_boundary
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_differs_call_boundary: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_differs_call_boundary
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_matches_allowed_handler_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_matches_allowed_handler_family
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_differs_allowed_handler_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_differs_allowed_handler_family
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_prefixes_allowed_handler_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_prefixes_allowed_handler_family
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_allowed_handler_family_prefixes: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_allowed_handler_family_prefixes
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_permission_handler_unknown: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_permission_handler_unknown
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_boundary_id_matches_permission_handler: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_boundary_id_matches_permission_handler
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_boundary_id_differs_permission_handler: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_boundary_id_differs_permission_handler
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_handler_path_boundary_id_permission_handler_unknown: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_handler_path_boundary_id_permission_handler_unknown
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_carry_after_frame: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_carry_after_frame
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_legacy_bridge: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_legacy_bridge
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_reject_other_transform: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_reject_other_transform
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_native_hits: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_native_hits
    );
    println!(
        "  runtime_evidence.resume_marker_provider_pair_close_legacy_fallbacks: {}",
        output
            .evidence_stats
            .resume_marker_provider_pair_close_legacy_fallbacks
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_candidates: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_candidates
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_native_hits: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_native_hits
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_legacy_fallbacks: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_legacy_fallbacks
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_shadow: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_shadow
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_shadow_match: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_shadow_match
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_shadow_mismatch: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_shadow_mismatch
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_shadow_legacy_visible: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_shadow_legacy_visible
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_shadow_permission_visible: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_shadow_permission_visible
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_no_boundary: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_no_boundary
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_blocked: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_blocked
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_call_boundary_mismatch: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_call_boundary_mismatch
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_foreign_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_foreign_family
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_permission_unknown: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_permission_unknown
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_exact_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_exact_family
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_permission_family_request_mismatch: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_permission_family_request_mismatch
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_reject_carry_after_frame: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_reject_carry_after_frame
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_permission_family_equals_request_path: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_permission_family_equals_request_path
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_permission_family_prefixes_request_path: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_permission_family_prefixes_request_path
    );
    println!(
        "  runtime_evidence.resume_marker_provider_prefix_boundary_request_path_prefixes_permission_family: {}",
        output
            .evidence_stats
            .resume_marker_provider_prefix_boundary_request_path_prefixes_permission_family
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_candidates: {}",
        output.evidence_stats.provider_foreign_boundary_candidates
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_with_provider_env_blocker: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_with_provider_env_blocker
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_without_provider_env_blocker: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_without_provider_env_blocker
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_provider_env_grants_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_provider_env_grants_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_provider_env_misses_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_provider_env_misses_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_blocked_by_marker_frame: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_blocked_by_marker_frame
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_with_any_provider_env: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_with_any_provider_env
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_without_any_provider_env: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_without_any_provider_env
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_any_provider_env_grants_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_any_provider_env_grants_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_any_provider_env_misses_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_any_provider_env_misses_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_nearest_provider_env_grants_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_nearest_provider_env_grants_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_nearest_provider_env_misses_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_nearest_provider_env_misses_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_nearest_provider_env_none: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_nearest_provider_env_none
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_marker_before_nearest_provider_env: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_marker_before_nearest_provider_env
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_any_later_provider_env_grants_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_any_later_provider_env_grants_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_any_later_provider_env_misses_permission: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_any_later_provider_env_misses_permission
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_provider_env_under_then_first: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_provider_env_under_then_first
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_provider_env_under_then_second: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_provider_env_under_then_second
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_nearest_provider_env_depth_sum: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_nearest_provider_env_depth_sum
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_nearest_provider_env_max_depth: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_nearest_provider_env_max_depth
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_permission_family_equals_request_path: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_permission_family_equals_request_path
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_permission_family_prefixes_request_path: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_permission_family_prefixes_request_path
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_request_path_prefixes_permission_family: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_request_path_prefixes_permission_family
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_handler_path_prefixes_request_path: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_handler_path_prefixes_request_path
    );
    println!(
        "  runtime_evidence.provider_foreign_boundary_request_path_prefixes_handler_path: {}",
        output
            .evidence_stats
            .provider_foreign_boundary_request_path_prefixes_handler_path
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_candidates: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_candidates
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_nearest_misses: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_nearest_misses
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_no_provider_env: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_no_provider_env
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_marker_before_provider_env: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_marker_before_provider_env
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_depth: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_depth
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_then_second: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_then_second
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_later_grant: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_later_grant
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_permission_family_request_mismatch: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_permission_family_request_mismatch
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_handler_path_related_to_request: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_handler_path_related_to_request
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_reject_carry_after_frame: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_reject_carry_after_frame
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_legacy_visible: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_legacy_visible
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_naive_visible: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_naive_visible
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_naive_match: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_naive_match
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_naive_mismatch: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_naive_mismatch
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_blocked_visible: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_blocked_visible
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_blocked_match: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_blocked_match
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_shadow_blocked_mismatch: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_shadow_blocked_mismatch
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_native_hits: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_native_hits
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_legacy_fallbacks: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_legacy_fallbacks
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_nearest_misses: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_nearest_misses
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_no_provider_env: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_no_provider_env
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_marker_before_provider_env: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_marker_before_provider_env
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_depth: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_depth
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_then_second: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_then_second
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_later_grant: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_later_grant
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_permission_family_request_mismatch: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_permission_family_request_mismatch
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_handler_path_related_to_request: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_handler_path_related_to_request
    );
    println!(
        "  runtime_evidence.provider_env_foreign_boundary_reject_carry_after_frame: {}",
        output
            .evidence_stats
            .provider_env_foreign_boundary_reject_carry_after_frame
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_shadow_candidates: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_shadow_candidates
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_shadow_legacy_visible: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_shadow_legacy_visible
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_shadow_invisible_match: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_shadow_invisible_match
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_shadow_invisible_mismatch: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_shadow_invisible_mismatch
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_no_provider_env: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_no_provider_env
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_marker_before_provider_env: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_marker_before_provider_env
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_depth: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_depth
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_then_second: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_then_second
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_later_grant: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_later_grant
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_permission_family_request_mismatch: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_permission_family_request_mismatch
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_handler_path_related_to_request: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_handler_path_related_to_request
    );
    println!(
        "  runtime_evidence.provider_env_foreign_miss_boundary_reject_carry_after_frame: {}",
        output
            .evidence_stats
            .provider_env_foreign_miss_boundary_reject_carry_after_frame
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_candidates: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_candidates
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_under_then_first: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_under_then_first
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_under_then_second: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_under_then_second
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_in_provider_env_next: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_in_provider_env_next
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_depth_sum: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_depth_sum
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_max_depth: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_max_depth
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_legacy_visible: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_legacy_visible
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_naive_visible: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_naive_visible
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_naive_match: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_naive_match
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_naive_mismatch: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_naive_mismatch
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_calls: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_calls
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_calls_for_shadow: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_calls_for_shadow
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_calls_for_rejected_native_candidate: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_calls_for_rejected_native_candidate
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_frame_steps: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_frame_steps
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_then_steps: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_then_steps
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_provider_env_steps: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_provider_env_steps
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_marker_frame_stops: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_marker_frame_stops
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_found: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_found
    );
    println!(
        "  runtime_evidence.provider_env_later_grant_placement_not_found: {}",
        output
            .evidence_stats
            .provider_env_later_grant_placement_not_found
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_native_eligible_if_enabled: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_native_eligible_if_enabled
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_native_hits_if_enabled: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_native_hits_if_enabled
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_native_shape_then_frames: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_native_shape_then_frames
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_native_shape_marker_frames: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_native_shape_marker_frames
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_native_shape_provider_env_frames: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_native_shape_provider_env_frames
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_native_shape_depth_sum: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_native_shape_depth_sum
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_native_shape_max_depth: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_native_shape_max_depth
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_legacy_shape_then_frames: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_legacy_shape_then_frames
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_legacy_shape_marker_frames: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_legacy_shape_marker_frames
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_legacy_shape_provider_env_frames: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_legacy_shape_provider_env_frames
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_legacy_shape_depth_sum: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_legacy_shape_depth_sum
    );
    println!(
        "  runtime_evidence.provider_env_foreign_later_grant_legacy_shape_max_depth: {}",
        output
            .evidence_stats
            .provider_env_foreign_later_grant_legacy_shape_max_depth
    );
    println!(
        "  runtime_evidence.continuation_resume_provider_steps: {}",
        output.evidence_stats.continuation_resume_provider_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_aggregate_steps: {}",
        output.evidence_stats.continuation_resume_aggregate_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_select_steps: {}",
        output.evidence_stats.continuation_resume_select_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_block_steps: {}",
        output.evidence_stats.continuation_resume_block_steps
    );
    println!(
        "  runtime_evidence.continuation_resume_ref_set_steps: {}",
        output.evidence_stats.continuation_resume_ref_set_steps
    );
    println!(
        "  runtime_evidence.request_whole_continuation_appends: {}",
        output.evidence_stats.request_whole_continuation_appends
    );
    println!(
        "  runtime_evidence.request_continuation_steps: {}",
        output.evidence_stats.request_continuation_steps
    );
    println!(
        "  runtime_evidence.catch_body_checks: {}",
        output.evidence_stats.catch_body_checks
    );
    println!(
        "  runtime_evidence.catch_boundary_entries: {}",
        output.evidence_stats.catch_boundary_entries
    );
    println!(
        "  runtime_evidence.catch_boundary_value_results: {}",
        output.evidence_stats.catch_boundary_value_results
    );
    println!(
        "  runtime_evidence.catch_boundary_effect_signals: {}",
        output.evidence_stats.catch_boundary_effect_signals
    );
    println!(
        "  runtime_evidence.catch_boundary_direct_tail_signals: {}",
        output.evidence_stats.catch_boundary_direct_tail_signals
    );
    println!(
        "  runtime_evidence.catch_boundary_direct_abortive_signals: {}",
        output.evidence_stats.catch_boundary_direct_abortive_signals
    );
    println!(
        "  runtime_evidence.catch_boundary_generic_request_signals: {}",
        output.evidence_stats.catch_boundary_generic_request_signals
    );
    println!(
        "  runtime_evidence.has_request_boundary_catch_same_handler: {}",
        output
            .evidence_stats
            .has_request_boundary_catch_same_handler
    );
    println!(
        "  runtime_evidence.has_request_boundary_catch_no_routed_handler: {}",
        output
            .evidence_stats
            .has_request_boundary_catch_no_routed_handler
    );
    println!(
        "  runtime_evidence.has_request_boundary_catch_foreign_handler_recurse: {}",
        output
            .evidence_stats
            .has_request_boundary_catch_foreign_handler_recurse
    );
    println!(
        "  runtime_evidence.has_request_boundary_ref_set: {}",
        output.evidence_stats.has_request_boundary_ref_set
    );
    println!(
        "  runtime_evidence.direct_tail_blocked_by_catch_boundary: {}",
        output.evidence_stats.direct_tail_blocked_by_catch_boundary
    );
    println!(
        "  runtime_evidence.direct_tail_target_catch_boundary_visible: {}",
        output
            .evidence_stats
            .direct_tail_target_catch_boundary_visible
    );
    println!(
        "  runtime_evidence.direct_tail_target_catch_boundary_provider_grant_clean: {}",
        output
            .evidence_stats
            .direct_tail_target_catch_boundary_provider_grant_clean
    );
    println!(
        "  runtime_evidence.direct_tail_target_catch_boundary_provider_grant_dirty: {}",
        output
            .evidence_stats
            .direct_tail_target_catch_boundary_provider_grant_dirty
    );
    println!(
        "  runtime_evidence.direct_tail_target_catch_boundary_to_generic_request: {}",
        output
            .evidence_stats
            .direct_tail_target_catch_boundary_to_generic_request
    );
    println!(
        "  runtime_evidence.marker_frame_entries: {}",
        output.evidence_stats.marker_frame_entries
    );
    println!(
        "  runtime_evidence.marker_frame_markers: {}",
        output.evidence_stats.marker_frame_markers
    );
    println!(
        "  runtime_evidence.marker_frame_add_id_markers: {}",
        output.evidence_stats.marker_frame_add_id_markers
    );
    println!(
        "  runtime_evidence.marker_frame_active_add_id_markers: {}",
        output.evidence_stats.marker_frame_active_add_id_markers
    );
    println!(
        "  runtime_evidence.marker_frame_frame_only_entries: {}",
        output.evidence_stats.marker_frame_frame_only_entries
    );
    println!(
        "  runtime_evidence.marker_frame_no_active_add_id_no_handler_entries: {}",
        output
            .evidence_stats
            .marker_frame_no_active_add_id_no_handler_entries
    );
    println!(
        "  runtime_evidence.marker_frame_expr_entries: {}",
        output.evidence_stats.marker_frame_expr_entries
    );
    println!(
        "  runtime_evidence.marker_frame_scoped_apply_entries: {}",
        output.evidence_stats.marker_frame_scoped_apply_entries
    );
    println!(
        "  runtime_evidence.marker_frame_marked_apply_entries: {}",
        output.evidence_stats.marker_frame_marked_apply_entries
    );
    println!(
        "  runtime_evidence.marker_frame_adapter_entries: {}",
        output.evidence_stats.marker_frame_adapter_entries
    );
    println!(
        "  runtime_evidence.marker_frame_continuation_resume_entries: {}",
        output
            .evidence_stats
            .marker_frame_continuation_resume_entries
    );
    println!(
        "  runtime_evidence.marker_frame_marked_force_entries: {}",
        output.evidence_stats.marker_frame_marked_force_entries
    );
    println!(
        "  runtime_evidence.resume_marker_plan_empty: {}",
        output.evidence_stats.resume_marker_plan_empty
    );
    println!(
        "  runtime_evidence.resume_marker_plan_pure_value: {}",
        output.evidence_stats.resume_marker_plan_pure_value
    );
    println!(
        "  runtime_evidence.resume_marker_plan_dynamic_scope: {}",
        output.evidence_stats.resume_marker_plan_dynamic_scope
    );
    println!(
        "  runtime_evidence.resume_marker_plan_enter_ops_total: {}",
        output.evidence_stats.resume_marker_plan_enter_ops_total
    );
    println!(
        "  runtime_evidence.resume_marker_plan_handler_boundary: {}",
        output.evidence_stats.resume_marker_plan_handler_boundary
    );
    println!(
        "  runtime_evidence.resume_marker_plan_active_add_id_ops: {}",
        output.evidence_stats.resume_marker_plan_active_add_id_ops
    );
    println!(
        "  runtime_evidence.resume_marker_plan_to_legacy_push_pop: {}",
        output.evidence_stats.resume_marker_plan_to_legacy_push_pop
    );
    println!(
        "  runtime_evidence.marked_force_value_fast_paths: {}",
        output.evidence_stats.marked_force_value_fast_paths
    );
    println!(
        "  runtime_evidence.marked_force_fallback_expr_thunks: {}",
        output.evidence_stats.marked_force_fallback_expr_thunks
    );
    println!(
        "  runtime_evidence.marked_force_fallback_effect_thunks: {}",
        output.evidence_stats.marked_force_fallback_effect_thunks
    );
    println!(
        "  runtime_evidence.marked_force_fallback_continuation_thunks: {}",
        output
            .evidence_stats
            .marked_force_fallback_continuation_thunks
    );
    println!(
        "  runtime_evidence.marked_force_fallback_adapter_thunks: {}",
        output.evidence_stats.marked_force_fallback_adapter_thunks
    );
    println!(
        "  runtime_evidence.marked_force_fallback_other: {}",
        output.evidence_stats.marked_force_fallback_other
    );
    println!(
        "  runtime_evidence.marked_force_active_add_id_markers: {}",
        output.evidence_stats.marked_force_active_add_id_markers
    );
    println!(
        "  runtime_evidence.marked_force_carry_after_frame_markers: {}",
        output.evidence_stats.marked_force_carry_after_frame_markers
    );
    println!(
        "  runtime_evidence.active_marker_plan_pushes: {}",
        output.evidence_stats.active_marker_plan_pushes
    );
    println!(
        "  runtime_evidence.active_marker_plan_dedupes: {}",
        output.evidence_stats.active_marker_plan_dedupes
    );
    println!(
        "  runtime_evidence.active_add_id_scans: {}",
        output.evidence_stats.active_add_id_scans
    );
    println!(
        "  runtime_evidence.active_add_id_path_candidates: {}",
        output.evidence_stats.active_add_id_path_candidates
    );
    println!(
        "  runtime_evidence.active_add_id_path_rejects: {}",
        output.evidence_stats.active_add_id_path_rejects
    );
    println!(
        "  runtime_evidence.active_add_id_entry_except_rejects: {}",
        output.evidence_stats.active_add_id_entry_except_rejects
    );
    println!(
        "  runtime_evidence.active_add_id_already_carried_rejects: {}",
        output.evidence_stats.active_add_id_already_carried_rejects
    );
    println!(
        "  runtime_evidence.active_add_id_hits: {}",
        output.evidence_stats.active_add_id_hits
    );
    println!(
        "  runtime_evidence.function_call_marker_plans: {}",
        output.evidence_stats.function_call_marker_plans
    );
    println!(
        "  runtime_evidence.function_call_marker_inputs: {}",
        output.evidence_stats.function_call_marker_inputs
    );
    println!(
        "  runtime_evidence.function_call_marker_outputs: {}",
        output.evidence_stats.function_call_marker_outputs
    );
    println!(
        "  runtime_evidence.list_merge_calls: {}",
        output.evidence_stats.list_merge_calls
    );
    println!(
        "  runtime_evidence.list_view_raw_calls: {}",
        output.evidence_stats.list_view_raw_calls
    );
    println!(
        "  runtime_evidence.list_values_copied: {}",
        output.evidence_stats.list_values_copied
    );
    print_runtime_evidence_run_timings(&timings, &build_timings);
}

fn print_runtime_evidence_run_timings(
    timings: &RuntimeEvidenceRunTimings,
    build_timings: &RuntimePhaseTimings,
) {
    println!(
        "  timing.args_parse: {}",
        format_duration(timings.args_parse)
    );
    println!(
        "  timing.collect: {}",
        format_duration(build_timings.collect)
    );
    println!(
        "  timing.control_build_cache: {}",
        build_timings.build_cache.as_str()
    );
    println!(
        "  timing.control_build_total: {}",
        format_duration(timings.control_build_total)
    );
    println!(
        "  timing.build_poly: {}",
        format_duration(build_timings.build_poly)
    );
    println!(
        "  timing.specialize: {}",
        format_duration(build_timings.specialize)
    );
    println!(
        "  timing.control_lower: {}",
        format_duration(build_timings.control_lower)
    );
    println!(
        "  timing.evidence_summary: {}",
        format_duration(timings.evidence_summary)
    );
    println!(
        "  timing.evidence_plan_build: {}",
        format_duration(timings.evidence_plan_build)
    );
    println!(
        "  timing.runtime_evidence_execute: {}",
        format_duration(timings.runtime_evidence_execute)
    );
    println!(
        "  timing.root_format: {}",
        format_duration(timings.root_format)
    );
    println!(
        "  timing.total_before_compare: {}",
        format_duration(timings.total_before_compare)
    );
}
