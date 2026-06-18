#!/usr/bin/env bash
set -euo pipefail

HEADER_COLUMNS=(
    case iter check collect load infer bodies drain resolve finish
    a_route a_sccrt scc_open scc_quant scc_inst scc_oth a_work w_ref w_probe w_aref w_asel w_asel_rec w_asel_m w_asel_eff w_asel_tc w_scc a_role a_taint a_rsolve a_udep a_quant q_gen q_pre q_fin
    g_comp g_roles g_merge g_dom g_sub g_cast g_rrole g_froles g_clean g_filter g_prep
    g_mrst g_srst g_crst g_rrst g_rin g_rreach g_rcoal g_rdom g_rsolvein
    a_inst i_clone i_sub i_roles i_runs i_maxrun i_targets i_reuse i_pvar i_pstk i_pnsub i_pfun i_pcon i_poth i_pdir a_record c_drain c_drains c_work c_sub c_subcall c_many c_invar c_vv c_posv c_maxq c_maxw c_lb c_ub c_lrep c_urep c_lenq c_uenq c_lrvv c_urvv c_vvub c_vvlb c_vvuin c_vvlin c_vvuenq c_vvlenq c_vvuski c_vvlski w_ref_n w_probe_n w_aref_n w_asel_n w_asel_rec_n w_asel_m_n w_asel_eff_n w_asel_tc_n w_scc_n scc_batches scc_ev scc_open_n scc_quant_n scc_inst_n scc_oth_n udep_n udep_in udep_e summary total run poly spec ctl_low vm_eval cval rinit rexec rfmt
    expr clone apply ap_m ap_p ap_con ap_cl ap_rcl ap_ad ap_ft ap_eff ap_k prim0 prim prim_part prim_done
    force f_m f_e f_v f_eff f_k f_ad effect host catch cont k_inv k_capc k_invc k_fclone k_sclone fr_unwrap k_max req_res c_val c_req cb_val cb_req cbr_val cbr_req cvb_val cvb_req
    mf mf_emp mf_push mf_vclose mf_rclose mf_res inst hit miss
    pfx pfx_seg peq peq_seg addscan frscan files modules values bodyless errors
)

main() {
    local repeat=1
    local release=1
    local run_vm=1
    local -a cases=()

    while (($# > 0)); do
        case "$1" in
            --repeat)
                if (($# < 2)); then
                    echo "missing value for --repeat" >&2
                    exit 2
                fi
                repeat="$2"
                shift 2
                ;;
            --debug)
                release=0
                shift
                ;;
            --infer-only)
                run_vm=0
                shift
                ;;
            --help|-h)
                print_usage
                exit 0
                ;;
            --)
                shift
                while (($# > 0)); do
                    cases+=("$1")
                    shift
                done
                ;;
            -*)
                echo "unknown option: $1" >&2
                print_usage >&2
                exit 2
                ;;
            *)
                cases+=("$1")
                shift
                ;;
        esac
    done

    if ((${#cases[@]} == 0)); then
        cases=(
            examples/showcase.yu
            examples/06_undet_once.yu
            examples/07_junction.yu
            examples/10_effect_handler.yu
            examples/13_console.yu
        )
    fi

    print_header

    local case_path
    for case_path in "${cases[@]}"; do
        run_case "$repeat" "$release" "$run_vm" "$case_path"
    done
}

run_case() {
    local repeat="$1"
    local release="$2"
    local run_vm="$3"
    local case_path="$4"
    local iteration

    for ((iteration = 1; iteration <= repeat; iteration++)); do
        run_case_once "$iteration" "$repeat" "$release" "$run_vm" "$case_path"
    done
}

run_case_once() {
    local iteration="$1"
    local repeat="$2"
    local release="$3"
    local run_vm="$4"
    local case_path="$5"
    local out_file time_file
    out_file="$(mktemp)"
    time_file="$(mktemp)"

    local -a cargo_args=(run -p yulang)
    if [[ "$release" == "1" ]]; then
        cargo_args+=(--release)
    fi
    cargo_args+=(--)
    cargo_args+=(check "$case_path")

    if ! env RUSTC_WRAPPER="${RUSTC_WRAPPER:-}" RUST_MIN_STACK="${RUST_MIN_STACK:-67108864}" \
        /usr/bin/time -p -o "$time_file" cargo "${cargo_args[@]}" >"$out_file" 2>&1
    then
        print_failed_row "$case_path" "$iteration"
        tail -n 20 "$out_file" >&2
        rm -f "$out_file" "$time_file"
        return
    fi

    local case_label check_real collect load infer summarize total files modules values bodyless errors
    local run_real run_poly run_spec run_control vm_eval control_validate runtime_init runtime_execute root_format
    local expr_evals expr_clones apply_value
    local apply_marked apply_primitive apply_constructor apply_closure
    local apply_recursive_closure apply_adapter apply_forced_thunk
    local apply_effect_op apply_continuation
    local primitive_zero_arity primitive_apply primitive_partial primitive_complete
    local force_thunk force_marked force_expr force_value force_effect
    local force_continuation force_adapter
    local effect_requests host_requests catch_matches continuations
    local continuation_invocations continuation_capture_clones continuation_invoke_clones
    local continuation_frames_cloned continuation_marker_scopes_cloned
    local shared_frame_unwrap_clones max_continuation_frames request_resume_steps
    local continue_value continue_request continue_bind_value continue_bind_request
    local continue_bind_result_value continue_bind_result_request
    local continue_value_bind_value continue_value_bind_request
    local marker_frame_calls marker_frame_empty marker_frame_pushes
    local marker_frame_value_closes marker_frame_request_closes marker_frame_resume_steps
    local instance_eval instance_hits instance_misses
    local path_prefix path_prefix_seg path_eq path_eq_seg active_add active_frame
    local lower_bodies lower_drain lower_resolve lower_finish
    local analysis_route analysis_route_scc_events
    local analysis_route_scc_open_use analysis_route_scc_quantify
    local analysis_route_scc_instantiate analysis_route_scc_other
    local analysis_work analysis_work_resolve_ref analysis_work_probe_select
    local analysis_work_apply_ref analysis_work_apply_select
    local analysis_work_apply_select_record_field analysis_work_apply_select_method
    local analysis_work_apply_select_effect_method analysis_work_apply_select_typeclass_method
    local analysis_work_scc
    local analysis_role analysis_taint analysis_role_solve analysis_unready_dependency
    local analysis_quantify analysis_quantify_generalize analysis_quantify_prerequisites
    local analysis_quantify_finalize analysis_instantiate analysis_record_field
    local generalize_compact generalize_collect_roles generalize_apply_merge
    local generalize_collect_dominance generalize_apply_subtype generalize_cast
    local generalize_resolve_roles generalize_final_roles generalize_final_cleanup
    local generalize_filter_roles generalize_prepared
    local generalize_merge_restarts generalize_subtype_restarts generalize_cast_restarts
    local generalize_role_restarts generalize_role_input_constraints
    local generalize_reachable_role_constraints generalize_coalesced_role_constraints
    local generalize_dominance_role_constraints generalize_role_resolve_inputs
    local instantiate_clone_scheme instantiate_subtype_predicate instantiate_insert_roles
    local instantiate_event_runs instantiate_max_event_run instantiate_unique_targets
    local instantiate_reused_target_events
    local instantiate_predicate_var instantiate_predicate_stack
    local instantiate_predicate_non_subtract instantiate_predicate_fun
    local instantiate_predicate_con instantiate_predicate_other
    local instantiate_direct_lower_predicates
    local work_resolve_ref_items work_probe_select_items work_apply_ref_items
    local work_apply_select_items work_apply_select_record_field_items
    local work_apply_select_method_items work_apply_select_effect_method_items
    local work_apply_select_typeclass_method_items work_scc_items
    local scc_event_batches scc_events scc_open_use_events
    local scc_quantify_events scc_instantiate_events scc_other_events
    local unready_role_dependency_scans unready_role_dependency_inputs
    local unready_role_dependency_edges
    local constraint_drain constraint_drains constraint_work constraint_subtype
    local constraint_subtype_calls constraint_subtype_many_calls
    local constraint_constrain_invariant_neu_calls constraint_constrain_var_var_direct_calls
    local constraint_constrain_pos_var_direct_calls
    local constraint_max_initial_queue constraint_max_work_items
    local constraint_lower_bounds_added constraint_upper_bounds_added
    local constraint_lower_replay_inputs constraint_upper_replay_inputs
    local constraint_lower_replay_enqueued constraint_upper_replay_enqueued
    local constraint_lower_replay_var_var constraint_upper_replay_var_var
    local constraint_var_var_direct_upper_bounds constraint_var_var_direct_lower_bounds
    local constraint_var_var_direct_upper_replay_inputs
    local constraint_var_var_direct_lower_replay_inputs
    local constraint_var_var_direct_upper_replay_enqueued
    local constraint_var_var_direct_lower_replay_enqueued
    local constraint_var_var_direct_upper_empty_replay_skipped
    local constraint_var_var_direct_lower_empty_replay_skipped
    case_label="$case_path"
    if ((repeat > 1)); then
        case_label="${case_path}#${iteration}"
    fi
    check_real="$(metric_from_time real "$time_file")"
    collect="$(phase_metric "collect" "$out_file")"
    load="$(phase_metric "load" "$out_file")"
    infer="$(phase_metric "infer" "$out_file")"
    lower_bodies="$(phase_metric "lower.bodies" "$out_file")"
    lower_drain="$(phase_metric "lower.drain" "$out_file")"
    lower_resolve="$(phase_metric "lower.resolve" "$out_file")"
    analysis_route="$(phase_metric "analysis.route" "$out_file")"
    analysis_route_scc_events="$(phase_metric "analysis.route_scc_events" "$out_file")"
    analysis_route_scc_open_use="$(phase_metric "analysis.route_scc_open_use" "$out_file")"
    analysis_route_scc_quantify="$(phase_metric "analysis.route_scc_quantify" "$out_file")"
    analysis_route_scc_instantiate="$(phase_metric "analysis.route_scc_instantiate" "$out_file")"
    analysis_route_scc_other="$(phase_metric "analysis.route_scc_other" "$out_file")"
    analysis_work="$(phase_metric "analysis.work" "$out_file")"
    analysis_work_resolve_ref="$(phase_metric "analysis.work_resolve_ref" "$out_file")"
    analysis_work_probe_select="$(phase_metric "analysis.work_probe_select" "$out_file")"
    analysis_work_apply_ref="$(phase_metric "analysis.work_apply_ref" "$out_file")"
    analysis_work_apply_select="$(phase_metric "analysis.work_apply_select" "$out_file")"
    analysis_work_apply_select_record_field="$(phase_metric "analysis.work_apply_select_record_field" "$out_file")"
    analysis_work_apply_select_method="$(phase_metric "analysis.work_apply_select_method" "$out_file")"
    analysis_work_apply_select_effect_method="$(phase_metric "analysis.work_apply_select_effect_method" "$out_file")"
    analysis_work_apply_select_typeclass_method="$(phase_metric "analysis.work_apply_select_typeclass_method" "$out_file")"
    analysis_work_scc="$(phase_metric "analysis.work_scc" "$out_file")"
    analysis_role="$(phase_metric "analysis.role" "$out_file")"
    analysis_taint="$(phase_metric "analysis.taint" "$out_file")"
    analysis_role_solve="$(phase_metric "analysis.role_solve" "$out_file")"
    analysis_unready_dependency="$(phase_metric "analysis.unready_role_dependency_scan" "$out_file")"
    analysis_quantify="$(phase_metric "analysis.quantify" "$out_file")"
    analysis_quantify_generalize="$(phase_metric "analysis.quantify_generalize" "$out_file")"
    analysis_quantify_prerequisites="$(phase_metric "analysis.quantify_prerequisites" "$out_file")"
    analysis_quantify_finalize="$(phase_metric "analysis.quantify_finalize" "$out_file")"
    generalize_compact="$(phase_metric "analysis.generalize_compact" "$out_file")"
    generalize_collect_roles="$(phase_metric "analysis.generalize_collect_roles" "$out_file")"
    generalize_apply_merge="$(phase_metric "analysis.generalize_apply_merge" "$out_file")"
    generalize_collect_dominance="$(phase_metric "analysis.generalize_collect_dominance" "$out_file")"
    generalize_apply_subtype="$(phase_metric "analysis.generalize_apply_subtype" "$out_file")"
    generalize_cast="$(phase_metric "analysis.generalize_cast" "$out_file")"
    generalize_resolve_roles="$(phase_metric "analysis.generalize_resolve_roles" "$out_file")"
    generalize_final_roles="$(phase_metric "analysis.generalize_final_roles" "$out_file")"
    generalize_final_cleanup="$(phase_metric "analysis.generalize_final_cleanup" "$out_file")"
    generalize_filter_roles="$(phase_metric "analysis.generalize_filter_roles" "$out_file")"
    generalize_prepared="$(phase_metric "analysis.generalize_prepared" "$out_file")"
    generalize_merge_restarts="$(phase_metric "analysis.generalize_merge_restarts" "$out_file")"
    generalize_subtype_restarts="$(phase_metric "analysis.generalize_subtype_restarts" "$out_file")"
    generalize_cast_restarts="$(phase_metric "analysis.generalize_cast_restarts" "$out_file")"
    generalize_role_restarts="$(phase_metric "analysis.generalize_role_restarts" "$out_file")"
    generalize_role_input_constraints="$(phase_metric "analysis.generalize_role_input_constraints" "$out_file")"
    generalize_reachable_role_constraints="$(phase_metric "analysis.generalize_reachable_role_constraints" "$out_file")"
    generalize_coalesced_role_constraints="$(phase_metric "analysis.generalize_coalesced_role_constraints" "$out_file")"
    generalize_dominance_role_constraints="$(phase_metric "analysis.generalize_dominance_role_constraints" "$out_file")"
    generalize_role_resolve_inputs="$(phase_metric "analysis.generalize_role_resolve_inputs" "$out_file")"
    analysis_instantiate="$(phase_metric "analysis.instantiate" "$out_file")"
    instantiate_clone_scheme="$(phase_metric "analysis.instantiate_clone_scheme" "$out_file")"
    instantiate_subtype_predicate="$(phase_metric "analysis.instantiate_subtype_predicate" "$out_file")"
    instantiate_insert_roles="$(phase_metric "analysis.instantiate_insert_roles" "$out_file")"
    instantiate_event_runs="$(phase_metric "analysis.instantiate_event_runs" "$out_file")"
    instantiate_max_event_run="$(phase_metric "analysis.instantiate_max_event_run" "$out_file")"
    instantiate_unique_targets="$(phase_metric "analysis.instantiate_unique_targets" "$out_file")"
    instantiate_reused_target_events="$(phase_metric "analysis.instantiate_reused_target_events" "$out_file")"
    instantiate_predicate_var="$(phase_metric "analysis.instantiate_predicate_var" "$out_file")"
    instantiate_predicate_stack="$(phase_metric "analysis.instantiate_predicate_stack" "$out_file")"
    instantiate_predicate_non_subtract="$(phase_metric "analysis.instantiate_predicate_non_subtract" "$out_file")"
    instantiate_predicate_fun="$(phase_metric "analysis.instantiate_predicate_fun" "$out_file")"
    instantiate_predicate_con="$(phase_metric "analysis.instantiate_predicate_con" "$out_file")"
    instantiate_predicate_other="$(phase_metric "analysis.instantiate_predicate_other" "$out_file")"
    instantiate_direct_lower_predicates="$(phase_metric "analysis.instantiate_direct_lower_predicates" "$out_file")"
    analysis_record_field="$(phase_metric "analysis.record_field" "$out_file")"
    constraint_drain="$(phase_metric "constraint.drain" "$out_file")"
    constraint_drains="$(phase_metric "constraint.drains" "$out_file")"
    constraint_work="$(phase_metric "constraint.work_items" "$out_file")"
    constraint_subtype="$(phase_metric "constraint.subtype_work_items" "$out_file")"
    constraint_subtype_calls="$(phase_metric "constraint.subtype_calls" "$out_file")"
    constraint_subtype_many_calls="$(phase_metric "constraint.subtype_many_calls" "$out_file")"
    constraint_constrain_invariant_neu_calls="$(phase_metric "constraint.constrain_invariant_neu_calls" "$out_file")"
    constraint_constrain_var_var_direct_calls="$(phase_metric "constraint.constrain_var_var_direct_calls" "$out_file")"
    constraint_constrain_pos_var_direct_calls="$(phase_metric "constraint.constrain_pos_var_direct_calls" "$out_file")"
    constraint_max_initial_queue="$(phase_metric "constraint.max_initial_queue" "$out_file")"
    constraint_max_work_items="$(phase_metric "constraint.max_work_items" "$out_file")"
    constraint_lower_bounds_added="$(phase_metric "constraint.lower_bounds_added" "$out_file")"
    constraint_upper_bounds_added="$(phase_metric "constraint.upper_bounds_added" "$out_file")"
    constraint_lower_replay_inputs="$(phase_metric "constraint.lower_replay_inputs" "$out_file")"
    constraint_upper_replay_inputs="$(phase_metric "constraint.upper_replay_inputs" "$out_file")"
    constraint_lower_replay_enqueued="$(phase_metric "constraint.lower_replay_enqueued" "$out_file")"
    constraint_upper_replay_enqueued="$(phase_metric "constraint.upper_replay_enqueued" "$out_file")"
    constraint_lower_replay_var_var="$(phase_metric "constraint.lower_replay_var_var" "$out_file")"
    constraint_upper_replay_var_var="$(phase_metric "constraint.upper_replay_var_var" "$out_file")"
    constraint_var_var_direct_upper_bounds="$(phase_metric "constraint.var_var_direct_upper_bounds" "$out_file")"
    constraint_var_var_direct_lower_bounds="$(phase_metric "constraint.var_var_direct_lower_bounds" "$out_file")"
    constraint_var_var_direct_upper_replay_inputs="$(phase_metric "constraint.var_var_direct_upper_replay_inputs" "$out_file")"
    constraint_var_var_direct_lower_replay_inputs="$(phase_metric "constraint.var_var_direct_lower_replay_inputs" "$out_file")"
    constraint_var_var_direct_upper_replay_enqueued="$(phase_metric "constraint.var_var_direct_upper_replay_enqueued" "$out_file")"
    constraint_var_var_direct_lower_replay_enqueued="$(phase_metric "constraint.var_var_direct_lower_replay_enqueued" "$out_file")"
    constraint_var_var_direct_upper_empty_replay_skipped="$(phase_metric "constraint.var_var_direct_upper_empty_replay_skipped" "$out_file")"
    constraint_var_var_direct_lower_empty_replay_skipped="$(phase_metric "constraint.var_var_direct_lower_empty_replay_skipped" "$out_file")"
    work_resolve_ref_items="$(phase_metric "analysis.work_resolve_ref_items" "$out_file")"
    work_probe_select_items="$(phase_metric "analysis.work_probe_select_items" "$out_file")"
    work_apply_ref_items="$(phase_metric "analysis.work_apply_ref_items" "$out_file")"
    work_apply_select_items="$(phase_metric "analysis.work_apply_select_items" "$out_file")"
    work_apply_select_record_field_items="$(phase_metric "analysis.work_apply_select_record_field_items" "$out_file")"
    work_apply_select_method_items="$(phase_metric "analysis.work_apply_select_method_items" "$out_file")"
    work_apply_select_effect_method_items="$(phase_metric "analysis.work_apply_select_effect_method_items" "$out_file")"
    work_apply_select_typeclass_method_items="$(phase_metric "analysis.work_apply_select_typeclass_method_items" "$out_file")"
    work_scc_items="$(phase_metric "analysis.work_scc_items" "$out_file")"
    scc_event_batches="$(phase_metric "analysis.scc_event_batches" "$out_file")"
    scc_events="$(phase_metric "analysis.scc_events" "$out_file")"
    scc_open_use_events="$(phase_metric "analysis.scc_open_use_events" "$out_file")"
    scc_quantify_events="$(phase_metric "analysis.scc_quantify_events" "$out_file")"
    scc_instantiate_events="$(phase_metric "analysis.scc_instantiate_events" "$out_file")"
    scc_other_events="$(phase_metric "analysis.scc_other_events" "$out_file")"
    unready_role_dependency_scans="$(phase_metric "analysis.unready_role_dependency_scans" "$out_file")"
    unready_role_dependency_inputs="$(phase_metric "analysis.unready_role_dependency_inputs" "$out_file")"
    unready_role_dependency_edges="$(phase_metric "analysis.unready_role_dependency_edges" "$out_file")"
    lower_finish="$(phase_metric "lower.finish" "$out_file")"
    summarize="$(phase_metric "summarize" "$out_file")"
    total="$(phase_metric "total" "$out_file")"
    files="$(top_metric "files" "$out_file")"
    modules="$(summary_metric "modules" "$out_file")"
    values="$(summary_metric "module values" "$out_file")"
    bodyless="$(summary_metric "bodyless declarations" "$out_file")"
    errors="$(summary_metric "lowering errors" "$out_file")"
    run_real="-"
    run_poly="-"
    run_spec="-"
    run_control="-"
    vm_eval="-"
    control_validate="-"
    runtime_init="-"
    runtime_execute="-"
    root_format="-"
    expr_evals="-"
    expr_clones="-"
    apply_value="-"
    apply_marked="-"
    apply_primitive="-"
    apply_constructor="-"
    apply_closure="-"
    apply_recursive_closure="-"
    apply_adapter="-"
    apply_forced_thunk="-"
    apply_effect_op="-"
    apply_continuation="-"
    primitive_zero_arity="-"
    primitive_apply="-"
    primitive_partial="-"
    primitive_complete="-"
    force_thunk="-"
    force_marked="-"
    force_expr="-"
    force_value="-"
    force_effect="-"
    force_continuation="-"
    force_adapter="-"
    effect_requests="-"
    host_requests="-"
    catch_matches="-"
    continuations="-"
    continuation_invocations="-"
    continuation_capture_clones="-"
    continuation_invoke_clones="-"
    continuation_frames_cloned="-"
    continuation_marker_scopes_cloned="-"
    shared_frame_unwrap_clones="-"
    max_continuation_frames="-"
    request_resume_steps="-"
    continue_value="-"
    continue_request="-"
    continue_bind_value="-"
    continue_bind_request="-"
    continue_bind_result_value="-"
    continue_bind_result_request="-"
    continue_value_bind_value="-"
    continue_value_bind_request="-"
    marker_frame_calls="-"
    marker_frame_empty="-"
    marker_frame_pushes="-"
    marker_frame_value_closes="-"
    marker_frame_request_closes="-"
    marker_frame_resume_steps="-"
    instance_eval="-"
    instance_hits="-"
    instance_misses="-"
    path_prefix="-"
    path_prefix_seg="-"
    path_eq="-"
    path_eq_seg="-"
    active_add="-"
    active_frame="-"
    if [[ "$run_vm" == "1" ]]; then
        read -r run_real run_poly run_spec run_control vm_eval control_validate runtime_init runtime_execute root_format expr_evals expr_clones apply_value apply_marked apply_primitive apply_constructor apply_closure apply_recursive_closure apply_adapter apply_forced_thunk apply_effect_op apply_continuation primitive_zero_arity primitive_apply primitive_partial primitive_complete force_thunk force_marked force_expr force_value force_effect force_continuation force_adapter effect_requests host_requests catch_matches continuations continuation_invocations continuation_capture_clones continuation_invoke_clones continuation_frames_cloned continuation_marker_scopes_cloned shared_frame_unwrap_clones max_continuation_frames request_resume_steps continue_value continue_request continue_bind_value continue_bind_request continue_bind_result_value continue_bind_result_request continue_value_bind_value continue_value_bind_request marker_frame_calls marker_frame_empty marker_frame_pushes marker_frame_value_closes marker_frame_request_closes marker_frame_resume_steps instance_eval instance_hits instance_misses path_prefix path_prefix_seg path_eq path_eq_seg active_add active_frame < <(measure_run_metrics "$release" "$case_path")
    fi

    print_columns \
        "$case_label" "$iteration" "$check_real" "$collect" "$load" "$infer" \
        "$lower_bodies" "$lower_drain" "$lower_resolve" "$lower_finish" \
        "$analysis_route" "$analysis_route_scc_events" "$analysis_route_scc_open_use" \
        "$analysis_route_scc_quantify" "$analysis_route_scc_instantiate" \
        "$analysis_route_scc_other" "$analysis_work" "$analysis_work_resolve_ref" \
        "$analysis_work_probe_select" "$analysis_work_apply_ref" \
        "$analysis_work_apply_select" "$analysis_work_apply_select_record_field" \
        "$analysis_work_apply_select_method" "$analysis_work_apply_select_effect_method" \
        "$analysis_work_apply_select_typeclass_method" "$analysis_work_scc" "$analysis_role" "$analysis_taint" \
        "$analysis_role_solve" "$analysis_unready_dependency" "$analysis_quantify" \
        "$analysis_quantify_generalize" \
        "$analysis_quantify_prerequisites" "$analysis_quantify_finalize" \
        "$generalize_compact" "$generalize_collect_roles" "$generalize_apply_merge" \
        "$generalize_collect_dominance" "$generalize_apply_subtype" "$generalize_cast" \
        "$generalize_resolve_roles" "$generalize_final_roles" "$generalize_final_cleanup" \
        "$generalize_filter_roles" "$generalize_prepared" \
        "$generalize_merge_restarts" "$generalize_subtype_restarts" "$generalize_cast_restarts" \
        "$generalize_role_restarts" "$generalize_role_input_constraints" \
        "$generalize_reachable_role_constraints" "$generalize_coalesced_role_constraints" \
        "$generalize_dominance_role_constraints" "$generalize_role_resolve_inputs" \
        "$analysis_instantiate" "$instantiate_clone_scheme" "$instantiate_subtype_predicate" \
        "$instantiate_insert_roles" "$instantiate_event_runs" "$instantiate_max_event_run" \
        "$instantiate_unique_targets" "$instantiate_reused_target_events" \
        "$instantiate_predicate_var" "$instantiate_predicate_stack" \
        "$instantiate_predicate_non_subtract" "$instantiate_predicate_fun" \
        "$instantiate_predicate_con" "$instantiate_predicate_other" \
        "$instantiate_direct_lower_predicates" "$analysis_record_field" \
        "$constraint_drain" "$constraint_drains" "$constraint_work" "$constraint_subtype" \
        "$constraint_subtype_calls" "$constraint_subtype_many_calls" \
        "$constraint_constrain_invariant_neu_calls" "$constraint_constrain_var_var_direct_calls" \
        "$constraint_constrain_pos_var_direct_calls" \
        "$constraint_max_initial_queue" "$constraint_max_work_items" \
        "$constraint_lower_bounds_added" "$constraint_upper_bounds_added" \
        "$constraint_lower_replay_inputs" "$constraint_upper_replay_inputs" \
        "$constraint_lower_replay_enqueued" "$constraint_upper_replay_enqueued" \
        "$constraint_lower_replay_var_var" "$constraint_upper_replay_var_var" \
        "$constraint_var_var_direct_upper_bounds" "$constraint_var_var_direct_lower_bounds" \
        "$constraint_var_var_direct_upper_replay_inputs" "$constraint_var_var_direct_lower_replay_inputs" \
        "$constraint_var_var_direct_upper_replay_enqueued" "$constraint_var_var_direct_lower_replay_enqueued" \
        "$constraint_var_var_direct_upper_empty_replay_skipped" "$constraint_var_var_direct_lower_empty_replay_skipped" \
        "$work_resolve_ref_items" "$work_probe_select_items" "$work_apply_ref_items" \
        "$work_apply_select_items" "$work_apply_select_record_field_items" \
        "$work_apply_select_method_items" "$work_apply_select_effect_method_items" \
        "$work_apply_select_typeclass_method_items" "$work_scc_items" \
        "$scc_event_batches" "$scc_events" "$scc_open_use_events" \
        "$scc_quantify_events" "$scc_instantiate_events" "$scc_other_events" \
        "$unready_role_dependency_scans" \
        "$unready_role_dependency_inputs" "$unready_role_dependency_edges" \
        "$summarize" "$total" "$run_real" "$run_poly" "$run_spec" "$run_control" "$vm_eval" \
        "$control_validate" "$runtime_init" "$runtime_execute" "$root_format" \
        "$expr_evals" "$expr_clones" "$apply_value" "$apply_marked" "$apply_primitive" \
        "$apply_constructor" "$apply_closure" "$apply_recursive_closure" "$apply_adapter" \
        "$apply_forced_thunk" "$apply_effect_op" "$apply_continuation" \
        "$primitive_zero_arity" "$primitive_apply" "$primitive_partial" "$primitive_complete" \
        "$force_thunk" "$force_marked" "$force_expr" "$force_value" "$force_effect" \
        "$force_continuation" "$force_adapter" "$effect_requests" "$host_requests" \
        "$catch_matches" "$continuations" "$continuation_invocations" \
        "$continuation_capture_clones" "$continuation_invoke_clones" \
        "$continuation_frames_cloned" "$continuation_marker_scopes_cloned" \
        "$shared_frame_unwrap_clones" "$max_continuation_frames" "$request_resume_steps" \
        "$continue_value" "$continue_request" "$continue_bind_value" "$continue_bind_request" \
        "$continue_bind_result_value" "$continue_bind_result_request" \
        "$continue_value_bind_value" "$continue_value_bind_request" \
        "$marker_frame_calls" "$marker_frame_empty" "$marker_frame_pushes" \
        "$marker_frame_value_closes" "$marker_frame_request_closes" "$marker_frame_resume_steps" \
        "$instance_eval" "$instance_hits" "$instance_misses" \
        "$path_prefix" "$path_prefix_seg" "$path_eq" "$path_eq_seg" "$active_add" "$active_frame" \
        "$files" "$modules" "$values" "$bodyless" "$errors"

    rm -f "$out_file" "$time_file"
}

print_header() {
    print_columns "${HEADER_COLUMNS[@]}"
}

print_failed_row() {
    local case_path="$1"
    local iteration="$2"
    local -a row=("$case_path" "$iteration" "FAILED")
    while ((${#row[@]} < ${#HEADER_COLUMNS[@]})); do
        row+=("-")
    done
    print_columns "${row[@]}"
}

print_columns() {
    local first="$1"
    shift
    printf "%-34s" "$first"
    for value in "$@"; do
        printf " %9s" "$value"
    done
    printf "\n"
}

phase_metric() {
    local name="$1"
    local path="$2"
    local line
    line="$(grep -E "^[[:space:]]+${name}:" "$path" | head -n 1 || true)"
    if [[ -z "$line" ]]; then
        echo "-"
        return
    fi
    echo "$line" | sed -E "s/^[[:space:]]+${name}:[[:space:]]+([^[:space:]]+).*/\1/"
}

metric_from_time() {
    local name="$1"
    local path="$2"
    awk -v key="$name" '$1 == key { print $2 }' "$path"
}

top_metric() {
    local name="$1"
    local path="$2"
    local line
    line="$(grep -E "^${name}:" "$path" | head -n 1 || true)"
    if [[ -z "$line" ]]; then
        echo "-"
        return
    fi
    echo "$line" | sed -E "s/^${name}:[[:space:]]+([^[:space:]]+).*/\1/"
}

summary_metric() {
    local name="$1"
    local path="$2"
    local line
    line="$(grep -E "^[[:space:]]+${name}:" "$path" | head -n 1 || true)"
    if [[ -z "$line" ]]; then
        echo "-"
        return
    fi
    echo "$line" | sed -E "s/^[[:space:]]+${name}:[[:space:]]+([^[:space:]]+).*/\1/"
}

measure_run_metrics() {
    local release="$1"
    local case_path="$2"
    local out_file time_file
    out_file="$(mktemp)"
    time_file="$(mktemp)"

    local -a cargo_args=(run -p yulang)
    if [[ "$release" == "1" ]]; then
        cargo_args+=(--release)
    fi
    cargo_args+=(--)
    cargo_args+=(--runtime-phase-timings --no-cache run --print-roots "$case_path")

    if ! env RUSTC_WRAPPER="${RUSTC_WRAPPER:-}" RUST_MIN_STACK="${RUST_MIN_STACK:-67108864}" \
        /usr/bin/time -p -o "$time_file" cargo "${cargo_args[@]}" >"$out_file" 2>&1
    then
        local -a failed=(FAILED)
        while ((${#failed[@]} < 67)); do
            failed+=("-")
        done
        echo "${failed[*]}"
        tail -n 20 "$out_file" >&2
    else
        local -a metrics=(
            "$(metric_from_time real "$time_file")"
            "$(phase_metric "run.build_poly" "$out_file")"
            "$(phase_metric "run.specialize" "$out_file")"
            "$(phase_metric "run.control_lower" "$out_file")"
            "$(phase_metric "run.vm_eval" "$out_file")"
            "$(phase_metric "run.control_validate" "$out_file")"
            "$(phase_metric "run.runtime_init" "$out_file")"
            "$(phase_metric "run.runtime_execute" "$out_file")"
            "$(phase_metric "run.root_format" "$out_file")"
            "$(phase_metric "run.expr_evals" "$out_file")"
            "$(phase_metric "run.expr_clones" "$out_file")"
            "$(phase_metric "run.apply_value" "$out_file")"
            "$(phase_metric "run.apply_marked" "$out_file")"
            "$(phase_metric "run.apply_primitive" "$out_file")"
            "$(phase_metric "run.apply_constructor" "$out_file")"
            "$(phase_metric "run.apply_closure" "$out_file")"
            "$(phase_metric "run.apply_recursive_closure" "$out_file")"
            "$(phase_metric "run.apply_adapter" "$out_file")"
            "$(phase_metric "run.apply_forced_thunk" "$out_file")"
            "$(phase_metric "run.apply_effect_op" "$out_file")"
            "$(phase_metric "run.apply_continuation" "$out_file")"
            "$(phase_metric "run.primitive_zero_arity" "$out_file")"
            "$(phase_metric "run.primitive_apply" "$out_file")"
            "$(phase_metric "run.primitive_partial" "$out_file")"
            "$(phase_metric "run.primitive_complete" "$out_file")"
            "$(phase_metric "run.force_thunk" "$out_file")"
            "$(phase_metric "run.force_marked" "$out_file")"
            "$(phase_metric "run.force_expr" "$out_file")"
            "$(phase_metric "run.force_value" "$out_file")"
            "$(phase_metric "run.force_effect" "$out_file")"
            "$(phase_metric "run.force_continuation" "$out_file")"
            "$(phase_metric "run.force_adapter" "$out_file")"
            "$(phase_metric "run.effect_requests" "$out_file")"
            "$(phase_metric "run.host_requests" "$out_file")"
            "$(phase_metric "run.catch_matches" "$out_file")"
            "$(phase_metric "run.continuations" "$out_file")"
            "$(phase_metric "run.continuation_invocations" "$out_file")"
            "$(phase_metric "run.continuation_capture_clones" "$out_file")"
            "$(phase_metric "run.continuation_invoke_clones" "$out_file")"
            "$(phase_metric "run.continuation_frames_cloned" "$out_file")"
            "$(phase_metric "run.continuation_marker_scopes_cloned" "$out_file")"
            "$(phase_metric "run.shared_frame_unwrap_clones" "$out_file")"
            "$(phase_metric "run.max_continuation_frames" "$out_file")"
            "$(phase_metric "run.request_resume_steps" "$out_file")"
            "$(phase_metric "run.continue_value" "$out_file")"
            "$(phase_metric "run.continue_request" "$out_file")"
            "$(phase_metric "run.continue_bind_value" "$out_file")"
            "$(phase_metric "run.continue_bind_request" "$out_file")"
            "$(phase_metric "run.continue_bind_result_value" "$out_file")"
            "$(phase_metric "run.continue_bind_result_request" "$out_file")"
            "$(phase_metric "run.continue_value_bind_value" "$out_file")"
            "$(phase_metric "run.continue_value_bind_request" "$out_file")"
            "$(phase_metric "run.marker_frame_calls" "$out_file")"
            "$(phase_metric "run.marker_frame_empty" "$out_file")"
            "$(phase_metric "run.marker_frame_pushes" "$out_file")"
            "$(phase_metric "run.marker_frame_value_closes" "$out_file")"
            "$(phase_metric "run.marker_frame_request_closes" "$out_file")"
            "$(phase_metric "run.marker_frame_resume_steps" "$out_file")"
            "$(phase_metric "run.instance_eval" "$out_file")"
            "$(phase_metric "run.instance_hits" "$out_file")"
            "$(phase_metric "run.instance_misses" "$out_file")"
            "$(phase_metric "run.path_prefix_checks" "$out_file")"
            "$(phase_metric "run.path_prefix_segments" "$out_file")"
            "$(phase_metric "run.path_eq_checks" "$out_file")"
            "$(phase_metric "run.path_eq_segments" "$out_file")"
            "$(phase_metric "run.active_add_scans" "$out_file")"
            "$(phase_metric "run.active_frame_scans" "$out_file")"
        )
        echo "${metrics[*]}"
    fi
    rm -f "$out_file" "$time_file"
}

print_usage() {
    cat <<'EOF'
usage: bench/static_analysis_bench.sh [--repeat N] [--debug] [--infer-only] [case.yu ...]

Runs representative Yulang programs through:
  cargo run -p yulang --release -- check

Without --infer-only it also measures:
  cargo run -p yulang --release -- --no-cache run --print-roots

Use --infer-only for cases that are useful to typecheck but not safe to run.

Columns:
  check    wall clock for `yulang check`
  collect  source collection timing reported by check
  load     sources::load timing reported by check
  infer    infer/check timing reported by check
  summary  diagnostic/summary timing reported by check
  total    total check timing reported by check
  run      wall clock for `yulang --no-cache run --print-roots`; omitted with --infer-only
  files/modules/values/bodyless/errors are taken from the check summary
EOF
}

main "$@"
