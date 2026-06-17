#!/usr/bin/env bash
set -euo pipefail

HEADER_COLUMNS=(
    case iter check collect load infer bodies drain resolve finish
    a_route a_work a_role a_taint a_rsolve a_quant q_gen q_pre q_fin
    g_comp g_roles g_merge g_dom g_sub g_cast g_rrole g_froles g_clean g_filter g_prep
    a_inst i_clone i_sub i_roles i_runs i_maxrun i_targets i_reuse a_record c_drain c_drains c_work c_sub c_subcall c_many c_invar c_vv c_maxq c_maxw summary total run poly spec ctl_low vm_eval
    expr clone apply force effect host catch cont inst hit miss
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
    local run_real run_poly run_spec run_control vm_eval
    local expr_evals expr_clones apply_value force_thunk effect_requests host_requests
    local catch_matches continuations instance_eval instance_hits instance_misses
    local path_prefix path_prefix_seg path_eq path_eq_seg active_add active_frame
    local lower_bodies lower_drain lower_resolve lower_finish
    local analysis_route analysis_work analysis_role analysis_taint analysis_role_solve
    local analysis_quantify analysis_quantify_generalize analysis_quantify_prerequisites
    local analysis_quantify_finalize analysis_instantiate analysis_record_field
    local generalize_compact generalize_collect_roles generalize_apply_merge
    local generalize_collect_dominance generalize_apply_subtype generalize_cast
    local generalize_resolve_roles generalize_final_roles generalize_final_cleanup
    local generalize_filter_roles generalize_prepared
    local instantiate_clone_scheme instantiate_subtype_predicate instantiate_insert_roles
    local instantiate_event_runs instantiate_max_event_run instantiate_unique_targets
    local instantiate_reused_target_events
    local constraint_drain constraint_drains constraint_work constraint_subtype
    local constraint_subtype_calls constraint_subtype_many_calls
    local constraint_constrain_invariant_neu_calls constraint_constrain_var_var_direct_calls
    local constraint_max_initial_queue constraint_max_work_items
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
    analysis_work="$(phase_metric "analysis.work" "$out_file")"
    analysis_role="$(phase_metric "analysis.role" "$out_file")"
    analysis_taint="$(phase_metric "analysis.taint" "$out_file")"
    analysis_role_solve="$(phase_metric "analysis.role_solve" "$out_file")"
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
    analysis_instantiate="$(phase_metric "analysis.instantiate" "$out_file")"
    instantiate_clone_scheme="$(phase_metric "analysis.instantiate_clone_scheme" "$out_file")"
    instantiate_subtype_predicate="$(phase_metric "analysis.instantiate_subtype_predicate" "$out_file")"
    instantiate_insert_roles="$(phase_metric "analysis.instantiate_insert_roles" "$out_file")"
    instantiate_event_runs="$(phase_metric "analysis.instantiate_event_runs" "$out_file")"
    instantiate_max_event_run="$(phase_metric "analysis.instantiate_max_event_run" "$out_file")"
    instantiate_unique_targets="$(phase_metric "analysis.instantiate_unique_targets" "$out_file")"
    instantiate_reused_target_events="$(phase_metric "analysis.instantiate_reused_target_events" "$out_file")"
    analysis_record_field="$(phase_metric "analysis.record_field" "$out_file")"
    constraint_drain="$(phase_metric "constraint.drain" "$out_file")"
    constraint_drains="$(phase_metric "constraint.drains" "$out_file")"
    constraint_work="$(phase_metric "constraint.work_items" "$out_file")"
    constraint_subtype="$(phase_metric "constraint.subtype_work_items" "$out_file")"
    constraint_subtype_calls="$(phase_metric "constraint.subtype_calls" "$out_file")"
    constraint_subtype_many_calls="$(phase_metric "constraint.subtype_many_calls" "$out_file")"
    constraint_constrain_invariant_neu_calls="$(phase_metric "constraint.constrain_invariant_neu_calls" "$out_file")"
    constraint_constrain_var_var_direct_calls="$(phase_metric "constraint.constrain_var_var_direct_calls" "$out_file")"
    constraint_max_initial_queue="$(phase_metric "constraint.max_initial_queue" "$out_file")"
    constraint_max_work_items="$(phase_metric "constraint.max_work_items" "$out_file")"
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
    expr_evals="-"
    expr_clones="-"
    apply_value="-"
    force_thunk="-"
    effect_requests="-"
    host_requests="-"
    catch_matches="-"
    continuations="-"
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
        read -r run_real run_poly run_spec run_control vm_eval expr_evals expr_clones apply_value force_thunk effect_requests host_requests catch_matches continuations instance_eval instance_hits instance_misses path_prefix path_prefix_seg path_eq path_eq_seg active_add active_frame < <(measure_run_metrics "$release" "$case_path")
    fi

    print_columns \
        "$case_label" "$iteration" "$check_real" "$collect" "$load" "$infer" \
        "$lower_bodies" "$lower_drain" "$lower_resolve" "$lower_finish" \
        "$analysis_route" "$analysis_work" "$analysis_role" "$analysis_taint" \
        "$analysis_role_solve" "$analysis_quantify" "$analysis_quantify_generalize" \
        "$analysis_quantify_prerequisites" "$analysis_quantify_finalize" \
        "$generalize_compact" "$generalize_collect_roles" "$generalize_apply_merge" \
        "$generalize_collect_dominance" "$generalize_apply_subtype" "$generalize_cast" \
        "$generalize_resolve_roles" "$generalize_final_roles" "$generalize_final_cleanup" \
        "$generalize_filter_roles" "$generalize_prepared" \
        "$analysis_instantiate" "$instantiate_clone_scheme" "$instantiate_subtype_predicate" \
        "$instantiate_insert_roles" "$instantiate_event_runs" "$instantiate_max_event_run" \
        "$instantiate_unique_targets" "$instantiate_reused_target_events" "$analysis_record_field" \
        "$constraint_drain" "$constraint_drains" "$constraint_work" "$constraint_subtype" \
        "$constraint_subtype_calls" "$constraint_subtype_many_calls" \
        "$constraint_constrain_invariant_neu_calls" "$constraint_constrain_var_var_direct_calls" \
        "$constraint_max_initial_queue" "$constraint_max_work_items" \
        "$summarize" "$total" "$run_real" "$run_poly" "$run_spec" "$run_control" "$vm_eval" \
        "$expr_evals" "$expr_clones" "$apply_value" "$force_thunk" "$effect_requests" "$host_requests" \
        "$catch_matches" "$continuations" "$instance_eval" "$instance_hits" "$instance_misses" \
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
        echo "FAILED - - - - - - - - - - - - - - - - - - - - -"
        tail -n 20 "$out_file" >&2
    else
        printf "%s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s\n" \
            "$(metric_from_time real "$time_file")" \
            "$(phase_metric "run.build_poly" "$out_file")" \
            "$(phase_metric "run.specialize" "$out_file")" \
            "$(phase_metric "run.control_lower" "$out_file")" \
            "$(phase_metric "run.vm_eval" "$out_file")" \
            "$(phase_metric "run.expr_evals" "$out_file")" \
            "$(phase_metric "run.expr_clones" "$out_file")" \
            "$(phase_metric "run.apply_value" "$out_file")" \
            "$(phase_metric "run.force_thunk" "$out_file")" \
            "$(phase_metric "run.effect_requests" "$out_file")" \
            "$(phase_metric "run.host_requests" "$out_file")" \
            "$(phase_metric "run.catch_matches" "$out_file")" \
            "$(phase_metric "run.continuations" "$out_file")" \
            "$(phase_metric "run.instance_eval" "$out_file")" \
            "$(phase_metric "run.instance_hits" "$out_file")" \
            "$(phase_metric "run.instance_misses" "$out_file")" \
            "$(phase_metric "run.path_prefix_checks" "$out_file")" \
            "$(phase_metric "run.path_prefix_segments" "$out_file")" \
            "$(phase_metric "run.path_eq_checks" "$out_file")" \
            "$(phase_metric "run.path_eq_segments" "$out_file")" \
            "$(phase_metric "run.active_add_scans" "$out_file")" \
            "$(phase_metric "run.active_frame_scans" "$out_file")"
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
