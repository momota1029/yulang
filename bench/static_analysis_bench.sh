#!/usr/bin/env bash
set -euo pipefail

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
    local lower_bodies lower_drain lower_resolve lower_finish
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
    if [[ "$run_vm" == "1" ]]; then
        read -r run_real run_poly run_spec run_control vm_eval expr_evals expr_clones apply_value force_thunk effect_requests host_requests catch_matches continuations instance_eval instance_hits instance_misses < <(measure_run_metrics "$release" "$case_path")
    fi

    printf "%-34s %5s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %6s %7s %7s %8s %6s\n" \
        "$case_label" "$iteration" "$check_real" "$collect" "$load" "$infer" \
        "$lower_bodies" "$lower_drain" "$lower_resolve" "$lower_finish" \
        "$summarize" "$total" "$run_real" "$run_poly" "$run_spec" "$run_control" "$vm_eval" \
        "$expr_evals" "$expr_clones" "$apply_value" "$force_thunk" "$effect_requests" "$host_requests" \
        "$catch_matches" "$continuations" "$instance_eval" "$instance_hits" "$instance_misses" \
        "$files" "$modules" "$values" "$bodyless" "$errors"

    rm -f "$out_file" "$time_file"
}

print_header() {
    printf "%-34s %5s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %6s %7s %7s %8s %6s\n" \
        "case" "iter" "check" "collect" "load" "infer" "bodies" "drain" \
        "resolve" "finish" "summary" "total" "run" "poly" "spec" "ctl_low" "vm_eval" \
        "expr" "clone" "apply" "force" "effect" "host" "catch" "cont" "inst" "hit" "miss" \
        "files" "modules" "values" "bodyless" "errors"
}

print_failed_row() {
    local case_path="$1"
    local iteration="$2"
    printf "%-34s %5s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %9s %6s %7s %7s %8s %6s\n" \
        "$case_path" "$iteration" "FAILED" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-"
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
        echo "FAILED - - - - - - - - - - - - - - -"
        tail -n 20 "$out_file" >&2
    else
        printf "%s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s\n" \
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
            "$(phase_metric "run.instance_misses" "$out_file")"
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
