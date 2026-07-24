#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
default_bin="$repo_root/target/release/yulang"
bin="${YULANG:-"$default_bin"}"
std_root="${YULANG_STD_ROOT:-"$repo_root/lib"}"
timestamp="$(date +%Y%m%d-%H%M%S)"
out_dir="${YULANG_PERF_GATE_OUTPUT_DIR:-"$repo_root/target/performance-gate/$timestamp"}"
summary="$out_dir/summary.txt"

test_timeout="${YULANG_PERF_GATE_TEST_TIMEOUT:-240s}"
run_timeout="${YULANG_PERF_GATE_RUN_TIMEOUT:-300s}"
bench_timeout="${YULANG_PERF_GATE_BENCH_TIMEOUT:-480s}"
adversarial_timeout="${YULANG_PERF_GATE_ADVERSARIAL_TIMEOUT:-30s}"
repeat="${YULANG_PERF_GATE_REPEAT:-1}"
std_prefix_boundary_max_slowdown="${YULANG_PERF_GATE_STD_PREFIX_BOUNDARY_MAX_SLOWDOWN:-5}"

run_hardening="${YULANG_PERF_GATE_HARDENING:-1}"
run_adversarial="${YULANG_PERF_GATE_ADVERSARIAL:-1}"
run_release_smoke="${YULANG_PERF_GATE_RELEASE_SMOKE:-1}"
run_source_metrics="${YULANG_PERF_GATE_SOURCE_METRICS:-1}"
run_marker_runtime="${YULANG_PERF_GATE_MARKER_RUNTIME:-1}"
run_static_bench="${YULANG_PERF_GATE_STATIC_BENCH:-1}"
build_release="${YULANG_PERF_GATE_BUILD_RELEASE:-1}"

# Exit contract: 0 means all selected workloads ran and required metrics were
# captured; nonzero means command failure, timeout, missing metric, or a
# workload-reported failure.

mkdir -p "$out_dir"
: >"$summary"

log() {
    printf '%s\n' "$*" | tee -a "$summary"
}

print_command() {
    local -a cmd=("$@")
    printf '$' >>"$summary"
    printf ' %q' "${cmd[@]}" >>"$summary"
    printf '\n' >>"$summary"
}

run_with_log() {
    local label="$1"
    local duration="$2"
    shift 2

    local log_file="$out_dir/$label.log"
    local time_file="$out_dir/$label.time"

    log ""
    log "## $label"
    print_command "$@"

    if command -v /usr/bin/time >/dev/null 2>&1; then
        /usr/bin/time -p -o "$time_file" timeout "$duration" "$@" >"$log_file" 2>&1
    else
        timeout "$duration" "$@" >"$log_file" 2>&1
    fi

    append_metrics "$label" "$log_file" "$time_file"
}

append_metrics() {
    local label="$1"
    local log_file="$2"
    local time_file="$3"

    {
        printf '\n### %s metrics\n' "$label"
        if [[ -s "$time_file" ]]; then
            sed 's/^/wall./' "$time_file"
        fi
        rg \
            '^(files:|summary:|[[:space:]]+(load\.(cst_parse|rowan_nodes|rowan_tokens)|infer|constraint\.(drain|drains|replay_[A-Za-z0-9_]*|max_replay_[A-Za-z0-9_]*|lower_replay_[A-Za-z0-9_]*|upper_replay_[A-Za-z0-9_]*|var_var_direct_[A-Za-z0-9_]*)|analysis\.(quantify_generalize|generalize_[A-Za-z0-9_]*|quantify|work|route|instantiate)|run\.(cache|runtime_execute|runtime_evidence\.active_add_id_(path_prefix_checks|scans)|request_resume_steps|continuation_[A-Za-z0-9_]*cloned|continuation_capture_clones|continuation_invoke_clones|effect_requests|catch_matches|continuations|frame_allocs)|total):)' \
            "$log_file" || true
    } >>"$summary"
}

metric_value() {
    local label="$1"
    local key="$2"
    local log_file="$out_dir/$label.log"
    if [[ ! -s "$log_file" ]]; then
        printf 'n/a'
        return
    fi
    awk -v key="$key:" '$1 == key { print $2; found = 1; exit } END { if (!found) print "n/a" }' "$log_file"
}

metric_values() {
    local label="$1"
    local key="$2"
    local log_file="$out_dir/$label.log"
    if [[ ! -s "$log_file" ]]; then
        printf 'n/a'
        return
    fi
    awk -v key="$key:" '
        $1 == key {
            if (found) {
                printf ","
            }
            printf "%s", $2
            found = 1
        }
        END {
            if (found) {
                printf "\n"
            } else {
                print "n/a"
            }
        }
    ' "$log_file"
}

wall_value() {
    local label="$1"
    local time_file="$out_dir/$label.time"
    if [[ ! -s "$time_file" ]]; then
        printf 'n/a'
        return
    fi
    awk '$1 == "real" { print $2; found = 1; exit } END { if (!found) print "n/a" }' "$time_file"
}

append_key_metrics_row() {
    local label="$1"
    local route_kind="${2:-single}"
    local route
    local runtime
    if [[ "$route_kind" == "multi" ]]; then
        route="$(metric_values "$label" "run.cache")"
        runtime="$(metric_values "$label" "run.runtime_execute")"
    else
        route="$(metric_value "$label" "run.cache")"
        runtime="$(metric_value "$label" "run.runtime_execute")"
    fi

    printf '| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n' \
        "$label" \
        "$(wall_value "$label")" \
        "$route" \
        "$(metric_value "$label" "infer")" \
        "$(metric_value "$label" "constraint.drain")" \
        "$(metric_value "$label" "constraint.epoch")" \
        "$(metric_value "$label" "constraint.replay_accepted")" \
        "$(metric_value "$label" "constraint.replay_duplicate")" \
        "$(metric_value "$label" "analysis.generalize_top_restart_root")" \
        "$(metric_value "$label" "analysis.generalize_top_restart_total_restarts")" \
        "$(metric_value "$label" "analysis.generalize_top_restart_constraint_epoch_delta")" \
        "$(metric_value "$label" "analysis.generalize_top_restart_role_epoch_delta")" \
        "$(metric_value "$label" "analysis.generalize_dominance_interval_inputs")" \
        "$(metric_value "$label" "analysis.generalize_dominance_polarity_occurrences")" \
        "$runtime" \
        "$(metric_value "$label" "run.runtime_evidence.active_add_id_path_prefix_checks")" \
        "$(metric_value "$label" "run.runtime_evidence.active_add_id_scans")" \
        "$(metric_value "$label" "load.cst_parse")" \
        "$(metric_value "$label" "load.rowan_nodes")" \
        "$(metric_value "$label" "load.rowan_tokens")"
}

append_key_metrics() {
    local key_metrics="$out_dir/key-metrics.md"
    {
        printf '\n## Key metrics\n\n'
        # Control VM's marker_scope_frame_touches counted continuation frames crossed while
        # consuming a separate marker-scope stack. Evidence VM scopes marker frames lexically,
        # so marker_frame_entries measures a different event and must not replace that column.
        printf '| workload | wall(s) | cache route | infer | constraint.drain | constraint epoch | replay accepted | replay duplicate | top restart root | top restarts | top epoch delta | top role delta | dom intervals | dom polarity occ | runtime execute | path prefix checks | active scans | load.cst_parse | load.rowan_nodes | load.rowan_tokens |\n'
        printf '| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n'
        append_key_metrics_row showcase-check-poly-std
        append_key_metrics_row nondet-no-cache
        append_key_metrics_row showcase-no-cache
        append_key_metrics_row yumark-html-no-cache
        append_key_metrics_row nondet-cache-warmup
        append_key_metrics_row nondet-cache-hit
        append_key_metrics_row yumark-html-cache-boundary
        append_key_metrics_row yumark-markdown-cache-boundary
        append_key_metrics_row marker-heavy-cache-hit
        append_key_metrics_row source-unit-cache-smoke multi
    } >"$key_metrics"
    cat "$key_metrics" | tee -a "$summary"
}

scan_workload_failures() {
    local log_dir="$1"
    local failed=0
    local log_file

    while IFS= read -r log_file; do
        local matches
        if matches="$(rg -n '(^|[[:space:]])FAILED([[:space:]]|$)' "$log_file")"; then
            local workload="${log_file#$log_dir/}"
            workload="${workload%.log}"
            echo "performance gate: workload reported failure: $workload ($log_file)" >&2
            printf '%s\n' "$matches" >&2
            failed=1
        fi
    done < <(find "$log_dir" -type f -name '*.log' | sort)

    if [[ "$failed" != "0" ]]; then
        return 1
    fi
}

key_metric_value() {
    local key_metrics="$1"
    local workload="$2"
    local field="$3"

    awk -F '|' -v workload="$workload" -v field="$field" '
        function trim(value) {
            gsub(/^[[:space:]]+|[[:space:]]+$/, "", value)
            return value
        }
        trim($2) == workload {
            print trim($field)
            found = 1
            exit
        }
        END {
            if (!found) {
                exit 1
            }
        }
    ' "$key_metrics"
}

require_key_metric() {
    local key_metrics="$1"
    local workload="$2"
    local field="$3"
    local metric="$4"
    local value

    if ! value="$(key_metric_value "$key_metrics" "$workload" "$field")"; then
        echo "performance gate: missing key metrics row: $workload ($key_metrics)" >&2
        return 1
    fi
    if [[ -z "$value" || "$value" == "n/a" || "$value" == "-" ]]; then
        echo "performance gate: missing key metric: $workload $metric ($key_metrics)" >&2
        return 1
    fi
}

require_key_metric_set() {
    local key_metrics="$1"
    local workload="$2"
    shift 2
    local missing=0

    while (($# > 0)); do
        require_key_metric "$key_metrics" "$workload" "$1" "$2" || missing=1
        shift 2
    done

    if [[ "$missing" != "0" ]]; then
        return 1
    fi
}

check_slowdown_ratio() {
    local label="$1"
    local baseline="$2"
    local candidate="$3"
    local maximum="$4"

    if ! awk -v baseline="$baseline" -v candidate="$candidate" -v maximum="$maximum" '
        BEGIN {
            if (baseline !~ /^[0-9]+([.][0-9]+)?$/ || baseline <= 0 ||
                candidate !~ /^[0-9]+([.][0-9]+)?$/ || candidate < 0 ||
                maximum !~ /^[0-9]+([.][0-9]+)?$/ || maximum <= 0) {
                exit 2
            }
            exit candidate <= baseline * maximum ? 0 : 1
        }
    '; then
        echo "performance gate: $label slowdown ${candidate}s / ${baseline}s exceeds ${maximum}x" >&2
        return 1
    fi
}

validate_std_prefix_boundary_slowdown() {
    local key_metrics="$1"
    local baseline
    local candidate

    baseline="$(key_metric_value "$key_metrics" yumark-html-no-cache 3)"
    candidate="$(key_metric_value "$key_metrics" yumark-html-cache-boundary 3)"
    check_slowdown_ratio \
        "std-prefix HTML cache boundary" \
        "$baseline" \
        "$candidate" \
        "$std_prefix_boundary_max_slowdown"
    log "std-prefix HTML slowdown: ${candidate}s / ${baseline}s (limit ${std_prefix_boundary_max_slowdown}x)"
}

validate_key_metrics() {
    local key_metrics="$1"
    local missing=0

    if [[ ! -s "$key_metrics" ]]; then
        echo "performance gate: missing key metrics file: $key_metrics" >&2
        return 1
    fi

    if [[ "$run_source_metrics" != "0" ]]; then
        require_key_metric_set "$key_metrics" showcase-check-poly-std \
            3 "wall(s)" \
            5 "infer" \
            6 "constraint.drain" \
            8 "replay accepted" \
            9 "replay duplicate" \
            19 "load.cst_parse" \
            20 "load.rowan_nodes" \
            21 "load.rowan_tokens" || missing=1
        require_key_metric_set "$key_metrics" nondet-no-cache \
            3 "wall(s)" \
            16 "runtime execute" \
            17 "path prefix checks" \
            18 "active scans" || missing=1
        require_key_metric_set "$key_metrics" showcase-no-cache \
            3 "wall(s)" \
            16 "runtime execute" \
            17 "path prefix checks" \
            18 "active scans" || missing=1
        require_key_metric_set "$key_metrics" yumark-html-no-cache \
            3 "wall(s)" \
            4 "cache route" \
            16 "runtime execute" || missing=1
        require_key_metric_set "$key_metrics" nondet-cache-warmup \
            3 "wall(s)" \
            4 "cache route" \
            16 "runtime execute" || missing=1
        require_key_metric_set "$key_metrics" nondet-cache-hit \
            3 "wall(s)" \
            4 "cache route" \
            16 "runtime execute" || missing=1
        require_key_metric_set "$key_metrics" yumark-html-cache-boundary \
            3 "wall(s)" \
            4 "cache route" \
            16 "runtime execute" || missing=1
        require_key_metric_set "$key_metrics" yumark-markdown-cache-boundary \
            3 "wall(s)" \
            4 "cache route" \
            16 "runtime execute" || missing=1
        require_key_metric_set "$key_metrics" source-unit-cache-smoke \
            3 "wall(s)" \
            4 "cache route" \
            16 "runtime execute" || missing=1
    fi

    if [[ "$run_marker_runtime" != "0" ]]; then
        require_key_metric_set "$key_metrics" marker-heavy-cache-hit \
            3 "wall(s)" \
            4 "cache route" \
            16 "runtime execute" \
            17 "path prefix checks" \
            18 "active scans" || missing=1
    fi

    if [[ "$missing" != "0" ]]; then
        return 1
    fi
}

ensure_release_binary() {
    if [[ "$bin" == "$default_bin" ]]; then
        if [[ "$build_release" != "0" || ! -x "$bin" ]]; then
            log "building release yulang"
            run_with_log build-release "$test_timeout" cargo build -q -p yulang --release
        fi
        return
    fi
    if [[ ! -x "$bin" ]]; then
        echo "performance gate: executable yulang binary not found: $bin" >&2
        exit 1
    fi
}

run_hardening_smoke() {
    local -a env_cmd=(
        env
        "YULANG=$bin"
        "YULANG_HARDENING_TEST_TIMEOUT=$test_timeout"
        "YULANG_HARDENING_SMOKE_TIMEOUT=$run_timeout"
        "YULANG_HARDENING_PUBLIC_EXAMPLES=${YULANG_PERF_GATE_PUBLIC_EXAMPLES:-0}"
        "YULANG_HARDENING_EVIDENCE_PUBLIC_EXAMPLES=${YULANG_PERF_GATE_EVIDENCE_PUBLIC_EXAMPLES:-0}"
        "YULANG_HARDENING_REPLAY_COMPARE=${YULANG_PERF_GATE_REPLAY_COMPARE:-0}"
        "YULANG_HARDENING_REPLAY_PUBLIC_DIFF=${YULANG_PERF_GATE_REPLAY_PUBLIC_DIFF:-0}"
        "YULANG_HARDENING_EVIDENCE_SMOKE=${YULANG_PERF_GATE_EVIDENCE_SMOKE:-0}"
        "YULANG_HARDENING_RELEASE_SMOKE=${YULANG_PERF_GATE_EMBED_RELEASE_SMOKE:-0}"
        "YULANG_HARDENING_DOCS_BUILD=${YULANG_PERF_GATE_DOCS_BUILD:-0}"
        "$repo_root/scripts/hardening-smoke.sh"
    )
    run_with_log hardening-smoke "$run_timeout" "${env_cmd[@]}"
}

run_adversarial_corpus() {
    local log_dir="$out_dir/adversarial-logs"
    local -a env_cmd=(
        env
        "YULANG=$bin"
        "TIMEOUT=$adversarial_timeout"
        "LOG_DIR=$log_dir"
        "$repo_root/tests/yulang/yulang-adversarial-corpus/probe.sh"
    )
    run_with_log adversarial-corpus "$run_timeout" "${env_cmd[@]}"
}

run_release_runtime_smoke() {
    run_with_log release-smoke "$run_timeout" "$repo_root/scripts/release-smoke.sh" "$bin"
}

run_source_metric_commands() {
    run_with_log showcase-check-poly-std "$run_timeout" \
        "$bin" --std-root "$std_root" check-poly-std "$repo_root/examples/showcase.yu"

    run_with_log nondet-no-cache "$run_timeout" \
        "$bin" --std-root "$std_root" --runtime-phase-timings --no-cache run --print-roots \
        "$repo_root/bench/nondet_20_discard.yu"

    run_with_log showcase-no-cache "$run_timeout" \
        "$bin" --std-root "$std_root" --runtime-phase-timings --no-cache run --print-roots \
        "$repo_root/examples/showcase.yu"

    run_with_log yumark-html-no-cache "$run_timeout" \
        "$bin" --std-root "$std_root" --runtime-phase-timings --no-cache run --print-roots \
        "$repo_root/tests/yulang/regressions/cache/std_prefix_yumark_html_fallback.yu"

    local cache_dir="$out_dir/cache"
    mkdir -p "$cache_dir"

    run_with_log nondet-cache-warmup "$run_timeout" \
        env "YULANG_CACHE_DIR=$cache_dir" \
        "$bin" --std-root "$std_root" --runtime-phase-timings run --print-roots \
        "$repo_root/bench/nondet_20_discard.yu"

    run_with_log nondet-cache-hit "$run_timeout" \
        env "YULANG_CACHE_DIR=$cache_dir" \
        "$bin" --std-root "$std_root" --runtime-phase-timings run --print-roots \
        "$repo_root/bench/nondet_20_discard.yu"

    run_with_log yumark-html-cache-boundary "$run_timeout" \
        env "YULANG_CACHE_DIR=$cache_dir" \
        "$bin" --std-root "$std_root" --runtime-phase-timings run --print-roots \
        "$repo_root/tests/yulang/regressions/cache/std_prefix_yumark_html_fallback.yu"

    run_with_log yumark-markdown-cache-boundary "$run_timeout" \
        env "YULANG_CACHE_DIR=$cache_dir" \
        "$bin" --std-root "$std_root" --runtime-phase-timings run --print-roots \
        "$repo_root/tests/yulang/regressions/cache/std_prefix_yumark_markdown_workload.yu"

    run_with_log source-unit-cache-smoke "$run_timeout" \
        "$repo_root/scripts/source-unit-cache-smoke.sh" "$bin"
}

write_marker_heavy_workload() {
    local path="$1"
    {
        printf 'use std::control::nondet::*\n\n'
        local iteration
        for ((iteration = 1; iteration <= 100; iteration++)); do
            printf '{\n'
            printf '    my xs = (each 1..20 + each 1..20).list\n'
            printf '    ()\n'
            printf '}\n\n'
        done
    } >"$path"
}

run_marker_heavy_runtime() {
    local case_path="$out_dir/nondet-100.yu"
    local cache_dir="$out_dir/marker-cache"
    write_marker_heavy_workload "$case_path"
    mkdir -p "$cache_dir"

    run_with_log marker-heavy-cache-warmup "$run_timeout" \
        env "YULANG_CACHE_DIR=$cache_dir" \
        "$bin" --std-root "$std_root" --runtime-phase-timings run --print-roots \
        "$case_path"

    run_with_log marker-heavy-cache-hit "$run_timeout" \
        env "YULANG_CACHE_DIR=$cache_dir" \
        "$bin" --std-root "$std_root" --runtime-phase-timings run --print-roots \
        "$case_path"
}

run_static_analysis_bench() {
    run_with_log static-analysis-bench "$bench_timeout" \
        env "YULANG=$bin" \
        "$repo_root/bench/static_analysis_bench.sh" --repeat "$repeat" \
        "$repo_root/examples/showcase.yu" \
        "$repo_root/bench/nondet_20_discard.yu"
}

main() {
    log "performance gate output: $out_dir"
    log "binary: $bin"
    log "std root: $std_root"
    log "repeat: $repeat"
    log "std-prefix boundary slowdown limit: ${std_prefix_boundary_max_slowdown}x"

    ensure_release_binary

    if [[ "$run_hardening" != "0" ]]; then
        run_hardening_smoke
    fi
    if [[ "$run_adversarial" != "0" ]]; then
        run_adversarial_corpus
    fi
    if [[ "$run_release_smoke" != "0" ]]; then
        run_release_runtime_smoke
    fi
    if [[ "$run_source_metrics" != "0" ]]; then
        run_source_metric_commands
    fi
    if [[ "$run_marker_runtime" != "0" ]]; then
        run_marker_heavy_runtime
    fi
    if [[ "$run_static_bench" != "0" ]]; then
        run_static_analysis_bench
    fi

    append_key_metrics
    scan_workload_failures "$out_dir"
    validate_key_metrics "$out_dir/key-metrics.md"
    if [[ "$run_source_metrics" != "0" ]]; then
        validate_std_prefix_boundary_slowdown "$out_dir/key-metrics.md"
    fi

    log ""
    log "performance gate ok"
    log "summary: $summary"
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
    main "$@"
fi
