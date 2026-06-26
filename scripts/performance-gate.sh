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

run_hardening="${YULANG_PERF_GATE_HARDENING:-1}"
run_adversarial="${YULANG_PERF_GATE_ADVERSARIAL:-1}"
run_release_smoke="${YULANG_PERF_GATE_RELEASE_SMOKE:-1}"
run_source_metrics="${YULANG_PERF_GATE_SOURCE_METRICS:-1}"
run_marker_runtime="${YULANG_PERF_GATE_MARKER_RUNTIME:-1}"
run_static_bench="${YULANG_PERF_GATE_STATIC_BENCH:-1}"
build_release="${YULANG_PERF_GATE_BUILD_RELEASE:-1}"

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
            '^(files:|summary:|[[:space:]]+(infer|constraint\.(drain|drains|replay_[A-Za-z0-9_]*|max_replay_[A-Za-z0-9_]*|lower_replay_[A-Za-z0-9_]*|upper_replay_[A-Za-z0-9_]*|var_var_direct_[A-Za-z0-9_]*)|analysis\.(quantify_generalize|generalize_[A-Za-z0-9_]*|quantify|work|route|instantiate)|run\.(cache|runtime_execute|active_add_scans|path_prefix_checks|request_resume_steps|marker_scope_[A-Za-z0-9_]*|continuation_[A-Za-z0-9_]*cloned|continuation_capture_clones|continuation_invoke_clones|effect_requests|catch_matches|continuations|frame_allocs)|total):)' \
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

    printf '| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n' \
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
        "$(metric_value "$label" "run.marker_scope_frame_touches")" \
        "$(metric_value "$label" "run.path_prefix_checks")" \
        "$(metric_value "$label" "run.active_add_scans")"
}

append_key_metrics() {
    local key_metrics="$out_dir/key-metrics.md"
    {
        printf '\n## Key metrics\n\n'
        printf '| workload | wall(s) | cache route | infer | constraint.drain | constraint epoch | replay accepted | replay duplicate | top restart root | top restarts | top epoch delta | top role delta | dom intervals | dom polarity occ | runtime execute | marker touches | path prefix checks | active scans |\n'
        printf '| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n'
        append_key_metrics_row showcase-check-poly-std
        append_key_metrics_row nondet-no-cache
        append_key_metrics_row showcase-no-cache
        append_key_metrics_row nondet-cache-warmup
        append_key_metrics_row nondet-cache-hit
        append_key_metrics_row marker-heavy-cache-hit
        append_key_metrics_row source-unit-cache-smoke multi
    } >"$key_metrics"
    cat "$key_metrics" | tee -a "$summary"
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

    log ""
    log "performance gate ok"
    log "summary: $summary"
}

main "$@"
