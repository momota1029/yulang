#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch="$(mktemp -d)"

cleanup() {
  rm -rf "$scratch"
}
trap cleanup EXIT

source_perf_gate() {
  YULANG_PERF_GATE_OUTPUT_DIR="$scratch/performance-gate-source" \
    source "$repo_root/scripts/performance-gate.sh"
}

assert_success() {
  local label="$1"
  shift
  if ! "$@"; then
    echo "not ok - $label" >&2
    exit 1
  fi
  echo "ok - $label"
}

assert_failure() {
  local label="$1"
  shift
  if "$@"; then
    echo "not ok - $label unexpectedly succeeded" >&2
    exit 1
  fi
  echo "ok - $label"
}

write_key_metrics() {
  local path="$1"
  local nondet_runtime="$2"
  cat >"$path" <<EOF
## Key metrics

| workload | wall(s) | cache route | infer | constraint.drain | constraint epoch | replay accepted | replay duplicate | top restart root | top restarts | top epoch delta | top role delta | dom intervals | dom polarity occ | runtime execute | marker touches | path prefix checks | active scans |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| showcase-check-poly-std | 0.10 | n/a | 1ms | 2ms | n/a | 3 | 4 | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a |
| nondet-no-cache | 0.20 | disabled | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | $nondet_runtime | 5 | 6 | 7 |
| showcase-no-cache | 0.30 | disabled | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 8ms | 9 | 10 | 11 |
| nondet-cache-warmup | 0.40 | control-hit | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 12ms | n/a | n/a | n/a |
| nondet-cache-hit | 0.50 | control-hit | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 13ms | n/a | n/a | n/a |
| marker-heavy-cache-hit | 0.60 | control-hit | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 14ms | 15 | 16 | 17 |
| source-unit-cache-smoke | 0.70 | merged-source-unit-prefix-hit,source-unit-prefix-hit | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a | 18us,19us | n/a | n/a | n/a |
EOF
}

source_perf_gate

log_dir="$scratch/logs"
mkdir -p "$log_dir"
printf 'case iter check\nbench/nondet 1 ok\n' >"$log_dir/static-analysis-bench.log"
assert_success "scan_workload_failures accepts clean logs" scan_workload_failures "$log_dir"

printf 'case iter check\nbench/nondet 1 FAILED -\n' >"$log_dir/static-analysis-bench.log"
failure_err="$scratch/failure.err"
scan_failed_fixture() {
  scan_workload_failures "$log_dir" 2>"$failure_err"
}
assert_failure "scan_workload_failures rejects FAILED rows" \
  scan_failed_fixture
rg -q 'static-analysis-bench' "$failure_err"
rg -q 'FAILED' "$failure_err"

key_metrics="$scratch/key-metrics.md"
write_key_metrics "$key_metrics" "20ms"
assert_success "validate_key_metrics accepts required rows" validate_key_metrics "$key_metrics"

write_key_metrics "$key_metrics" "n/a"
metrics_err="$scratch/metrics.err"
missing_metrics_fixture() {
  validate_key_metrics "$key_metrics" 2>"$metrics_err"
}
assert_failure "validate_key_metrics rejects missing required cells" \
  missing_metrics_fixture
rg -q 'nondet-no-cache runtime execute' "$metrics_err"
