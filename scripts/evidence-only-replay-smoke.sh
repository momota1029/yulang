#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${YULANG:-"$repo_root/target/debug/yulang"}"
std_root="$repo_root/lib"
test_timeout="${YULANG_EVIDENCE_ONLY_TEST_TIMEOUT:-240s}"
check_timeout="${YULANG_EVIDENCE_ONLY_CHECK_TIMEOUT:-240s}"
adversarial_timeout="${YULANG_EVIDENCE_ONLY_ADVERSARIAL_TIMEOUT:-360s}"
run_adversarial="${YULANG_EVIDENCE_ONLY_RUN_ADVERSARIAL:-1}"

export YULANG_REPLAY_EVIDENCE_ONLY_SKIP="${YULANG_REPLAY_EVIDENCE_ONLY_SKIP:-1}"
export YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT="${YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT:-32}"

run_timeout() {
  local duration="$1"
  shift
  printf '\n$'
  printf ' %q' timeout "$duration" "$@"
  printf '\n'
  timeout "$duration" "$@"
}

run_timeout "$test_timeout" \
  cargo test -q -p infer unannotated_compose_protects_callback_return_from_outer_callee \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang public \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang check_poly_std_reports_summary_and_type_errors_without_dumping_defs \
  -- --test-threads=1

run_timeout "$test_timeout" cargo build -q -p yulang

if [[ ! -x "$bin" ]]; then
  echo "evidence-only replay smoke: executable yulang binary not found: $bin" >&2
  exit 1
fi

metrics_log="${TMPDIR:-/tmp}/yulang-evidence-only-showcase.$$"
printf '\n$ %q %q %q --std-root %q check-poly-std %q > %q\n' \
  timeout "$check_timeout" "$bin" "$std_root" "$repo_root/examples/showcase.yu" "$metrics_log"
timeout "$check_timeout" "$bin" --std-root "$std_root" \
  check-poly-std "$repo_root/examples/showcase.yu" >"$metrics_log"
rg 'constraint\.replay_(accepted|evidence_only|duplicate|prefiltered)|constraint\.replay_weighted_routing_shadow_var_var_(frontier_graph_edges|compose_cache_hits|compose_cache_misses)|summary:' \
  "$metrics_log" || true
printf 'showcase metrics: %s\n' "$metrics_log"

if [[ "$run_adversarial" != "0" ]]; then
  export YULANG="$bin"
  export TIMEOUT="${YULANG_EVIDENCE_ONLY_ADVERSARIAL_CASE_TIMEOUT:-30s}"
  run_timeout "$adversarial_timeout" \
    "$repo_root/tests/yulang/yulang-adversarial-corpus/probe.sh"
fi

printf '\nevidence-only replay smoke ok\n'
