#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${YULANG:-"$repo_root/target/release/yulang"}"
test_timeout="${YULANG_HARDENING_TEST_TIMEOUT:-240s}"
smoke_timeout="${YULANG_HARDENING_SMOKE_TIMEOUT:-360s}"
run_public_examples="${YULANG_HARDENING_PUBLIC_EXAMPLES:-1}"
run_evidence_public_examples="${YULANG_HARDENING_EVIDENCE_PUBLIC_EXAMPLES:-1}"
run_replay_compare="${YULANG_HARDENING_REPLAY_COMPARE:-1}"
run_replay_public_diff="${YULANG_HARDENING_REPLAY_PUBLIC_DIFF:-1}"
run_evidence_smoke="${YULANG_HARDENING_EVIDENCE_SMOKE:-1}"
run_release_smoke="${YULANG_HARDENING_RELEASE_SMOKE:-1}"
run_source_unit_cache_smoke="${YULANG_HARDENING_SOURCE_UNIT_CACHE_SMOKE:-1}"
run_docs_build="${YULANG_HARDENING_DOCS_BUILD:-0}"
evidence_skip_limit="${YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT:-16}"

run_timeout() {
  local duration="$1"
  shift
  printf '\n$'
  printf ' %q' timeout "$duration" "$@"
  printf '\n'
  timeout "$duration" "$@"
}

if [[ ! -x "$bin" ]]; then
  run_timeout "$test_timeout" cargo build -q -p yulang --release
fi

if [[ ! -x "$bin" ]]; then
  echo "hardening smoke: executable yulang binary not found: $bin" >&2
  exit 1
fi

run_timeout "$test_timeout" \
  cargo test -q -p infer unannotated_compose_protects_callback_return_from_outer_callee \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang public \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang cache::tests::compiled_unit_artifact_merge \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang --test cli source_unit_prefix \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang check_poly_std_reports_summary_and_type_errors_without_dumping_defs \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang run_control_source_text_with_embedded_std_runs_junction_tour_example \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang run_control_source_text_with_embedded_std_choice_recovers_from_parse_fail \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang run_control_source_text_with_embedded_std_keeps_repeated_callback_hygiene \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang run_control_source_text_with_embedded_playground_std_runs_list_update_example \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p yulang run_control_source_text_with_embedded_playground_std_runs_nondet_once_range \
  -- --test-threads=1

run_timeout "$test_timeout" \
  cargo test -q -p control-vm routes_foreign_thunk_effect_past_inner_handler_like_oracle \
  -- --test-threads=1

if [[ "$run_public_examples" != "0" ]]; then
  run_timeout "$smoke_timeout" "$repo_root/scripts/public-example-smoke.sh" "$bin"
fi

if [[ "$run_evidence_public_examples" != "0" ]]; then
  run_timeout "$smoke_timeout" \
    env YULANG_REPLAY_EVIDENCE_ONLY_SKIP=1 \
      YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT="$evidence_skip_limit" \
      "$repo_root/scripts/public-example-smoke.sh" "$bin"
fi

if [[ "$run_release_smoke" != "0" ]]; then
  run_timeout "$smoke_timeout" "$repo_root/scripts/release-smoke.sh" "$bin"
fi

if [[ "$run_source_unit_cache_smoke" != "0" ]]; then
  run_timeout "$smoke_timeout" "$repo_root/scripts/source-unit-cache-smoke.sh" "$bin"
fi

if [[ "$run_replay_compare" != "0" ]]; then
  run_timeout "$smoke_timeout" \
    env YULANG="$bin" "$repo_root/scripts/replay-skip-compare.sh"
fi

if [[ "$run_replay_public_diff" != "0" ]]; then
  run_timeout "$smoke_timeout" \
    env YULANG="$bin" "$repo_root/scripts/replay-skip-public-diff.sh"
fi

if [[ "$run_evidence_smoke" != "0" ]]; then
  run_timeout "$smoke_timeout" \
    env YULANG="$bin" "$repo_root/scripts/evidence-only-replay-smoke.sh"
fi

if [[ "$run_docs_build" != "0" ]]; then
  run_timeout "$smoke_timeout" npm --prefix "$repo_root/web/docs" run build
fi

printf '\nhardening smoke ok: %s\n' "$bin"
