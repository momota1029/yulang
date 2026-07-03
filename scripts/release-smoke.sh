#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${1:-"$repo_root/target/debug/yulang"}"
timeout_duration="${YULANG_SMOKE_TIMEOUT:-30s}"
contract_smoke="${YULANG_SMOKE_CONTRACTS:-${YULANG_SMOKE_FILE_RESOURCE_CONTRACT:-1}}"
contract_timeout_duration="${YULANG_SMOKE_CONTRACT_TIMEOUT:-${YULANG_SMOKE_FILE_RESOURCE_TIMEOUT:-180s}}"

if [[ ! -x "$bin" ]]; then
  echo "release smoke: executable yulang binary not found: $bin" >&2
  echo "build one first, for example: cargo build -p yulang" >&2
  exit 1
fi

tmp="$(mktemp -d)"
cleanup() {
  rm -rf "$tmp"
}
trap cleanup EXIT

export HOME="$tmp/home"
export XDG_CACHE_HOME="$tmp/xdg-cache"
export YULANG_CACHE_DIR="$tmp/yulang-cache"
mkdir -p "$HOME" "$XDG_CACHE_HOME" "$YULANG_CACHE_DIR"

std_root="$tmp/lib/std"
main="$tmp/main.yu"
ref_loop="$tmp/ref-loop.yu"

run_with_timeout() {
  local duration="$1"
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout "$duration" "$@"
  else
    "$@"
  fi
}

run() {
  run_with_timeout "$timeout_duration" "$@"
}

path_for_compare() {
  if command -v cygpath >/dev/null 2>&1; then
    cygpath -m "$1"
  else
    printf '%s\n' "$1"
  fi
}

cat >"$main" <<'YULANG'
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once.show
YULANG

cat >"$ref_loop" <<'YULANG'
{
    my $x = 0
    for i in 0..:
        if i == 100: last
        &x = $x + 1
    $x
}
YULANG

run "$bin" --std-root "$std_root" install std >/dev/null 2>&1
test -f "$std_root/std.yu"

run "$bin" --std-root "$std_root" check "$main" >/dev/null
run_output="$(run "$bin" --std-root "$std_root" run --print-roots "$main")"
case "$run_output" in
  *'"just (3, 4, 5)"'*) ;;
  *)
    echo "release smoke: unexpected run output" >&2
    echo "$run_output" >&2
    exit 1
    ;;
esac

ref_loop_output="$(run "$bin" --std-root "$std_root" --no-cache run --print-roots "$ref_loop")"
if [[ "$ref_loop_output" != "run roots [100]" ]]; then
  echo "release smoke: unexpected ref loop output" >&2
  echo "$ref_loop_output" >&2
  exit 1
fi

host_manifest_output="$(run "$bin" --std-root "$std_root" debug host-act-manifest)"
expected_console_manifest='act=std.io.console.out op=write tier=sync path=std.io.console.out.write'
expected_file_manifest='act=std.io.file.file op=meta tier=sync path=std.io.file.file.meta'
expected_file_ambient_manifest='act=std.io.file.file op=ambient_touch tier=sync path=std.io.file.file.ambient_touch'
expected_clock_manifest='act=std.time.clock op=now tier=sync path=std.time.clock.now sig=() -> [std::time::clock] std::time::instant surface=contract column=9'
expected_file_range_raw_surface='act=std.io.file.file op=read_at tier=sync path=std.io.file.file.read_at sig=(std::text::path::path, std::data::range::range) -> [std::io::file::file] std::data::result::result (std::text::str::str, std::data::range::range) std::io::file::io_err surface=raw-compat column=6'
expected_suspend_multi_tier='tier=suspend-multi-shot'
if [[ "$host_manifest_output" != *"$expected_console_manifest"* ||
  "$host_manifest_output" != *"$expected_file_manifest"* ||
  "$host_manifest_output" != *"$expected_file_ambient_manifest"* ||
  "$host_manifest_output" != *"$expected_clock_manifest"* ||
  "$host_manifest_output" != *"$expected_file_range_raw_surface"* ||
  "$host_manifest_output" != *"$expected_suspend_multi_tier"* ]]; then
  echo "release smoke: unexpected host act manifest output" >&2
  echo "$host_manifest_output" >&2
  exit 1
fi

if [[ "$contract_smoke" != "0" ]]; then
  contract_cases_manifest="$repo_root/tests/yulang/cases.toml"
  if [[ ! -f "$contract_cases_manifest" ]]; then
    echo "release smoke: contract manifest not found: $contract_cases_manifest" >&2
    exit 1
  fi
  file_resource_cases=(
    file_text_with_commit
    file_text_with_rollback_on_error
    file_text_with_undet_last_write_wins
    file_text_unscoped_handler_discharge
    file_text_mock_matches_native_shape
    file_text_with_nested_cross_file
    file_native_protocol_load_store_meta
    file_native_protocol_typed_failures
    file_native_helper_typed_failures
    file_native_invalid_path_typed_failure
    file_native_meta_file
    file_native_meta_missing
    file_native_meta_directory
    file_text_with_native_commit
    file_text_with_native_rollback_on_error
    file_text_with_native_undet_last_write_wins
    file_text_with_native_nested_cross_file
    file_text_with_native_nested_state_var
    file_unsupported_host
    file_meta_unsupported_host
    file_read_text_unsupported_host
    file_write_text_unsupported_host
    file_text_unsupported_host
    file_text_native_missing_typed_io_err
    file_ambient_get_untouched_missing_host_io_error
    file_ambient_set_untouched_missing_host_io_error
    file_text_mock_ambient_typed_not_found
  )
  file_resource_case_args=()
  for case_name in "${file_resource_cases[@]}"; do
    file_resource_case_args+=(--case "$case_name")
  done
  file_resource_output="$(run_with_timeout "$contract_timeout_duration" \
    "$bin" --std-root "$std_root" contract \
    --contract file-resource \
    "${file_resource_case_args[@]}" \
    "$contract_cases_manifest")"
  expected_file_resource_output="contract cases ok: ${#file_resource_cases[@]}"
  if [[ "$file_resource_output" != "$expected_file_resource_output" ]]; then
    echo "release smoke: unexpected file-resource contract output" >&2
    echo "$file_resource_output" >&2
    exit 1
  fi

  lambda_my_cases=(
    lambda_my_binder_state_protocol
    file_text_with_commit_lambda_my
  )
  lambda_my_case_args=()
  for case_name in "${lambda_my_cases[@]}"; do
    lambda_my_case_args+=(--case "$case_name")
  done
  lambda_my_output="$(run_with_timeout "$contract_timeout_duration" \
    "$bin" --std-root "$std_root" contract \
    "${lambda_my_case_args[@]}" \
    "$contract_cases_manifest")"
  expected_lambda_my_output="contract cases ok: ${#lambda_my_cases[@]}"
  if [[ "$lambda_my_output" != "$expected_lambda_my_output" ]]; then
    echo "release smoke: unexpected lambda-my contract output" >&2
    echo "$lambda_my_output" >&2
    exit 1
  fi

  host_act_cases=(
    console_unsupported_host
    console_mock_out_handler
    std_console_out_write_public_signature
  )
  host_act_case_args=()
  for case_name in "${host_act_cases[@]}"; do
    host_act_case_args+=(--case "$case_name")
  done
  host_act_output="$(run_with_timeout "$contract_timeout_duration" \
    "$bin" --std-root "$std_root" contract \
    --contract host-act \
    "${host_act_case_args[@]}" \
    "$contract_cases_manifest")"
  expected_host_act_output="contract cases ok: ${#host_act_cases[@]}"
  if [[ "$host_act_output" != "$expected_host_act_output" ]]; then
    echo "release smoke: unexpected host-act contract output" >&2
    echo "$host_act_output" >&2
    exit 1
  fi

  time_cases=(
    instant_duration_core
    instant_duration_debug
    instant_display_rfc3339
    duration_units
    clock_now_native
    clock_now_unsupported_host
    clock_mock_now_handler
    std_time_clock_now_public_signature
    std_time_instant_add_public_signature
    std_time_instant_sub_public_signature
    std_time_nanos_public_signature
    std_time_micros_public_signature
    std_time_millis_public_signature
    std_time_secs_public_signature
    std_time_mins_public_signature
    std_time_hours_public_signature
    std_time_days_public_signature
    std_time_duration_add_public_signature
    std_time_duration_sub_public_signature
  )
  time_case_args=()
  for case_name in "${time_cases[@]}"; do
    time_case_args+=(--case "$case_name")
  done
  time_output="$(run_with_timeout "$contract_timeout_duration" \
    "$bin" --std-root "$std_root" contract \
    --contract time \
    "${time_case_args[@]}" \
    "$contract_cases_manifest")"
  expected_time_output="contract cases ok: ${#time_cases[@]}"
  if [[ "$time_output" != "$expected_time_output" ]]; then
    echo "release smoke: unexpected time contract output" >&2
    echo "$time_output" >&2
    exit 1
  fi
fi

cache_path="$(run "$bin" cache path)"
expected_cache_path="$(path_for_compare "$YULANG_CACHE_DIR")"
actual_cache_path="$(path_for_compare "$cache_path")"
case "$actual_cache_path" in
  "$expected_cache_path") ;;
  *)
    echo "release smoke: cache path escaped isolated env" >&2
    echo "expected: $expected_cache_path" >&2
    echo "actual:   $actual_cache_path" >&2
    exit 1
    ;;
esac
run "$bin" cache clear >/dev/null

if [[ "${YULANG_SMOKE_SERVER:-0}" == "1" ]]; then
  server_timeout="${YULANG_SMOKE_SERVER_TIMEOUT:-2s}"
  set +e
  if command -v timeout >/dev/null 2>&1; then
    timeout "$server_timeout" "$bin" --std-root "$std_root" server >/dev/null 2>&1
    status=$?
  else
    "$bin" --std-root "$std_root" server >/dev/null 2>&1 &
    server_pid=$!
    sleep 2
    kill "$server_pid" >/dev/null 2>&1
    wait "$server_pid" >/dev/null 2>&1
    status=124
  fi
  set -e
  if [[ "$status" != "0" && "$status" != "124" ]]; then
    echo "release smoke: yulang server failed to start, status $status" >&2
    exit 1
  fi
fi

echo "release smoke ok: $bin"
