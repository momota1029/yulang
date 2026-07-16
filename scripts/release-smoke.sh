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
native_server="$tmp/native-server.yu"

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

cat >"$native_server" <<'YULANG'
{
    my listener = net::listen 0
    say listener.port
    my req = listener.accept()
    req.respond req.payload
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
expected_manifest_hash='compiler host manifest:
  hash='
expected_clock_manifest='act=std.time.clock op=now tier=sync path=std.time.clock.now sig=() -> [std::time::clock] std::time::instant surface=contract column=13 symbol=yu_host_3std4time5clock_3now'
expected_net_port_manifest='act=std.io.net.net op=port tier=sync path=std.io.net.net.port sig=std::io::net::listener -> [std::io::net::net] int surface=contract column=10 symbol=yu_host_3std2io3net3net_4port'
expected_server_accept_manifest='act=std.io.net.server op=accept tier=suspend-multi-shot path=std.io.net.server.accept sig=std::io::net::listener -> [std::io::net::server] std::io::net::request surface=contract column=11 symbol=yu_host_3std2io3net6server_6accept'
expected_file_range_raw_surface='act=std.io.file.file op=read_at tier=sync path=std.io.file.file.read_at sig=(std::text::path::path, std::data::range::range) -> [std::io::file::file] std::data::result::result (std::text::str::str, std::data::range::range) std::io::file::io_err surface=raw-compat column=6 symbol=yu_host_3std2io4file4file_7read_at'
expected_suspend_multi_tier='tier=suspend-multi-shot'
if [[ "$host_manifest_output" != *"$expected_manifest_hash"* ||
  "$host_manifest_output" != *"$expected_console_manifest"* ||
  "$host_manifest_output" != *"$expected_file_manifest"* ||
  "$host_manifest_output" != *"$expected_file_ambient_manifest"* ||
  "$host_manifest_output" != *"$expected_clock_manifest"* ||
  "$host_manifest_output" != *"$expected_net_port_manifest"* ||
  "$host_manifest_output" != *"$expected_server_accept_manifest"* ||
  "$host_manifest_output" != *"$expected_file_range_raw_surface"* ||
  "$host_manifest_output" != *"$expected_suspend_multi_tier"* ]]; then
  echo "release smoke: unexpected host act manifest output" >&2
  echo "$host_manifest_output" >&2
  exit 1
fi

run_native_tcp_echo_smoke() {
  if ! command -v python3 >/dev/null 2>&1; then
    echo "release smoke: python3 is required for native TCP echo smoke" >&2
    exit 1
  fi

  set +e
  python3 - <<'PY'
import errno
import socket
import sys

try:
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.bind(("127.0.0.1", 0))
except OSError as error:
    if error.errno in (errno.EPERM, errno.EACCES):
        sys.exit(2)
    print(error, file=sys.stderr)
    sys.exit(1)
finally:
    if "sock" in locals():
        sock.close()
PY
  probe_status=$?
  set -e
  if [[ "$probe_status" == "2" ]]; then
    return 0
  fi
  if [[ "$probe_status" != "0" ]]; then
    echo "release smoke: localhost TCP bind probe failed" >&2
    exit 1
  fi

  native_stderr="$tmp/native-server.stderr"
  coproc YULANG_NATIVE_TCP_SMOKE {
    "$bin" --std-root "$std_root" --no-cache run --host native "$native_server" 2>"$native_stderr"
  }
  native_server_pid="$YULANG_NATIVE_TCP_SMOKE_PID"
  if ! IFS= read -r -t 10 native_port <&"${YULANG_NATIVE_TCP_SMOKE[0]}"; then
    kill "$native_server_pid" >/dev/null 2>&1 || true
    wait "$native_server_pid" >/dev/null 2>&1 || true
    echo "release smoke: native TCP server did not print a port" >&2
    cat "$native_stderr" >&2 || true
    exit 1
  fi
  if [[ ! "$native_port" =~ ^[0-9]+$ ]]; then
    kill "$native_server_pid" >/dev/null 2>&1 || true
    wait "$native_server_pid" >/dev/null 2>&1 || true
    echo "release smoke: native TCP server printed invalid port: $native_port" >&2
    cat "$native_stderr" >&2 || true
    exit 1
  fi

  if ! native_echo_output="$(python3 - "$native_port" <<'PY'
import socket
import sys

port = int(sys.argv[1])
payload = b"release-smoke-native-echo"
with socket.create_connection(("127.0.0.1", port), timeout=10) as sock:
    sock.settimeout(10)
    sock.sendall(payload)
    sock.shutdown(socket.SHUT_WR)
    chunks = []
    while True:
        chunk = sock.recv(4096)
        if not chunk:
            break
        chunks.append(chunk)
response = b"".join(chunks)
if response != payload:
    print(f"unexpected response: {response!r}", file=sys.stderr)
    sys.exit(1)
print("native tcp echo ok")
PY
  )"; then
    kill "$native_server_pid" >/dev/null 2>&1 || true
    wait "$native_server_pid" >/dev/null 2>&1 || true
    echo "release smoke: native TCP echo client failed" >&2
    cat "$native_stderr" >&2 || true
    exit 1
  fi
  kill "$native_server_pid" >/dev/null 2>&1 || true
  wait "$native_server_pid" >/dev/null 2>&1 || true
  if [[ "$native_echo_output" != "native tcp echo ok" ]]; then
    echo "release smoke: unexpected native TCP echo output" >&2
    echo "$native_echo_output" >&2
    exit 1
  fi
}

run_native_tcp_echo_smoke

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
    file_ref_lines_each_update_chain_native
    file_ref_lines_each_update_chain_mock
    file_ref_lines_each_update_chain_unsupported_host
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

  protocol_sugar_cases=(
    do_binding_state_protocol
    lambda_my_binder_state_protocol
    file_text_with_commit_do
    file_text_with_commit_lambda_my
  )
  protocol_sugar_case_args=()
  for case_name in "${protocol_sugar_cases[@]}"; do
    protocol_sugar_case_args+=(--case "$case_name")
  done
  protocol_sugar_output="$(run_with_timeout "$contract_timeout_duration" \
    "$bin" --std-root "$std_root" contract \
    "${protocol_sugar_case_args[@]}" \
    "$contract_cases_manifest")"
  expected_protocol_sugar_output="contract cases ok: ${#protocol_sugar_cases[@]}"
  if [[ "$protocol_sugar_output" != "$expected_protocol_sugar_output" ]]; then
    echo "release smoke: unexpected protocol-sugar contract output" >&2
    echo "$protocol_sugar_output" >&2
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

  diagnostics_cases=(
    type_annotation_mismatch
    unresolved_value_name
    missing_local_binding_body
    catch_missing_arm_body
    unhandled_nondet_effect_error
  )
  diagnostics_case_args=()
  for case_name in "${diagnostics_cases[@]}"; do
    diagnostics_case_args+=(--case "$case_name")
  done
  diagnostics_output="$(run_with_timeout "$contract_timeout_duration" \
    "$bin" --std-root "$std_root" contract \
    --contract diagnostics \
    "${diagnostics_case_args[@]}" \
    "$contract_cases_manifest")"
  expected_diagnostics_output="contract cases ok: ${#diagnostics_cases[@]}"
  if [[ "$diagnostics_output" != "$expected_diagnostics_output" ]]; then
    echo "release smoke: unexpected diagnostics contract output" >&2
    echo "$diagnostics_output" >&2
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
