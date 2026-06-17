#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${1:-"$repo_root/target/debug/yulang"}"
timeout_duration="${YULANG_EXAMPLE_SMOKE_TIMEOUT:-30s}"
std_root="$repo_root/lib"

if [[ ! -x "$bin" ]]; then
  echo "public example smoke: executable yulang binary not found: $bin" >&2
  echo "build one first, for example: cargo build -p yulang" >&2
  exit 1
fi

run() {
  if command -v timeout >/dev/null 2>&1; then
    timeout "$timeout_duration" "$@"
  else
    "$@"
  fi
}

expect_contains() {
  local label="$1"
  local haystack="$2"
  local needle="$3"
  if [[ "$haystack" != *"$needle"* ]]; then
    echo "public example smoke: unexpected output for $label" >&2
    echo "missing: $needle" >&2
    echo "$haystack" >&2
    exit 1
  fi
}

expect_run_roots() {
  local file="$1"
  local expected="$2"
  local output
  output="$(run "$bin" --std-root "$std_root" run --print-roots "$repo_root/$file")"
  expect_contains "$file" "$output" "$expected"
}

expect_run_stdout() {
  local file="$1"
  local expected="$2"
  local output
  output="$(run "$bin" --std-root "$std_root" run "$repo_root/$file")"
  if [[ "$output" != "$expected" ]]; then
    echo "public example smoke: unexpected stdout for $file" >&2
    echo "expected:" >&2
    printf '%s' "$expected" >&2
    echo "actual:" >&2
    printf '%s' "$output" >&2
    exit 1
  fi
}

expect_run_roots examples/01_struct_with.yu "run roots [25]"
expect_run_roots examples/02_refs.yu "run roots [(11, 21)]"
expect_run_roots examples/03_for_last.yu "run roots [5]"
expect_run_roots examples/04_sub_return.yu "run roots [5]"
expect_run_roots examples/05_undet_all.yu "run roots [[5, 6, 7, 6, 7, 8, 7, 8, 9]]"
expect_run_roots examples/06_undet_once.yu "(3, 4, 5)"
expect_run_roots examples/07_junction.yu "run roots [1]"
expect_run_roots examples/08_types.yu "run roots [42]"
expect_run_roots examples/09_optional_record_args.yu "run roots [6, 2, 12, 12]"
expect_run_roots examples/10_effect_handler.yu 'run roots [(9, "3\n6\n")]'
run "$bin" --std-root "$std_root" check "$repo_root/examples/11_attached_impl.yu" >/dev/null
expect_run_roots examples/12_cast.yu "run roots []"
expect_run_stdout examples/13_console.yu $'Hello, World\n3'
expect_run_roots examples/showcase.yu "run roots [25,"
expect_run_roots examples/showcase.yu "[111, 11, 101, 1, 110, 10, 100, 0]"

echo "public example smoke ok: $bin"
