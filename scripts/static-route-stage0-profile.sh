#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${YULANG:-"$repo_root/target/release/yulang"}"
std_root="${YULANG_STD_ROOT:-"$repo_root/lib"}"
timeout_duration="${YULANG_STATIC_ROUTE_STAGE0_TIMEOUT:-240s}"
cache_args=()
if [[ "${YULANG_STATIC_ROUTE_STAGE0_USE_CACHE:-0}" != "1" ]]; then
  cache_args+=(--no-cache)
fi

if [[ ! -x "$bin" ]]; then
  echo "static route stage0 profile: executable yulang binary not found: $bin" >&2
  echo "build one first, for example: cargo build -q -p yulang --release" >&2
  exit 1
fi

run_timeout() {
  if command -v timeout >/dev/null 2>&1; then
    timeout "$timeout_duration" "$@"
  else
    "$@"
  fi
}

print_profile() {
  local source="$1"
  printf '## %s\n' "$source"
  run_timeout "$bin" --std-root "$std_root" "${cache_args[@]}" debug evidence-vm-run \
    --runtime-evidence-profile-deep \
    "$repo_root/$source" \
    | grep -E \
      '^(  evidence\.static_route_|  runtime_evidence\.static_route_runtime_hits_|run roots)'
  printf '\n'
}

print_profile "bench/nondet_20_discard.yu"
print_profile "examples/showcase.yu"
print_profile "examples/03_for_last.yu"
print_profile "examples/02_refs.yu"
