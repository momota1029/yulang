#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${YULANG:-"$repo_root/target/release/yulang"}"
test_timeout="${YULANG_RELEASE_GATE_TEST_TIMEOUT:-300s}"
smoke_timeout="${YULANG_RELEASE_GATE_SMOKE_TIMEOUT:-420s}"
build_timeout="${YULANG_RELEASE_GATE_BUILD_TIMEOUT:-900s}"

run_fmt="${YULANG_RELEASE_GATE_FMT:-1}"
run_core_tests="${YULANG_RELEASE_GATE_CORE_TESTS:-1}"
run_release_build="${YULANG_RELEASE_GATE_BUILD_RELEASE:-1}"
run_hardening="${YULANG_RELEASE_GATE_HARDENING:-1}"
run_docs_build="${YULANG_RELEASE_GATE_DOCS_BUILD:-1}"
run_web_build="${YULANG_RELEASE_GATE_WEB_BUILD:-0}"

run_timeout() {
  local duration="$1"
  shift
  printf '\n$'
  printf ' %q' timeout "$duration" "$@"
  printf '\n'
  timeout "$duration" "$@"
}

if [[ "$run_fmt" != "0" ]]; then
  run_timeout "$test_timeout" cargo fmt --check
fi

if [[ "$run_core_tests" != "0" ]]; then
  run_timeout "$test_timeout" \
    cargo test -q -p parser -p infer -p yulang -- --test-threads=1
fi

if [[ "$run_release_build" != "0" || ! -x "$bin" ]]; then
  run_timeout "$test_timeout" cargo build -q -p yulang --release
fi

if [[ ! -x "$bin" ]]; then
  echo "release gate: executable yulang binary not found: $bin" >&2
  exit 1
fi

if [[ "$run_hardening" != "0" ]]; then
  run_timeout "$smoke_timeout" \
    env \
      "YULANG=$bin" \
      "YULANG_HARDENING_TEST_TIMEOUT=$test_timeout" \
      "YULANG_HARDENING_SMOKE_TIMEOUT=$smoke_timeout" \
      "YULANG_HARDENING_DOCS_BUILD=$run_docs_build" \
      "$repo_root/scripts/hardening-smoke.sh"
elif [[ "$run_docs_build" != "0" ]]; then
  run_timeout "$smoke_timeout" npm --prefix "$repo_root/web/docs" run build
fi

if [[ "$run_web_build" != "0" ]]; then
  run_timeout "$build_timeout" npm --prefix "$repo_root/web" run build
fi

printf '\nrelease gate ok: %s\n' "$bin"
