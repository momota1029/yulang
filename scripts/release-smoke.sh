#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${1:-"$repo_root/target/debug/yulang"}"
timeout_duration="${YULANG_SMOKE_TIMEOUT:-30s}"

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

run() {
  if command -v timeout >/dev/null 2>&1; then
    timeout "$timeout_duration" "$@"
  else
    "$@"
  fi
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
