#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${1:-"$repo_root/target/debug/yulang"}"
timeout_duration="${YULANG_SOURCE_UNIT_CACHE_SMOKE_TIMEOUT:-30s}"

if [[ ! -x "$bin" ]]; then
  echo "source unit cache smoke: executable yulang binary not found: $bin" >&2
  echo "build one first, for example: cargo build -p yulang" >&2
  exit 1
fi

tmp="$(mktemp -d)"
cleanup() {
  rm -rf "$tmp"
}
trap cleanup EXIT

cache_root="$tmp/cache"
main="$tmp/main.yu"
a="$tmp/a.yu"
b="$tmp/b.yu"
mkdir -p "$cache_root"

run() {
  if command -v timeout >/dev/null 2>&1; then
    timeout "$timeout_duration" "$@"
  else
    "$@"
  fi
}

cat >"$main" <<'YULANG'
mod a;
mod b;
(a::x, b::y)
YULANG

cat >"$a" <<'YULANG'
pub x = 10
YULANG

cat >"$b" <<'YULANG'
pub y = 2
YULANG

first_output="$(
  YULANG_CACHE_DIR="$cache_root" \
    run "$bin" --no-prelude run --print-roots "$main"
)"
if [[ "$first_output" != "run roots [(10, 2)]" ]]; then
  echo "source unit cache smoke: unexpected warmup output" >&2
  echo "$first_output" >&2
  exit 1
fi

cat >"$main" <<'YULANG'
mod a;
mod b;
my keep v = v
keep (a::x, b::y)
YULANG

second_log="$tmp/second.stderr"
second_output="$(
  YULANG_CACHE_DIR="$cache_root" \
    run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
      2>"$second_log"
)"
if [[ "$second_output" != "run roots [(10, 2)]" ]]; then
  echo "source unit cache smoke: unexpected cached output" >&2
  echo "$second_output" >&2
  exit 1
fi

cat "$second_log"
if ! rg -q 'run\.cache: merged-source-unit-prefix-hit' "$second_log"; then
  echo "source unit cache smoke: expected merged source-unit prefix hit" >&2
  cat "$second_log" >&2
  exit 1
fi

echo "source unit cache smoke ok: $bin"
