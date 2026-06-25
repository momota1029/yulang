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

run() {
  if command -v timeout >/dev/null 2>&1; then
    timeout "$timeout_duration" "$@"
  else
    "$@"
  fi
}

run_independent_merge_smoke() {
  case_dir="$tmp/independent"
  cache_root="$tmp/independent-cache"
  main="$case_dir/main.yu"
  a="$case_dir/a.yu"
  b="$case_dir/b.yu"
  mkdir -p "$cache_root" "$case_dir"

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
    echo "source unit cache smoke: unexpected independent warmup output" >&2
    echo "$first_output" >&2
    exit 1
  fi

  cat >"$main" <<'YULANG'
mod a;
mod b;
my keep v = v
keep (a::x, b::y)
YULANG

  second_log="$tmp/independent-second.stderr"
  second_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$second_log"
  )"
  if [[ "$second_output" != "run roots [(10, 2)]" ]]; then
    echo "source unit cache smoke: unexpected independent cached output" >&2
    echo "$second_output" >&2
    exit 1
  fi

  cat "$second_log"
  if ! rg -q 'run\.cache: merged-source-unit-prefix-hit' "$second_log"; then
    echo "source unit cache smoke: expected merged source-unit prefix hit" >&2
    cat "$second_log" >&2
    exit 1
  fi

  rm -rf "$cache_root/artifacts/control-vm" "$cache_root/artifacts/poly"
  third_log="$tmp/independent-third.stderr"
  third_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$third_log"
  )"
  if [[ "$third_output" != "run roots [(10, 2)]" ]]; then
    echo "source unit cache smoke: unexpected independent compiled-unit output" >&2
    echo "$third_output" >&2
    exit 1
  fi

  cat "$third_log"
  if ! rg -q 'run\.cache: compiled-unit-hit' "$third_log"; then
    echo "source unit cache smoke: expected compiled-unit hit after merged prefix materialization" >&2
    cat "$third_log" >&2
    exit 1
  fi
}

run_dependency_closure_smoke() {
  case_dir="$tmp/dependency"
  cache_root="$tmp/dependency-cache"
  main="$case_dir/main.yu"
  a="$case_dir/a.yu"
  b="$case_dir/a/b.yu"
  mkdir -p "$cache_root" "$case_dir/a"

  cat >"$main" <<'YULANG'
mod a;
a::x
YULANG

  cat >"$a" <<'YULANG'
mod b;
pub x = b::y
YULANG

  cat >"$b" <<'YULANG'
pub y = 7
YULANG

  first_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude run --print-roots "$main"
  )"
  if [[ "$first_output" != "run roots [7]" ]]; then
    echo "source unit cache smoke: unexpected dependency warmup output" >&2
    echo "$first_output" >&2
    exit 1
  fi

  cat >"$main" <<'YULANG'
mod a;
my keep v = v
keep a::x
YULANG

  second_log="$tmp/dependency-second.stderr"
  second_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$second_log"
  )"
  if [[ "$second_output" != "run roots [7]" ]]; then
    echo "source unit cache smoke: unexpected dependency cached output" >&2
    echo "$second_output" >&2
    exit 1
  fi

  cat "$second_log"
  if ! rg -q 'run\.cache: source-unit-prefix-hit' "$second_log"; then
    echo "source unit cache smoke: expected source-unit prefix hit" >&2
    cat "$second_log" >&2
    exit 1
  fi

  rm -rf "$cache_root/artifacts/control-vm" "$cache_root/artifacts/poly"
  third_log="$tmp/dependency-third.stderr"
  third_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$third_log"
  )"
  if [[ "$third_output" != "run roots [7]" ]]; then
    echo "source unit cache smoke: unexpected dependency compiled-unit output" >&2
    echo "$third_output" >&2
    exit 1
  fi

  cat "$third_log"
  if ! rg -q 'run\.cache: compiled-unit-hit' "$third_log"; then
    echo "source unit cache smoke: expected compiled-unit hit after source-unit prefix materialization" >&2
    cat "$third_log" >&2
    exit 1
  fi
}

run_independent_merge_smoke
run_dependency_closure_smoke

echo "source unit cache smoke ok: $bin"
