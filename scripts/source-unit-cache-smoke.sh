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

run_editable_realm_band_smoke() {
  case_dir="$tmp/editable-realm-band"
  cache_root="$tmp/editable-realm-band-cache"
  main="$case_dir/main.yu"
  helper="$case_dir/helper.yu"
  helper_inner="$case_dir/helper/inner.yu"
  view="$case_dir/view.yu"
  mkdir -p "$cache_root" "$case_dir/helper"

  cat >"$case_dir/realm.toml" <<'YULANG'
[realm]
identity = "smoke/editable-realm-band"
YULANG

  cat >"$main" <<'YULANG'
use realm/helper::answer
use realm/view::describe
describe answer
YULANG

  cat >"$helper" <<'YULANG'
mod inner;
use band::inner::value as inner_value
pub answer = inner_value
YULANG

  cat >"$helper_inner" <<'YULANG'
our value = 42
YULANG

  cat >"$view" <<'YULANG'
pub describe value = value
YULANG

  first_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude run --print-roots "$main"
  )"
  if [[ "$first_output" != "run roots [42]" ]]; then
    echo "source unit cache smoke: unexpected editable realm/band warmup output" >&2
    echo "$first_output" >&2
    exit 1
  fi

  cat >"$main" <<'YULANG'
use realm/helper::answer
use realm/view::describe
my keep value = value
keep (describe answer)
YULANG

  second_log="$tmp/editable-realm-band-second.stderr"
  second_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$second_log"
  )"
  if [[ "$second_output" != "run roots [42]" ]]; then
    echo "source unit cache smoke: unexpected editable realm/band cached output" >&2
    echo "$second_output" >&2
    exit 1
  fi

  cat "$second_log"
  if ! rg -q 'run\.cache: (source-unit-prefix-hit|merged-source-unit-prefix-hit)' "$second_log"; then
    echo "source unit cache smoke: expected source-unit prefix hit for editable realm/band imports" >&2
    cat "$second_log" >&2
    exit 1
  fi

  rm -rf "$cache_root/artifacts/control-vm" "$cache_root/artifacts/poly"
  third_log="$tmp/editable-realm-band-third.stderr"
  third_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$third_log"
  )"
  if [[ "$third_output" != "run roots [42]" ]]; then
    echo "source unit cache smoke: unexpected editable realm/band compiled-unit output" >&2
    echo "$third_output" >&2
    exit 1
  fi

  cat "$third_log"
  if ! rg -q 'run\.cache: compiled-unit-hit' "$third_log"; then
    echo "source unit cache smoke: expected compiled-unit hit after editable realm/band prefix materialization" >&2
    cat "$third_log" >&2
    exit 1
  fi
}

run_struct_cast_smoke() {
  case_dir="$tmp/struct-cast"
  cache_root="$tmp/struct-cast-cache"
  main="$case_dir/main.yu"
  deps="$case_dir/deps.yu"
  mkdir -p "$cache_root" "$case_dir"

  cat >"$main" <<'YULANG'
mod deps;
(deps::Box { value: 1 }).value
YULANG

  cat >"$deps" <<'YULANG'
pub struct Box { value: int }
pub cast(x: int): Box = Box { value: x }
YULANG

  first_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude run --print-roots "$main"
  )"
  if [[ "$first_output" != "run roots [1]" ]]; then
    echo "source unit cache smoke: unexpected struct/cast warmup output" >&2
    echo "$first_output" >&2
    exit 1
  fi

  cat >"$main" <<'YULANG'
mod deps;
my wants_box(x: deps::Box) = x.value
wants_box 2
YULANG

  rm -rf "$cache_root/artifacts/control-vm" "$cache_root/artifacts/poly"
  second_log="$tmp/struct-cast-second.stderr"
  second_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$second_log"
  )"
  if [[ "$second_output" != "run roots [2]" ]]; then
    echo "source unit cache smoke: unexpected struct/cast compiled-unit output" >&2
    echo "$second_output" >&2
    exit 1
  fi

  cat "$second_log"
  if ! rg -q 'run\.cache: source-unit-prefix-hit' "$second_log"; then
    echo "source unit cache smoke: expected source-unit prefix hit for struct/cast dependency" >&2
    cat "$second_log" >&2
    exit 1
  fi
}

run_effect_contract_smoke() {
  case_dir="$tmp/effect-contract"
  cache_root="$tmp/effect-contract-cache"
  main="$case_dir/main.yu"
  deps="$case_dir/deps.yu"
  mkdir -p "$cache_root" "$case_dir"

  cat >"$main" <<'YULANG'
mod deps;
pub use deps::*
our handle(action: [signal] _) = catch action:
  signal::ping(), k -> k 5
  v -> v
handle: use_it \() -> signal::ping()
YULANG

  cat >"$deps" <<'YULANG'
pub act signal:
  pub ping: () -> int
pub use_it(f: () -> [signal] int) = f ()
YULANG

  first_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude run --print-roots "$main"
  )"
  if [[ "$first_output" != "run roots [5]" ]]; then
    echo "source unit cache smoke: unexpected effect contract warmup output" >&2
    echo "$first_output" >&2
    exit 1
  fi

  cat >"$main" <<'YULANG'
mod deps;
pub use deps::*
our handle(action: [signal] _) = catch action:
  signal::ping(), k -> k 7
  v -> v
my keep v = v
keep (handle: use_it \() -> signal::ping())
YULANG

  rm -rf "$cache_root/artifacts/control-vm" "$cache_root/artifacts/poly"
  second_log="$tmp/effect-contract-second.stderr"
  second_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$second_log"
  )"
  if [[ "$second_output" != "run roots [7]" ]]; then
    echo "source unit cache smoke: unexpected effect contract cached output" >&2
    echo "$second_output" >&2
    exit 1
  fi

  cat "$second_log"
  if ! rg -q 'run\.cache: source-unit-prefix-hit' "$second_log"; then
    echo "source unit cache smoke: expected source-unit prefix hit for effect contract dependency" >&2
    cat "$second_log" >&2
    exit 1
  fi
}

run_role_impl_smoke() {
  case_dir="$tmp/role-impl"
  cache_root="$tmp/role-impl-cache"
  main="$case_dir/main.yu"
  deps="$case_dir/deps.yu"
  mkdir -p "$cache_root" "$case_dir"

  cat >"$main" <<'YULANG'
mod deps;
pub use deps::*
1.display
YULANG

  cat >"$deps" <<'YULANG'
pub role Display 'a:
  pub x.display: int
impl int: Display:
  pub x.display = x
YULANG

  first_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude run --print-roots "$main"
  )"
  if [[ "$first_output" != "run roots [1]" ]]; then
    echo "source unit cache smoke: unexpected role impl warmup output" >&2
    echo "$first_output" >&2
    exit 1
  fi

  cat >"$main" <<'YULANG'
mod deps;
pub use deps::*
my keep v = v
keep 2.display
YULANG

  rm -rf "$cache_root/artifacts/control-vm" "$cache_root/artifacts/poly"
  second_log="$tmp/role-impl-second.stderr"
  second_output="$(
    YULANG_CACHE_DIR="$cache_root" \
      run "$bin" --no-prelude --runtime-phase-timings run --print-roots "$main" \
        2>"$second_log"
  )"
  if [[ "$second_output" != "run roots [2]" ]]; then
    echo "source unit cache smoke: unexpected role impl cached output" >&2
    echo "$second_output" >&2
    exit 1
  fi

  cat "$second_log"
  if ! rg -q 'run\.cache: source-unit-prefix-hit' "$second_log"; then
    echo "source unit cache smoke: expected source-unit prefix hit for role impl dependency" >&2
    cat "$second_log" >&2
    exit 1
  fi
}

run_independent_merge_smoke
run_dependency_closure_smoke
run_editable_realm_band_smoke
run_struct_cast_smoke
run_effect_contract_smoke
run_role_impl_smoke

echo "source unit cache smoke ok: $bin"
