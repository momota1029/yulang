#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
YULANG_BIN="${YULANG_BIN:-"$ROOT/target/debug/yulang"}"
REPEAT="${YULANG_NATIVE_BENCH_REPEAT:-1}"
KEEP_TEMP=0
MODES="${YULANG_NATIVE_BENCH_MODES:-vm,value-exe,cps-repr-exe,native}"

usage() {
  cat <<'EOF'
usage: bench/native_cps_opt_trace.sh [--repeat N] [--modes LIST] [--keep-temp] [FILES...]

Runs small native/backend comparison probes and prints CPS optimization trace
lines. LIST is a comma-separated set of:

  vm,value-exe,cps-repr-exe,native

Environment:

  YULANG_BIN                  yulang binary path (default: target/debug/yulang)
  YULANG_NATIVE_BENCH_REPEAT  run count per mode (default: 1)
  YULANG_NATIVE_BENCH_MODES   default mode list
  YULANG_NATIVE_BENCH_SKIP_BUILD=1 skips the initial cargo build
EOF
}

paths=()
while (($#)); do
  case "$1" in
    --repeat)
      REPEAT="${2:?missing repeat count}"
      shift 2
      ;;
    --modes)
      MODES="${2:?missing mode list}"
      shift 2
      ;;
    --keep-temp)
      KEEP_TEMP=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      paths+=("$@")
      break
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      paths+=("$1")
      shift
      ;;
  esac
done

if [[ "${YULANG_NATIVE_BENCH_SKIP_BUILD:-0}" != "1" ]]; then
  (cd "$ROOT" && cargo build -q -p yulang)
elif [[ ! -x "$YULANG_BIN" ]]; then
  (cd "$ROOT" && cargo build -q -p yulang)
fi

tmp_dir="$(mktemp -d)"
if ((KEEP_TEMP)); then
  echo "native-cps-opt-trace: keeping temp dir $tmp_dir" >&2
else
  trap 'rm -rf "$tmp_dir"' EXIT
fi

if ((${#paths[@]} == 0)); then
  cat >"$tmp_dir/pure_arithmetic.yu" <<'YU'
my add x y = x + y
add 40 2
YU

  cat >"$tmp_dir/partial_closure.yu" <<'YU'
my add x y = x + y
my add40 = add 40
add40 2
YU

  cat >"$tmp_dir/list_map.yu" <<'YU'
[1, 2, 3, 4].map (\x -> x + 1)
YU

  cat >"$tmp_dir/list_fold.yu" <<'YU'
[1, 2, 3, 4].fold 0 (\acc x -> acc + x)
YU

  paths=(
    "$tmp_dir/pure_arithmetic.yu"
    "$tmp_dir/partial_closure.yu"
    "$tmp_dir/list_map.yu"
    "$tmp_dir/list_fold.yu"
    "$ROOT/examples/04_sub_return.yu"
    "$ROOT/examples/05_undet_all.yu"
    "$ROOT/examples/07_junction.yu"
  )
fi

IFS=',' read -r -a mode_list <<<"$MODES"

run_mode() {
  local mode="$1"
  local path="$2"
  case "$mode" in
    vm)
      "$YULANG_BIN" run "$path"
      ;;
    value-exe)
      "$YULANG_BIN" native --kind run-value-exe "$path"
      ;;
    cps-repr-exe)
      YULANG_CPS_OPT_TRACE=1 "$YULANG_BIN" native --kind run-cps-repr-exe "$path"
      ;;
    native)
      YULANG_CPS_OPT_TRACE=1 "$YULANG_BIN" native "$path"
      ;;
    *)
      echo "unknown mode: $mode" >&2
      return 2
      ;;
  esac
}

printf 'native-cps-opt-trace: bin=%s repeat=%s modes=%s\n' "$YULANG_BIN" "$REPEAT" "$MODES"

for path in "${paths[@]}"; do
  case_name="$(basename "$path")"
  printf '\n== %s ==\npath=%s\n' "$case_name" "$path"
  for mode in "${mode_list[@]}"; do
    best=""
    last_status=0
    last_out="$tmp_dir/out.txt"
    last_err="$tmp_dir/err.txt"
    : >"$last_out"
    : >"$last_err"

    for ((i = 1; i <= REPEAT; i++)); do
      start_ns="$(date +%s%N)"
      set +e
      run_mode "$mode" "$path" >"$last_out" 2>"$last_err"
      last_status=$?
      set -e
      end_ns="$(date +%s%N)"
      real="$(awk -v start="$start_ns" -v end="$end_ns" 'BEGIN { printf "%.3f", (end - start) / 1000000000 }')"
      if [[ -z "$best" || "$(awk -v a="$real" -v b="$best" 'BEGIN { print (a < b) ? 1 : 0 }')" == "1" ]]; then
        best="$real"
      fi
    done

    printf '[%s] status=%s best_real=%ss\n' "$mode" "$last_status" "${best:-?}"
    trace="$(grep '^\[CPS-OPT\]' "$last_err" | tail -n 1 || true)"
    if [[ -n "$trace" ]]; then
      printf '  trace: %s\n' "$trace"
    fi
    if ((last_status != 0)); then
      printf '  stderr: %s\n' "$(tail -n 1 "$last_err")"
    else
      printf '  output: %s\n' "$(tail -n 1 "$last_out")"
    fi
  done
done
