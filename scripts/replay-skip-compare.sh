#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${YULANG:-"$repo_root/target/release/yulang"}"
std_root="${YULANG_STD_ROOT:-"$repo_root/lib"}"
timeout_duration="${YULANG_REPLAY_COMPARE_TIMEOUT:-240s}"
skip_limit="${YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT:-16}"

if [[ "$#" -gt 0 ]]; then
  cases=("$@")
else
  cases=(
    "examples/showcase.yu"
    "examples/effect-hygiene/01_higher_order_inference.yu"
    "examples/effect-hygiene/02_local_sub_handler.yu"
    "examples/effect-hygiene/03_data_position_private_tail.yu"
    "tests/yulang/regressions/effect/public_type_display_order_signatures.yu"
  )
fi

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/yulang-replay-skip-compare.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT

metric() {
  local log="$1"
  local key="$2:"
  awk -v key="$key" '$1 == key { print $2; found = 1; exit } END { if (!found) print "-" }' "$log"
}

run_check() {
  local mode="$1"
  local rel="$2"
  local path="$repo_root/$rel"
  local log="$tmpdir/${mode}-${rel//\//_}.log"

  case "$mode" in
    default)
      if ! env -u YULANG_REPLAY_EVIDENCE_ONLY_SKIP \
        -u YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT \
        timeout "$timeout_duration" "$bin" --std-root "$std_root" \
        check-poly-std "$path" >"$log"; then
        echo "failed: $mode $rel" >&2
        cat "$log" >&2
        exit 1
      fi
      ;;
    evidence)
      if ! env YULANG_REPLAY_EVIDENCE_ONLY_SKIP=1 \
        YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT="$skip_limit" \
        timeout "$timeout_duration" "$bin" --std-root "$std_root" \
        check-poly-std "$path" >"$log"; then
        echo "failed: $mode $rel" >&2
        cat "$log" >&2
        exit 1
      fi
      ;;
    *)
      echo "unknown mode: $mode" >&2
      exit 1
      ;;
  esac

  printf '%-66s %-8s %10s %10s %10s %10s %10s %10s %10s\n' \
    "$rel" \
    "$mode" \
    "$(metric "$log" infer)" \
    "$(metric "$log" constraint.drain)" \
    "$(metric "$log" total)" \
    "$(metric "$log" constraint.replay_accepted)" \
    "$(metric "$log" constraint.replay_evidence_only)" \
    "$(metric "$log" constraint.replay_duplicate)" \
    "$(metric "$log" constraint.replay_prefiltered)"
}

printf 'binary: %s\n' "$bin"
printf 'std root: %s\n' "$std_root"
printf 'evidence-only skip limit: %s\n\n' "$skip_limit"
printf '%-66s %-8s %10s %10s %10s %10s %10s %10s %10s\n' \
  "case" "mode" "infer" "drain" "total" "accepted" "evidence" "duplicate" "prefilter"
printf '%0.s-' {1..156}
printf '\n'

for input in "${cases[@]}"; do
  case "$input" in
    "$repo_root"/*) rel="${input#"$repo_root"/}" ;;
    /*)
      echo "case must be inside repo: $input" >&2
      exit 1
      ;;
    *) rel="$input" ;;
  esac
  run_check default "$rel"
  run_check evidence "$rel"
done
