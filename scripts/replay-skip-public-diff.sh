#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${YULANG:-"$repo_root/target/release/yulang"}"
std_root="${YULANG_STD_ROOT:-"$repo_root/lib"}"
timeout_duration="${YULANG_REPLAY_DIFF_TIMEOUT:-240s}"
skip_limit="${YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT:-16}"

if [[ "$#" -gt 0 ]]; then
  cases=("$@")
else
  cases=(
    "examples/effect-hygiene/01_higher_order_inference.yu"
    "examples/effect-hygiene/02_local_sub_handler.yu"
    "examples/effect-hygiene/03_data_position_private_tail.yu"
    "tests/yulang/regressions/effect/data_position_effect_function_public_signature.yu"
    "tests/yulang/regressions/effect/nested_data_position_effect_function_public_signature.yu"
    "tests/yulang/regressions/effect/nested_handler_contract_public_signatures.yu"
    "tests/yulang/regressions/effect/public_type_display_order_signatures.yu"
    "tests/yulang/regressions/effect/sub_return_callback_public_signature.yu"
  )
fi

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/yulang-replay-skip-public-diff.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT

run_dump() {
  local mode="$1"
  local rel="$2"
  local path="$repo_root/$rel"
  local out="$tmpdir/${mode}-${rel//\//_}.poly"

  case "$mode" in
    default)
      env -u YULANG_REPLAY_EVIDENCE_ONLY_SKIP \
        -u YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT \
        timeout "$timeout_duration" "$bin" --std-root "$std_root" \
        dump-poly-std "$path" >"$out"
      ;;
    evidence)
      env YULANG_REPLAY_EVIDENCE_ONLY_SKIP=1 \
        YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT="$skip_limit" \
        timeout "$timeout_duration" "$bin" --std-root "$std_root" \
        dump-poly-std "$path" >"$out"
      ;;
    *)
      echo "unknown mode: $mode" >&2
      exit 1
      ;;
  esac

  printf '%s\n' "$out"
}

printf 'binary: %s\n' "$bin"
printf 'std root: %s\n' "$std_root"
printf 'evidence-only skip limit: %s\n\n' "$skip_limit"

for input in "${cases[@]}"; do
  case "$input" in
    "$repo_root"/*) rel="${input#"$repo_root"/}" ;;
    /*)
      echo "case must be inside repo: $input" >&2
      exit 1
      ;;
    *) rel="$input" ;;
  esac

  default_out="$(run_dump default "$rel")"
  evidence_out="$(run_dump evidence "$rel")"
  if ! cmp -s "$default_out" "$evidence_out"; then
    echo "replay skip public diff: output changed for $rel" >&2
    diff -u "$default_out" "$evidence_out" >&2 || true
    exit 1
  fi
  printf 'ok %s\n' "$rel"
done

printf '\nreplay skip public diff ok\n'
