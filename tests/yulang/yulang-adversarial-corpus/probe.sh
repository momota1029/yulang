#!/usr/bin/env bash
set -uo pipefail

YULANG="${YULANG:-./target/debug/yulang}"
TIMEOUT="${TIMEOUT:-20s}"
ROOT="$(cd "$(dirname "$0")" && pwd)"
LOG_DIR="${LOG_DIR:-${TMPDIR:-/tmp}/yulang-adversarial-probe.$$}"

mkdir -p "$LOG_DIR"

failures=0
LAST_STATUS=0
LAST_LOG=""

ok() {
  printf 'ok - %s\n' "$1"
}

not_ok() {
  printf 'not ok - %s\n' "$1"
  failures=$((failures + 1))
}

log_name() {
  printf '%s' "$1" | sed 's/[^A-Za-z0-9_.-]/_/g'
}

run_cmd() {
  local label="$1"
  shift
  local name
  name="$(log_name "$label")"
  LAST_LOG="$LOG_DIR/$name.log"

  printf '\n===== %s =====\n' "$label"
  printf '$'
  printf ' %q' "$@"
  printf '\n'
  timeout "$TIMEOUT" "$@" >"$LAST_LOG" 2>&1
  LAST_STATUS=$?
  printf 'exit=%s log=%s\n' "$LAST_STATUS" "$LAST_LOG"
}

show_tail() {
  tail -n 40 "$LAST_LOG"
}

expect_success() {
  local label="$1"
  shift
  run_cmd "$label" "$@"
  if [[ "$LAST_STATUS" -eq 0 ]]; then
    ok "$label"
  else
    not_ok "$label"
    show_tail
  fi
}

expect_success_contains() {
  local label="$1"
  local pattern="$2"
  shift 2
  run_cmd "$label" "$@"
  if [[ "$LAST_STATUS" -ne 0 ]]; then
    not_ok "$label"
    show_tail
    return
  fi
  if rg -q -- "$pattern" "$LAST_LOG"; then
    ok "$label"
  else
    not_ok "$label (missing pattern: $pattern)"
    show_tail
  fi
}

expect_nonzero() {
  local label="$1"
  shift
  run_cmd "$label" "$@"
  if [[ "$LAST_STATUS" -ne 0 && "$LAST_STATUS" -ne 124 ]]; then
    ok "$label"
  else
    not_ok "$label"
    show_tail
  fi
}

expect_public_type_clean() {
  local label="$1"
  local file="$2"
  local symbol="$3"
  run_cmd "$label" "$YULANG" dump "$file" --poly
  if [[ "$LAST_STATUS" -ne 0 ]]; then
    not_ok "$label"
    show_tail
    return
  fi

  local line
  line="$(rg -F "\"$symbol\":" "$LAST_LOG" | head -n 1 || true)"
  if [[ -z "$line" ]]; then
    not_ok "$label (missing public symbol: $symbol)"
    show_tail
    return
  fi

  local type_part
  type_part="${line%% = *}"
  printf '%s\n' "$type_part"
  if [[ "$type_part" == *AllExcept* || "$type_part" == *"#"* || "$type_part" == *tick* ]]; then
    not_ok "$label (public type leaked private effect evidence)"
  else
    ok "$label"
  fi
}

for file in "$ROOT"/*.yu; do
  expect_success "check $(basename "$file")" "$YULANG" check "$file"
done

expect_public_type_clean \
  "01 public type projection" \
  "$ROOT/01_recursive_data_position_replay.yu" \
  "box.spin"
expect_success_contains \
  "02 VM result" \
  '^run roots \[6\]$' \
  "$YULANG" run --no-cache --print-roots "$ROOT/02_repeated_callback_hygiene.yu"
expect_success_contains \
  "02 interpreter result" \
  '^run roots \[6\]$' \
  "$YULANG" run --no-cache --print-roots --interpreter "$ROOT/02_repeated_callback_hygiene.yu"
expect_nonzero \
  "03 VM rejects same-path typed operations" \
  "$YULANG" run --no-cache --print-roots "$ROOT/03_parameterized_effect_capture.yu"
expect_nonzero \
  "03 interpreter rejects same-path typed operations" \
  "$YULANG" run --no-cache --print-roots --interpreter "$ROOT/03_parameterized_effect_capture.yu"
expect_success_contains \
  "04 computed SCC diagnostic" \
  'computed value fetch in recursive component' \
  "$YULANG" check "$ROOT/04_computed_scc_cycle.yu"
expect_nonzero \
  "05 VM rejects computed closure ref escape" \
  "$YULANG" run --no-cache --print-roots "$ROOT/05_value_restriction_closure_ref.yu"
expect_nonzero \
  "05 interpreter rejects computed closure ref escape" \
  "$YULANG" run --no-cache --print-roots --interpreter "$ROOT/05_value_restriction_closure_ref.yu"
expect_success_contains \
  "06 VM result" \
  '^run roots \[\[\(false, 1\), \(true, 1\)\]\]$' \
  "$YULANG" run --no-cache --print-roots "$ROOT/06_multishot_ref_after_fork.yu"
expect_success_contains \
  "06 interpreter result" \
  '^run roots \[\[\(false, 1\), \(true, 1\)\]\]$' \
  "$YULANG" run --no-cache --print-roots --interpreter "$ROOT/06_multishot_ref_after_fork.yu"
expect_nonzero \
  "07 VM rejects polymorphic recursion at specialize/run" \
  "$YULANG" run --no-cache --print-roots "$ROOT/07_polymorphic_recursion_termination.yu"
expect_nonzero \
  "07 interpreter rejects polymorphic recursion at specialize/run" \
  "$YULANG" run --no-cache --print-roots --interpreter "$ROOT/07_polymorphic_recursion_termination.yu"
expect_public_type_clean \
  "08 public type projection" \
  "$ROOT/08_two_private_data_tails.yu" \
  "box.handle_both"

printf '\nlogs: %s\n' "$LOG_DIR"
if [[ "$failures" -ne 0 ]]; then
  printf 'failures: %s\n' "$failures"
  exit 1
fi

printf 'all adversarial probes passed\n'
