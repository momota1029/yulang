#!/usr/bin/env bash
# Report the state of a dot from its heartbeat file on a work branch.
#
# usage: tools/check-dots-heartbeat.sh <remote/branch> <dot-name> [stale-minutes]
#   e.g. tools/check-dots-heartbeat.sh origin/work/dots-main dots-main 20
#
# Reads notes/heartbeat/<dot-name>.md on the branch (see the standing orders: a heartbeat every 10 minutes).
# Prints one line and exits:
#   alive    <age> min: cycle N, <activity>         (exit 0)
#   completed <age> min: cycle N                     (exit 0)
#   STALE    <age> min: cycle N was running ...      (exit 1)  -> the cycle probably crashed
#   NO-HEARTBEAT                                     (exit 2)
set -u
ref=${1:?usage: check-dots-heartbeat.sh <remote/branch> <dot-name> [stale-minutes]}
dot=${2:?usage: check-dots-heartbeat.sh <remote/branch> <dot-name> [stale-minutes]}
limit=${3:-20}
git fetch -q "${ref%%/*}" "${ref#*/}" 2>/dev/null || { echo "error: fetch failed"; exit 2; }
hb=$(git show "$ref:notes/heartbeat/$dot.md" 2>/dev/null) || { echo "NO-HEARTBEAT ($ref notes/heartbeat/$dot.md)"; exit 2; }
field() { printf '%s\n' "$hb" | sed -n "s/^[ -]*$1: *//p" | head -1; }
status=$(field status); cycle=$(field cycle); updated=$(field updated); activity=$(field activity)
ts=$(date -u -d "$updated" +%s 2>/dev/null) || { echo "error: cannot parse updated: $updated"; exit 2; }
age=$(( ( $(date +%s) - ts ) / 60 ))
if [ "$status" = "completed" ]; then echo "completed $age min: cycle $cycle"; exit 0; fi
if [ "$age" -gt "$limit" ]; then echo "STALE $age min: cycle $cycle was running (last: $activity)"; exit 1; fi
echo "alive $age min: cycle $cycle, $activity"; exit 0
