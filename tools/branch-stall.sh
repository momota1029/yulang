#!/usr/bin/env bash
# Report when a branch has had no work commit for N minutes.
#
# usage: tools/branch-stall.sh <remote/branch> <minutes>
#   e.g. tools/branch-stall.sh origin/integration/m1-final 40
#
# "Work commit" = any commit whose subject does not start with spec:/handoff:/notes:/docs:
# (those are supervisor decision records, not progress by a prover).
# Prints one line and exits: "alive <age> min: <subject>" or "STALLED <age> min: <subject>".
# Exit code 0 = alive, 1 = stalled, 2 = error. Meant to run from cron / a scheduled agent.
set -u
ref=${1:?usage: branch-stall.sh <remote/branch> <minutes>}
limit=${2:?usage: branch-stall.sh <remote/branch> <minutes>}
git fetch -q "${ref%%/*}" "${ref#*/}" 2>/dev/null || { echo "error: fetch failed"; exit 2; }
line=$(git log "$ref" -200 --format='%ct %s' | grep -v -E '^[0-9]+ (spec|handoff|notes|docs):' | head -1)
[ -n "$line" ] || { echo "error: no work commit found"; exit 2; }
ts=${line%% *}; subject=${line#* }
age=$(( ( $(date +%s) - ts ) / 60 ))
if [ "$age" -gt "$limit" ]; then echo "STALLED $age min: $subject"; exit 1; else echo "alive $age min: $subject"; exit 0; fi
