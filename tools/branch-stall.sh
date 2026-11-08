#!/usr/bin/env bash
# Report when a branch has had no work commit for N minutes.
#
# usage: tools/branch-stall.sh <remote/branch> <minutes>
#   e.g. tools/branch-stall.sh origin/integration/m1-final 40
#
# "Work commit" = a non-merge commit touching lean/Yulang or lean/SpecExamples.lean.
# Prints one line and exits: "alive <age> min: <subject>" or "STALLED <age> min: <subject>".
# Exit code 0 = alive, 1 = stalled, 2 = error. Meant to run from cron / a scheduled agent.
set -u
ref=${1:?usage: branch-stall.sh <remote/branch> <minutes>}
limit=${2:?usage: branch-stall.sh <remote/branch> <minutes>}
git fetch -q "${ref%%/*}" "${ref#*/}" 2>/dev/null || { echo "error: fetch failed"; exit 2; }
# Only non-merge commits touching the Lean sources count as work. Committer time (%ct) is used, so a
# supervisor commit of a worker's tree (the usual case for Codex) resets the clock: this measures
# the branch, not a particular worker.
line=$(git log "$ref" --no-merges -50 --format='%ct %s' -- lean/Yulang lean/SpecExamples.lean | head -1)
[ -n "$line" ] || { echo "error: no work commit found"; exit 2; }
ts=${line%% *}; subject=${line#* }
age=$(( ( $(date +%s) - ts ) / 60 ))
if [ "$age" -gt "$limit" ]; then echo "STALLED $age min: $subject"; exit 1; else echo "alive $age min: $subject"; exit 0; fi
