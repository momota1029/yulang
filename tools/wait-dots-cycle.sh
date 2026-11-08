#!/usr/bin/env bash
# Block until a NEW dots cycle report appears on work/dots-main, then print one line and exit.
#
# usage: tools/wait-dots-cycle.sh <last-known-N> [max-minutes] [interval-seconds]
#   defaults: max 110 minutes, poll every 60 s.
# Meant for `Bash run_in_background` (limit 2 hours), not Monitor (30 minute cap).
# Output: "dots-cycle-report <N> <sha7>"  or  "dots-cycle-wait-timeout (last known <N>)".
# A cycle report = a file notes/handoff/dots-cycle-<N>.md with N greater than <last-known-N>.
set -u
last=${1:?usage: wait-dots-cycle.sh <last-known-N> [max-minutes] [interval-seconds]}
maxmin=${2:-110}
interval=${3:-60}
end=$(( $(date +%s) + maxmin * 60 ))
while [ "$(date +%s)" -lt "$end" ]; do
  if git fetch -q origin work/dots-main 2>/dev/null; then
    top=$(git ls-tree -r --name-only origin/work/dots-main notes/handoff 2>/dev/null \
          | sed -n 's#.*dots-cycle-\([0-9][0-9]*\)\.md#\1#p' | sort -n | tail -1)
    if [ -n "${top:-}" ] && [ "$top" -gt "$last" ]; then
      echo "dots-cycle-report $top $(git rev-parse --short origin/work/dots-main)"; exit 0
    fi
  fi
  sleep "$interval"
done
echo "dots-cycle-wait-timeout (last known $last)"
