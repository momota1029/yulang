#!/usr/bin/env bash
# Block until a NEW dots cycle report appears on work/dots-main, then print one line and exit.
#
# usage: tools/wait-dots-cycle.sh <last-known-N> [max-minutes] [interval-seconds] [dot-name] [stale-minutes]
#   defaults: max 110 minutes, poll every 60 s, dot-name dots-main, stale 25 minutes.
#   110 minutes is just under the 2 hour limit of a background command; re-arm after each event.
# Meant for `Bash run_in_background` (limit 2 hours), not Monitor (30 minute cap).
# Output: "dots-cycle-report <N> <sha7>", "dots-stale <heartbeat line>" (the heartbeat of the dot is
# older than stale-minutes while running: the cycle probably crashed), or "dots-cycle-wait-timeout (last known <N>)".
# A cycle report = a file notes/handoff/dots-cycle-<N>.md with N greater than <last-known-N>.
set -u
last=${1:?usage: wait-dots-cycle.sh <last-known-N> [max-minutes] [interval-seconds]}
maxmin=${2:-110}
interval=${3:-60}
dot=${4:-dots-main}
case "$dot" in
  dots-audit) branch=work/dots-audit; rx='^notes/audit/cycle-\([0-9][0-9]*\)\.md$'; lsdir=notes/audit ;;
  *)          branch=work/$dot;       rx='^notes/handoff/dots-cycle-\([0-9][0-9]*\)\.md$'; lsdir=notes/handoff ;;
esac
stale=${5:-25}
here=$(cd "$(dirname "$0")" && pwd)
end=$(( $(date +%s) + maxmin * 60 ))
while [ "$(date +%s)" -lt "$end" ]; do
  if git fetch -q origin "$branch" 2>/dev/null; then
    top=$(git ls-tree -r --name-only "origin/$branch" "$lsdir" 2>/dev/null \
          | sed -n "s#$rx#\\1#p" | sort -n | tail -1)
    if [ -n "${top:-}" ] && [ "$top" -gt "$last" ]; then
      echo "dots-cycle-report $dot $top $(git rev-parse --short "origin/$branch")"; exit 0
    fi
  fi
  hb=$("$here/check-dots-heartbeat.sh" "origin/work/$dot" "$dot" "$stale" 2>/dev/null); rc=$?
  if [ "$rc" -eq 1 ]; then echo "dots-stale $hb"; exit 0; fi
  sleep "$interval"
done
echo "dots-cycle-wait-timeout (last known $last)"
