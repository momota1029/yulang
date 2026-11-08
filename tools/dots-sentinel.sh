#!/usr/bin/env bash
# Long-lived sentinel for one dot: prints one line per EVENT and keeps running.
#
# usage: tools/dots-sentinel.sh <dot-name> <last-known-report-N> [stale-minutes] [interval-seconds] [max-minutes]
#   defaults: stale 25, interval 60, max 110 minutes (just under the 2 hour background limit; re-arm after it ends).
#
# Events (each printed once per occurrence, no repeats while the state does not change):
#   dots-report <dot> <N> <sha7>        a new cycle report appeared
#   dots-stale  <dot> ...               the heartbeat went stale (the cycle probably crashed or is blocked)
#   dots-alive-again <dot> ...          the heartbeat is fresh again after a stale period
#   sentinel-timeout <dot>              max-minutes reached (re-arm)
# Unlike wait-dots-cycle.sh it does NOT exit on the first stale state: a dot that stays stale
# does not end the watch, and a dot that recovers and falls again is reported again.
set -u
dot=${1:?usage: dots-sentinel.sh <dot-name> <last-known-report-N> [stale-minutes] [interval-seconds] [max-minutes]}
last=${2:?missing last-known-report-N}
stale=${3:-25}
interval=${4:-60}
maxmin=${5:-110}
here=$(cd "$(dirname "$0")" && pwd)
case "$dot" in
  dots-audit) branch=work/dots-audit; lsdir=notes/audit;    rx='^notes/audit/cycle-\([0-9][0-9]*\)\.md$' ;;
  *)          branch=work/$dot;       lsdir=notes/handoff;  rx='^notes/handoff/dots-cycle-\([0-9][0-9]*\)\.md$' ;;
esac
state=unknown   # unknown|alive|stale
end=$(( $(date +%s) + maxmin * 60 ))
while [ "$(date +%s)" -lt "$end" ]; do
  if git fetch -q origin "$branch" 2>/dev/null; then
    top=$(git ls-tree -r --name-only "origin/$branch" "$lsdir" 2>/dev/null | sed -n "s#$rx#\\1#p" | sort -n | tail -1)
    if [ -n "${top:-}" ] && [ "$top" -gt "$last" ]; then
      echo "dots-report $dot $top $(git rev-parse --short "origin/$branch")"; last=$top
    fi
    hb=$("$here/check-dots-heartbeat.sh" "origin/$branch" "$dot" "$stale" 2>/dev/null); rc=$?
    if [ "$rc" -eq 1 ] && [ "$state" != stale ]; then echo "dots-stale $dot: $hb"; state=stale
    elif [ "$rc" -eq 0 ] && [ "$state" = stale ]; then echo "dots-alive-again $dot: $hb"; state=alive
    elif [ "$rc" -eq 0 ]; then state=alive
    elif [ "$rc" -eq 1 ]; then state=stale; fi
  fi
  sleep "$interval"
done
echo "sentinel-timeout $dot"
