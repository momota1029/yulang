#!/usr/bin/env bash
# Print one line whenever a work/* branch on the remote is created or advances.
#
# usage: tools/watch-work-branches.sh [remote] [interval-seconds] [max-minutes]
#   defaults: origin 60 29
# Meant for the Monitor tool (30 minute cap per Monitor, so max-minutes defaults to 29).
# Output lines: "work-branch-updated <branch> <sha7> (new|advanced)"  or  "work-watch-timeout".
# Baseline = the branches present at start (not reported); only changes after that are reported.
set -u
remote=${1:-origin}
interval=${2:-60}
maxmin=${3:-29}
declare -A seen
snapshot() { git ls-remote --heads "$remote" 'refs/heads/work/*' 2>/dev/null; }
while read -r sha ref; do [ -n "${ref:-}" ] && seen["$ref"]=$sha; done < <(snapshot)
end=$(( $(date +%s) + maxmin * 60 ))
while [ "$(date +%s)" -lt "$end" ]; do
  sleep "$interval"
  while read -r sha ref; do
    [ -n "${ref:-}" ] || continue
    if [ -z "${seen[$ref]:-}" ]; then echo "work-branch-updated ${ref#refs/heads/} ${sha:0:7} (new)"; seen["$ref"]=$sha
    elif [ "${seen[$ref]}" != "$sha" ]; then echo "work-branch-updated ${ref#refs/heads/} ${sha:0:7} (advanced)"; seen["$ref"]=$sha; fi
  done < <(snapshot)
done
echo "work-watch-timeout (re-arm if still needed)"
