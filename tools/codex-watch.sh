#!/usr/bin/env bash
# Print one line per Codex worker whose session log shows task_complete (codex-done) or an
# aborted turn (codex-aborted), then exit.
#
# usage: tools/codex-watch.sh <threadId>:<label>[@N] [<threadId>:<label>[@N] ...]
#
# A worker thread that was resumed with a follow-up already holds the earlier
# task_complete lines. "@N" waits until the log holds at least N of them: use the
# number already present plus one (`grep -c '"type":"task_complete"' <log>`).
# Without "@N" the count is 1. N counts ended turns (completed or aborted); use the number
# of `task_complete`/`turn_aborted` lines already in the log plus one.
#
# Meant for the Monitor tool (see rules/codex-delegation.md). It is a bash script
# on purpose: the login shell may be zsh, which does not split an unquoted
# variable into words, so an inline loop over "$pending" silently misbehaves.
# Stops after about 29 minutes (a Monitor lives at most 30) with a timeout line
# that lists the workers still pending, so silence is never ambiguous.
set -u
[ "$#" -gt 0 ] || { echo "usage: $0 <threadId>:<label>[@N] ..." >&2; exit 2; }

pending=("$@")
for _ in $(seq 1 580); do
  next=()
  for entry in "${pending[@]}"; do
    tid=${entry%%:*}
    rest=${entry#*:}
    label=${rest%@*}
    want=1
    case "$rest" in *@*) want=${rest##*@} ;; esac
    log=$(find "$HOME/.codex/sessions" -name "*${tid}*.jsonl" 2>/dev/null | head -n 1)
    done_count=0
    [ -n "$log" ] && done_count=$(grep -c '"type":"task_complete"' "$log")
    # An interrupted turn (watchdog, user stop) logs turn_aborted, never task_complete.
    last_end=""
    end_count=0
    if [ -n "$log" ]; then
      end_count=$(grep -c -E '"type":"(task_complete|turn_aborted)"' "$log")
      last_end=$(grep -o -E '"type":"(task_complete|turn_aborted)"' "$log" | tail -n 1)
    fi
    if [ "$end_count" -ge "$want" ] && [ "$last_end" = '"type":"task_complete"' ]; then
      echo "codex-done ${label} ${tid}"
    elif [ "$end_count" -ge "$want" ] && [ "$last_end" = '"type":"turn_aborted"' ]; then
      echo "codex-aborted ${label} ${tid} (turn interrupted: resume with agent_send)"
    else
      next+=("$entry")
    fi
  done
  pending=("${next[@]+"${next[@]}"}")
  [ "${#pending[@]}" -eq 0 ] && exit 0
  sleep 3
done
echo "codex-timeout pending: ${pending[*]}"
