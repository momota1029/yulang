# Delegating to Codex workers

Canonical mechanics for dispatching Codex workers through the `codex-agents` MCP tools (`mcp__codex-agents__*`: `agent_start`, `agent_result`, `agent_wait`, `agent_review`, `agent_fork`, `agent_handoff`). The older `codex-flow` and `codex@openai-codex` plugins are retired.

Authority and verification stay with the delegator (see `workflow.md`). Observed failure patterns are in `codex-quirks.md`. Model and effort are chosen per call.

## Dispatch

`agent_start` returns at once with `status: running`; the worker runs in a separate process. Launch independent workers in one message, then do other work.

Put these in the tool call itself. Model names written only in the prompt have no effect, and omitting `model` silently runs the default (this mistake happened twice):

- `model` and `effort`. Read current names from `~/.codex/models_cache.json` (`slug`, `supported_reasoning_levels`); names go stale.
- `cwd`, absolute. Omitted, it is the MCP server's start directory.
- `sandbox`: `read-only` for investigation and review, `workspace-write` only for workers meant to edit.
- `approvalPolicy: "never"` for unattended workers, so they do not stall on an approval nobody answers.
- `watchdogSeconds` so an abandoned worker stops; `label` for the fleet listing.

Before sending, check the actual call parameters (not the prompt) for `model`, `effort`, `cwd` and `sandbox`.

The prompt must be self-contained, because the worker cannot see this conversation: objective, scope, constraints, stop condition, required checks, and "do not edit / commit / push" where it applies. `agent_handoff` imports the transcript instead; use it only when restating the context is costly. Use `agent_review` for plain "review this diff" tasks.

Write the prompt in English. Workers inherit `AGENTS.md`, whose Japanese conversation tone applies only when answering the user; an English instruction from a delegator puts the worker outside that rule and its report comes back in plain English.

Concurrent writers need separate `cwd` values (one git worktree each). Several writers on one `cwd` do not run in parallel and can collide.

## Collect

1. Do other work, then `agent_result` (no arguments returns every worker). Trust `done: true`, not the message alone: a final message can appear while `status` is still `running`.
2. `agent_wait` with every outstanding id in `agentIds` and `mode: "all"`. It blocks the whole turn and is capped at 55 s per call; use it only when nothing else is left.
3. Across turns: the Monitor recipe below.

No completion notice arrives by itself.

## Wake on completion (across turns)

A worker's log is `~/.codex/sessions/YYYY/MM/DD/rollout-*-<threadId>.jsonl`; it gains an `event_msg` with `"type":"task_complete"` when the turn ends. Start a `Monitor` that prints one line when it appears. The notice wakes the session, which then calls `agent_result`.

```sh
tid=<threadId from agent_start>
for i in $(seq 1 600); do
  f=$(find ~/.codex/sessions -name "*$tid*" 2>/dev/null | head -1)
  if [ -n "$f" ] && grep -q '"type":"task_complete"' "$f"; then
    echo "codex-done <agentId> <label>"; exit 0
  fi
  sleep 3
done
echo "codex-timeout <agentId>"
```

- A Monitor lives at most 30 minutes (`timeout_ms` up to 1800000); re-arm for longer jobs. Keep the timeout line so silence is distinguishable from a quiet wait.
- It sees normal completion only. A worker that crashes or is interrupted may never write `task_complete` (unverified); confirm the event names before relying on the watch for those cases.
- The wake-up reaches the session, not the user's phone. Add `PushNotification` for long work.

## Capacity

- `mcp__usage-guard__check_usage_limits` returns the delegator's session and weekly usage. `data_freshness: "unavailable"` means the sample is over five minutes old; treat the numbers as a rough guide.
- The server allows 32 active workers. Worker cost is real: one read-only survey of 16 markdown files used about 2M input tokens (mostly cached). Scope surveys narrowly.

## Recovery

When a call times out or a worker looks stuck: `agent_status` for one worker, `agent_events` for detail, `agent_interrupt` to stop a turn, `agent_resume` with a `threadId` after an MCP restart. A worker that edited files leaves its diff behind; inspect the diff rather than trusting the report.
