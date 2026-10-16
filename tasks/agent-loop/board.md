# Resident research-loop board

Status: NOT-STARTED; workflow infrastructure only, no workers launched here.
Branch: `research/simple-sub-intrusion`
Session: unassigned
Runtime baseline: unresolved; reconcile current HEAD, worktree and live workers.
Owner: no active lease; Luna grants this file exclusively to the dispatcher.
Contract: [README](README.md) and [workflow decision](../../notes/design/2026-10-16-resident-research-loop.md).

## Role state

| Role | Actual worker ID | State | Requested model/effort | Observed model/effort | Current packet / exact lease |
| --- | --- | --- | --- | --- | --- |
| next_action_selector (dispatcher) | none | NOT-STARTED | gpt-6.1-sol / high | unknown | none |
| implementer | none | NOT-STARTED | gpt-6-luna / high | unknown | none |
| prover | none | NOT-STARTED | gpt-6.1-sol / high | unknown | none |

## Canonical TODOs

| ID / original gate locator | Target / state | Necessary dependencies | Frozen inputs / proposed or granted outputs | Acceptance evidence / next action |
| --- | --- | --- | --- | --- |

No tasks imported yet. Resolve current summaries and actual unfinished leases
from `tasks/current.md`, `tasks/research-lab.md` and runtime evidence first. Do not
reopen completed gates or copy historical claims of running workers.

## Intake receipts

None. Record request ID, revision, frozen SHA-256, canonical task ID and intake
acknowledgement here. Identical ID/hash intake is idempotent.

## Latest dispatcher decision

None. At authorized loop startup, ask the dispatcher for Luna's next action and
both producer assignments after runtime reconciliation. Record actual dispatch,
review and integration receipts; a proposed packet is not RUNNING or DONE.
