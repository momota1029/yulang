---
name: yulang-research-loop
description: Maintain Yulang's resident Sol implementation, proof and task-dispatch lanes during authorized research/simple-sub-intrusion work. Use on startup, restart, results, blockers and next-action boundaries; Luna always consults the dispatcher, routes mutual TODOs and keeps safe implementation advancing.
---

# Run the resident Yulang research loop

Read `AGENTS.md` and `notes/design/2026-10-16-resident-research-loop.md`.
The latter supersedes occasional next-action selection for this loop. Keep the
user-selected Luna primary; do not silently switch the primary model. This
skill is a primary-only workflow, not a background service. A delegated child
reads its role and TODO contract, returns to its delegator, and never starts a
second trio. Plan/status-only and maintenance
requests do not authorize production work or require a trio launch.

## Establish the session

Resolve branch/HEAD/status, the authorized goal, applicable user decisions and
question-board evidence. Read current summaries and exact relevant bounded
sections of `tasks/current.md` and `tasks/research-lab.md`. Read
`tasks/agent-loop/README.md` and the board. Reconcile real worker identities,
leases and frozen dependencies; stale queue text is not a live worker. Adopt
healthy existing roles rather than duplicating them.

Read `.codex/config.toml` and the three role files. Maintain one resident
`next_action_selector` (dispatcher), `implementer` and `prover`. Normal launches
use configured Sol/high, explicit native settings when supported, and
`fork_turns: "none"`. Pass the bounded role contract without parent history.
Give the dispatcher the exact board lease and each producer exact artifact paths
plus one unique inbox path. Only Luna actually dispatches, grants leases,
appoints independent reviewers and performs Git integration.

Use supported message/resume operations for healthy workers. For an exhausted
worker, freeze/stop its writes before a replacement receives its lease. Honor
actual capacity and the global budget; reduce optional lanes first. Use the
canonical bounded capacity retry and unsupported-role fallback. Without a spawn
interface use the same logical roles serially and label degraded mode honestly.

## Ask, dispatch, collect, ask again

At the start and EVERY next-action boundary, ask the dispatcher: "Given this
frozen evidence and current lane/lease state, what should Luna do next, and what
should the implementer and prover work on?" Include result/review/blocker
receipts, changed dependencies, inbox IDs/hashes and actual runtime identities.
Use the `yulang-next-action` skill for this consultation.

Require a next Luna action, both lane states, selected ready packets or exact
blockers, acceptance evidence, proposed paths, dependency/check/resource owners
and next consultation trigger. Validate safety and authority, then dispatch the
selected ready implementation and proof concurrently when inputs/leases allow.
Reject unsafe proposals with the concrete reason and ask for a revised choice.
Do not turn consultation into Luna choosing arbitrary unrelated work.

Each bounded packet may contain multiple tool calls. Do not ask again before
each read/edit/test inside that packet. Consult after results, blockers, reviews,
worker exits, new user decisions, dependency changes, restart, assigning a new
packet or deciding to wait/finish. Coalesce already-available events; do not wait
for every worker to finish and do not busy-poll. Preserve safe running packets.

## Close the mutual TODO loop

Implementer submits missing proof obligations; prover submits required source
construction, retained invariants and implementation/evidence work. Either may
also propose work for its own lane. Use the assigned inbox and README fields;
freeze before notifying Luna and wait for intake acknowledgement before appending.
The dispatcher records deduplicated requests and can originate the next concrete
implementation task from inspected progress. A request is not a lease or proof.

On every consultation demand a ready implementation successor when one exists;
an unrelated open proof is not a reason to leave the implementer idle. Keep
necessary A/B dependencies and production gates honest. Use only the smallest
explicitly provisional evidence slice to break a real construction/proof cycle.
Do not use more plans or conditional lemmas as a substitute for construction.

## Review, escalate and checkpoint

Route localized evidence-backed bottlenecks from any role to one bounded native
Astra assignment under the decision; normal work returns to Sol. Record requested
and observed settings separately. No override support means no claim of Astra
execution. Never run two writers of one lease or substitute a producer's review
for fresh independent certification.

Luna sends actual launch/review/integration receipts back to the dispatcher.
Freeze the scheduling board and artifacts before a coherent checkpoint; keep
pending question bundles and unrelated work outside commits. Apply normal
review and push rules. Before stopping, consult once with the actual completion
or blocker evidence and preserve owners/next steps. Do not claim ongoing work
after session termination or claim a config edit started any workers.
