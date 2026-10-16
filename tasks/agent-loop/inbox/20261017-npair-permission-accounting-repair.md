# Frozen handoff: NPAIR Permission accounting repair

Sprint `npair-permission-publication-accounting-repair-20261017`, contract
SHA-256 `755aed57c162f46f2d3688bc07ef8ce078fb63da868c697e9b646de9ec4bfb21`.
Primary author Luna/high; repair cap 60 seconds. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN.

Frozen failed-review target:
`tasks/agent-loop/snapshots/20261017-npair-producer-pre-accounting-repair.rs`,
SHA-256 `f1b489b0aaa13718454223d8162893ff0c24f3ad17b790130eb19e0e862ac14d`.
Original implementation handoff remains unchanged at SHA-256
`f24ba90278a70edbf4a601818755b7c43ee67ec34aa67bf0456ebbf359287cb5`.

## Repair

At Permission publication, compute both checked post-transfer values before
state mutation. Once the nested path/concrete-ID allocations are moved into
`formal_permissions`, increase retained `formal_permission_bytes` and subtract
that same byte count from local and graph scratch before sampling resources.
The temporary outer `Vec<FormalPermission>` capacity remains scratch until it
is dropped. This closes the architect's major double-count finding.

Accounting argument:

- Before publication, State does not include the new Permission backing;
  scratch includes fixed recursion buffers, temporary outer capacity and all
  nested path/ID capacities.
- Immediately after publication, State includes the retained Permission
  backing. Scratch subtracts exactly those nested capacities and continues to
  include the outer temporary vector and other recursion buffers.
- After dropping temporary buffers, the remaining scratch envelope is
  subtracted. State continues to count the retained record/backing capacities.
- On failure before publication, no record/backing charge transfers; cleanup
  removes the full scratch envelope. On failure after publication, normal route
  rollback truncates records and restores the checkpointed backing-byte count;
  retained outer vector capacity stays charged as state capacity.

Only `candidate_effect.rs` differs from the failed-review target. Final source
SHA-256: `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`.
`git diff --check` passed. No builds, tests, probes, Cargo or compiler
execution. No source behavior, consumer, provider, `At`, transport, subtraction
or preflight change. Fresh sequential compiler-referee (60s), architect (90s)
and spec-auditor (60s) review of corrected bytes is pending.

Primary STOPPED after freezing this handoff; no descendants. Integration waits
for all three reviewers and Luna adjudication.
