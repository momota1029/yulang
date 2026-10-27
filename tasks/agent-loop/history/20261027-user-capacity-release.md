# User-directed release of stale assignment capacity

Date: 2026-10-27
Authority: explicit current-user instruction to release the quarantined
reservations, add the rule, and synchronize with running agents.

## Live-roster synchronization

The collaboration roster was inspected before the override. `/root` was the
only RUNNING agent. Every listed child was completed; none was RUNNING or
WAITING, so there was no live child to notify or await. The nine legacy IDs
below were absent from the live roster.

## Capacity disposition

The user explicitly released the administrative capacity reservations for:

- `/root/resident_dispatcher_loop_a`
- `/root/resident_implementer_idle`
- `/root/runtime_source_supplier_proof`
- `/root/handler_graph_recursive_trace_review_astra_r2`
- `/root/handler_recursive_trace_review2_astra_r2`
- `foreign/01a17150-2005-7562-81fd-359b3e7a268c`
- `foreign/01a17251-405f-7c81-8d75-ce784095f7c8`
- `foreign/01a17251-2e11-78d0-8779-8219addb6b37`
- `/root/r63_view_coverage_review`

Their worker observations remain `UNKNOWN`; this receipt does not claim that
they stopped. Historical writer paths remain quarantined and unavailable for
reuse. The `/root/r63_view_coverage_review` inbox lease is recorded as
`QUARANTINED`. The override releases resource-capacity accounting only.

## Rule changes

The explicit-user capacity override and required live-roster synchronization
were added to `AGENTS.md`, `rules/goal-driven-sprints.md`, and
`tasks/agent-loop/README.md`. No compiler source or proof artifact changed, and
no new agent was started by this maintenance action.
