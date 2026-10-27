# User-directed capacity release and live-agent sync

Date: 2026-10-27
Authority: explicit user directive to release the UNKNOWN assignment reservations, add the rule, and synchronize with active agents.

## Live roster

The collaboration roster was checked before applying this directive. `/root` was the only RUNNING agent. Every child was `completed`; no non-primary agent was RUNNING or WAITING, so no child required notification or a cessation wait. The active r2 implementation and proof workers had both returned terminal handoffs and are recorded STOPPED in `current.json`.

## Capacity result

The directive targets the complete UNKNOWN-assignment reservation set. Its nine legacy reservations were already released by the user under `tasks/agent-loop/history/20261027-user-capacity-release.md` (SHA-256 `7d30faa71449af50c50539307b3a11d062735b64d522eac93656467ff94968a8`). This application is idempotent and releases no additional slots. The exact reservation identities are:

- `/root/resident_dispatcher_loop_a`
- `/root/resident_implementer_idle`
- `/root/runtime_source_supplier_proof`
- `/root/handler_graph_recursive_trace_review_astra_r2`
- `/root/handler_recursive_trace_review2_astra_r2`
- `foreign/01a17150-2005-7562-81fd-359b3e7a268c`
- `foreign/01a17251-405f-7c81-8d75-ce784095f7c8`
- `foreign/01a17251-2e11-78d0-8779-8219addb6b37`
- `/root/r63_view_coverage_review`

Their observations remain UNKNOWN and their exact paths remain quarantined. This record makes no claim that they stopped.

## Rule

`AGENTS.md`, `rules/goal-driven-sprints.md`, and `tasks/agent-loop/README.md` now state the capacity-only override, live-roster synchronization and notification requirement, path quarantine, and idempotent accounting.
