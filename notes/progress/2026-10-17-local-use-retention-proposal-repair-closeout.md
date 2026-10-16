# Local-use retention proposal repair closeout

Sprint: `local-use-retention-proposal-repair-20261017`, revision 1,
contract SHA-256 `8d1bd53dab64ae049a04ca506bc75f469479de3b7b4a525d6f1c0900c9578cb4`.
Outcome: **ENDED — PROPOSAL REVIEWED; IMPLEMENTATION APPROVAL PENDING**.

## Frozen proposal

Design: `notes/design/2026-10-17-local-use-retention-code-contract.md`,
SHA-256 `1dd2bab703624a51d50dca95e35ffbddd117b940bf95aca6b9b610f7d0425c2a`.
Handoff: `tasks/agent-loop/inbox/20261017-local-use-retention-code-proposal-repair.md`,
SHA-256 `e2a0f6afafbb74785d2d5c7bc16753cbbfb0a9ef6d2b01b6b37897e808331c4d`.
The prior proposal and handoff are preserved as immutable snapshots in
`tasks/agent-loop/snapshots/20261017-local-use-retention-proposal-pre-repair.md`
and `tasks/agent-loop/snapshots/20261017-local-use-retention-proposal-handoff-pre-repair.md`.

The corrected patch keeps `LocalFreshRoute.rows` as its single existing owner,
moves the other eight `FreshUse` fields once into a route-owned record, and
accounts route header, row capacity and non-row backing capacities exactly once.
Existing `shadow_apply` and test field accesses remain unchanged. The patch is
unapplied. Retaining construction maps increases session memory and may cause
earlier resource-limit rejection; the practical envelope and overhead are
unmeasured, and no unchanged resource-acceptance claim is made.

## Independent reviews

- Architect delta: **CLEAN** within source applicability, commit/rollback and
  accounting scope. All supplied artifact/source pins matched. `rows` remains
  the only row-vector owner and all other fields move exactly once. Runtime,
  allocator overhead, lifetime and invalidation remain unverified.
- Spec audit: **CLEAN** within semantic and authority scope. Corrected M2 still
  claims equality only for valid pinned-`v0` evaluations; invalidation is
  separate. The maps do not establish Permission, At, provider lineage,
  consumer/subtraction or parent closure. Explicit user approval remains
  required before compiler code.

Both reviewers STOPPED. Their full receipts were returned directly to Luna and
summarized in `tasks/agent-loop/current.json`.

## Limits and accounting

No compiler or test file changed. No tests, builds, probes, Cargo or compiler
execution ran. `python3 tools/agent_sprint.py check` passed as static protocol
consistency only. Proof M2 remains CLEAN only in its finite conditional scope;
whole native `rho_u`, source/native adequacy, the original parent, the actual
consumer and production remain OPEN.

Charged: Luna proposal repair 120s, architect 90s, spec auditor 90s and closeout
coordination 30s = 330s. The remaining 30s reserve is retired; no budget carries
over. The prior proposal sprint ended PARTIAL, with its unused 240s retired.

The foreign modified file `tasks/agent-loop/sprints/authentic-source-and-forward-handler-20261017.json`,
three historical UNKNOWN reservations and quarantined board lease remain
preserved. Luna is waiting for the user's decision on the exact proposal and
its memory/resource tradeoff. No code lease is active.
