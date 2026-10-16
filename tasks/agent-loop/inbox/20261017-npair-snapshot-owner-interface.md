# Frozen readiness handoff

Sprint `npair-snapshot-owner-interface-20261017`, revision 1, contract SHA-256
`243525db31b3999778f6fd79eeb3de52399cff0e1a864c555615bb55bf6afed5`.
Assignment `NPAIR-SNAPSHOT-OWNER-INTERFACE-20261017`, handoff revision 1.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

Author: Luna/high primary; current-session. Exact output leases are this handoff
and `notes/design/2026-10-17-npair-snapshot-owner-interface.md`. Requested
model/effort Luna/high; observed settings UNKNOWN. Readiness cap 240s.

Outcome class: read-only owner-interface readiness Draft. The complete relevant
state is owned by `InferenceSession`/`GraphState`, `candidate_effect::State`,
`candidate_context::State` and a selected route graph. Safe `&InferenceSession`
borrowing can exclude `&mut` changes, but existing accessors do not expose all
required evidence. `CircuitEvidence<'a>` is a selected partial relation closure;
it omits full physical BoundEvidence and private FormalPermission records.
BoundEvidence and formal-permission accessors, plus a successful route
quiescence/selection gate, remain to be designed and independently proved.

The design supplies an owner-bound private aggregate proposal, exact field and
mutation table, complete-evidence enumeration, shared iterative witness DAG,
cycle/failure handling, repeated-scan and capacity accounting requirements.
Proposed access is not implemented; no compiler code, API, semantic or
production authority is granted. The independent Sol/high proof lane must now
verify borrow ownership, quiescence, mutation exclusion, full evidence and
expiration before rollback/reuse. The proof must distinguish existing access
from proposed access and may return an exact blocker.

Frozen design SHA-256: `45b789c89c81cf335b25e6ff79b622572cf5d6e4d58932023ab8fe7843225e27`. This readiness
handoff does not close the parent or authorize validator implementation. No
tests, builds, probes, Cargo or source/compiler execution.
