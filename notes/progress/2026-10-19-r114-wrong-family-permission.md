# R114 closeout: wrong-family permission input boundary

**Status: CLOSED_INPUT_BOUNDARY_PARTIAL_REVIEWED; fixed packet NOT_RUN.** Rev1
pre-edit review was CLEAN, but the proof producer found a new required owner:
HIR source-key construction delegates to unpinned
`source_identity::{source_keys,try_source_keys}`. That owner is needed to prove
the `signal` and `other` declarations have distinct authentic IDs for this
source. Rev1 says a new required owner stops the packet, so Luna did not read it
or expand the pin set.

## Reviewed partial evidence

A fresh independent compiler/source review returned CLEAN for the conditional
runtime consumer argument only. Given authentic distinct family IDs, row
`[other]` is projected to the receiver, the program's Lambda excludes the
closed-primitive bypass, and `Receiving::local_grant` returns false for request
family `signal` because that family is absent from the row. If the request
reaches the matching catch with that receiving boundary, the runtime returns
`HandlerEvidence` before result publication.

The distinct-ID constructor premise, request/catch reachability, complete
source-to-runtime correspondence and public CLI result remain OPEN. The
implementation worker created the leased test and handoff before the stop
arrived; both are **FROZEN_UNVERIFIED**. No test, build or CLI command ran. The
one-shot R114 command remains **NOT_RUN** and has no retry authority.

- [R114 rev1 contract](/home/momota1029/rust/yulang/tasks/agent-loop/sprints/cli-wrong-family-permission-20261019-r114-rev1.md), SHA-256 `7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`.
- [Conditional proof note](/home/momota1029/rust/yulang/notes/theory/2026-10-19-r114-wrong-family-permission.md), SHA-256 `447875018fee0f7a7e131658223ea9e7066b860fe8e8c3c35513877edf795f92`.
- [Proof handoff](/home/momota1029/rust/yulang/tasks/agent-loop/inbox/20261019-r114-proof.md), SHA-256 `1e557c2adbcf53861701fa0a11679124fde1ebf87606a35624c923be6eba3f18`.
- Frozen unverified test: [cli_permission_boundary.rs](/home/momota1029/rust/yulang/tools/inference-playground/tests/cli_permission_boundary.rs), SHA-256 `3efcf117612a513250a4396f5f21c15a0a3b2b89ac4ce27518979df8b3b93f13`.
- Frozen implementation handoff: [R114 implementation receipt](/home/momota1029/rust/yulang/tasks/agent-loop/inbox/20261019-r114-implementation.md), SHA-256 `6eecb772e7ee30d7582c1f5d89b47e9310273f18a393c550f464f67960cf609e`.
- Independent conditional source review: [R114 compiler review](/home/momota1029/rust/yulang/tasks/agent-loop/inbox/20261019-r114-compiler-review.md), SHA-256 recorded in current state. Luna transcribed the read-only reviewer message.

This packet changes no language or production semantics. It closes only as a
hard input-boundary stop with conditional reviewed evidence. R113 remains
NOT_RUN at its separate literal-decoder boundary; R111 remains
NOT_RUN/FROZEN_UNVERIFIED; R112's finite method/role constructor obstruction
and R100-P2 remain OPEN. The six-front effect goal, proof-backed method/role
behavior and runnable ordinary/effectful source remain active.

## Next frontier

The boundary selector recommends ordered handler priority through a successful
public source execution. This is a different effect front from R113/R114.
Before dispatch, Luna must pin an exact approved source with competing handler
candidates, the governing order rule, and every constructor/consumer owner,
including any literal conversion and result conversion. The next packet must
not repeat R109's failed range assertion or infer general hygiene from one run.
