# Frozen implementation handoff: concrete-only NPAIR producer

Sprint: `npair-concrete-producer-realization-20261017`, continuation revision 2,
contract SHA-256 `54bb2bc76e518fb01ad66ec0f21426a0d623aa7d533ad09e0dda87af2594c239`.
Assignment: Luna/high primary, maximum 1080 seconds. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN.

## Approval and applied scope

The user approved the exact bounded producer proposal by replying
“採択で構いません” to its approval request. Pinned approval receipt:
`notes/progress/2026-10-17-npair-concrete-producer-approval.md`, SHA-256
`cd81ea1385b1304da283ef8ee15cdd626b98d1759cf79aa372f672e53c5bab67`.
Effective reviewed design SHA-256:
`a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce`.
Revision-3 compiler/architecture/spec handoff SHA-256:
`6ec84d409f261345ab682c1d37b6d41126fb7d69fff2577ab580bc92a295c3d1`.

Only `crates/yu-solver/src/candidate_effect.rs` changed. It adds an internal
negative-pair predicate for nonempty concrete-only rows; creates one fresh
shared effect row for both polar projections; retains source-owned inert
Permission records with owner, parameter, occurrence, scope, typed Function
path, source row key and concrete IDs; and preserves the original four-step
construction/allocation order and links 43/44. Permission records publish only
after both links succeed. The existing Checkpoint stores vector length and
backing-byte snapshots so route rollback truncates records and restores
accounting. Source preflight refusal, root computation effects and all other
source cases are unchanged.

The record is not consumed by this patch. It does not authenticate an arrival,
provider, original semantic `w`, `At`, transport, a consumer or subtraction.
Mixed, multiple-symbolic and explicit-empty cases remain refused by this
bounded producer. Parent/source/native/production gates remain OPEN.

## Accounting and validation

Owned record storage counts the retained vector capacity plus the capacities
of each typed path and concrete-ID vector using checked arithmetic. Cloned
source/owner/scope identities retain shared immutable Arc-backed payloads; no
new registry or identity allocation is added. Temporary permission paths and
IDs are included in scratch accounting. Checkpoint snapshots require no
additional dynamic undo vector.

Static checks: `git diff --check` passed. `rustfmt --check` parsed the file but
reported widespread formatting differences in the pre-existing file; it did
not modify source. No tests, builds, probes, Cargo or compiler execution were
run, as prohibited by this contract.

Applied source SHA-256: `f1b489b0aaa13718454223d8162893ff0c24f3ad17b790130eb19e0e862ac14d`.
The other three direct producer source hashes remain equal to the frozen
continuation pins. Fresh sequential review of the applied bytes remains
required: compiler referee, architect and spec auditor, each with an 80-second
cap. Previous reviews concern only the unapplied design.

Luna/high primary STOPPED after freezing this handoff. No descendants or other
writers. Review and integration remain pending.
