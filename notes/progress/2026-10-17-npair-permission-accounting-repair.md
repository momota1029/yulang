# NPAIR Permission publication accounting repair

The approved concrete-only producer patch was adjudicated and integrated as a
bounded producer result. This does not close `CHOOSE-SOURCE-2 /
RECEIVE-NEGATIVE-PAIR-20261017`: authentic source preflight still refuses the
negative form, and source admission, authentic `At`, transport, consumption,
subtraction and production remain open.

## Before and after

The applied producer initially published nested Permission path/ID allocations
into retained state while their byte charge remained in candidate scratch. The
architect review identified that the post-publication sample could count the
same backing allocations twice. The failed target is preserved byte-for-byte
at `tasks/agent-loop/snapshots/20261017-npair-producer-pre-accounting-repair.rs`
(SHA-256 `f1b489b0aaa13718454223d8162893ff0c24f3ad17b790130eb19e0e862ac14d`).

The repair transfers exactly the retained Permission backing charge out of
scratch before resource sampling. The temporary outer vector remains scratch
charged until drop. Both subtractions and retained-byte addition are checked
before publication; checkpoint rollback truncates retained records and restores
the retained backing-byte count. Publication remains after links 43/44.

Corrected source: `crates/yu-solver/src/candidate_effect.rs`, SHA-256
`11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`.
Repair handoff: `tasks/agent-loop/inbox/20261017-npair-permission-accounting-repair.md`,
SHA-256 `5cc00163e67e3129b4fc57d59c89575644ea6c6258be39ec0f5988f7dc90a68f`.
The fixed contract is
`tasks/agent-loop/sprints/npair-permission-publication-accounting-repair-20261017.md`,
SHA-256 `755aed57c162f46f2d3688bc07ef8ce078fb63da868c697e9b646de9ec4bfb21`.

## Review and limits

Fresh sequential compiler-referee, architect, and specification reviews were
all CLEAN on the corrected frozen bytes. They verified the approved concrete-
only scope and the accounting/rollback/publication boundary. Primary
adjudication accepts this bounded repair. Static resource accounting is
reviewed; runtime resource-boundary behavior remains unverified.

No tests, builds, probes, Cargo, or compiler execution ran. The only check was
`python3 tools/agent_sprint.py check` (static consistency, not independent
review or live execution), which passed. The earlier approved implementation
and its source/seed proof artifacts are preserved with the sprint records.

The correction envelope used 300/360 seconds: repair 60, three reviews 210,
and coordination 30. The unused 60-second reserve is retired; no allocation
was transferred from predecessor sprints. Three historical UNKNOWN worker
reservations and the quarantined board lease remain preserved.

Next, revisit the receive obligation using the full retained producer evidence
and establish a constructive descriptor-to-seed association, or name the exact
missing producer field/event. Keep source admission and parent closure OPEN.
