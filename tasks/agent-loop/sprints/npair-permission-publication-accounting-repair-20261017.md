# Sprint: NPAIR Permission publication accounting repair

ID: `npair-permission-publication-accounting-repair-20261017`.
Status: READY; source write starts only after pins and pre-repair snapshot verify.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Primary: Luna/high, sole writer and Git integrator.

## Fixed outcome

Repair the major finding in the approved concrete-only producer: when
Permission path/ID backing allocations move from temporary records into
retained `EffectAlgebraState`, transfer their byte charge from
`CandidateGraph::scratch_bytes` before the post-publication resource sample.
Keep only the temporary outer vector's capacity in scratch until that vector is
dropped. Demonstrate by static accounting that each backing allocation is
charged once before publication, once as retained after publication, and zero
after route rollback. No source semantics or representation changes.

Parent remains OPEN. The approved producer, source preflight refusal, explicit
empty/mixed/multiple-symbolic refusals and separate NPAIR authentication,
consumer, transport and subtraction gates stay as they are.

## Frozen target and dependencies

Failed applied target, preserved byte-for-byte at
`tasks/agent-loop/snapshots/20261017-npair-producer-pre-accounting-repair.rs`,
SHA-256 `f1b489b0aaa13718454223d8162893ff0c24f3ad17b790130eb19e0e862ac14d`.
Original implementation handoff remains frozen at
`tasks/agent-loop/inbox/20261017-npair-concrete-producer-implementation.md`,
SHA-256 `f24ba90278a70edbf4a601818755b7c43ee67ec34aa67bf0456ebbf359287cb5`.
The predecessor continuation contract SHA is
`54bb2bc76e518fb01ad66ec0f21426a0d623aa7d533ad09e0dda87af2594c239`.
Its applied review target is **not** the target of this sprint.

Architecture finding by `/root/npair_producer_applied_arch_review`:
after `formal_permissions.extend(permissions.drain(..))`, nested backing bytes
remain charged in `graph.scratch_bytes` while `State::bytes` includes them in
`formal_permission_bytes` at `sample_f4_resources`. The reviewer observed
double-counting; a false resource-limit refusal is a possible but unverified
consequence. Exact repair site is only `candidate_effect.rs` publication.

The allowed code owner is the pre-repair source hash above. Before writing,
verify it again, verify the preserved review/handoff and predecessor pins, and
record Luna's current-session active receipt. A source mismatch stops this
packet.

## Lanes and exact leases

Luna/high repair cap: 60 seconds. Write only:

- `crates/yu-solver/src/candidate_effect.rs`
- `tasks/agent-loop/inbox/20261017-npair-permission-accounting-repair.md`

Create and freeze the exact pre-repair source snapshot before editing:

- `tasks/agent-loop/snapshots/20261017-npair-producer-pre-accounting-repair.rs`

Fresh sequential reviewers of corrected bytes: compiler_referee 60s,
architect 90s, spec_auditor 60s. Each verifies source/handoff/snapshot hashes;
architect reconciles before-publication, after-publication, temporary-drop and
rollback accounting. Authors/reviewers STOP between lanes. No worker
descendants.

Coordination cap 30s; reserve 60s. Fresh envelope total 360s. No time transfers
from the completed predecessor (2260s charged; unused 80s specification review
and 60s reserve retired) or authenticated-seed sprint (1440s charged).

## Non-goals and stop conditions

No build, test, probe, Cargo or compiler execution. No second source file,
semantic change, new registry/identity, consumer, At, transport, subtraction,
source preflight, expected-output or fixture change. Stop before any expanded
edit or if the correction cannot preserve the approved transaction/rollback
boundary. Do not integrate until all three fresh reviewers are CLEAN and Luna
adjudicates. Keep the source unintegrated otherwise.
