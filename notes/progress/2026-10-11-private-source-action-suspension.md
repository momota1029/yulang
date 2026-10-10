# Private source-action suspension slice

Date: 2026-10-11
Status: reviewed bounded continuation implementation; lower operations and full lifecycle remain synchronous/open.
Authority: `notes/design/2026-10-11-private-candidate-suspension-contract.md`, §§2–3 and §6.
Baseline: `abdec245c9efc3d8a02c0f5e0865af1d5163a643`.

## Implemented behavior

Candidate source execution now has a retained private action frame containing
the original loose/root schedule, next action index, construction/publication
stage, and synthetic wait. `LocalAnnotation` and `Install` retain the exposed
term after construction and publish it in a separate step. Completed local-use
actions stay behind the cursor, so a wait after one use does not freshen it a
second time. An unchanged wait returns before source work and resource sampling.

The route journal snapshots an already-existing source frame and restores its
cursor, stage, retained term, and wait on rollback. Local-slot undo is retained
with it. Active source-frame and route-snapshot bytes are included in resource
sampling. Synchronous source callers still pass `Support::READY`; only private
tests inject the synthetic boundary wait.

## Review and verification

Selected mode: M2 for the source cursor crossing construction/publication and
route rollback ownership. A compiler-referee found no in-slice semantic or
transaction finding. A spec-auditor found no conformance issue in this slice.
Both reviews excluded lifecycle invalidation/recomputation, lower-operation
suspension, production recognition/readiness, and §7 closure. No separate
performance review was needed: the source frame and route snapshot are
fixed-size, action advancement is constant work, and repeated wait performs no
work or sampling.

Focused checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 source_local_annotation_wait_retains_construction_and_restores_prior_frame_on_failure -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 source_cursor_wait_after_completed_local_use_does_not_freshen_it_again -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --offline --jobs=1
git diff --check
```

Both tests use real parsed source schedules with a synthetic wait token; they
do not supply source recognition or certificate evidence. The tests emitted
three existing dormant warnings for `RetainedInput` fields,
`CircuitEvidence.parents`, and `owned_bytes`; these remain assigned to the
future certificate consumer. No broad suite or benchmark was run.

## Remaining gate

This slice does not retain freshening, bound restoration, replay, typed drain,
Function dispatch, extrusion, or recomputation across suspension. It has no
lifecycle mutation generation, authenticated support registry, selective
withdrawal, dependency-ordered recomputation, or resumable SCC publication.
The q113 source decision remains open. The conditional restoration proof and
incidence mutation audit identify a deferral boundary: cross-component changes
that alter an unfinished frame's owner/vector/fiber incidence must be deferred
until the exact dependency owner is implemented and the correspondence closes;
ordinary same-boundary callback mutation must preserve live-index behavior.
The §7 source audit found no authentic certificate/observation join and no
source-owned late Function/swap witness. Production certificates remain
disabled.

Next implementation seam: join lifecycle generation and exact support/consumer
registration to the source cursor, then retain the fresh-use restoration and
typed-child handoff so invalidation can withdraw and recompute earlier completed
children before the saved continuation. Keep the authentic §7 source join as an
open requirement, not a synthetic test result.
