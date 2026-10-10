# Owned typed-drain continuation foundation

Date: 2026-10-11
Status: reviewed synchronous implementation checkpoint; full suspension lifecycle remains open.
Authority: `notes/design/2026-10-11-private-candidate-suspension-contract.md`, §§2–4 and §6.
Baseline: `919864319bf216d9b8803dd1095941a571f78e78`.

## Implemented slice

The shadow candidate context now retains an owned typed-drain frame while one
synchronous drain runs. It records the popped work item and transported
relation, provenance and processing scopes, dispatch stage, transition count,
Function children and enqueue cursor, plus deferred replay acknowledgements.
Function-port admission and queue insertion are separate retained steps, so a
child relation survives an enqueue failure. Frame and acknowledgement storage
is reserved fallibly, included in retained-byte accounting, and route-created
frames are removed on rollback. A regression exercises the admitted-child
ordering, enqueue cursor, byte census, rollback and retry.

The accounting repair records acknowledgement-buffer capacity growth before a
later fallible replay-completion undo reservation can drop the frame. Its
failure-injection regression verifies the transient peak, queued-versus-consumed
cursor, rollback and successful retry.

This remains a synchronous foundation. There is no suspended `CandidateRun`,
resume driver, source/freshening/extrusion/recomputation frame, lifecycle
generation or observation withdrawal, or resumable SCC publication. Existing
drains pop their frames before returning. Production certificates remain
disabled, and the source-owned §7 late-Function/swap scenario remains required.

## Review and verification

The compiler-referee delta review closed the accepted event-time accounting
finding and found no new finding within the repaired delta. The initial
compiler-referee review had identified the transient acknowledgement-buffer
peak; the repair and focused failure-injection witness address it. The
spec-auditor found no issue in the synchronous slice. The performance auditor
found the added census scan costs Θ(D) per retained-resource sample for D live
typed drains; the inspected synchronous source paths have at most one active
drain. It recommended retaining the direct scan and reassessing if later
suspension makes nested live drains possible. Reviewers did not certify the
future lifecycle or source completeness.

Checks run on the repaired code:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-apply-candidate --offline --jobs=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --offline --jobs=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 replay_completion_undo_failure_samples_transient_ack_buffer_before_drop -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 owned_function_dispatch_retains_admitted_child_until_enqueue_and_rolls_back -- --test-threads=1
git diff --check
```

All listed checks passed. The feature check emitted three existing dormant
warnings (`RetainedInput` fields, `CircuitEvidence.parents`, and `owned_bytes`);
these remain assigned to the future certificate consumer. No broad test suite,
benchmark or timing measurement was run. `cargo fmt --all -- --check` and
individual whole-file `rustfmt --check` attempts did not pass because of
pre-existing format drift across unrelated repository files; no formatter
writes were made.

## Next gate

Implement the actual owned continuation/resume and lifecycle owners: observation
support registration, selective withdrawal and ordered recomputation, rollback
of mutations to pre-existing frames and graph/frontier state, then atomic SCC
publication. Preserve the independent restoration-correspondence proof and
observation-owner audit as bounded evidence only. Do not enable certificates
until the authentic source-owned §7 regression and required review close.
