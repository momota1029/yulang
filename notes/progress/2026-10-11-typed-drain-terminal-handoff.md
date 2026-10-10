# Typed-drain terminal acknowledgement and parent handoff

Date: 2026-10-11
Status: reviewed internal synchronous continuation foundation; full suspension lifecycle remains open.
Baseline: `1ef31cb07ca370ba9a7b80b125f7450f01006cf8`.
Authority: `notes/design/2026-10-11-private-candidate-suspension-contract.md`, §§3–6.

## Implemented slice

The retained typed-drain frame now has explicit acknowledgement and return-ready
stages. It resumes from its completed-acknowledgement cursor, and the pre-pop
owner records which child acknowledgements have current-route undo prepared.
After a transaction commits a partial terminal prefix, the retained frame resets
that preparation frontier to the completed cursor so a later route prepares its
own undo before continuing.

Terminal completion transfers the exact replay handle to its existing
restoration owner. A retired final replay remains retained while that parent
points to it; restoration advancement releases the handle in the existing
order. Route rollback restores a pre-existing typed-drain frame, including its
stage, cursors, acknowledgement allocation and stack position. The active and
undo storage are included in retained-byte accounting.

The terminal path samples resource usage when retained allocation grows, before
acknowledgement or frame removal can release that storage. Unchanged
acknowledgement and return-ready transitions do not trigger another full
resource traversal. Completion reuses the pre-pop acknowledgement reservation;
the terminal loop adds no per-child undo-journal search or allocation.

Tests cover partial acknowledgement, an injected preparation failure, commit
and resume from the saved cursor, rollback of pre-existing frames, final-child
and empty-batch ownership in transactional and nontransactional routes, and a
cold-capacity resource-ledger peak.

## Review and verification

The packet received a pre-write spec audit. Initial post-write compiler-referee
and spec-auditor reviews found one resource-ledger major and one duplicate
completion-reservation minor. Structural performance review identified
per-acknowledgement journal scans and unnecessary full resource samples. One
batched repair added an owner-local prepared cursor and growth-triggered
sampling. Delta compiler-referee and performance-auditor reviews found no
remaining blocking, major or minor findings.

Checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 typed_drain_terminal_ -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 queued_replay_child_waits_for_successful_typed_drain_and_rolls_back_both_cursors -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 retained_restoration_retries_saved_opposites_without_reemitting_accepted_bound -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 restoration_previous_replay_pointer_controls_reclamation_and_rollback_bytes -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --offline --jobs=1
git diff --check
```

All focused tests and the no-feature package check passed. The feature test
build emits the three existing dormant retained-input `dead_code` warnings;
their production consumer remains disabled. No benchmark or timing measurement
was run; the performance review closed the observed work-multiplication risks
structurally. No workspace-wide suite or format rewrite was run.

## Limits and next gate

This slice adds terminal retained-state machinery without an outward
`Suspended` result. It does not make typed work interruptible inside dispatch,
diagnostic helpers, replay generation, freshening, or bound restoration. It
does not add lifecycle observation withdrawal/recomputation, incidence
deferral, or source/SCC continuation. The authentic source-owned §7 regression
and production certificate readiness remain open; certificates remain
disabled. q113 A/B, full Simple-sub inference, soundness/principality, and F5
cutover also remain open.

Next gate: join a resumable local-use freshening/restoration chain to the
retained typed-child driver, preserving exact source identity and saved live
opposite-index behavior. Defer external incidence changes that can alter a
suspended frame until their footprints establish the required disjointness.
