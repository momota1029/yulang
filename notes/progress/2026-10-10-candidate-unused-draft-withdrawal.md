# Candidate unused F5 draft dependency withdrawal

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `939301d65b4255689425f04bb2ff0b3120e001ee`
Authority: [explicit active withdrawal policy](../design/2026-10-10-simple-sub-legacy-withdrawal.md)
Mode: M1; one implementer, one independent regression reviewer
Measurement budget: zero samples/processes

## Actual removed dependency

`InferenceSession::try_new` previously reserved legacy `DraftScheme` scratch
even for graph inference. This allocation was unused: candidate SCC execution
returns into graph staging before every mutable legacy draft consumer.
Candidate startup could nevertheless fail if the unused Drafts reservation
failed. The existing `legacy_closed` owner condition now guards both its capacity
read and reservation. Candidate graph staging already owns its captured graphs;
no additional staging mechanism or inference restriction was introduced.

Default inference and historical `CandidateValueObservation` retain the actual
legacy owner and its fallible reservation. The empty candidate vector remains
in shared storage/accounting; removing an unused reserve does not fabricate
closed results or declare public F5 migration complete.

## Review and verification

`remaining_legacy_dependency_map` localized the unused lane and distinguished
it from genuine legacy public clients and already-symbolic retained-expression
graph recipes. `candidate_unused_drafts_withdrawal` changed only solver `lib.rs`.
Fresh `candidate_unused_drafts_review` verified the frozen hash, direct callers,
draft consumers, sampled resource fields, genuine candidate tests, legacy
control and panic-safe TLS cleanup; no findings. Existing assertions, public
signatures, fixtures and diagnostic expectations are unchanged.

All Cargo commands used `RUSTC_WRAPPER=`, `timeout 180`, `--offline`, `-j 2`;
tests used `-- --test-threads=1`. One Cargo process ran at a time.

- `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_lifecycle_retirement`: 7 passed.
- Same feature, `--lib f5b_reserve_lanes_fail_before_publication_and_clean_retry_preserves_committed_handles`: 1 passed.
- Same feature, `--test candidate_lifecycle_retirement`: 2 passed.
- `cargo check -p yu-solver`: passed.
- `cargo check -p yu-solver --all-targets --all-features`: passed.
- Scoped whitespace and frozen hash checks passed.

Ten distinct tests pass without warnings. New controls arm the unused lane,
solve actual candidate source with nonempty exports/two fresh uses/two Calls,
then prove the still-armed failure is consumed by ordinary solve with atomic
owner release and clean retry. A nonempty SCC input verifies candidate draft
capacity and sampled retained bytes stay zero. Default failure coverage still
includes the legacy Drafts lane.

This removes startup allocation and constant bookkeeping; it adds no traversal,
clone, cache or hot-path work. No benchmark was warranted. The workspace check
at the immediately preceding coherent producer boundary remains historical
evidence; it was not repeated for this one-owner guard. Broad solver/backend
suites and complete semantic proofs were not run.

## Remaining requirements and records

No theorem was proved, retired or marked closed by this resource change.
Complete Call, effect hygiene, soundness, principality, actual execution and
attachment suppliers, independent public schemes and target `yulang3` default
replacement remain required. Historical observer/default closed owners remain
actual callers requiring separate migration.

Synchronized: `tasks/current.md`, design index, withdrawal authority's
implementation status and the original withdrawal delivery. Pending question
directories remain unstaged/uncommitted.
