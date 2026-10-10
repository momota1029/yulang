# Local-use freshening and restoration continuation slice

Date: 2026-10-11
Status: reviewed conditional internal continuation; production suspension and §7 remain open.
Source baseline: `18f13d938be7e7c85df8525c5dd2fb6a4c999671`
Branch at integration: `research/simple-sub-intrusion`

## Scope and authority

This M2 slice implements the next existing Authoritative gate under the private
candidate suspension contract §§3–6 and contextual attachment/admission §§4–6.
The Local route now retains the captured graph, one fresh-use identity and its
post-construction remaps, ordered bound cursor, current restoration handle, and
final publication stage in candidate-owned state. The production wrapper still
drives synchronously to completion. Only a closed `cfg(test)` script injects
committed pauses; it holds one exclusive mutable session borrow and offers no
external incidence mutation, Support/READY decision, or production
`CandidateRun::Suspended` outcome. Capture, remap construction, replay batch
generation, typed Dispatch/Function, diagnostics, and child terminal processing
remain atomic.

Each captured bound is admitted once. The LocalUse parent records its returned
restoration handle before the next step; saved opposite count and live
canonical-owner/direct/exact indexed reads remain in the existing restoration
owner. The parent advances only after that owner returns completion. The final
value link and `LocalFreshRoute` publication occur once, before the source
cursor advances. Continuation and restoration-undo storage are included in
retained/resource accounting.

Publication growth exposed a rollback-capacity defect during verification.
The repair retains the prior `local_routes` allocation in the route journal,
moves its entries into a geometrically grown replacement, restores the old
allocation without allocation on rollback, and drops it only after commit.
Existing rollback/accounting assertions were preserved. Moving entries occurs
only on capacity growth, for amortized O(1) publication and no graph/row clone.
Both active and undo capacity are included in route resource samples.

## Review and verification

The pre-write spec audit found no new semantic decision and required ownership
of the exact LocalUse state, live indexed restoration, completion-before-parent
advance, and rollback of pre-existing frames. The first frozen review round
used a compiler-referee and spec-auditor. The compiler-referee found no issue;
the spec-auditor identified the publication-capacity rollback defect above.
After the batched repair, a fresh compiler-referee closed that finding by source
inspection and found no material growth-path performance risk. The test-only
cross-session result comparator was separately pre-write checked: independently
collected terms must be validated in their own stores and compared by their
structure because arena brands differ. That comparison does not claim
provenance parity.

Passed focused checks:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 --lib parsed_local_use_retains_one_fresh_parent_across_committed_pause_and_failed_resume -- --test-threads=1`
- `... --lib internal_restoration_owner_steps_keep_multiple_live_products_and_return_ownership -- --test-threads=1`
- `... source_cursor_wait_after_completed_local_use_does_not_freshen_it_again -- --test-threads=1`
- `... --lib typed_drain_terminal_ -- --test-threads=1` (3 tests)
- `... --lib retained_restoration_retries_saved_opposites_without_reemitting_accepted_bound -- --test-threads=1`
- `... --lib restoration_previous_replay_pointer_controls_reclamation_and_rollback_bytes -- --test-threads=1`
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --offline --jobs=1`
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-apply-candidate --offline --jobs=1`
- `git diff --check`

The focused Local test initially found the capacity rollback failure, then a
test-only false mismatch from comparing branded handles across separately
collected sessions. Both were repaired without weakening the rollback
expectation or changing test names. Final focused and package checks passed.
Feature-enabled compilation still reports three existing `dead_code` warnings
for the disabled retained-input certificate consumer (`RetainedInput` payload,
`CircuitEvidence::parents`, and `owned_bytes`). Production readiness remains
incomplete; those warnings are recorded at that owning gate. No formatter,
benchmark, or broad test suite ran. Measurement budget: zero benchmark
processes and zero samples.

## Closure boundary and next gate

This closes only the conditional LocalUse parent/accepted-restoration seam and
its exact rollback/accounting path. The internal test script is not evidence of
an authentic §7 source certificate. Production support/readiness/filter and
dependent-observation registration remain incomplete; no production
suspension, cross-component incidence deferral, invalidation/withdrawal and
recomputation, or resumable SCC publication is enabled. The typed drain still
runs atomically. The falsified future nonterminal Dispatch/Function case still
requires re-preparing the outstanding acknowledgement prefix after a commit
before resumed side effects, pops, or another acknowledgement append.

Next gate: close that nonterminal acknowledgement-prefix ownership under the
suspension contract, while preserving terminal-only reset semantics; then
continue with lifecycle/deferral ownership and the authentic source-owned §7
regression. q113, complete Simple-sub inference, soundness/principality, and F5
cutover remain open.
