# Synthetic source-boundary support ownership

## Scope and authority

This M2 implementation slice follows the Authoritative private candidate
suspension contract §§2–7 and contextual-admission design §§4–6. It gives one
retained source boundary an explicit private support identity and withdrawal
action. Support creation is test-only and does not authorize candidate
certificates.

## Change

The synthetic support registration retains a stable ID, lifecycle generation,
watched relation footprint and validity state. A new exact `FunctionPort`
dependency invalidates registrations watching either endpoint relation. Exact
duplicates and unrelated endpoint mutations leave permissions intact.

Support attaches only to an already constructed `PublishLocal` source frame.
The source driver checks that owner registration before publication. Invalid
support returns a stable suspension while retaining the term and cursor;
caller-supplied `READY` or raw wait generations cannot bypass it. An explicit
replacement registration permits retry. Publication clears the frame
attachment. IDs from rolled-back registrations are never reused.

Context rollback restores pre-existing validity, support membership, lifecycle
generation and source-frame attachment alongside dependency rollback. The
source support records, watched vectors, registration and invalidation logs,
checkpoint frontiers and enlarged frame are included in retained-byte
accounting.

## Review and verification

The pre-write spec-auditor found no blocking conformance issue and supplied
acceptance conditions. Post-write compiler-referee and spec-auditor reviews
found no BLOCKING, major or minor findings in this bounded slice.

Passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 exact_source_support_ -- --test-threads=1` — 3 tests.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 source_cursor_wait_after_completed_local_use_does_not_freshen_it_again -- --test-threads=1`.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 source_local_annotation_wait_retains_construction_and_restores_prior_frame_on_failure -- --test-threads=1`.
- `git diff --check`.

The broader `source_` filter ran 60 unit tests; 55 passed, four were ignored,
and one unrelated F4 resource-accounting test failed. The exact test
`f4_distinct_use_routes_share_one_source_scheme_scale_matrix_is_linear` fails
on the unchanged pinned baseline `f13dbb7ab540c0d566cd03ae4e06bfc6666c8371`
with the same sample-count mismatch (6021 observed vs 6017 expected). No
expectation was changed. This gate does not alter the F4 sampler's call sites.

Focused runs report the three existing dormant-certificate `dead_code`
warnings for retained-input fields/methods. No benchmark or formatter was run
for this slice. The package formatter check had already shown broad pre-existing
drift; no broad rewrite was applied.

## Open obligations

This synthetic source-boundary permission is not a production certificate or
complete support inventory. It does not register memo, replay, physical-bound,
graph-slot, or SCC consumers; suspend freshening, restoration, typed drain,
Function dispatch or extrusion; withdraw/recompute completed sibling
observations; or close readiness, filter, dependent-observation and authentic
§7 source-recognition witnesses. Production certificates remain disabled.
q113 source-state, complete Simple-sub inference, soundness/principality and F5
cutover remain open.

## Next gate

Retain the lower fresh-use/restoration/typed-child continuation and resolve the
atomic replay-acknowledgement/parent-advance handoff. Keep incidence-changing
cross-component mutations deferred unless their read/write footprints prove
disjointness. Then integrate ordered observation withdrawal/recomputation and
atomic SCC publication toward the authentic §7 source regression.
