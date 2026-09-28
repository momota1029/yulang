# F5c family-1 and family-6 owner-event checkpoint

Status: family-1 live-variable events and family-6 streaming owner events are
implemented in the resource-probe configuration, independently reviewed, and
verified with focused tests and checks. The eight-family gate remains open;
family 3 is next. No preflight, matrix row, benchmark, or scale process ran.

Authority: the Authoritative
[`F5c no-numeric-resource-cap addendum`](../design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md)
and the owner coverage map in
[`F5c streaming owner event coverage map`](f5c-streaming-owner-gap-map-2026-09-28.md).

## Checkpoint scope

Family 1 now records stable owner IDs for all ten top-level live-variable
vectors and four nested buffers for each value/effect row. It observes the
sink-open state, mutations, row rollback, finish, and returned-error cleanup.
Terminal current capacity/bytes and same-time owner peaks reconcile to the
family-1 observer tuple.

Family 6 now keeps the same owner ID while a raw walker vector becomes a
tracked union/intersection child vector. The in-process peak sampler suppresses
the intermediate source-plus-walker sample and samples after the walker charge
is released, so the buffer contributes once at the handoff. Raw buffers drop
before release events on fallible local paths and on `F5cGeneralizer` field
drop. The family-aware replay checker accepts family-1 and family-6 owner
events, enforces the family-1 terminal release suffix, and supports repeated
family-6 component checkpoints.

The existing six-buffer `FlatDraft` carrier and same-ID staged transfer remain
the earlier committed boundary recorded in
[`FlatDraft owner carrier checkpoint`](f5c-flatdraft-owner-carrier-checkpoint-2026-09-28.md).
This checkpoint extends that boundary; it does not run the matrix or claim
all-eight-family completion.

## Changed paths and diff units

- Observer, event ownership, and rollback integration:
  `crates/yu-solver/src/lib.rs`,
  `crates/yu-solver/src/f5c_draft_heap.rs`,
  `crates/yu-solver/src/f5c_generalization.rs`.
- Family-6 owner observation and replay integration:
  `crates/yu-solver/src/f5c_binder_substitution.rs`,
  `crates/yu-solver/src/f5c_generalization/flat_source_arena.rs`,
  `crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs`,
  `crates/yu-solver/src/f5c_materialization.rs`,
  `crates/yu-solver/src/f5c_normalization.rs`,
  `crates/yu-solver/src/f5c_replay.rs`,
  `crates/yu-solver/src/f5c_tree_analysis.rs`,
  `tools/check_f5c_resource_matrix.py`.
- Focused event, replay, and failure witnesses:
  `crates/yu-solver/src/tests/f5c_flat_walk_sink.rs`,
  `crates/yu-solver/src/tests/f5c_generalization_transactions.rs`,
  `crates/yu-solver/src/tests/f5c_replay.rs`,
  `crates/yu-solver/src/tests/f5c_resource_probe.rs`,
  `crates/yu-solver/src/tests/f5c_tree_analysis.rs`.

No snapshot, fixture, test name, diagnostic expectation, or semantic assertion
was changed to fit current output.

## Review and verification

Review mode: M2 delta review. Independent compiler and performance reviews
found and closed two ownership defects: adoption temporarily double-counted a
family-6 buffer, and some error/drop paths released owners before raw buffers
were destroyed. A follow-up compiler/spec review confirmed the corrected
same-time transfer, local error cleanup, `F5cGeneralizer` field drop order,
and both union/intersection failed-adoption witnesses. The failure witness
forces the adoption API's returned-error branch directly; it does not inject
that rare checked-accounting error through each of its four production
callers.

The performance review found one test-only `O(C × H)` scan at
`lib.rs:13509`/`f5c_draft_heap.rs:601`, where C is finalized components and H
is the physical-owner registry's high-water slot count. This uses free-list
reuse, is compiled only with `test + f5c_resource_probe`, and has no production
effect. It was not measured in this checkpoint; measure it if probe runtime
becomes material before using large diagnostic runs.

Focused checks passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe raw_walker_transfer_has_one_same_time_buffer --lib --offline -j 2 -- --test-threads=1`
- `RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe failed_raw_walker_adoption_drops_buffer_before_release --lib --offline -j 2 -- --test-threads=1`
- `RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe f5c_boxed_reentry_second_lane_failure_rolls_back_and_retries --lib --offline -j 2 -- --test-threads=1`
- `RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe f5c_live_variable_events_ --lib --offline -j 2 -- --test-threads=1` (3 passed)
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --offline -j 2`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe --offline -j 2`
- `git diff --check`
- A synthetic offline replay containing a family-1 terminal checkpoint/release,
  a family-6 unclassified-to-union transfer, and repeated family-6 checkpoints
  passed `replay_f6_events`.

Measurement budget consumed: zero. No preflight, matrix, benchmark, or scale
process ran. The checked family-peak correction remains unfinished for other
families, including family 3. The next checkpoint implements structured-pair
events and extends the family-aware replay; preflight remains ineligible until
same-time event reconciliation and terminal ownership are complete for every
required family.
