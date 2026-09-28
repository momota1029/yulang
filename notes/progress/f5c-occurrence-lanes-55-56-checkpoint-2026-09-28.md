# F5c occurrence lane 55/56 checkpoint

Status: verified, reviewable code checkpoint on `yulang3`, based on commit
`1b9e98f6`. This slice closes the isolated occurrence-owner event gap for
`PostROccurrenceOrder` (lane 55) and `PostROccurrenceSeen` (lane 56). It does
not close the surrounding post-R implementation or the all-family event fold.

Authority: the Authoritative F5c no-numeric-resource-cap addendum and the
physical event/peak contract in
[`F5c no-cap scale measurement plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md).
The previously checkpointed raw owner lifecycle in
[`f5c_draft_heap.rs`](../../crates/yu-solver/src/f5c_draft_heap.rs) supplies the
probe-only owner events used here.

## Exact diff unit

- [`f5c_generalization.rs`](../../crates/yu-solver/src/f5c_generalization.rs):
  carries the boxed flat-source meter into the occurrence walk, owns the
  ordered vector until Q scanning finishes, and releases the seen set only
  after its buffer drops. Probe assertions reconcile both public and
  independent counters at each reserve and insert.
- [`f5c_tree_analysis.rs`](../../crates/yu-solver/src/f5c_tree_analysis.rs):
  observes the flat walk's seen-set and ordered-vector capacity/requested-length
  transitions after reserve and insertion.
- [`f5c_draft_heap.rs`](../../crates/yu-solver/src/f5c_draft_heap.rs): adds the
  test-only raw-owner shape assertion used to check live length and capacity.
- [`f5c_flat_walk_sink.rs`](../../crates/yu-solver/src/tests/f5c_flat_walk_sink.rs):
  replays the sidecar trace for boxed, flat, and forced reserve-failure cases;
  checks stable distinct IDs, slot sizes, capacity transitions, terminal
  counters, and lane 56 release before lane 55.

The probe instrumentation and synchronous ledger assertions compile only under
`all(test, feature = "f5c_resource_probe")`. The failed-reserve fixture seeds
lane 55's requested count to `usize::MAX`; its independent count remains zero
because checked overflow returns before updating it. Lane 56's one successful
reserve precedes that failure. No production event schema or resource formula
changes in this slice.

## Review and verification

Selected M1 for this bounded implementation: one independent specification
delta reviewer, no broader review panel. The final review against the four-file
diff was clean. An earlier review's missing intermediate ledger/release checks
were added before this final review.

Checks run in an isolated worktree based on `1b9e98f6`:

- `RUSTC_WRAPPER= cargo test -p yu-solver --lib --features f5c_resource_probe --offline -j 2 post_r_occurrence_owner_events_match_live_lanes_and_failure -- --test-threads=1` (1 passed)
- `RUSTC_WRAPPER= cargo test -p yu-solver --lib --features f5c_resource_probe --offline -j 2 post_r -- --test-threads=1` (9 passed)
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --offline -j 2`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe --offline -j 2`
- `git diff --check`

The new `f5c_generalization.rs` hunks were formatted manually. A whole-file
rustfmt check was omitted because that file already has unrelated formatting
drift outside this diff; `f5c_tree_analysis.rs` and the touched test file were
formatted. No broad suite, benchmark, preflight, or scale process ran;
measurement budget consumed: zero.

## Next gate

Implement the family-1 live-variable physical owner events from the
[`streaming owner coverage map`](f5c-streaming-owner-gap-map-2026-09-28.md).
Family 3 and family-aware replay/terminal-live-owner reconciliation remain
open. Do not start preflight or scale rows until the all-eight-family
same-time event fold is implemented and independently reviewed.
