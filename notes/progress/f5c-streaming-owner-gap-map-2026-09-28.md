# F5c streaming owner event coverage map

Status: read-only path audit complete for the family-1 live-variable lanes,
family-3 structured-pair lanes, and family-6 occurrence lanes 55/56. No new
event implementation or matrix run is verified by this map.

Authority: the Authoritative F5c no-numeric-resource-cap addendum and its
physical-event requirements in
[`F5c no-cap scale measurement plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md).

## Verified checkpoint boundary

The feature-gated raw owner lifecycle in
[`f5c_draft_heap.rs`](../../crates/yu-solver/src/f5c_draft_heap.rs) is already
committed and independently verified by the
[`raw walker owner checkpoint`](f5c-raw-walker-owner-checkpoint-2026-09-28.md).
It provides create, requested-length/capacity observation, release, and
same-ID transfer operations. This does not verify any family-specific event
coverage.

Lane 55 (`PostROccurrenceOrder`) and lane 56 (`PostROccurrenceSeen`) identifiers
and slot definitions already exist in the committed source. Their occurrence
call sites remain uncommitted. The smallest independent implementation slice
is `f5c_generalization.rs` plus `f5c_tree_analysis.rs`: attach the flat source's
probe meter, create occurrence owners, observe capacity and requested length
after reserve/insert, and release owners only after their buffers drop. Keep
the committed `F5cPostRSelection` representation and `Walker::new(memo)`;
other post-R lane wrappers and replay plumbing are not dependencies. The
current dirty hunks in these files mix those unrelated changes, so they cannot
be staged wholesale. Reconstruct this slice against branch HEAD and verify it
in isolation before treating lane 55/56 as complete.

## Family 1: live-variable owner map

The event sink currently has no family-1 create/shape/grow/release events.
Ten top-level `InferenceSession` vectors are live before the matrix sink opens:
`live_components`, `bounds`, `effect_bounds`, `value_levels`, `effect_levels`,
`value_metadata`, `effect_metadata`, `extrusion_stack`,
`extrusion_value_marks`, and `extrusion_effect_marks`. Seed their current
length/capacity after opening the sink. Subsequent mutation owners are
`fresh_value_at_level`, `fresh_effect_at_level`, `push_extrusion`, extrusion
completion, route-transaction rollback, and session finish.

Each value/effect bounds row also owns four distinct nested vectors: direct
lower/upper bounds and exact lower/upper endpoints. Assign a stable identity
to every physical row buffer; observe reserve/insert and truncate/drop paths,
including matrix seed helpers. Existing aggregate nested request/insert/remove
counters cannot reconstruct these individual lifetimes. Reconcile terminal
events with the boundary tuple before accepting the family peak.

## Family 3: structured-pair owner map

Family 3 is lanes 24–44 in `lib.rs`. Top-level owners include `typed_pairs`,
`typed_worklist`, diagnostic delta/index, reverse-graph and SCC scratch,
errors, and reported errors. These allocations are created before the sink
opens, so seed their live states immediately after opening and before facts
are admitted.

Lane 25 sums the capacity/requested length of child vectors inside
`TypedPairMemo::Value`; those are separate physical allocations and require
stable per-child identities and individual release events. Cover admissions,
queue pushes, diagnostic edges/completion, scratch preparation/clearing,
incompatible-pair reporting, and rollback truncations. `errors` moves into
`SolvedModule` and remains live after `InferenceSession::finish()` while the
sidecar is closed; do not emit an early release. The terminal fold must permit
that live owner and reconcile it with the captured terminal lane tuple.

The untracked matrix checker currently folds every event as family 6 and
requires all event owners to be released. It must become family-aware before
family-1 or family-3 events can share the stream: select the intended lane
family during replay, retain per-family same-time peak aggregates, and define
the terminal-live-owner reconciliation explicitly. Treating component IDs as
resource-family IDs is invalid.

## Next checkpoint

First reconstruct and isolate the two-file lane-55/56 patch against HEAD, then
run its focused tests in an isolated worktree and commit/push that narrow gate.
After that, implement event ownership family by family, starting with the
live-variable rows, and only then widen the common event replay to structured
pairs. No preflight or scale row is eligible until all eight families have
same-time event aggregation and terminal reconciliation.

This map is an M0 record-only checkpoint. It ran no compiler command, test,
benchmark, preflight, or scale process; measurement budget consumed: zero.
