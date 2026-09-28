# F5c streaming owner event coverage map

Status: family-1 live-variable, family-3 structured-pair, and family-6
streaming-owner events are implemented, independently reviewed, and
focused-verified. Other required physical families remain open; no matrix,
preflight, or scale row ran.

Authority: the Authoritative F5c no-numeric-resource-cap addendum and its
physical-event requirements in
[`F5c no-cap scale measurement plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md).

## Verified checkpoint boundary

The feature-gated raw owner lifecycle in
[`f5c_draft_heap.rs`](../../crates/yu-solver/src/f5c_draft_heap.rs) is already
committed and independently verified by the
[`raw walker owner checkpoint`](f5c-raw-walker-owner-checkpoint-2026-09-28.md).
The six-buffer `FlatDraft` carrier and atomic same-ID staged transfer are
committed in the
[`FlatDraft owner carrier checkpoint`](f5c-flatdraft-owner-carrier-checkpoint-2026-09-28.md).
Family-specific extensions now record family-1 live-variable and family-6
streaming owner events; exact paths and checks are in the
[`family-1/family-6 event checkpoint`](f5c-family1-family6-events-checkpoint-2026-09-29.md).

Lane 55 (`PostROccurrenceOrder`) and lane 56 (`PostROccurrenceSeen`) occurrence
call sites are included in the family-6 streaming event checkpoint. The
checkpoint preserves the committed `F5cPostRSelection` representation and
`Walker::new(memo)`.

## Family 1: live-variable owner map — implemented

The event sink now records create/shape/grow/release events for ten top-level
`InferenceSession` vectors that are live before the matrix sink opens:
`live_components`, `bounds`, `effect_bounds`, `value_levels`, `effect_levels`,
`value_metadata`, `effect_metadata`, `extrusion_stack`,
`extrusion_value_marks`, and `extrusion_effect_marks`. Seed their current
length/capacity after opening the sink. Events cover
`fresh_value_at_level`, `fresh_effect_at_level`, `push_extrusion`, extrusion
completion, route-transaction rollback, and session finish.

Each value/effect bounds row also owns four distinct nested vectors: direct
lower/upper bounds and exact lower/upper endpoints. Every physical row buffer
has a stable identity; reserve/insert and truncate/drop paths, including
matrix seed helpers, are observed. Terminal events reconcile with the
boundary tuple and same-time family peak.

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

Implemented and reviewed in the
[`family-3 structured-pair event checkpoint`](f5c-family3-structured-pair-events-checkpoint-2026-09-29.md).
The checkpoint includes all 20 top-level owners, one owner per child vector,
the same-ID `errors` transfer, and family-3 terminal replay rules. It excludes
the rollback journal's distinct vectors from the `TypedPairs` and
`ReportedErrors` session owners.

The matrix checker is now family-aware for event families 1, 3, and 6. It
retains per-family same-time peaks, enforces the family-1 terminal-live-owner
reconciliation and release-only suffix, enforces family 3's terminal-live
`errors` owner and same-ID transfer, and accepts repeated family-6 component
checkpoints. The remaining physical families still need event coverage and
terminal rules before the all-eight-family stream is complete.

## Next checkpoint

Audit the remaining physical families against F5 §34's exact lane list and
same-time owner requirements, then take the next bounded event-coverage slice.
No preflight or scale row is eligible until all eight families have same-time
event aggregation and terminal reconciliation, followed by a reviewed fresh
diagnostic plan.

This map was updated to record the completed family-1/family-6 checkpoint. The
focused tests and checks are listed in its checkpoint note; no benchmark,
preflight, or scale process ran. Measurement budget consumed: zero.
