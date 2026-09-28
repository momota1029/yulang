# F5c §34 family-6 closed-normalization-index owner-event checkpoint

Status: the scoped `f5c_resource_probe` event slice for §34 family 6 is
implemented, independently reviewed, and compile-checked. The all-eight-family
event gate remains open because §34 family 5 is still incomplete. The original
six-buffer `FlatDraft` owner carrier and same-ID staged transfer are recorded
separately in [the carrier checkpoint](f5c-flatdraft-owner-carrier-checkpoint-2026-09-28.md).

## Exact paths and diff units

- `crates/yu-solver/src/f5c_draft_heap.rs`: add fixed-size normalization owner
  events and same-time current/peak totals; let the six transferred output
  buffers use normalization owner kinds and atomically move those same IDs to
  their existing staged-buffer kinds.
- `crates/yu-solver/src/f5c_draft.rs`: attach normalization owners to the six
  output vectors only on the staged batch path. Direct flat normalization keeps
  its established generalization-scratch owner kinds.
- `crates/yu-solver/src/f5c_normalization.rs`: observe the 13 base lanes and
  15 flat-index lanes at growth/shape changes, release owners after their
  backing vectors die, and retain per-lane and joint peak accounting.
- `crates/yu-solver/src/lib.rs`: reconcile the streamed normalization event
  totals with the family-6 row total and sampled independent peak; record a
  zero-current terminal checkpoint.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: emit the normalization
  current/retained/peak tuple and all 28 lane growth counts in each matrix row.
- `tools/check_f5c_resource_matrix.py`: replay event kinds 584–611, reconcile
  all lanes, require release at EOF, and allow only the six lane-21–26
  normalization-to-staged same-ID transfers.

The 28 lane IDs map in order to matrix lanes 101–128. Lane 16 remains
intentionally ownerless under the existing physical-lane contract. Output lanes
21–26 keep one allocation owner across normalization and staged ownership. The
replay rejects other cross-family transfers. The row field `family5_event` and
event-kind range 584–611 are compatibility names in the sidecar implementation;
they represent semantic §34 family 6, `closed_normalization_index`. The older
`family6_event` field continues to represent semantic §34 family 7,
`generalization_scratch`; the distinct lane ranges and kind decoder preserve
that established format.

The lifecycle delta review found that lanes 18–20 (`work`, `positive_scratch`,
and `negative_scratch`) outlived their local vectors in the event stream until
after staged claim. They now release immediately after the rebuild call has
dropped those vectors, on both success and error, before output transfer. The
later handoff release is idempotent. The same review confirmed collect-scratch
release on early errors and normalizer-owner release after backing-vector drop.

## Review and verification

Selected M2: `spec_auditor` and `regression_auditor`. The initial reviews
confirmed the lane contract, one-owner accounting, exact same-ID transfer,
reserve-error event order, failure cleanup, per-lane reconciliation, peak, and
terminal zero state. Regression review found two early-error lifetime gaps in
collect scratch and normalizer teardown; both were repaired and delta-reviewed.
The subsequent targeted review found the lane-18–20 release ordering issue;
both reviewers independently closed that repair. No concrete finding remains
in the scoped static review.

Compile-only and static checks passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --lib --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- Python AST parse of `tools/check_f5c_resource_matrix.py`
- `git diff --check`

No test was run. No matrix, preflight, benchmark, scale run, or measurement was
performed; measurement budget consumed is zero. Runtime event replay therefore
remains unverified. Production builds compile no family-6 event observer.

## Next gate and limits

The remaining event-coverage gate is semantic §34 family 5, `closed_type_arena`,
owned by `yu-types`. The read-only architecture review has selected fixed
current/peak and call-local aggregate observation at the existing reconciliation
sites, then a solver-side combination with owners stable across the synchronous
indexed-finalizer call. No implementation or runtime event validation for that
slice is included here. After family 5 closes, review the full eight-family
event fold and the fresh diagnostic plan before any preflight or matrix work.
