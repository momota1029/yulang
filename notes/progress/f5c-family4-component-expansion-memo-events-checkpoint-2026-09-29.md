# F5c family-4 component memo event checkpoint

Status: §34 family-4 physical owner events and replay are implemented and
independently reviewed in the `f5c_resource_probe` configuration. The
all-eight-family event and measurement gates remain open. No test, matrix row,
preflight, benchmark, or scale process ran.

Authority: F5 §§26/34 in the
[`F5 foundation`](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md),
the Authoritative
[`no-numeric-resource-cap addendum`](../design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md),
and the
[`remaining owner-event map`](f5c-remaining-owner-event-map-2026-09-29.md).

## Verified boundary

This checkpoint covers §34 family 4 `component_expansion_memo`, matrix lanes
45–64: the 16 memo containers and four generalizer scratch lanes. Each lane has
its own physical owner ID. Actual requested lengths and capacities are observed
after reserve and shape changes; clear and drop release the owner only after
its physical buffer has been dropped. The replay retains the simultaneous
event peak, reconciles the family-4 row tuple and all 20 lane records, accepts
one terminal zero-current checkpoint, and rejects later family-4 events or
surviving family-4 owners.

The six-buffer `FlatDraft` carrier and atomic same-ID staged transfer remain
the separate earlier checkpoint in
[`FlatDraft owner carrier`](f5c-flatdraft-owner-carrier-checkpoint-2026-09-28.md).
Family 1, family 3, and §34 family 7 (sidecar name `family6`) retain their
separate event checkpoints. This family-4 slice does not close other §34
families or authorize matrix measurement.

## Changed paths and diff units

- `crates/yu-solver/src/f5c_draft_heap.rs`: family-4 lane kinds 551–570, fixed
  owner storage, current/peak aggregation, and checkpoint emission.
- `crates/yu-solver/src/f5c_generalization.rs`: record actual memo and
  generalizer scratch capacity/shape after physical mutations; release lanes
  after clear/reset and arrange memo observer drop after scratch buffers.
- `crates/yu-solver/src/lib.rs`: refresh copied memo lanes after successful
  and rollback clear; reconcile event totals against the row and sampled memo
  peak; emit the terminal family-4 checkpoint.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: add the family-4 event
  capacity, retained-byte, and peak tuple to each matrix row.
- `tools/check_f5c_resource_matrix.py`: replay family 4, verify its shape and
  owner invariants, lane tuples, peak, checkpoint, and zero-live EOF rule.

## Review and verification

Selected M2 with `spec_auditor` and `compiler_referee`. Both completed the
bounded independent review without a concrete finding in the family-4 contract,
replay, or owner lifecycle. Runtime event replay, tests, and failure/drop
execution remain unverified.

Compile-only checks passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --offline -j 2`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe --offline -j 2`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --offline -j 2`
- `python3 -c 'import ast, pathlib; ast.parse(pathlib.Path("tools/check_f5c_resource_matrix.py").read_text())'`
- `git diff --check`

No tests, matrix, preflight, benchmark, or scale process ran; measurement budget
consumed: zero. The next mapped slice is §34 family 2 `inference_type_arena`;
families 2, 5, 6, and 8 still need event coverage before a fresh diagnostic
plan review and any matrix execution.
