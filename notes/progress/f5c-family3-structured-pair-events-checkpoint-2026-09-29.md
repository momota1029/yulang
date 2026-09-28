# F5c family-3 structured-pair event checkpoint

Status: family-3 structured-pair owners and family-aware replay are implemented
and independently reviewed in the `f5c_resource_probe` configuration. The
all-eight-family measurement gate remains open. No matrix row, preflight,
benchmark, or scale process ran.

Authority: the Authoritative
[`F5c no-numeric-resource-cap addendum`](../design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md),
F5 §26/§34 in the
[`F5 foundation draft`](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md),
and the family-3 owner map in
[`F5c streaming owner event coverage map`](f5c-streaming-owner-gap-map-2026-09-28.md).

## Verified boundary

The already committed six-buffer `FlatDraft` carrier and atomic same-ID staged
transfer remain the exact prior boundary in the
[`FlatDraft owner carrier checkpoint`](f5c-flatdraft-owner-carrier-checkpoint-2026-09-28.md).
Family-1 live-variable and family-6 streaming-owner events remain the separate
verified scope in the
[`family-1/family-6 event checkpoint`](f5c-family1-family6-events-checkpoint-2026-09-29.md).
This checkpoint adds family 3 only; it does not claim all-eight-family closure
or authorize matrix measurement.

## Changed paths and diff units

- `crates/yu-solver/src/f5c_draft_heap.rs`: family-3 physical owner kind,
  aggregate current/peak accounting, top-level owner lifecycle, per-child
  vector owner lifecycle, and checkpoint emission.
- `crates/yu-solver/src/lib.rs`: `DiagnosticChildren` owns each child-vector
  identity while preserving vector behavior; 20 session lanes are seeded after
  sink open and observed at reserves, shape changes, rollback, scratch clear,
  and finish. `errors` remains live and transfers under the same owner ID into
  `SolvedModule`.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: matrix row output includes
  the family-3 capacity, retained-byte, and peak tuple.
- `tools/check_f5c_resource_matrix.py`: replay folds family 3, checks its
  unique checkpoint and same-time peak, accepts only the terminal live `errors`
  owner, and rejects family-3 shape or same-ID transfer events that alter the
  physical allocation.

The independent `RouteMutationJournal` vectors are not attributed to the
session's `TypedPairs` or `ReportedErrors` owner identities. Their reserve
calls share capacity-lane labels, so family-3 observation is attached only to
the actual session fields. Journal memory stays under the existing separate
resource accounting.

## Review and verification

Selected M2 with `spec_auditor` and `compiler_referee`. Initial review found
and closed five major/blocking issues: the replay allowed family-3 SHAPE and
TRANSFER to change physical size; aggregate reconciliation read the previous
boundary's cached totals; rollback cleared the queue without a shape event;
top-level map growth was recorded after later fallible work; and shared
capacity-lane labels attributed rollback-journal buffers to session owners.
Delta review of all fixes found no remaining issue in the inspected scope.

Checks passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --offline -j 2`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe --offline -j 2`
- `python3 -c 'import ast, pathlib; ast.parse(pathlib.Path("tools/check_f5c_resource_matrix.py").read_text())'`
- `git diff --check`

No tests were run. `cargo fmt --all -- --check` did not produce a clean result;
it reported formatting differences across unrelated workspace files, so no
workspace-wide formatting was applied. No matrix, preflight, benchmark, or
scale process ran; measurement budget consumed: zero.

The next gate is a read-only map of the remaining F5c physical families and
their same-time owner events, followed by one bounded implementation slice.
The exhausted 39-process preflight campaign remains closed. Do not begin a new
preflight or scale run until all required families are reconciled and the fresh
diagnostic plan is reviewed.
