# F5c §34 physical-lane replay checkpoint

Status: the event-backed physical-lane layout and offline replay are
implemented and statically reviewed. Runtime reconciliation remains open. No
preflight, diagnostic, matrix, or scale process has run after this change.

## Exact paths and diff units

- `crates/yu-solver/src/lib.rs`: grow the fixed test observer from 256 to 261
  lanes. Preserve the three existing family-7 source rows, then reserve one
  row for each owner kind 5–22. Shift 98 walker rows to 150–247, family-8
  rows to 248–254, and route rows to 255–260.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: align lane identities
  with that layout and add one ignored `GuardedCycle/D/32/4000` diagnostic
  entrypoint.
- `tools/check_f5c_resource_matrix.py`: replay sidecar ownership events into
  rows 0–17, 24–44, and 129–247, totaling 158 event-backed physical rows.
  Require exact current capacity and retained-byte agreement, one slot size
  per row, and event peaks that cover the sampled row peak. Use the replayed
  same-time peak as canonical input to per-lane ratios. Keep the ordinary
  36-row/12-series matrix and the exact one-row diagnostic selection.

Family-7 rows are: owner kinds 1–2 at 129–130; kinds 3–4 share row 131 because
they have the same physical slot type; kinds 5–10 at 132–137; staged outer kind
11 at 138; staged buffers 12–17 at 139–144; indexed buffers 18–22 at 145–149;
and walker kinds 32–129 at 150–247. Unknown family-6 kinds are rejected.
Unclassified kind 0 is allowed only with zero requested and allocated capacity.
Same-ID transfers retain their event identity through subtract/add owner
adjustments, so replay peaks describe simultaneous live physical lanes instead
of sums of historical maxima.

## Review and verification

Selected M2 with `spec_auditor` and `regression_auditor`. The specification
review found a blocking hole where unmapped owner kinds could bypass row
accounting. A narrow review of the repair confirmed rejection of unmapped kinds
on creation and both sides of mutation/transfer; kind 0 remains an empty
placeholder, and checkpoint records remain valid. The regression review found
the lane shifts, ordinary matrix selector, and exact diagnostic tuple aligned.
No remaining scoped finding is open.

Static checks passed:

- `RUSTC_WRAPPER= cargo check -q -p yu-solver --tests --features f5c_resource_probe`
- `python3 -m py_compile tools/check_f5c_resource_matrix.py`
- `git diff --check`

The Rust source did not change after the feature-enabled test-target compile
check; the last follow-up changed only Python owner-kind admission. No test,
resource probe, preflight, diagnostic, matrix, benchmark, or measurement ran.
Measurement budget consumed is zero. The canonical event replay and ratios are
still runtime-unverified.

## Next gate

The no-cap measurement plan records a fresh two-process first runtime gate: a
60-second seven-builder preflight followed by a 300-second corrected
`D=32,K=4,000` diagnostic, with 10-second termination grace per process,
process-tree RSS and host-memory monitoring, and unique `/tmp` logs/sidecars.
The performance-auditor review of that host/disk protocol is pending. Do not
start either process until that review closes. If the diagnostic passes, use
its elapsed time, peak RSS, event count, and sidecar size to set and review the
remaining 36-row matrix budget.
