# F5c §34 family-5 closed-type-arena aggregate-peak checkpoint

Status: the scoped `f5c_resource_probe` aggregate-peak slice for §34 family 5
is implemented, independently reviewed, and compile-checked. With this slice,
all eight §34 resource families have static event or reconciliation coverage.
The all-family runtime fold and measurement gate remain open; no matrix or
preflight process has run after this implementation.

## Exact paths and diff units

- `crates/yu-types/src/lib.rs`: add one feature-gated fixed aggregate
  high-water scalar to `F5cResourceProbeSummary`. Recompute it from the current
  retained bytes of all 36 arena, scratch, and indexed lanes at complete
  existing reconciliation, temporary release, rollback, and finish points.
  It never sums the lanes' independent historical peaks.
- `crates/yu-solver/src/lib.rs`: use the fixed aggregate peak for semantic
  family 5 lane 65–100, fold its current capacity/bytes from the fixed lane
  summary, preserve existing call-local checkpoint arithmetic for
  source-resident owners, and check the final receipt and scratch/indexed zero
  state.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: emit a separate
  `closed_type_event` tuple and the successful-checkpoint upper witness. The
  existing `family5_event` remains the compatibility name for semantic §34
  family 6 normalization.
- `tools/check_f5c_resource_matrix.py`: validate the 36-lane family total,
  aggregate high-water bounds, terminal scratch/indexed release, and checkpoint
  witness.

The finalizer resets its production `peak_bytes` to retained bytes at the start
of each attempt. Therefore `ClosedTypeAccountingCheckpoint::peak_bytes_during_call()`
already gives the call-local same-time peak used when the solver combines it
with source allocations held stable through the synchronous indexed-finalizer
call. No separate call-peak field was added. The remaining independent evidence
was the cross-call simultaneous peak for the 36 enumerated physical lanes:
summing per-lane maxima would combine capacities observed at different times.
The new observer uses one fixed, allocation-free 36-lane fold per opt-in probe
reconciliation and adds no callback or event history. The default feature-off
build contains no added observer path.

At FinishOutput, the eight permanent arena lanes remain owned by the solved
closed-type arena. All 17 scratch lanes and 11 indexed temporary lanes have
zero current capacity and retained bytes. The row's `closed_type_event`
reconciles to lanes 65–100 and to the finalization receipt. Its aggregate peak
is bounded by successful call-local finalizer checkpoints and covers every
lane's independent historical peak.

## Review and verification

Selected M2: `spec_auditor` and `regression_auditor`, both clean. They reviewed
the current-lane fold, same-time peak, call-local checkpoint preservation,
feature-off behavior, family index and row tuple, successful finalizer
checkpoint witness, terminal arena retention, and scratch/indexed cleanup.
No concrete finding remains in the scoped static review.

Compile-only and static checks passed:

- `RUSTC_WRAPPER= cargo check -p yu-types --lib --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --lib --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --lib`
- Python AST parse of `tools/check_f5c_resource_matrix.py`
- `git diff --check`

No test was run. No matrix, preflight, benchmark, scale run, or measurement was
performed; measurement budget consumed is zero. The row and offline replay
remain statically reviewed but runtime-unverified.

## Next gate and limits

Next, review the complete eight-family row/checker fold and the current
preflight/diagnostic plan, including the corrected `guarded_cycle(D,K)`
companion and its resource envelope. Run no preflight until the fresh plan and
its process and memory monitoring limits are finalized under `rules/performance.md`.
