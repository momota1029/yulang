# F5c family-8 instantiation-substitution owner-event checkpoint

Status: the scoped `f5c_resource_probe` event slice for §34 family 8 is
implemented, independently reviewed, and compile-checked. The all-eight-family
event gate remains open; matrix, preflight, benchmark, and scale work remain
closed until families 5 and 6 plus the fresh diagnostic plan are reviewed.

## Exact paths and diff units

- `crates/yu-solver/src/f5c_draft_heap.rs`: add the feature/test-only
  `InstantiationLane` event family, fixed-size owner slots, per-family
  current/peak totals, and checkpoint event.
- `crates/yu-solver/src/lib.rs`: observe the seven `InstantiationScratch`
  vectors/maps/sets after reservation attempts (including errors), successful
  shape mutations, work pops, clear, scratch reuse, and nested instantiation;
  reconcile family current and peak with row lanes 230–236 and terminal state.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: emit the family-8
  checkpoint tuple in the existing matrix row.
- `tools/check_f5c_resource_matrix.py`: replay kinds 577–583, validate the
  family checkpoint and simultaneous peak, and reconcile each lane's current,
  peak, and finish checkpoint.

The event lanes are: substitution map (230), positive memo map (231), negative
memo map (232), positive effect set (233), negative effect set (234), parts
vector (235), and work vector (236). Event kinds are 577–583 respectively.
Each event owner ID follows its physical allocation through scratch `take`,
swap, reuse, and nested constrain/route paths. Reservation results are observed
before propagating errors; insertion, pop, and clear shape changes are observed
at their mutation sites. Event tokens are dropped after the scratch buffers so
RELEASE follows the backing-buffer destruction. The FinishOutput row records a
zero-current checkpoint and preserves the event-time peak.

## Review and verification

Selected M2: `spec_auditor` and `compiler_referee`, with no concrete findings.
The exact slot list, row tuple, per-lane replay, peak reconciliation, EOF
release contract, scratch moves, reserve-error observations, and drop ordering
were reviewed. No code was changed after review.

Compile-only and static checks passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --lib --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests`
- `python3 -c 'import ast; ast.parse(open("tools/check_f5c_resource_matrix.py").read())'`
- `git diff --check`

No test was executed. No matrix, preflight, benchmark, scale run, or
measurement was performed; measurement budget consumed is zero. Production
builds compile no family-8 observer code.

## Next gate and limits

The next bounded slice is an architecture review of §34 family 6
`closed_normalization_index`, focused on the six FlatDraft output vectors
already physically owned by the generalizer and also named as normalization
lanes 21–26. Resolve the existing ownership/reclassification topology before
adding events, so the same six buffers are counted exactly once. §34 family 5
`closed_type_arena` also remains open and has a separate cross-crate observer
authority boundary. Do not begin matrix work until both event families and the
fresh diagnostic plan have passed their required reviews.

Runtime replay of reserve-failure, rollback, nested reuse, and terminal paths
was not exercised because tests and matrix execution remain gated. The scoped
compile checks establish type correctness, not runtime trace validity.
