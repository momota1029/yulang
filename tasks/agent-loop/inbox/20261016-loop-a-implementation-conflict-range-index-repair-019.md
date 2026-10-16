# I14-R1: bound conflict-location prefetch to observable records

- **Request ID:** `20261016-loop-a-implementation-conflict-range-index-repair-019`
- **Revision:** 1
- **Owner:** Luna primary
- **Parent:** I14, request `20261016-loop-a-implementation-conflict-range-index-018` rev1. Original receipt and original R23/R24 reviews remain frozen; this repair is a separate delta.
- **Branch/baseline:** `research/simple-sub-intrusion`, `6ab6882e058b47e91e64c5c2646aa4bfb00a7667`.
- **I14-R1 source base:** original I14 frozen `tools/inference-playground/src/lib.rs` SHA-256 `a6abe438a8f2540aa084f9b61533650536afe41dcb53873167b8f7401c409915`.
- **Frozen source:** `tools/inference-playground/src/lib.rs` SHA-256 `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb`.

## Change and invariant

Only the occurrence iterator passed from `prepare` into `conflict_ranges_for` is bounded with `.take(output::WORK_CAP)`. The generic helper remains uncapped. The complete diagnostic loop, `observe(1)` placement, ordering, error formatting, source-location fallback and cap rejection are unchanged.

The report charges one work entry before each diagnostic lookup. Thus record 16,385 cannot pass `observe(1)` and cannot require a prefetched range. The adapter bounds prefetch to at most `min(E, WORK_CAP)` records while preserving duplicate record positions. Byte-cap failure can stop rendering earlier than WORK_CAP; prefetch can still exceed the number actually rendered. This does not claim source traversal is charged per visited node or proportional to printed diagnostics.

The new unit test `tests::conflict_range_index_limits_prefetch_to_observable_prefix` applies the same outer `.take(WORK_CAP)` adapter, counts all WORK_CAP repeated authentic occurrence records, and chains a panicking tail. It asserts the prefix was consumed, the tail was not forced, one authentic borrowed range was returned, and deduplication is preserved. The earlier root/foreign/empty test remains unchanged.

## Read-only dependency pins

These pins were verified for I14 and remain the selected inputs for the repair review:

- `tools/inference-playground/tests/runtime.rs` — `2a263b532a1db0fceafb2787e5783461b3a6684f5a7a74c45995943ec2060e90`
- `tools/inference-playground/src/output.rs` — `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a`
- `crates/yu-hir/src/module.rs` — `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`
- `crates/yu-solver/src/shadow_apply.rs` — `4155a3bb3e632dee66a5db498cbff6f3a63da68e1b5d1d04b18719db610fe1a4`
- `crates/yu-solver/src/lib.rs` — `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`
- `notes/design/2026-10-16-module-expression-source-owner.md` — `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`
- `tools/inference-playground/src/output.rs` cap-owner pin — repeated above; `WORK_CAP = 16_384`.

## Verification

Three selected commands ran serially with one Cargo process, `CARGO_BUILD_JOBS=2`, 180-second timeout each:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --lib tests::conflict_range_index_ -- --test-threads=1` — exit 0; exactly 2 passed (the authentic-range and observable-prefix tests), 15 filtered.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --lib output::tests::multiple_graphs_share_the_aggregate_work_boundary -- --exact --test-threads=1` — exit 0; 1 passed, 16 filtered.
3. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime discarded_expression_type_conflicts_keep_source_locations -- --exact --test-threads=1` — exit 0; 1 passed, 16 filtered.

`git diff --check -- tools/inference-playground/src/lib.rs` passed. No benchmark, broad suite, timing sample, source restriction, solver mutation or new API. **Delta review and integration remain pending.**
