# F5c source-owner online-shadow checkpoint

Status: the fixed online owner shadow now includes the 15 source-owner rows
missing from the earlier 204-row ledger. It represents 219 physical lane rows
plus a joint current/peak subtotal. The full event trace remains intact,
including FlatDraft kinds 12–17. This checkpoint closes the source-row gap;
it does not close the global same-time ledger gate or authorize scale/resource
measurement.

## Scope and authority

This is an implementation slice under the existing F5 §§26/34 authority and
the F5c flat indexed stack and shared-walker designs. The architect's prior
adjudication requires the online shadow to include physical rows omitted by a
sidecar-only total and to compose with closed-type and route baselines at the
same observation time. This slice adds the omitted source-owner rows only.
The global composition and exact-kind trace suppression remain separate gates.

Changed paths:

- `crates/yu-solver/src/f5c_draft_heap.rs`
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`
- `tools/check_f5c_resource_matrix.py`
- `tasks/current.md`

## Ledger rows and behavior

The source rows cover physical rows 129–138 and 145–149. SourceHeldBounds and
SourceActiveBounds map to the single shared row 131. The other rows track
SourceOuter, SourceSidecar, positive and negative function arguments/results,
union/intersection children, StagedOuter, and IndexedBuffer indices 0–4.
Register, capacity/shape replacement, release, classification, and same-ID
transfers update fixed arrays in O(1). No new event kind or per-event data is
serialized.

The witness covers all source kinds, validates source classification and
release, and includes a real `Vec::try_reserve_exact` capacity increase before
the reserve callback returns an error. It checks current and peak accounting
after the failed operation and confirms that release debits current while
retaining peak. The replay requires source event kinds 1–11 and 18–22, verifies
the merged row 131, same-ID walker-to-source transfer targets 2, 9, and 10,
matching releases, and all 219 exact rows against offline replay.

## Review and verification

M2 pre-write review used `spec_auditor` and `performance_auditor`. Post-write
review found two major witness gaps: transfer/release event kinds were not
required by replay, and a `usize::MAX` reserve witness did not actually grow.
One batched implementer repair addressed both. A fresh specification delta
review confirmed exact event coverage, transfer targets and IDs, real growth
followed by an error, current/peak/release evidence, and preservation of the
staged path. The performance review found O(1) updates, no new serialization,
and no material hot-path issue.

The fixed state grows by 480 bytes per thread (6,560 to 7,040 bytes on the
reviewed 64-bit target). Six staged copies add 2,880 copied bytes per batch,
or 5,760 read/write bytes. The measurement budget consumed zero samples or
processes.

Checks passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe f5c_walker_online_shadow_witness --lib --offline -j 2 -- --test-threads=1`
- `python3 tools/check_f5c_resource_matrix.py --walker-shadow-witness /tmp/f5c-source-shadow-final.bin --walker-shadow-totals /tmp/f5c-source-shadow-final.txt`
- Python `ast.parse` for `tools/check_f5c_resource_matrix.py`
- `git diff --check`

The replay accepted 417 full sidecar events and matched 219 exact rows plus the
joint total. `cargo fmt --all -- --check` reports formatting drift across 18
Rust source files, including older code in the two touched Rust files; the
focused change did not apply repository-wide formatting. No scale/resource
process, diagnostic, or matrix row ran.

## Next gate

Compose the online solver shadow with exact baselines. At
`record_flat_finalizer_peak`, replace closed-type current with that finalizer
call's `peak_bytes_during_call()` exactly once while other solver lanes remain
fixed. At later route samples, incorporate the exact current route baseline.
Prove co-temporal current and peak totals through an offline replay witness.
Keep full serialization during this gate. Only after composition, replay, and
a fresh performance review close may serialization be suppressed for exact
non-transferring kinds 54–56 and 116. Keep kinds 12–17 in the trace.
