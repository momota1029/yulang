# F5c `yu-types` probe checkpoint

Status: verified, reviewable sub-slice on `yulang3`, based on commit
`4e1aa637`. This checkpoint adds opt-in physical observations for the 36
private closed-finalizer lanes. It does not close cross-family same-time peak
aggregation or authorize a matrix run.

Authority: the Authoritative F5c no-numeric-resource-cap addendum §§2–4 and the
`yu-types` lane-observation contract in
[`F5c no-cap scale measurement plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md).
The existing `f5c_resource_probe` feature remains the only enablement path.

## Exact diff unit

- [`crates/yu-types/src/lib.rs`](../../crates/yu-types/src/lib.rs): samples
  current requested length, actual capacity, slot size, retained bytes, peak
  bytes, growths, and clear/transfer point in fixed arrays for 8 arena, 17
  scratch, and 11 indexed-temporary lanes. The observer has no growing event
  history and is absent when the feature is disabled.
- Finalization now drops the actual scratch vectors before recording terminal
  zero scratch capacity. It checks that the terminal 36-lane retained sum
  equals the arena retained receipt while preserving historical per-lane
  peaks. The indexed temporary lanes are already released by their existing
  finalization path before the terminal sample.
- `indexed_probe_clears_temporary_current_before_commit_reserve` checks the
  indexed temporary peak, zero current indexed/scratch capacity after finish,
  retained sum versus receipt, and preserved scratch peak.

The initial independent spec review found a major gap: terminal scratch had
been zeroed in the probe before its buffers dropped, without comparing the
36-lane current sum to the receipt. The repair drops the actual scratch owner
first and adds the receipt equality assertion. A fresh spec delta review is
clean. The review also suggested removing `retained_bytes` visibility; it is
now private again and remains test-only.

## Verification

Checks run:

- `RUSTC_WRAPPER= cargo test -p yu-types --lib --features f5c_resource_probe --offline -j 2 indexed_probe_clears_temporary_current_before_commit_reserve -- --test-threads=1` (1 passed)
- `RUSTC_WRAPPER= cargo check -p yu-types --lib --offline -j 2`
- `RUSTC_WRAPPER= cargo check -p yu-types --lib --features f5c_resource_probe --offline -j 2`
- `git diff --check -- crates/yu-types/src/lib.rs`

The first test launch through the configured `sccache` wrapper failed with
`EPERM`; the same focused test passed with `RUSTC_WRAPPER=`. No broad suite,
benchmark, preflight, or scale process ran. Measurement budget consumed: zero.

## Next gate

Implement family-1 live-variable owner events and shared event replay, as
specified in the
[`streaming owner coverage map`](f5c-streaming-owner-gap-map-2026-09-28.md).
The other solver families and same-time eight-family reconciliation remain
open.
