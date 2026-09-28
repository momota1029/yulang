# F5c owner-peak preflight failure checkpoint

Status: the second supervised preflight, after the ZST capacity correction,
failed at the test-only family peak coverage assertion during its second
fixture case. Its failure did not print the exact family and values. A
panic-only diagnostic was added to that assertion, independently reviewed,
and feature-enabled test-target compile-checked. No diagnostic or matrix
process ran.

## Exact paths and diff boundary

- `crates/yu-types/src/lib.rs:1078-1081`: the preceding checkpoint changes
  only feature-gated `f5c_probe_shape` capacity reporting for zero-sized slots.
  The independent review found this does not alter retained-byte or peak-byte
  calculations.
- `crates/yu-solver/src/lib.rs:16093-16111`: maps eight owner peaks to family
  ranges and asserts that each peak covers current retained bytes. The current
  panic is at line 16105, before more specific family reconciliations. The
  diagnostic-only follow-up keeps the predicate/control flow unchanged and
  reports boundary, family, row range, owner peak, retained total, and lane
  values.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs:17-19,2119-2135`: the
  preflight case order identifies the failing fixture as `IdentityAliases/U/32`.
- `notes/progress/f5c-no-cap-scale-measurement-plan-2026-09-28.md`: records the
  failed attempt, resource samples, and revised preflight-only allowance.
- `tasks/current.md`: records the active next gate.

## Attempt and preserved evidence

Run ID `20260929-zst-retry-01` exited 101 after 5.02 seconds. It emitted one
complete tuple before failing:

```text
family=IndependentIdentities dimension=D size=32 companion=none count=35896 checksum=134038160 bytes=2297352
```

The failing `IdentityAliases/U/32` case panicked with
`matrix owner family peak must cover current retained bytes`. The supervisor
recorded peak process-group RSS 618,283,008 bytes, minimum `MemAvailable`
27,877,134,336 bytes, sidecar high-water 220,808 bytes, and minimum free disk
666,033,414,144 bytes.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-zst-retry-01.log`
- `/tmp/f5c-preflight-20260929-zst-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-zst-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-zst-retry-01.events`

The partial sidecar contains 3,450 complete persisted records. Because the
buffered event writer did not flush on panic, it does not reveal the failing
boundary, family, peak, or retained value.

## Cause assessment and next gate

The failure's boundary is in `IdentityAliases/U/32`; the exact family remains
unknown because the assertion emits no context. The read-only audit inspected
the owner-family mapping and each peak producer. The ZST fix cannot explain this
failure: it changes only zero-sized physical capacity, which keeps retained
bytes at zero, and leaves all byte peaks unchanged. The audit's direct peak
producers are the bound-table current peak, streamed owner-event peaks for
families 2/3/4/6/8, the closed-type aggregate, and the source/walker joint peak.

The contextual diagnostic in `crates/yu-solver/src/lib.rs` preserves the
original assertion condition and accounting. A `spec_auditor` review found the
message fields correct and no invariant or control-flow change. Focused checks
passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- `git diff --check`

Run one fresh supervised preflight retry to identify the violated family and
peak producer; do not lower or remove the invariant.

The new retry has a 60-second process timeout plus 10-second termination grace.
Together with the first two attempts and planned 300-second diagnostic and
150-second checker, the maximum is five measured invocations and 561.08 seconds
including grace, within the ordinary 8-invocation/10-minute allowance. The
user authorized autonomous continuation and expanded time/memory budgets; no
approval pause is needed.
