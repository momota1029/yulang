# F5c owner-peak preflight failure checkpoint

Status: the second supervised preflight, after the ZST capacity correction,
failed at the test-only family peak coverage assertion during its second
fixture case. A panic-only diagnostic identified the third attempt's missing
closed-probe snapshot during incoming routing. The test+feature-gated route
handoff repair is implemented, specification/performance reviewed, and
feature-enabled test-target compile-checked. Each active matrix boundary now
requires one live, handoff, or finished probe, so no boundary can silently
skip the 36 physical rows. No diagnostic or matrix process ran.

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
- `crates/yu-solver/src/lib.rs:14863-14960,15996-16011`: incoming routing
  temporarily moves the live finalization session out of `self`; the observer
  has no closed probe during that handoff and leaves its 36 current lane rows
  unchanged. The repair adds a temporary feature-gated snapshot field, captures
  it at take, uses it for observer reconciliation, and clears it after restore.
- `crates/yu-types/src/lib.rs:1038-1048,1618-1620,1677-1678`: the
  authoritative same-time aggregate peak folds current retained bytes and is
  updated at the inspected physical lane reconciliation points.
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

## Third preflight with contextual assertion

Run ID `20260929-owner-peak-retry-01` exited 101 after 6.03 seconds. The added
assertion identified `IncomingRoute`, family 4, rows 65–100, with `owner_peak=0`
and `retained=340`. Its lane slice showed 36 current physical rows whose
retained-byte sum is 340; the family peak came from `closed_probe.map_or(0, ..)`.
The supervisor recorded peak process-group RSS 746,856,448 bytes, minimum
`MemAvailable` 27,867,635,712 bytes, sidecar high-water 220,808 bytes, and
minimum free disk 666,106,630,144 bytes.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-owner-peak-retry-01.log`
- `/tmp/f5c-preflight-20260929-owner-peak-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-owner-peak-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-owner-peak-retry-01.events`

## Cause assessment and next gate

The failure occurred in the `IdentityAliases/U/32` fixture. The contextual
assertion located it at `IncomingRoute` in family 4 (`closed_type_arena`): 36
current rows sum to 340 bytes, but the selected owner peak is zero. The cause is
the temporary ownership handoff in `route_incoming_inner`: it takes the live
`ClosedTypeFinalizationSession` into a local, then invokes incoming-route
sampling before restoring the session. At that instant both
`self.finalization.as_ref()` and `self.f5c_matrix_finished_closed` are `None`.
The observer skips the 36 closed-lane updates but leaves the prior `current`
values in place; it then maps absent `closed_probe` to owner peak zero. The
partial sidecar cannot identify this because it is not flushed on panic.

The read-only audit checked the closed-type aggregate producer and its direct
sampling sites; `yu-types` updates `aggregate_peak_bytes` from same-time current
retained bytes. The ZST repair is unrelated: it leaves non-ZST retained bytes
and all byte peaks unchanged.

The fix copies `finalization.f5c_resource_probe()` to a test+feature-gated
field only while the route handoff is active. Observer selection preserves the
authoritative `aggregate_peak_bytes`; it is not reconstructed from lane
history. The field clears immediately after session restoration, including the
injected reserve-error path. Every active matrix sample now requires a live,
handoff, or finished probe, and reconciles all 36 rows; the prior silent
no-probe skip is removed. The test-only current sum, per-family peak, and
terminal receipt/checkpoint assertions remain active.

The route snapshot is 2,032 bytes on this 64-bit host and copies once for each
incoming use route only in the probe build. The D=32/K=4,000 diagnostic has 32
routes, or 65,024 copied bytes; seven preflight cases are bounded by 455,168
bytes (about 0.44 MiB). `performance_auditor` judged this immaterial to the
reviewed 300-second diagnostic and process limits, based on static call counts
and structure; no timing experiment was run.

Selected M1 with `spec_auditor` and `performance_auditor`; both reviews were
clean for exact lane reconciliation and bounded snapshot cost. A follow-up
`spec_auditor` delta review was also clean for the explicit required-probe
assertion and removal of the skip branch. The final focused check passed after
that addition:

- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`

Run the fresh supervised preflight next; it must prove that every boundary
with live closed lanes has a probe, all 36 retained bytes sum to
`current_closed_retained_bytes`, and the aggregate peak covers current bytes
and each lane's independent historical peak. The terminal event must still
reconcile with the finish receipt and successful finalizer checkpoint witness.

The new retry has a 60-second process timeout plus 10-second termination grace.
Together with the first three attempts and planned 300-second diagnostic and
150-second checker, the maximum is six measured invocations and 567.11 seconds
including grace, within the ordinary 8-invocation/10-minute allowance. The
user authorized autonomous continuation and expanded time/memory budgets; no
approval pause is needed.
