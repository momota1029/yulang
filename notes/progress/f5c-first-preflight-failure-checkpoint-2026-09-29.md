# F5c first preflight failure checkpoint

Status: the first supervised preflight was executed and failed before emitting
its summary. No diagnostic or matrix process ran. A read-only root-cause audit
identified a feature-gated physical-capacity probe defect; the one-helper
repair is independently reviewed and passes focused feature-enabled compile
checks. The supervised retry is the next gate.

## Exact paths and evidence

- `notes/progress/f5c-no-cap-scale-measurement-plan-2026-09-28.md`: reviewed
  three-process plan and the first attempt's bounded process/memory evidence.
- `tasks/current.md`: active gate and immediate next action.
- `crates/yu-types/src/lib.rs:1078`: `f5c_probe_shape` copies the raw capacity
  of each vector into the physical-lane summary.
- `crates/yu-solver/src/lib.rs:16108-16111,16143-16144`: family capacities
  are summed into `u128`, then family 5's terminal total is converted to
  `usize`.
- `crates/yu-types/src/lib.rs:737-751,1283-1308`: the permanent arena and
  finalizer scratch each include two `Vec<()>` lanes.

The supervised preflight ran with `RUN_ID=20260928T204753Z` and exited 101
after 16.06 seconds. The ignored test panicked while converting
`observer.family_capacity[4]`, with `TryFromIntError(())`. The supervisor
recorded minimum host `MemAvailable` of 27,408,719,872 bytes, sampled peak
process-group RSS of 1,215,074,304 bytes, sidecar high-water 2,296,968 bytes,
and minimum free disk of 666,050,269,184 bytes.

Preserved evidence:

- `/tmp/f5c-preflight-20260928T204753Z.log`
- `/tmp/f5c-preflight-20260928T204753Z.monitor.jsonl`
- `/tmp/f5c-preflight-20260928T204753Z.summary.json`
- `/tmp/f5c-preflight-20260928T204753Z.events`

## Cause and bounded repair

`Vec<()>` reports `usize::MAX` capacity as a zero-sized-type sentinel while
allocating no element storage. The probe forwarded that sentinel as physical
capacity for four family-5 lanes (matrix lanes 69, 70, 79, and 80). This made
the aggregate family capacity unrepresentable in the solver's `usize`
terminal event. The later family-7 row expansion does not overlap these rows.

The repair is limited to `f5c_probe_shape` in
`crates/yu-types/src/lib.rs`:
keep `lane.len()` as the requested length; report physical capacity `0` when
`size_of::<T>() == 0`; retain `lane.capacity()` for non-zero-sized slots.
Retained bytes continue to be capacity times slot size. This repairs the
physical allocation witness and does not change language or production
allocation behavior. The fixed-size family fold, lane map, and replay checker
stay in their existing checkpoints.

## Verification and next gate

The failed attempt consumed one process invocation and 16.06 seconds. It
produced no successful preflight tuple; the sidecar remains preserved for
forensics. The scoped repair received a clean `spec_auditor` review of the
helper, probe lane, solver consumer, checker tuple, and governing physical-lane
contract. Focused checks passed:

- `RUSTC_WRAPPER= cargo check -p yu-types --lib --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- `git diff --check`

No diagnostic, offline replay, matrix row, benchmark, or scale process has run.

The retry is one preflight process with a 60-second timeout and the same
supervisor thresholds and 10-second TERM-to-KILL grace. Use fresh run ID
`20260929-zst-retry-01` and unique `/tmp/f5c-preflight-20260929-zst-retry-01.*`
paths. Including the failed 16.06-second attempt, this gate and the planned
diagnostic/replay consume at most four measured process invocations and
556.06 seconds (16.06 + 60 + 300 + 150 seconds, plus three 10-second grace
periods), leaving 43.94 seconds inside the ordinary 8-process/10-minute
budget. The retry must pass before either downstream command runs. The user
has authorized autonomous continuation and expanded time/memory budgets; no
approval pause is required.
