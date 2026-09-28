# F5c first-runtime resource supervisor checkpoint

Status: an executable resource supervisor and the first corrected diagnostic
protocol are implemented and independently reviewed. No preflight, diagnostic,
matrix, or measurement process has run.

## Exact paths and diff units

- `tools/run_f5c_resource_process.py`: supervise one direct command in a new
  process group. Sample live group RSS, host `MemAvailable`, sidecar/log size,
  and filesystem free bytes about once per second. Require at least 8 GiB of
  available memory and `max(8 GiB, 2 * (sidecar bytes + log bytes))` of disk
  space before launch and while running. On a threshold breach, command
  timeout, or SIGINT/SIGTERM, send TERM to the group, wait 10 seconds, and KILL
  remaining processes. Keep monitoring descendants even after the leader
  exits. Save JSONL samples and a JSON run summary; only a zero-status command
  with no remaining group process is success. `--existing-sidecar` admits one
  read-only regular input sidecar for offline replay, counts it toward the
  disk floor, and still requires new log/monitor/summary outputs.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: before each of the seven
  preflight builders removes its transient sidecar, check the file length with
  checked arithmetic against `8 + 64 * event_count`, then emit a bounded tuple,
  event count, checksum, and byte count to the captured log.
- `notes/progress/f5c-no-cap-scale-measurement-plan-2026-09-28.md`: document the
  fail-closed three-process sequence: 60-second preflight, 300-second
  `GuardedCycle/D/32/4000` diagnostic, and 150-second offline replay. Each has
  a 10-second termination grace. Maximum duration is 510 nominal seconds plus
  30 seconds grace, leaving 60 seconds within the ordinary 10-minute budget.
  A `set -euo pipefail` shell session stops before later commands after any
  nonzero supervisor result.

The supervisor includes `/usr/bin/time -v` in the process log for the command's
own statistics and separately records the sampled sum of resident pages across
the entire process group. Diagnostic sidecar length is checked against the
emitted count; the preflight log preserves the exact size for each sidecar even
though the harness deletes it immediately. The offline replay is O(E) time and
O(live owner IDs plus lane kinds) memory and has the same host and disk floors.

## Review and verification

Selected M1 with `performance_auditor`. The first review required an executable
process-group supervisor, numeric memory/disk stops, an explicit checker
timeout, and preflight event-size data. The repair review found two further
blockers: replay needed to accept its existing sidecar as read-only input, and
preflight needed to enforce the event-count/file-size relationship. A narrow
delta review confirmed both fixes. No remaining finding is open in the scoped
process protocol.

Static checks passed:

- `python3 -m py_compile tools/run_f5c_resource_process.py`
- `RUSTC_WRAPPER= cargo check -q -p yu-solver --tests --features f5c_resource_probe`
- `git diff --check`

No test, process supervisor, preflight, diagnostic, matrix, benchmark, or
measurement ran. Runtime supervisor behavior and the physical-event replay
remain unverified. Measurement budget consumed is zero.

## Next gate

Run the reviewed three-process first gate from the measurement plan under one
unique run ID. Check the preflight's seven count/checksum/byte records, the
diagnostic sidecar length (`8 + 64 * event_count`), and successful replay.
Keep all outputs in `/tmp`; do not start the next process unless the prior
supervisor returns success. Use diagnostic elapsed time, sampled peak group
RSS, event count, and sidecar size to set the next reviewed 36-row budget.
