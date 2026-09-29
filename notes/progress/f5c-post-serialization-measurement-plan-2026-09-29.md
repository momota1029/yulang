# F5c post-serialization measurement plan — 2026-09-29

## Purpose and authority

The prior isolated `GuardedCycle/D=32/K=32` run used the `emit:false`
preflight, timed out after 120 seconds, and left a partial sidecar that cannot
be replayed. Its one-process authorization is consumed. This plan tests whether
the newly reviewed exact-kind suppression permits one complete, replayable
trace for that same tuple. It does not authorize K=4,000, a diagnostic, or
matrix rows.

The plan is within the existing F5 §§26/34 and no-cap addendum §4 evidence
gate. The read-only `architect` confirmed that one exact ignored
`emit:true` entrypoint and one exact replay selector are test/tool plumbing,
provided the tuple and production/matrix paths stay unchanged. Independent
pre-write plan reviews by `spec_auditor` and `performance_auditor` found the
bounded gate conforming and within the ordinary measurement budget. Primary
budget approval: one supervised solver invocation and one conditional offline
replay, with no retry.
The entrypoint and selector are now implemented and post-write reviewed. A
blocking mixed-selector early-return hole was repaired, then closed by a fresh
`spec_auditor` delta review. The performance delta review found no issue. No
measurement process has run under this plan.

## Exact input and process sequence

Input: one `GuardedCycle`, dimension `D`, size `32`, companion `K=32` case.
The entrypoint uses the existing guarded-cycle builder with `emit:true`, keeps
`F5C_FULL_WALKER_EVENTS` unset so exact kinds 54–56/116 remain suppressed, and
retains the completed sidecar. The checker selector accepts exactly this one
row and sidecar. It runs the existing full family, physical-lane, owner, and
session replay (all 261 physical lanes), then returns before matrix
adjacent-size ratio checks. Existing `from_env`, matrix tuple admission,
36-row validation, and the D=32/K=4,000 diagnostic remain unchanged.

Run exactly one supervised solver process. Use the existing process supervisor
with a 180-second wall timeout, a fixed 10-second TERM grace, offline Cargo,
`-j 2`, and one test thread. Compilation/startup is inside that timeout. Use a
unique run ID and unique `/tmp` log, monitor, summary, and sidecar paths. Before
start and throughout the run, require at least 8 GiB `MemAvailable` and at
least 8 GiB free disk, with the supervisor's sidecar/log multiplier check.
Sample process-group RSS, host availability, disk, log, and sidecar once per
second. Do not enable the full-event oracle mode.

Only if the solver exits successfully with no surviving child process, one
complete row, and a closed retained sidecar, run exactly one offline replay
process with a 60-second timeout and the same 10-second grace. This replay is
the sole measured checker sample. No warm-up or timing repetition is useful:
the decision is complete/replayable event-volume evidence, not a speedup
claim. The total budget is two process invocations, 240 seconds of timeout,
and at most 260 seconds including both TERM graces.

Run ID: `20260929-post-serialization-d32k32-01`. Exact invocations:

```text
python3 tools/run_f5c_resource_process.py --timeout-seconds 180 --log /tmp/f5c-post-serialization-d32k32-01.log --monitor /tmp/f5c-post-serialization-d32k32-01.monitor.jsonl --summary /tmp/f5c-post-serialization-d32k32-01.summary.json --sidecar /tmp/f5c-post-serialization-d32k32-01.events -- env -u F5C_FULL_WALKER_EVENTS cargo test -p yu-solver --lib --features f5c_resource_probe f5c_guarded_cycle_32_32_capture --offline -j 2 -- --ignored --nocapture --test-threads=1
python3 tools/run_f5c_resource_process.py --timeout-seconds 60 --log /tmp/f5c-post-serialization-d32k32-01-replay.log --monitor /tmp/f5c-post-serialization-d32k32-01-replay.monitor.jsonl --summary /tmp/f5c-post-serialization-d32k32-01-replay.summary.json --sidecar /tmp/f5c-post-serialization-d32k32-01.events --existing-sidecar -- python3 tools/check_f5c_resource_matrix.py --guarded-cycle-32-32 /tmp/f5c-post-serialization-d32k32-01.log
```

For a successful sidecar, verify `8 + 64 × record_count` bytes and its logged
checksum. Report retained identity records `R` and interval certificates `C`
separately. The protocol writes six fixed terminal records (four excluded
lanes, owner, and session) and at most one interval certificate per retained
record plus one final certificate, so successful size is
`8 + 64 × (R + C + 6)`, with `C ≤ R + 1` and upper expression `128R + 456`
bytes. This is an accounting identity, not a full-run completion or memory
bound.

## Stop conditions and acceptance

Stop the sequence immediately on a timeout, nonzero exit, process survivor,
host memory/disk floor breach, missing or duplicate row/sidecar, partial
64-byte record, byte/count/checksum mismatch, missing terminal certificate,
failed physical-lane/family/session reconciliation, or checker timeout. A
solver failure gets no replay process. Preserve the logs, monitor samples,
summary, and sidecar for diagnosis; do not retry, raise a timeout, or start a
different input in this plan.

Acceptance requires the exact single tuple, complete sidecar length/checksum,
all 261 physical lanes and family reductions reconciled, suppressed lane and
joint owner current/peak reconciled, composed session current/peak reconciled,
and no retained staged-transfer identity mismatch. Report elapsed time,
process-group peak RSS, minimum `MemAvailable` and free disk, monitor sample
count, `R`, `C`, record count, bytes, and checksum. The large hybrid trace
does not independently reconstruct suppressed owner IDs; the previously
passed complete small full-event oracle remains the lifecycle parity evidence.

The prior 120-second partial prefix had 5,502,335 events, including 5,496,399
target-kind records. A static same-prefix output counterfactual would be
`R=5,936`, at most 11,879 records / 760,264 bytes. This says nothing about
completion, runtime, peak memory, or retained kind-116 solver memory. The
suppression reduces sidecar serialization but does not reduce path-expanded
solver work or retained reentry paths.

If this run and replay pass, stop and review that evidence before selecting
another tuple or process budget. In particular, this plan does not authorize
the D=32/K=4,000 diagnostic or any matrix row.
