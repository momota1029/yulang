# F5c guarded-cycle in-flight progress observer plan — 2026-09-29

## Question and authority

The exact `GuardedCycle/D=32/K=32` retained-sidecar capture timed out at 180
seconds before a row was emitted. Its 393,216-byte sidecar contained 6,143
complete records plus a 56-byte fragment and is not replayable. The last 12
monitor samples showed the sidecar flat while process RSS rose from about 1.89
GB to 1.98 GB. This does not identify the memory owner or the solver's work
progress.

The source audit found that `record_reentry` scans the active path, copies
trace hops into new vectors, and retains guarded paths until the component
success or rollback cleanup. The 2,048 distinct uncacheable-state assertion is
checked after the solve; it does not bound repeated reentry copies or work.
The observed RSS is consistent with retained reentry paths and ongoing solver
work, but that is inference only.

The read-only architect review confirmed a fixed-size
`cfg(all(test, feature = "f5c_resource_probe"))` in-flight observer fits F5 §§26/34 and no-cap
§4 if it changes no production behavior, public counter meaning, row output,
sidecar encoding, or solver result. The read-only performance review rejected
logging from `F5cDraftWorkMeter::charge`, because it is called from many inner
loops. The approved local plan samples only at existing generalization
task-pop boundaries, using geometric work-count milestones; output is bounded
to at most 64 records across the entire run, including all roots/components.
Use run-wide emitted-count state and disarm after record 64; local work
thresholds may reset with a new generalizer. Normal Cargo/test lines do not
count toward this progress-record cap. Each record reads current scalar counts for
work, retained `Reentries`, `ReentryPaths` lane capacity/bytes, current path,
active/frame depth, and the local worklist capacity. It scans no vector and
does not alter the 64-byte replay sidecar. If a single task is long, the next
sample is delayed until the next task boundary; absence of a line during that
interval is not evidence of no work.

Mode M1: test-only measurement instrumentation with one `performance_auditor`
review, which found the bounded boundary-sampling approach acceptable and
warned against a hook inside `charge`. Primary budget approval covers only the
single 120-second capture and conditional 60-second replay below; it does not
authorize a repeat.

Implementation review: the observer is confined to
`cfg(all(test, feature = "f5c_resource_probe"))`. The task-pop hook is after
the existing work-meter charge and pop. It reads only scalar fields and emits
at next-power-of-two cumulative work milestones; one thread-local state spans
all roots/components and disarms after 64 records. The RAII guard clears it on
return or unwind. A focused post-write `performance_auditor` review found no
blocking issue: there is one TLS lookup per task pop in probe builds, fixed
scalar reads and bounded formatting on at most 64 milestones, and no added
production-path work, traversal, clone, sidecar field, or counter change. The
compile-only feature build and `git diff --check` passed. No ignored workload
has run for this gate.

## Measurement budget

This is a separate diagnostic plan; the earlier 180-second attempt is consumed
and will not be retried under its plan. After the test-only observer is
implemented and receives focused post-write performance review, run at most
one exact `GuardedCycle/D=32/K=32` progress capture. Use 120 seconds plus a
10-second TERM grace. A complete row and sidecar may be followed by one offline
replay process capped at 60 seconds plus a 10-second grace. Total maximum: two
process invocations and 200 seconds including both grace periods. No warm-up,
repetition, or retry.

Use 8-GiB `MemAvailable` and free-disk floors, with one-second process-group
RSS/availability/disk/log/sidecar sampling and the existing supervisor's
sidecar/log multiplier check. Keep the full-event environment variable unset.
Use unique run artifacts. Before any new process, inspect the active branch and
host floors again.

Run ID: `20260929-guarded-progress-d32k32-01`. Exact invocations after the
progress entrypoint is implemented and reviewed:

```text
python3 tools/run_f5c_resource_process.py --timeout-seconds 120 --log /tmp/f5c-guarded-progress-d32k32-01.log --monitor /tmp/f5c-guarded-progress-d32k32-01.monitor.jsonl --summary /tmp/f5c-guarded-progress-d32k32-01.summary.json --sidecar /tmp/f5c-guarded-progress-d32k32-01.events -- env -u F5C_FULL_WALKER_EVENTS cargo test -p yu-solver --lib --features f5c_resource_probe f5c_guarded_cycle_32_32_progress_capture --offline -j 2 -- --ignored --nocapture --test-threads=1
python3 tools/run_f5c_resource_process.py --timeout-seconds 60 --log /tmp/f5c-guarded-progress-d32k32-01-replay.log --monitor /tmp/f5c-guarded-progress-d32k32-01-replay.monitor.jsonl --summary /tmp/f5c-guarded-progress-d32k32-01-replay.summary.json --sidecar /tmp/f5c-guarded-progress-d32k32-01.events --existing-sidecar -- python3 tools/check_f5c_resource_matrix.py --guarded-cycle-32-32 /tmp/f5c-guarded-progress-d32k32-01.log
```

Stop on timeout, nonzero exit, process survivor, or host floor breach. The
observer enforces its run-wide 64-record cap in code. After completion or
timeout, validate progress-line shape/count from the captured log; malformed
or more than 64 progress lines rejects the run, and no replay follows. The
supervisor does not parse progress records while the solver runs, so its
120-second wall limit contains that check. Preserve artifacts and do not retry
or select another tuple. If the run completes, replay only after complete
row/count/checksum/sidecar-length checks. Report milestone work deltas against
reentry count, retained
path capacity/bytes, active path/frame depths, RSS, elapsed time, and
sidecar bytes. Do not infer an allocator owner or total-work bound from RSS
alone.

The process is useful only to distinguish whether sampled work and retained
`ReentryPaths` capacity continue to rise while serialization remains low. It
does not establish a semantic mismatch, prove an all-input complexity order,
or authorize a larger timeout, a K=4,000 diagnostic, or matrix rows. Any next
solver process needs a separate reviewed budget after this evidence is
adjudicated.

## Attempt outcome

The observer was implemented in `f5c_generalization.rs` and the ignored
entrypoint added in `tests/f5c_resource_probe.rs`. Focused compile-only
verification passed:

```text
RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe --offline -j 2 --no-run
git diff --check
```

The post-write `performance_auditor` review found the bounded task-pop hook
acceptable. Its one TLS lookup per task pop exists only in test+feature builds;
each record reads fixed scalars and formatting is limited to 64 records. A
delta review of the first-record separator repair was also clean.

The authorized progress capture ran once and timed out at 120 seconds. The
supervisor exited with status -15 at 121.335 seconds after TERM; one process
invocation and 121.335 seconds were consumed, and no replay invocation ran.
There was no completed row, so the sidecar is incomplete and not replayable.
The monitor recorded 125 samples, 1,290,932,224-byte peak process-group RSS,
29,548,920,832-byte minimum `MemAvailable`, and 665,915,027,456-byte minimum
free disk. Neither 8-GiB floor was breached. Peak log and sidecar sizes were
4,632 and 51,412,992 bytes.

The captured log contains 26 sequential progress records, from work=2 through
work=134,217,817. Reentries rose from zero to 634,860; retained
`ReentryPaths` capacity rose from zero to 41,862,272 slots (1,004,694,528
bytes). The first record was concatenated to libtest's unfinished `test ...`
prefix, so the capture does not pass the plan's standalone-line validation.
The implementation now starts the first record on a fresh line; its
compile-only check and focused performance delta review passed. The single-run
budget is consumed, so the formatting repair was not exercised by another
capture. The observer data and RSS do not prove allocator ownership or a total
work bound. No timeout retry, larger tuple, or matrix row is authorized by
this plan.
