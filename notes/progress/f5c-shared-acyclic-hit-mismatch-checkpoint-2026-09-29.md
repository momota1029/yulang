# F5c shared-acyclic hit-count preflight checkpoint

Status: the family-1 seed-ledger and family-4 capacity-decrease observer fixes
are reviewed, compiled, and pushed. The eighth supervised preflight passed the
first four D=32 rows, then timed out while producing a 654 MB sidecar with over
10 million complete events. No resource floor was breached. A fresh event-kind
histogram showed that most records were raw-walker SHAPE events. The approved
raw-walker coalescing slice is now implemented and reviewed; its focused
synthetic replay witness passed. The exact paths, event rules, focused checks,
and the single new preflight budget are recorded below. This does not touch the
separately checkpointed six-buffer kinds 12–17 or their same-ID staged
transfer.

## Failed attempt and evidence

### Fifth preflight: shared-summary hit count

Run ID `20260929-logical-term-count-retry-01` exited 101 after 5.025 seconds.
It completed the `IndependentIdentities/D/32` and `IdentityAliases/U/32`
tuples, then failed at
`crates/yu-solver/src/tests/f5c_resource_probe.rs:1872` in the shared acyclic
fixture. The test had already passed its logical-term count, raw-state, and
summary-admission assertions. The failing comparison was:

```text
assertion `left == right` failed
left: 4032
right: 1984
```

For `D=32` and `K=32`, §34 expects `2*K*(D-1) = 1,984` hits. After the use-row
alias repair in the following retry, this assertion passed.

The fifth-attempt supervisor recorded peak process-group RSS 576,876,544
bytes, minimum `MemAvailable` 27,883,868,160 bytes, sidecar high-water
4,561,224 bytes, minimum free disk 665,995,304,960 bytes, and 9 monitor
samples.

### Sixth preflight: family-1 event reconciliation

Run ID `20260929-shared-acyclic-hit-retry-01` exited 101 after 5.024 seconds.
It completed the first two tuples and reached FinishOutput in the shared
acyclic fixture, then stopped at
`crates/yu-solver/src/lib.rs:16180` with event-ledger `(capacity, retained)`
`(1856, 27328)` against family-1 `(1952, 27984)`. The supervisor recorded
peak process-group RSS 607,596,544 bytes, minimum `MemAvailable`
27,833,888,768 bytes, sidecar high-water 5,421,448 bytes, minimum free disk
666,045,722,624 bytes, and 9 monitor samples.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.log`
- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.events`
- `/tmp/f5c-preflight-20260929-shared-acyclic-hit-retry-01.log`
- `/tmp/f5c-preflight-20260929-shared-acyclic-hit-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-shared-acyclic-hit-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-shared-acyclic-hit-retry-01.events`

## Authority and current gate

### Eighth preflight: event-volume timeout

Run ID `20260929-memo-capacity-decrease-retry-01` was terminated at the
45-second wall timeout; the supervisor reports exit `-15` after 46.164
seconds. It emitted the first four D=32 events (independent identities, aliases,
shared acyclic, and independent acyclic), then continued in the guarded-cycle
case without reaching its terminal event. The sidecar contained 10,221,439
complete 64-byte records and a partial trailing record when the process was
terminated; high-water size was 654,172,160 bytes. The supervisor recorded
peak process-group RSS 773,201,920 bytes, minimum `MemAvailable`
27,627,048,960 bytes, minimum free disk 665,381,261,312 bytes, and 50 monitor
samples. The active 8-GiB memory/disk floors held.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-memo-capacity-decrease-retry-01.log`
- `/tmp/f5c-preflight-20260929-memo-capacity-decrease-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-memo-capacity-decrease-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-memo-capacity-decrease-retry-01.events`

The timeout is not evidence of a compiler semantic mismatch or a memory/disk
floor failure. However, the 10.2-million-event partial stream is not a valid
replay input and exceeds the expected event size from earlier attempts. A
`performance_auditor` requires a static bound on GuardedCycle event production
and remaining fixtures, plus evidence that offline replay can process that
volume, before justifying another retry. A streamed read-only histogram found
10,221,439 complete records, 56 trailing bytes, and these operation totals:
657,602 CREATE, 8,684,774 SHAPE, 435,753 GROW, and 443,310 RELEASE. The largest
SHAPE kinds are `Tasks` (3,972,821), `Path` (883,113), and `Values` (827,118).
Family-4 lanes 11, 16, 17, and 18 account for 1,402,369 request-only SHAPEs.
The rest is mostly raw-walker owners. A fresh `spec_auditor`, `compiler_referee`,
and `architect` confirmed that §34 does not require serializing every
same-capacity family-4 requested-length change: in-memory lane state and exact
boundary/GROW/DECREASE records preserve the contract. This observer optimization
is within the current gate, but it only removes the family-4 portion. A separate
fresh `spec_auditor` review found the same conformance for raw-walker kinds
32–129; the architect review is conditional on validating `requested <=
capacity` at every observation before suppressing SHAPE serialization. Keep the
in-memory request current and preserve lifecycle/transfer records and sampled
lane requests. These kinds are separate from FlatDraft kinds 12–17 and their
same-ID staged transfer.

The performance audit attributes the large stream to test-only observer output,
not evidence of production allocation growth or extra solver visits. Linear
scaling from K=32 to K=4,000 would suggest roughly 1.28 billion records / 82 GB,
but this is an extrapolation scenario, not an upper bound; the authoritative
GuardedCycle builder does not assert a total-work order. Establish the request
witness/check path and the post-coalescing event scale before setting new
preflight, diagnostic, or replay limits.

The 10-invocation/600-second approval
covered this eighth preflight followed by conditional diagnostic/replay; it
covers no further process after the timeout. Assess whether same-capacity,
request-only SHAPE records can be coalesced in the relevant remaining owner
families without reopening the separately checkpointed carrier/transfer work.
Do not run diagnostic/replay until a fresh static performance bound and
approval close this gap.

### Seventh preflight: family-4 capacity observation

Run ID `20260929-live-event-seed-retry-01` exited 101 after 7.029 seconds. It
emitted `IndependentIdentities/D/32`, `IdentityAliases/U/32`,
`SharedAcyclic/D/32/K=32`, and `IndependentAcyclic/D/32/K=32`, then panicked in
the guarded-cycle fixture at
`crates/yu-solver/src/f5c_draft_heap.rs:453` with
`memo buffers release before capacity shrinks`. The supervisor recorded peak
process-group RSS 667,705,344 bytes, minimum `MemAvailable` 27,693,441,024
bytes, sidecar high-water 17,776,640 bytes, minimum free disk 666,078,367,744
bytes, and 11 monitor samples.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-live-event-seed-retry-01.log`
- `/tmp/f5c-preflight-20260929-live-event-seed-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-live-event-seed-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-live-event-seed-retry-01.events`

The assertion is in the test-only `ComponentMemoEvents::observe`, not the
compiler's inference path. It assumes each observed family-4 capacity remains
monotone until release. The memo observes standard HashMap capacities for
`roots`, `incidence_heads`, `active_rows`, and `active_conflicts`. HashMap
capacity is usable slots; tombstone removals can lower the reported value
without releasing the backing allocation. F5 §34 measures the container's
reported `.capacity()` times slot size, so this is an in-place accounting
transition under the existing contract. Preserve the owner ID and historical
peak while applying the signed decrease to current family totals and replay.
The adjacent `active_set` HashSet capacity is cached at reservation but its
reported capacity can also change on insertion/removal; refresh that cache
before physical memo observations. A fresh reviewer confirmed no design change
is needed. The exact failing HashMap lane is not proven because the assertion
does not include lane and old/new capacity.

The repair emits event operation `DECREASE` for a lower reported capacity,
keeping the owner ID, lane, and slot size; it applies the signed change to
current totals while preserving peaks and growth counts. The offline checker
accepts that operation only for family 4 with the same owner shape and a
strictly lower capacity. `active_set` capacity is refreshed after insertions,
normal removals, and rollback removals before memo observations. Tombstone-only
decreases do not set the clear marker; a logical transition to empty and the
existing explicit release/reset paths retain their markers. The post-write
`spec_auditor` review is clean. Verification passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- Python `ast.parse` syntax check for `tools/check_f5c_resource_matrix.py`

Run the eighth supervised preflight with ID
`20260929-memo-capacity-decrease-retry-01`; diagnostics remain blocked until it
passes.

F5 foundation §34 in
`notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
defines `shared_acyclic(D,K)` as D roots entering one 2K-state cone, with 2K
summary admissions and `2K(D-1)` summary hits. In
`matrix_graph_session`, after assigning fresh rows to definition roots, the
fixture overwrites each internal use row with its target root row. The SCC
`route_internal` then adds a self edge for each use and replays that root's
seeded `PositiveFunction` bound into itself. This creates two cone traversals
per root. The measured `2K(2D-1) = 4,032` is consistent with that fixture path.
The counter owner counts reused transitive incidences and is not implicated by
the inspected path.

The compiler audit's smallest repair is to retain each internal use
component's original row instead of overwriting it. `InferenceSession::try_new`
assigns those collected rows unique dense ordinals before admission; the
fixture later appends fresh definition-root rows. The batch freezes SCC
membership independently of these mutable live ordinals. After removing the
overwrite, each internal route adds an edge from a fresh root to an original
use row: the solver records the root in the use row's direct-lower list and
the use row in the root's direct-upper list. Positive generalization follows
direct-lower/exact-lower edges, so this route cannot return to a fresh root or
add a second cone request. The same direction leaves each guarded-cycle root
with its one seeded rotation edge. Original source rows are not seeded roots,
and all rows begin generic, so the inspected old-row graph adds neither a
positive root traversal nor a non-generic closure seed.

The pre-write `spec_auditor` confirmed that deleting only the use-row overwrite
preserves the §34 shared acyclic cone, independent-cone case, and guarded-cycle
rotations without changing expected formulas or output assertions. The six-line
alias loop was removed. Post-write spec delta review confirmed the D fresh root
setup, source/admission order, all three builder shapes, and formulas are
unchanged. Focused check passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`

The supervised preflight must now prove the exact schemes and summary counters.
Do not change the approved hit formula to fit the current fixture output.

The previous logical-term repair remains limited to reading
`TermLaneState.lengths[3]` for before/after counts; its exact formulas and
specification review are unaffected by this later assertion.

The sixth preflight's family-1 event mismatch was a fixture observer gap, not unaccounted
production capacity. `matrix_seed_value_bound` and `matrix_seed_value_edge`
now report the touched value row after successful reserve and push to the
independent `F5cLiveEventLedger`. The first observation captures capacity at
the old length; the second captures the inserted length with the same
capacity. In the shared D=32/K=32 fixture, 62 direct-edge slots plus 34
exact-bound slots total the observed 96-slot delta; `62*4 + 34*12 = 656`
bytes matches exactly. Post-write spec review confirmed lane mapping, no
duplicate owner events, and unchanged formulas. Both acyclic and guarded-cycle
builders share these seed helpers. The feature-enabled test-target compile
passed. The seventh preflight passed the earlier shared-hit and family-1
reconciliation checks, then reached the family-4 HashMap capacity-decrease
observer failure described above.

## Remaining measurement budget

Eight preflight invocations are complete and used 101.40 seconds combined. The
performance review and primary approval allowed 10 total invocations and a
600-second cap, conditional on this eighth preflight passing before diagnostic
and replay. It timed out, so no further process is covered. Keep the 8-GiB
floors, process-group monitoring, and all 36 matrix rows. That 10/600 campaign
is exhausted. The user's standing authorization permits autonomous budget
expansion; the new process below is a separately reviewed and recorded
one-invocation budget.

### Raw-walker request-event coalescing and next preflight

The implementation is limited to raw-walker owner kinds 32–129 and the
required observed-map removal path:

- `crates/yu-solver/src/f5c_draft_heap.rs`: `RawWalkerOwner::observe` validates
  `requested <= capacity` on every observation and always updates its stored
  request/capacity. It emits GROW only for a strict increase, DECREASE for a
  strict decrease, and no event for same-capacity request-only changes. Owner
  creation, release, transfer identity, and the request field at serialized
  growth/decrease boundaries remain intact.
- `crates/yu-solver/src/f5c_generalization.rs`:
  `ObservedWalkerMap::remove` observes reported capacity after removal, closing
  the `BoxedRawBounds` path that could otherwise miss a capacity decrease.
- `tools/check_f5c_resource_matrix.py`: op7 accepts either existing family-4
  lanes or walker kinds 32–129, only with identical owner kind and slot size,
  strictly lower capacity, zero target, and the general `requested <= actual`
  invariant. Kinds 12–17 and their family-6 transfer rule are unchanged.

Selected M2. Pre-write `spec_auditor`, `architect`, and `compiler_referee`
reviews established the request validation, reported-capacity decrease, and
missing map-removal observation conditions. Post-write `spec_auditor` review
is clean. The `performance_auditor` found the observation count unchanged and
the extra work bounded to validation/comparison/state writes; it recommends
one supervised D=32/K=32 preflight as the next evidence and defers any
K=4,000 diagnostic or replay budget until that result is reviewed. The
primary authorized this one process under the user's standing budget decision.

Focused verification passed in the implementation pass:

- Three focused `yu-solver` test invocations covering raw-walker owner events,
  observed walker sets, and same-ID transfer.
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- Python syntax compilation of `tools/check_f5c_resource_matrix.py`.
- Synthetic `replay_f6_events` witness: accepted CREATE/GROW/DECREASE/GROW/
  RELEASE under one owner ID, reconciled lane 150 to zero current and an
  8-slot/64-byte peak, and rejected five malformed DECREASE cases, including
  staged kind 12.
- `git diff --check`.

The separately authorized supervised preflight ran once with run ID
`20260929-raw-walker-coalescing-preflight-01`:

```sh
python3 tools/run_f5c_resource_process.py --timeout-seconds 60 \
  --log /tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.log \
  --monitor /tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.monitor.jsonl \
  --summary /tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.summary.json \
  --sidecar /tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.events \
  -- /usr/bin/time -v cargo test -p yu-solver --lib \
  --features f5c_resource_probe f5c_resource_matrix_preflight \
  --offline -j 2 -- --ignored --nocapture --test-threads=1
```

The supervisor sets `RUSTC_WRAPPER` empty, enforces 8-GiB minimum available
memory and disk reserve, samples the process group once per second, and sends
TERM followed by KILL after the fixed 10-second grace. This process budget is
one invocation and at most 60 seconds plus that grace. It is measurement
containment, not a language input or compiler-work cap. Do not start the
corrected K=4,000 diagnostic, replay, or matrix rows until the result and event
volume are reviewed.

It compiled in 4.28 seconds, completed the first four D=32 rows, and then hit
the 60-second wall limit while the guarded-cycle row was still producing
events. The supervisor sent TERM/KILL; exit status was `-15` after 61.178
seconds. No memory or disk floor was breached. The partial sidecar has
282,443,776 bytes, 4,413,183 complete records, and 56 trailing bytes. Its
operation totals are 987,547 CREATE, 1,936,673 SHAPE, 739,431 GROW, 664,966
RELEASE, and 84,566 DECREASE. The process peaked at 666,099,712 bytes of group
RSS; minimum `MemAvailable` was 30,472,093,696 bytes, minimum free disk was
666,602,938,368 bytes, and the supervisor took 65 samples. The first four
completed row summaries were:

- `IndependentIdentities/D/32`: 23,256 events, 1,488,392 bytes.
- `IdentityAliases/U/32`: 29,640 events, 1,896,968 bytes.
- `SharedAcyclic/D/32/K=32`: 34,577 events, 2,212,936 bytes.
- `IndependentAcyclic/D/32/K=32`: 308,239 events, 19,727,304 bytes.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.log`
- `/tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.summary.json`
- `/tmp/f5c-preflight-20260929-raw-walker-coalescing-preflight-01.events`

This timeout is not evidence of a semantic mismatch or resource-floor
failure, and the partial stream is not a valid replay input. A fresh
`performance_auditor` found that 1,936,673 SHAPE events remain in the partial
stream, of which 1,932,317 are family-4 component-memo kinds 562, 567, 568, and
569. Its single-path counterfactual after suppressing those events is about
2,480,866 records / 158.8 MB, not a bound or completion estimate. Streaming
observation showed the sidecar and RSS still rising at the timeout; the
measured headroom is local evidence only.

The `ComponentMemoEvents::observe` same-capacity SHAPE coalescing repair is now
implemented in `crates/yu-solver/src/f5c_draft_heap.rs`. It preserves
`requested <= capacity`, updates stored request/capacity on every observation,
keeps strict GROW/DECREASE events and signed current/peak accounting, and leaves
CREATE/release/identity intact. Post-write `spec_auditor` review is clean. The
focused check passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --lib --features f5c_resource_probe component_memo_ --offline -j 2 -- --test-threads=1` (2 passed).
- `git diff --check -- crates/yu-solver/src/f5c_draft_heap.rs`.

The spec review's minor replay-coverage note is closed by primary review:
omitting same-capacity request-only records changes no physical current/peak
transition, the shared observer code covers all 20 family-4 lanes, and the
focused test exercises the strict decrease/growth/release sequence plus the
latest in-memory request. The sampled request witness remains in the separate
lane summary and is not reconstructed from every sidecar mutation.

The source audit could prove the D=32/K=32 fixture's 2,048 uncacheable states,
128 terms, and 128 seeded bounds, but it found no useful upper bound on
path-expanded solver visits or owner-event output. F5's no-cap addendum leaves
guarded-cycle total-work order open. This does not block one ordinary,
supervised measurement aimed specifically at the confirmed family-4 emission
delta. The performance review supports exactly one isolated D=32/K=32 run
under a 120-second timeout plus 10-second TERM grace, the existing 8-GiB
memory/disk floors, and one-second group monitoring. It does not support
K=4,000 scaling or replay yet.

An `architect` confirmed an ignored entrypoint can invoke the existing
GuardedCycle D=32/K=32 case with `emit:false` inside the current §26/§34 gate;
the approved `from_env` selector and matrix tuples must remain unchanged. The
entrypoint has been added as `f5c_guarded_cycle_32_32_preflight` in
`crates/yu-solver/src/tests/f5c_resource_probe.rs`; the focused test-target
compile passed with
`RUSTC_WRAPPER= cargo test -p yu-solver --lib --features f5c_resource_probe --no-run`.
The post-write `spec_auditor` review is clean. Its exact tuple matches the
existing preflight case and preserves the sidecar byte check and removal. The
initial compile invocation without `RUSTC_WRAPPER=` failed before build because
sccache could not start; the retry above passed.

The primary authorizes this single isolated measurement (run ID
`20260929-family4-coalescing-isolated-guarded-cycle-01`):

```sh
python3 tools/run_f5c_resource_process.py --timeout-seconds 120 \
  --log /tmp/f5c-preflight-20260929-family4-coalescing-isolated-guarded-cycle-01.log \
  --monitor /tmp/f5c-preflight-20260929-family4-coalescing-isolated-guarded-cycle-01.monitor.jsonl \
  --summary /tmp/f5c-preflight-20260929-family4-coalescing-isolated-guarded-cycle-01.summary.json \
  --sidecar /tmp/f5c-preflight-20260929-family4-coalescing-isolated-guarded-cycle-01.events \
  -- /usr/bin/time -v cargo test -p yu-solver --lib \
  --features f5c_resource_probe f5c_guarded_cycle_32_32_preflight \
  --offline -j 2 -- --ignored --nocapture --test-threads=1
```

The compile finished in 0.26 seconds. The isolated case then timed out at 120
seconds while still generating GuardedCycle events; no assertion or terminal
event summary ran. The supervisor terminated it after 120.292 seconds with
status `-15`. No floor was breached. Peak process-group RSS was
1,358,286,848 bytes, minimum `MemAvailable` was 29,573,771,264 bytes, minimum
free disk was 666,216,099,840 bytes, and the monitor took 124 samples. The
partial sidecar contains 352,149,504 bytes, 5,502,335 complete records, and 56
trailing bytes. It cannot be replayed.

The one-pass operation histogram is 2,352,229 CREATE, 1,558,334 GROW, 1,587,416
RELEASE, 4,356 SHAPE, no TRANSFER/CHECKPOINT/DECREASE. The family-4
request-only SHAPE coalescing worked: no kind 551–570 SHAPE event remains. The
remaining 4,356 SHAPEs are family-1 kinds 512–529, family-3 kinds 530–550, and
one WalkerLane kind. The four largest kinds are all WalkerLane:

| Kind | Walker lane | CREATE | GROW | RELEASE |
| --- | --- | ---: | ---: | ---: |
| 54 | `FlatComparison` | 793,708 | 200,096 | 793,708 |
| 55 | `FlatPositiveParts` | 193,419 | 193,419 | 193,419 |
| 56 | `FlatNegativeParts` | 600,289 | 400,192 | 600,289 |
| 116 | `ReentryPaths` | 763,930 | 763,930 | 0 |

Kinds 54–56 are short-lived physical vectors created in
`crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs` during repeated
flat comparisons and part collection; their owner IDs are created/grown/
released around each operation. Kind 116 comes from
`F5cGeneralizer::record_reentry` in `crates/yu-solver/src/f5c_generalization.rs`.
When a guarded path is retained, its `Vec<F5cTraceHop>` and `RawWalkerOwner`
move together into `reentries` and `reentry_path_owners`; the partial run has
not reached their release. This is path-expanded retained data, not only
test-observer churn.

The fresh performance auditor recommends no further solver process yet. The
architect's evidence ruling is that §§26/34 require exact requested/current
capacity, retained and simultaneous peak bytes, growth and lifecycle/transfer
witnesses, but do not require an offline serialized record for every transient
owner. A fixed-size test-only online ledger is allowed only if it observes
every lane transition, maintains checked per-lane and global current/peak at
the same time, preserves owner-local identity/slot/request/lifecycle checks,
and remains independent from production counters. A four-kind-only aggregate
cannot preserve cross-family same-time peaks. Full identity evidence for the
FlatDraft kinds 12–17 transfer remains intact.

Next gate: selected M2. Obtain a `spec_auditor` review of the online ledger
invariants and a `performance_auditor` review of its cost/sidecar reduction;
then implement the smallest sound observer slice, prove it against the old
offline replay on a small complete witness, and obtain a fresh process budget.
No solver process, replay, K=4,000 diagnostic, or matrix row is currently
authorized. The user's standing time/memory authorization does not remove this
review gate.
