# F5c shared-acyclic hit-count preflight checkpoint

Status: the family-1 seed-ledger and family-4 capacity-decrease observer fixes
are reviewed, compiled, and pushed. The eighth supervised preflight passed the
first four D=32 rows, then timed out while producing a 654 MB sidecar with over
10 million complete events. No resource floor was breached. A fresh event-kind
histogram shows that most records are raw-walker SHAPE events, while
family-4-only coalescing would save about 1.4 million records. §26/§34 review
allows omitting request-only family-4 sidecar records while retaining exact
in-memory and boundary state. A fresh exact-conformance review also allows
coalescing same-capacity raw-walker SHAPEs for owner kinds 32–129 if every
observation still updates and validates its in-memory request, and all CREATE,
GROW, RELEASE, TRANSFER, and boundary state remains exact. This does not touch
the six-buffer kinds 12–17 or their same-ID staged transfer. The old 10/600
budget is exhausted; a bounded campaign and the existing request-witness path
still need closure.

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
floors, process-group monitoring, and all 36 matrix rows. Before resuming,
apply and review the request-only SHAPE coalescing conditions above, establish
the sampled request-witness path and expected event-count/replay-cost bounds,
then obtain a fresh performance review and primary approval for a concrete
bounded sequence. The linear K=32-to-4,000 event estimate is 1.28 billion
records / 82 GB, but is not a static upper bound and does not justify another
process by itself.

The user authorized autonomous continuation and expanded time/memory budgets;
no approval pause is needed for this scoped continuation.
