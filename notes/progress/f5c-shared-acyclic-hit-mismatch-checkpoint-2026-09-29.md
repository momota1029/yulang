# F5c shared-acyclic hit-count preflight checkpoint

Status: the sixth supervised preflight passed the shared-summary hit count,
then found 96 fixture-seeded slots (656 bytes) absent from the independent
family-1 event ledger at FinishOutput. Both seed helpers now report each
successful reservation and insertion to `F5cLiveEventLedger`. Post-write
`spec_auditor` review confirmed correct lanes, no duplicate owner events, and
unchanged formulas; the feature-enabled test-target compile passed. The
seventh and final preflight under the approved extension is next. Diagnostics
remain blocked until it succeeds.

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

The family-1 event mismatch was a fixture observer gap, not unaccounted
production capacity. `matrix_seed_value_bound` and `matrix_seed_value_edge`
now report the touched value row after successful reserve and push to the
independent `F5cLiveEventLedger`. The first observation captures capacity at
the old length; the second captures the inserted length with the same
capacity. In the shared D=32/K=32 fixture, 62 direct-edge slots plus 34
exact-bound slots total the observed 96-slot delta; `62*4 + 34*12 = 656`
bytes matches exactly. Post-write spec review confirmed lane mapping, no
duplicate owner events, and unchanged formulas. Both acyclic and guarded-cycle
builders share these seed helpers. The feature-enabled test-target compile
passed; the seventh supervised preflight remains to verify the repair.

## Remaining measurement budget

Six preflight invocations are complete and used 48.21 seconds combined. The
`performance_auditor` provided written justification for one bounded extension
above the ordinary eight-process limit: one more preflight, then the already
reviewed diagnostic and replay only if that preflight succeeds. The primary
approves this extension under `rules/performance.md`, capped at 9 total
invocations and 600 seconds. Allocate a 45-second timeout plus 10-second grace
to preflight, 300 seconds plus 10-second grace to diagnostic, and 150 seconds
plus 10-second grace to replay. The maximum is 573.21 seconds. If this seventh
preflight fails, stop the campaign and reassess; no eighth preflight is
approved by this plan.

The user authorized autonomous continuation and expanded time/memory budgets;
no approval pause is needed for this scoped continuation.
