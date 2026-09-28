# F5c shared-acyclic hit-count preflight checkpoint

Status: after the logical-term measurement repair, the fifth supervised
preflight again completed the first two fixtures but failed during
`SharedAcyclic/D/32/K=32`. The exact-contract expectation for shared-summary
hits is 1,984; the observer recorded 4,032. A `compiler_referee` traced the
excess to the fixture assigning every use component its target root row. The
resulting self-routes replay each seeded function bound, making each root
traverse the cone twice. The remaining repair question is whether removing that
alias leaves the source-ring use rows isolated from extra root paths. No
expected value has changed. Diagnostic and matrix processes remain blocked.

## Failed attempt and evidence

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

For `D=32` and `K=32`, §34 expects `2*K*(D-1) = 1,984` hits. The supervisor
recorded peak process-group RSS 576,876,544 bytes, minimum `MemAvailable`
27,883,868,160 bytes, sidecar high-water 4,561,224 bytes, minimum free disk
665,995,304,960 bytes, and 9 monitor samples.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.log`
- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-logical-term-count-retry-01.events`

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

The compiler audit's smallest proposed repair is to retain each internal use
component's original row instead of overwriting it. Before writing, trace the
resulting root-to-use constraints and confirm that the source-ring rows do not
introduce extra qualifying root paths; then validate the fixture against §34.
Do not change the approved hit formula to fit the current fixture output.

The previous logical-term repair remains limited to reading
`TermLaneState.lengths[3]` for before/after counts; its exact formulas and
specification review are unaffected by this later assertion.

## Remaining measurement budget

The five completed supervised preflights used 16.06, 5.02, 6.03, 11.05, and
5.03 seconds. The next corrected preflight is allocated a 45-second timeout
and 10-second termination grace under fresh run ID
`20260929-shared-acyclic-hit-retry-01`. If it succeeds, the reviewed
300-second diagnostic and 150-second replay use processes seven and eight;
the maximum total is 548.19 seconds, leaving 51.81 seconds within the
8-process/10-minute budget. If it fails, keep diagnostic/replay blocked and
reassess the measurement plan before spending any further process invocation.

The user authorized autonomous continuation and expanded time/memory budgets;
no approval pause is needed for this scoped continuation.
