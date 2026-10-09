# Candidate closed-lifecycle dependency retirement

Date: 2026-10-10
Baseline: `5bbbdff7b6e90426a0aafe5573b576d82e77c6a1`
Status: bounded private implementation verified; full inference goal active
Authority: [user-selected withdrawal](../design/2026-10-10-simple-sub-legacy-withdrawal.md)
and [architect-confirmed packet](2026-10-10-candidate-closed-lifecycle-retirement-next-gate.md)
Mode: M2; semantic and regression reviewers; measurement budget zero

## Actual dependency removed

Private candidate startup no longer constructs a
`ClosedTypeFinalizationSession`; candidate finish never delegates closed
finalization. Graph batches also skip the unused closed-scheme slot allocation,
including historical private graph workers. The candidate owns genuine
`CandidateSolvedResult` / `FrozenInferenceData` rather than a legacy
`SolvedModule` with missing closed data. Shared execution preserves real HIR,
store, errors, projections, graph, Call inputs and resource accounting.

`candidate_call::observe` borrows its actual HIR, store and Call inputs.
Candidate export, fresh-use, conflict, effect-handle and foreign-HIR checks
retain their ownership. Ordinary `SolvedModule` and historical
`CandidateValueObservation` keep genuine closed finalization. No dummy arena,
receipt or empty closed scheme replaces the removed prerequisite.

This removes a runtime construction dependency superseded by live graph
solving and use-time freshening. It does not close a semantic proof obligation.
No DAG proof status changes in this slice. Independent post-finish transformed
public schemes, complete Call, hygiene, soundness and principality remain open.

## Independent review and repair

Producer: `candidate_lifecycle_retirement`, five explicitly leased solver
paths; no child Git operations. Frozen semantic review:
`co_effect_frozen_semantics`; regression review:
`candidate_lifecycle_regressions`. One accepted major: the intrusion test
still accessed `root_scheme_positions` directly on the new candidate result.
Initial all-target check independently reproduced E0609.

After both reviews completed, fresh producer `lifecycle_owner_repair` changed
that single access to `solved.data.root_scheme_positions`, preserving all
assertions, fixtures and traversal. Fresh semantic delta review found it
closed; earlier clean areas carried forward. No other major/blocking finding.

## Executed verification

All Cargo commands use `RUSTC_WRAPPER= timeout 180`, `-j 2 --offline`;
test commands additionally use `-- --test-threads=1`. One Cargo process at a
time. Final checks pass without warnings:

| Command after `cargo` | Result |
| --- | --- |
| `check -p yu-solver --all-targets --features shadow-apply-candidate` | pass |
| `check -p yu-solver` | pass |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_lifecycle_retirement` | 5 passed |
| `test -p yu-solver --features shadow-apply-candidate --test candidate_lifecycle_retirement` | 2 passed |
| `test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation` | 5 passed |
| `test -p yu-hir --features shadow --lib module::source_annotation::tests` | 1 passed |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests` | 6 passed |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests` | 5 passed |
| `test -p yu-solver --features shadow-apply-candidate --lib candidate_graph_call_` | 2 passed |
| `test -p yu-solver --features shadow-apply-candidate --test simple_sub_local_source_retirement` | 5 passed |
| `test -p yu-solver --features shadow-apply-candidate --test shadow_apply_candidate` | 19 passed |
| `test -p yu-solver --features shadow-apply-candidate --lib f5d_source_identity_boxed_and_flat_candidates_agree` | 1 passed |
| `test -p yu-solver --features shadow-apply-candidate --lib f5c_shared_closed_child_is_instantiated_once_per_use` | 1 passed |

Total: 52 passed. Actual constructor/finish delegates have single instrumented
wrappers; thread-local test probes count real calls and inject legacy failures.
Candidate counts remain zero, even with both legacy failures armed. Guards
exercise failure/drop HIR release, final resource failure before publication,
actual retained observations and ordinary closed counts/failures.

`git diff --check` passes. No benchmark, workspace/backend suite, exhaustive F5
suite or full semantic proof ran. Existing deep annotation fixtures retain
their explicit 16 MiB workers; the separately recorded parser stack risk is
unchanged. Records synchronized: this delivery, next-gate packet,
`tasks/current.md`, design index and withdrawal authority implementation status.

## Next gate

Authentic Unit primitive and source adapters precede operation declaration,
inert request-carrier formation and actual justified result consumers. Source
Apply alone cannot justify injecting a family contribution or an extra Force.
Private candidate results are not the selected independent public schemes.
Production/default F5 replacement on target `yulang3` remains pending.
