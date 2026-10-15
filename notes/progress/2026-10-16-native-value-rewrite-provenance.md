# Native Value dispatch: actual extrusion rewrite provenance

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Status: bounded causal repair and native operational retention gate complete
Code baseline: native `bf0562382`; full working HEAD `43d8ab1a1`

## Cause and existing authority

`dispatch_live_item` reuses every nonempty non-Function diagnostic-child
frontier as if it were an actual whole-Value extrusion rewrite. That frontier
also contains ordinary opposite-bound replay consequences and canonical
diagnostic edges. These constructors establish consequences, not a certificate
that replaces the original contextual bound for every later interaction.

The [Authoritative contextual attachment contract §4](../design/2026-10-10-contextual-attachment-admission-design.md)
requires retained contextual obligations/provenance or a proved discharge.
`candidate_context_value_rewrite` itself requires an actual whole-Value
extrusion rewrite. Independent architecture inspection and semantic referee
`checked_result_semantics` confirm the producer/consumer mismatch and authorize
the causal repair under that existing contract. No new language decision,
source restriction, F5 cutover or complete H2 certification follows.

The [constructive mutation audit](../theory/2026-10-16-native-relation-duplicate-preservation.md)
and [complementary source trace](2026-10-16-native-relation-duplicate-falsifier.md)
authenticate repeated `x <= alpha` with different call-source relations and
an ordinary `Int <= alpha` diagnostic child. The later relation is stamped
without its original bound association. This is not an observable type-result
counterexample: `x:int` can compensate scalar inclusion, and Derived children
retain some provenance. The missing argument is the certified replacement of
all original contextual obligations, rather than disappearance of all evidence.

## Repair acceptance

Only the genuine changed whole-Value extrusion constructor may establish
semantic rewrite eligibility. Dispatch reuses that retained rewrite; ordinary
diagnostic consequences use the normal contextual-bound admission path.
Preserve genuine recapture, existing copied graphs, canonical handling,
generation invalidation and route rollback. Neither diagnostic existence,
`field=None` nor endpoint shape certifies extrusion provenance.

Focused verification must inspect the second authentic bound relation/source
association, ordinary diagnostic children, genuine retained extrusion reuse,
mixed diagnostics, rollback and intrusion replay. No expectation is changed
merely to match current output.

## Mode and resource budget

Architecture selects a candidate-only inline
`retained_extrusion_rewrite: Option<CanonicalValuePairKey>` on the existing
Value pair memo. New entries start empty; canonicalization runs first and
does not populate it. Only the genuine extrusion producer computes and
publishes one final rewritten pair after successful construction. A retained
value is consumed before that producer can run again, so direct state
induction establishes at most one live replacement per original key.
Ordinary diagnostic-edge identity and deduplication remain unchanged.

Memo replacement, completion invalidation and root reopening preserve the
replacement. Candidate journaling copies it, and existing rollback restores
it with the retained copied graph or removes a newly admitted memo. The
setter must reject an inconsistent replacement. Reuse drives exactly that
one child with current relation/context and authentic recapture; an empty
field follows ordinary bound admission regardless of diagnostic descendants.
This retains the existing generation/persistence policy, with no new registry.

Mode M2, one implementation pass and at most two closure reviewers:
`compiler_referee` for responsibility/lifecycle and `performance_auditor` for
the changed memo hot path. Primary owns all Cargo and Git operations.
Convergence: all accepted major findings repaired in one batched pass, exact
focused verification, resource accounting and current task/design records.

The static cost audit finds the old dispatch performs O(RD) heavy child
recapture/context/queue operations for R revisits and D diagnostic children.
It authorizes no benchmark claim. Representation selection must account for
memory, journal reconstruction and repeated dispatch; avoid another registry
or allocating fresh copy graphs. Timing budget remains zero samples/processes
unless a concrete unresolved decision later requires measurement.

Independent semantic `checked_result_semantics` and resource
`rewrite_provenance_cost` closure reviews are CLEAN. One new lifecycle fixture
initially attempted Fresh admission with unfinished diagnostic work. The
batched repair uses a separate identical solver instance driven through two
complete production `constrain_live_item` calls and asserts quiescence before
the original rollback assertions. No unfinished state was cleared, production
code changed or expectation weakened. A minor proof qualification now
distinguishes the authentic source trace from manually constructed mixed
diagnostic coverage. The semantic delta reviewer accepts both repairs.

The [constructive invariant and actual code bridge](../theory/2026-10-16-native-retained-value-rewrite-invariant.md)
has fresh independent semantic acceptance, including the original local native
operational obligation-retention composition. The primary accepts that gate
under its existing transition/drain laws. This is not source MODEL or semantic
adequacy of every underlying extrusion/context rewrite.

## Exact verification

All Cargo runs used two build jobs, one test thread and a 180-second timeout.
The unchanged authentic regression has SHA-256
`2a5550bef88d985c4d344247c9c91c865a49c2e7e3ab5a9b620b1f074261f5a0`.
It was transplanted unchanged into a disposable detached `8d2699197` worktree:
0 passed/1 failed at the missing original-bound association. The same test
passes after repair. Cached baseline binaries from shared-target reuse were
excluded; candidate evidence uses a fresh root-source compilation. The
disposable worktree was removed after exact fixture equality verification.

Commands below share the prefix `CARGO_BUILD_JOBS=2 timeout 180s`:

```sh
cargo test --locked -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests::repeated_source_argument_keeps_original_bound_relations_with_ordinary_diagnostics -- --exact --test-threads=1
cargo test --locked -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests:: -- --test-threads=1
cargo test --locked -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests::exact_relation_completion_keeps_contexts_and_component_kinds_distinct -- --exact --test-threads=1
cargo check --locked -p yu-solver
cargo test --locked -p yu-playground -- --test-threads=1
```

Final results: authentic regression 1 pass; intrusion module 17 pass; contextual
completion 1 pass; default-feature solver check pass; playground phase check
108 pass, zero failures/ignored/warnings. `git diff --check` and focused
documentation/hash checks pass. The authentic regression is included in the
17 intrusion cases, rather than an additional distinct case.

Observed build/verification resources (not timing benchmarks): baseline
reproduction 30.29 s / 1,454,296 KiB peak; fresh fixed reproduction 23.00 s /
1,460,548 KiB; final intrusion module 4.39 s / 944,872 KiB; default check
3.08 s / 387,536 KiB; playground 8.45 s / 665,796 KiB. Logs and `.resources`
files are under `/tmp/yulang-native-rewrite-*-20261016.*`. Benchmark processes
and samples: zero. Exact memo padding-dependent byte growth was not queried;
the static resource audit confirms constant inline growth and actual-size
accounting, with no new collection or child scan.

The unfiltered 711-test solver library, broad contextual suite, workspace
tests/check and timing benchmarks were omitted. Their resource behavior is
not required for this focused repair; the known playground package supplies
the M2 phase check. No broad run is repeated after these record updates.

## Residual parents

Native operational duplicate retention is closed at the reviewed scope.
Semantic adequacy of underlying extrusion/context operations, source MODEL,
generalization, H1/H2/U, soundness/principality and F5 remain OPEN. This gate
does not promote those separate source or production obligations.
