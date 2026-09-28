# F5c no-cap §26/§34 scale measurement plan

Status: Reviewed; measurement campaign approved; execution pending successful preflight
Reviewed-by: spec_auditor, performance_auditor (matrix, formulas, safety, and budget deltas closed without unresolved findings)
Observer-scope delta review: architect, spec_auditor, performance_auditor; no blocking or major findings
Approved-by: user
Approved-at: 2026-09-28
Decision scope: deterministic logical-counter and per-lane capacity evidence for the approved no-numeric-cap F5c policy, including a narrowly gated yu-types observation feature needed to report its private physical lanes
Authority: `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` §§26, 34, 36; `notes/design/2026-09-22-f5b-terminal-finish-evidence-boundary-addendum.md`; `notes/design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md` §§3–4; `rules/performance.md`; existing closed capture plans dated 2026-09-27 and 2026-09-28
No probe, measurement, or test for this plan has run.

## Purpose and exclusions

Prepare fresh evidence for the still-required F5c scale families after the
user approved removal of deterministic input-size/work caps and fixed compiler
runtime cutoffs. The matrix measures exact logical counts and physical
capacity/retained/peak observations. It does not select a numeric admission
limit, assert an end-to-end wall-time guarantee, or authorize production
cutover.

The existing §15 capture plans are exhausted. Do not repeat their source-ring,
seeded-depth/width, failure, rollback, or reserve/retry captures. Those remain
historical evidence for their own gates. The matrix below is a new set of
parameterized F5 §§26/34 builders that does not exist in the current harness.
The current test module has four ignored resource probes:
`f5c_candidate_resource_probe_source_functions`,
`f5c_candidate_resource_probe_scale`,
`f5c_candidate_resource_probe_failures`, and
`f5c_resource_probe_scale_families`; none implements this §34 matrix.
Implement the builders in
`crates/yu-solver/src/tests/f5c_resource_probe.rs` and a separate
`#[cfg(test)]` observer in `crates/yu-solver/src/lib.rs` to retain fixed-size
per-lane/per-boundary summaries at the existing resource and flat-candidate
checkpoints. `yu-types` is compiled as a normal dependency of solver tests, so
its `#[cfg(test)]` internals are unavailable there; the user approved a narrow
`f5c_resource_probe` opt-in feature in `yu-types`, forwarded only by the
same-named `yu-solver` feature, for closed-type physical-lane observation. The
feature exposes a doc-hidden fixed-size summary for its 8 arena, 17 scratch,
and 11 indexed-temporary lanes. It must not add a growing event history, drive
the terminal-capacity seam, or change semantic results, counter values, or
transaction behavior. Separately, the measurement implementation must add the
two §26-required `ProductionCounters` fields and same-named accessors for
`generalization_quantifier_writes` and
`generalization_recursive_binder_writes`. Count each successful selected Q/R
binder write once at the completed member-draft owner; do not count candidate
attempts, repeated R rounds, map probes, or finalizer copies. These counters
are part of the existing §26/§34 production contract, not observer effects.
With the feature disabled (the default), no observer fields, hooks, branches,
or allocations are compiled into `yu-types`.

Allocate solver observer storage before the measured solve, update both
observers without per-event allocation, and disable the flat path's growing
`boundary_order` history for matrix runs. Do not use
`F5cCandidateCapture`'s 64-row log. This measurement-only feature does not
change the approved 37-process campaign or enable production cutover.

## Authority mapping and exact run matrix

F5 §26 requires 1k/2k/4k isolated runs for identity, alias-use, shared-graph,
and arena-factorization families. F5 §34 gives these executable forms and adds
independent acyclic graphs, guarded cycles, and closed normalization. Map
`shared-graph` to `shared_acyclic(D,K)` because it is the builder whose D roots
share one K-node graph; run `independent_acyclic` and `guarded_cycle` as their
separate §34 families.

F5 §34 says to vary D, K, M, or U one named dimension at a time at 1k/2k/4k.
For each two-parameter builder, this plan measures both named dimensions in
separate isolated processes. The companion dimension stays fixed at 8 for
graph/normalization builders and 1,000 for the arena-factorization builder.
No companion dimension changes within a series. Thus the full matrix contains
12 one-dimension series and 36 independent measured processes.

| §34 builder / §26 family | Dimension series | Fixed companion | Required cases |
| --- | --- | --- | --- |
| `independent_identities(D)` / identity | `D` | none | `D = 1,000; 2,000; 4,000` |
| `identity_aliases(U)` / alias-use | `U` | one identity | `U = 1,000; 2,000; 4,000` |
| `shared_acyclic(D,K)` / shared-graph | `D`; `K` | `K=8`; `D=8` | each varied dimension = `1,000; 2,000; 4,000` |
| `independent_acyclic(D,K)` | `D`; `K` | `K=8`; `D=8` | each varied dimension = `1,000; 2,000; 4,000` |
| `guarded_cycle(D,K)` | `D`; `K` | `K=8`; `D=8` | each varied dimension = `1,000; 2,000; 4,000` |
| `normalization(D,K)` | `D`; `K` | `K=8`; `D=8` | each varied dimension = `1,000; 2,000; 4,000` |
| `arena_factor(M,U)` / arena-factorization | `M`; `U` | `U=1,000`; `M=1,000` | each varied dimension = `1,000; 2,000; 4,000` |

This full per-dimension reading is conservative where §34 does not give
companion values. Reviewers must confirm that the matrix conforms to the
Authoritative contract before implementation or execution. Any proposed
reduction in the matrix requires a separate reviewed authority decision.

## Exact builder contracts

Each builder returns and asserts its constructed edge, bound, term, key, and
frontier cardinalities. Assert the exact public counters below before emitting
the physical record:

- `independent_identities(D)`: `facts=5D`, `Q=D`, `R=0`, and zero
  `generalization_shared_summary_hits`.
- `identity_aliases(U)`: substitutions and fresh value variables are `U`;
  instantiation visits are `5U`.
- `shared_acyclic(D,K)`: raw states and summary admissions are `2K`; shared
  summary hits are `2K(D-1)`; uncacheable states are zero.
- `independent_acyclic(D,K)`: raw states and summary admissions are `2DK`;
  shared summary hits are zero.
- `guarded_cycle(D,K)`: recursive binder writes are `D`; cyclic-cone summary
  admissions are zero; uncacheable states are `2DK`.
- `normalization(D,K)`: normalized-key writes and hash admissions are
  `D(K+1)`; descriptor comparisons equal the independent prescribed
  mergesort-comparison oracle built from integer keys; normalization performs
  no recursive comparisons.
- `arena_factor(M,U)`: instantiation visits are `5U`, fresh values are `U`,
  substitution peak is one slot, and those three observations are independent
  of `M`.

Also assert the §26 identity/alias/shared-graph/arena-factorization logical
counts exactly as their §34 builder contracts specialize them. Use the flat
candidate and existing ordered Q/R, normalization, and finalizer paths. Require
successful output with no diagnostics for every success case. Do not use
`F5cCandidateCapture`'s 64-record session history for these many-root cases;
the test-only observer must retain only fixed-size per-lane/per-boundary
summaries and independent maxima, with bounded allocation established before
the measured session starts.

## Physical observations and reconciliation

At the existing named O(1) checkpoints and actual capacity-growth events,
record current requested slots, actual capacity, retained bytes, peak bytes,
and growths for every physical lane in the eight §34 resource families:

`live_variable_tables`, `inference_type_arena`, `structured_pair_memo`,
`component_expansion_memo`, `closed_type_arena`,
`closed_normalization_index`, `generalization_scratch`, and
`instantiation_substitution`.

The `closed_type_arena` family includes all 36 physical lanes owned by
`yu-types`: 8 permanent arena lanes, 17 finalization scratch lanes, and 11
indexed-temporary lanes. `yu-types` owns and updates those fixed-size lane
summaries at its existing reserve/reconciliation events and boundary
checkpoints; the solver observer reads them at finalizer checkpoints instead
of reconstructing them from the aggregate accounting checkpoint. The
independent ledger reconciles same-time cross-crate peaks exactly once.

The independent test ledger also records slot size, clear/transfer point, and
the aggregate semantic-arena and inference-session retained/peak totals. Every
physical lane is counted once. For each dimension series, assert exact logical
formulae and that each adjacent 1k→2k and 2k→4k actual capacity, retained-byte,
and peak-byte ratio is `<2.5`, following F5 §§26/34. Report zero-to-zero
observations as zero and stop for review on a zero-to-nonzero transition whose
ratio is undefined. Do not compare resource observations against a compiler
admission threshold.

Retain the F5 §36 normalization formula and exact descriptor-word comparison
schedule. Physical peaks are observations, not admission criteria. No timing
samples are collected. `/usr/bin/time -v` may report whole-process RSS for
diagnosis; it is not added to candidate lane totals or treated as product RSS.

## Commands and process budget

The ignored preflight entrypoint is `f5c_resource_matrix_preflight`. It runs all
seven builders at `D/K/M/U=32`, asserts every builder formula and per-lane
ledger, and emits one bounded summary. Invoke its exact unique Cargo filter in
one process:

```text
timeout --signal=TERM --kill-after=10s 60s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib --features f5c_resource_probe f5c_resource_matrix_preflight --offline -j 2 -- --ignored --nocapture --test-threads=1
```

All preflight and matrix commands enable `yu-solver`'s
`f5c_resource_probe` feature, which forwards the opt-in observer feature to
`yu-types`. Include `--features f5c_resource_probe` in each Cargo invocation;
ordinary default-feature builds do not compile the observer. Cargo feature
unification applies to the selected build, so do not substitute a workspace
`--all-features` command for the isolated campaign commands.

The separate ignored matrix entrypoint is planned as the unique filter
`f5c_resource_matrix_case`, dispatched by these required environment values:
`F5C_RESOURCE_MATRIX_FAMILY`, `F5C_RESOURCE_MATRIX_DIMENSION`,
`F5C_RESOURCE_MATRIX_SIZE`, and
`F5C_RESOURCE_MATRIX_COMPANION`. One invocation constructs exactly one row of
the matrix and exits after its assertions and summary. The test implementation
must validate the environment tuple against the 1k/2k/4k table above,
including the literal `none` companion for the first two rows, and reject
unknown/missing values.

Command template for one matrix row (`TIMEOUT` is 30, 60, or 120 seconds for
sizes 1,000, 2,000, or 4,000 respectively):

```text
timeout --signal=TERM --kill-after=10s TIMEOUT /usr/bin/time -v env RUSTC_WRAPPER= F5C_RESOURCE_MATRIX_FAMILY=FAMILY F5C_RESOURCE_MATRIX_DIMENSION=DIMENSION F5C_RESOURCE_MATRIX_SIZE=SIZE F5C_RESOURCE_MATRIX_COMPANION=COMPANION cargo test -p yu-solver --lib --features f5c_resource_probe f5c_resource_matrix_case --offline -j 2 -- --ignored --nocapture --test-threads=1
```

Set `COMPANION=none` for `independent_identities` and `identity_aliases`; use
the numeric fixed companion shown in the table for every other row. A
successful, reviewed preflight result is required before the matrix runs.

Run the preflight and matrix processes strictly serially and isolated. After
the preflight, run one process for each of the 36 tuples in the table, with no
retry or extra dimension. The preflight budget is 1 process/60 seconds; the
matrix has 36 processes/42 minutes nominal timeout sum. The complete campaign
is 37 processes/43 minutes nominal. Harness startup is inside each timeout;
because the first timeout stops the campaign, at most one additional 10-second
kill grace applies. This one complete campaign exceeds both the
ordinary 8-process/10-minute budget and the distinct 16-process/20-minute
user-approval threshold in `rules/performance.md`. Before the preflight or any
matrix run, record independent spec/performance plan review, written
performance-auditor justification, primary approval, and explicit user
approval for the full 37-process/43-minute nominal campaign. The user approved
the full campaign on 2026-09-28. That approval authorizes the
1-process/60-second preflight first and conditionally authorizes the remaining
36-process/42-minute matrix only after the preflight passes and its result is
reviewed. Approval of the no-cap design alone did not approve this experiment
budget.

Written performance-auditor justification (2026-09-28): F5 §§26/34 require
dimension-specific exact-counter and physical-lane evidence at three sizes;
single-size or aggregated runs cannot establish the prescribed adjacent
ratios or expose work multiplication as each named dimension grows. The
exhausted §15 captures do not contain these seven builders. This campaign
collects deterministic counts and capacity observations only, with no timing
repetitions. The primary approves the full campaign conditionally on explicit
user approval; the approval was given on 2026-09-28. No process is authorized
before the test-only harness is implemented and reviewed.

Prior whole-process maxima were 556,296 KiB for the §15 scale capture and
647,412 KiB for the failure capture, including build. At plan preparation,
`free -h` showed 31 GiB total and 28 GiB available. Host `MemAvailable` must
be at least 8 GiB before each process and remain at least 8 GiB while it runs;
this is an external measurement-host safety threshold, not a compiler input or
runtime cap. The
preflight and matrix builds use offline Cargo with one test
thread and two build jobs; any test-binary rebuild is inside that row's timeout.
Confirm the actual rustc/Cargo versions and host at execution time. Capture
stdout/stderr and `/usr/bin/time -v` per row in uniquely named `/tmp` logs; do
not commit logs.

Existing §15 rollback/retry and failed-reserve/retry evidence remains closed
under the exhausted plans above and is not repeated here. This plan adds no
failure injection or retry dimension.

## Stop conditions

Stop the entire matrix at the first wrong family cardinality, exact counter or
oracle mismatch, missing per-lane observation, independent-ledger divergence,
ratio failure, unexpected diagnostic, unexpected `IdentityExhausted`, absent
successful result, or per-process timeout. Preserve the failing log and mark
the plan incomplete. Do not rerun or replace an input dimension without a new
reviewed plan and budget approval.

Before each serial process, inspect host `MemAvailable`; do not start below
8 GiB. Monitor process RSS and host availability during each run and stop the
campaign if `MemAvailable` falls below 8 GiB, or at the first other
resource-safety concern, timeout, or failed assertion.

Do not use the largest passing point to derive a supported-input limit. These
repository-bounded records do not certify all-input complexity, choose a
numeric boundary, or authorize production/API cutover. The source-level
ordinary-family proofs and separate reviewed production gate remain required.
