# Ordinary inference cutover entrypoints

Date: 2026-10-10
Inspected checkpoint: `7334dcfdb6f9d57eff04f02fb575fbba1ef1b414`
Mode: read-only explorer mapping; M0 primary record synchronization
Scope: existing library callers and target refs; no new cutover authority

## Actual ordinary path

The feature-free route is `yu_hir::lower_module` →
`ConstraintBatch::collect(hir)` → `SolvedModule::solve` →
`InferenceSession::run` → ordinary SCC execution and F5 scheme publication.
Candidate source formation, graph mode and source actions require explicit
selection; enabling their Cargo feature alone does not retarget ordinary calls.

The owning seams are:

- HIR `module.rs::lower_module`: default source formation does not select the
  candidate Apply/local carrier.
- Solver `ConstraintBatch::collect` and `InferenceSession::try_new`: ordinary
  collection disables graph mode, and session startup has no candidate graph.
- `execute_scc_plan` / `execute_scc_plan_inner`: ordinary scheme generation
  uses F5 drafts, normalization, finalization and installation.
- `route_incoming_inner`: ordinary uses instantiate `ClosedValueScheme`;
  candidate uses freshen retained graphs.
- `finish` / `SolvedModule::root_value_for`: the result/session shell still
  assumes finalized closed schemes. Candidate graph publication does not fill
  that table. Ordinary Function observations currently collapse to `Unknown`.

Replacing those owners requires the approved complete public scheme and fresh
ordinary-use consumer, rather than merely returning `CandidateInference` from
an ordinary accessor. The current candidate also rejects internal SCC uses;
the approved recursive behavior remains an implementation requirement.

## Existing consumers and scope

Repository Rust search found no inference callers outside `yu-solver` tests.
The workspace has no compiler/CLI/LSP/Wasm crate implementation. `yu-core`
contains gated shadow routes, and VM/native libraries are placeholders.
There is no existing application/backend inference selection to flip.
`ClosedValueScheme` consumers reside in solver/types only.

The architecture describes future `PublicInterface` and `CoreModule` boundaries,
but those Rust interfaces do not yet exist. This mapping adds no requirement
to build new applications or backends solely for the user's inference/F5
replacement task. Existing approved publication and consumer obligations remain.

## Target and final evidence

Local `yulang3`, `origin/yulang3` and direct remote lookup all identify
`32f0a06314434c5dec12383f6b20f2cbcf472752`. At the inspected checkpoint,
target-only commits: 0; research-only commits: 2,203. The target contains none
of the current candidate source/scheme/extrusion or generic local-carrier files.
No replacement or target-branch integration has occurred. The complete intended
range and every outbound commit still need integration scrutiny.

Completion must establish ordinary source formation/collection, complete
solve/generalization, independent module/local fresh uses, complete public
publication and structured errors/availability behavior on the target branch.
Default execution must use the successor rather than retired F5 export/use.
Private candidate builds cannot prove that replacement. Existing charter Gate E
and canonical cutover prerequisites retain their scope; this map closes none.

No builds, tests, execution probes or measurements ran for this mapping. The
primary rechecked the target remote hash and bounded code diff; no Git ref or
source mutation was performed by the explorer.
