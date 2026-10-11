# Private candidate conflict export guard

Date: 2026-10-11
Status: implemented and independently reviewed; private candidate boundary only
Baseline: `593f7ee8a9109744f75782983e3d57ff51e8bd04`
Authority: user-approved [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md), §4

`CandidateInference::solve` continues the candidate run and retains its
diagnostics when source-generated constraints conflict. `candidate_conflicts`
remains available. `CandidateInference::export` now refuses every graph export
when the completed module result contains a solver conflict. This prevents an
inconsistent candidate graph from crossing this private export boundary; it
does not turn the private candidate into public source rejection or a public
typing result. The guard is an O(1) error-vector emptiness check and allocates
nothing. Module-wide refusal is conservative because per-root conflict
validity has not been established.

The focused regression uses `my bridge x = 1 1`: it confirms the Int/Function
conflict remains observable and export fails. A conflict-free
`my bridge x = x` still exports. Independent compiler-referee delta review
found no blocking, major or minor issue. The review covered the changed export
boundary, direct callers, tests, diagnostics access and the distinction between
row-identity observation and graph export.

Verification:

```text
CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib shadow_apply::tests:: -- --test-threads=1
15 passed, 652 filtered
git diff --check -- crates/yu-solver/src/shadow_apply.rs
passed
```

Still open: completeness of conflict detection; conflicts across every
propagation, freshening and generalization path; public source rejection;
ordinary HIR Apply admission; public scheme publication; complete Call,
effect hygiene, soundness, principality and F5 replacement. No public acceptance
consumer was established by the source audit. This bounded guard is not evidence
that those gates are complete.

Changed code path: `crates/yu-solver/src/shadow_apply.rs`, guarded export and
one focused regression. Review: independent `compiler_referee`, no findings.
No Git operation was performed by the implementer or reviewer.

## Fresh-use graph boundary follow-up (2026-10-12)

The same private result also exposed captured scheme graphs through
`CandidateInference::fresh_use`, which bypassed the existing export guard. It
now returns `None` whenever the completed candidate retains any solver errors,
before examining either local-use or module-use routes. The check preserves
`candidate_conflicts`, `effect_conflict`, and `source_call` for diagnostics and
construction observations. As with export, the module-wide guard is
conservative; per-root conflict validity is not established.

The focused regression covers an invalid `apply 1` and valid `apply id`: it
checks retained Int/Function diagnostics, conflict-gated export and fresh-use,
and retained source-call observations. The owning test passed. An independent
compiler-referee review of this delta found no blocking, major, or minor
finding.

```text
cargo test -p yu-solver --features shadow-apply-candidate shadow_apply::tests::candidate_graph_fresh_use_refuses_conflicts_and_preserves_valid_use -- --exact --test-threads=1
1 passed; other tests filtered
git diff --check -- crates/yu-solver/src/shadow_apply.rs
passed
```

The gate remains private graph-consumer safety only. `CandidateValueObservation`,
ordinary F5 paths, complete conflict reflection, source rejection, public
publication, soundness, principality, effect hygiene and F5 replacement are
not certified by this follow-up.

Changed code path: `crates/yu-solver/src/shadow_apply.rs`,
`CandidateInference::fresh_use` and its focused regression. No Git operation
was performed by the implementer or reviewer.
