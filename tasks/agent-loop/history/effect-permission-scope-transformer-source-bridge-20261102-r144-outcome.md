# R144 outcome — scoped transformer source regression

Status: **REVIEWED REGRESSION CANDIDATE; UNCOMPILED / UNEXECUTED**. No production behavior changed and no production defect is claimed.

## Rust source outcome

`crates/yu-solver/src/candidate_scope.rs` adds one `#[cfg(test)]` module. It uses an independent sequential oracle over `BTreeSet` primitives and covers bounded short operation sequences, order distinctions, release tombstones, duplicate/unsorted initial sets, unrelated protections, remap/evaluate behavior with a guard input both absent and present, collision rejection, and exactly-once calls per distinct support ID. Every bounded sequence is split at each boundary and checks `evaluate(first.then(second), initial)` against direct successive production evaluation, including nonprimitive right transformers. The source prefix containing all production definitions is byte-identical to admitted baseline.

Initial fresh review rejected one version of the test candidate for three coverage defects. Luna corrected only the test module. Fresh delta review accepted final source SHA-256 `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`; the production prefix retains SHA-256 `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`. Final review receipt: `tasks/agent-loop/history/effect-permission-scope-remap-r144-review.md`, SHA-256 `31b28f71460890b92d87911c49318c8525a21fbb2ddf5f7d1ceff60cfb7568a7`. The candidate remains explicitly uncompiled and unexecuted; no tests, Rust/Cargo, Lean, build or scratch operation ran under this sprint.

## Rust/Lean correspondence and remaining premise

The separate source/proof handoff `tasks/agent-loop/inbox/effect-permission-scope-remap-r144-proof.md`, SHA-256 `dfcd7412c4d2592327e4b4c2e2e481531d008026d77fd5d2636d50da9b4e4581`, maps existing stamp/protect/release/composition callers to the approved effect-scope policy and Lean `NativeScopeTransformer` laws. The reviewed clean source boundary has no direct `ScopeTransformer.remap` invocation. Existing fresh-use identity construction conditionally gives injectivity on valid pre-copy IDs, but authenticating the shared map and the combined transformer/demand/incoming-state support below external pre-copy allocation cuts remains open. This finite source regression does not prove arbitrary composition, caller injectivity, source/native equality, or allocation-failure behavior.

R143 remains `KERNEL_CHECKED_RESEARCH_ONLY`. Its ordered permission model is not shown equal to a native Rust table or invocation. Effect hygiene H, A/B, `YulangClosure.SourceProblem.InferenceSoundness`, principality, termination and production remain OPEN. The next discriminating source step is the external fresh-map/support bridge; owner: Luna.

No dirty/quarantined Rust or runtime path was read, modified, staged or integrated. No environment, target directory, worktree or extra build output was created.
