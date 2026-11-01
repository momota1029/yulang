# R155 outcome — scheme residual held

Sprint: `EFFECT-PERMISSION-SCHEME-RESIDUAL/20261102-R155`
Baseline: `1dbb738de8af1b186ae56ca347e591ae0a1b3d83`
Contract SHA-256: `1fb5c38fb14f6f11c1ac8d26930168f2b7bf0422948e4f79c0fcd3b916bd1309`

## Outcome

**HOLD / NO_PATCH.** The sole remaining `candidate_scheme.rs` hunk is not an independently safe Rust change. It removes the reviewed, session-owned permission binder already present in the pushed R153 source baseline. The replacement accepts route, arena, effect state, registration table, and occurrence as separate arguments; local numeric checks do not establish a common `InferenceSession` owner. It also drops the exact source origin, Lambda recipe/HIR, raw entry, captured representative, and mapped native row joins without equivalent replacement evidence.

A conditional interface/certificate falsifier joins session A's route/arena with session B's authentic effect state/formals when numeric registration, occurrence, and raw row coincide. This demonstrates the missing common-owner check under those premises; no committed caller exists for this binder, and no runtime reachability or erroneous suppression was demonstrated. Registration IDs, packed permission positions, concrete member ordinals, and native view coordinates remain distinct. Full operation identity remains separate from family equality. Provider and Lambda constructor/source owners need not be equal for returned/local functions.

No candidate source was applied, staged, committed, or pushed. R153's exact source-only integration approval does not extend to this changed candidate.

## Frozen evidence

- Input diff: `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-input.patch`, SHA-256 `6ffdb7fda9f822a40024498160eedcac4cc6950ebc4b7bf93548e497b296664f`.
- Implementation handoff: `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-source.md`, SHA-256 `66b2c471f0d32c646cd55d5b8ce0ecac1b8f215b3e1bfa32ef59920b0dcf318f`.
- NO_PATCH marker: `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155.patch`, SHA-256 `4afc0c7a18ce6112446c8be8565df142c4346debce3d3721edb25971397d1ccd`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-proof.md`, SHA-256 `29a9099a8f0cccae1658ee458e671ef75216b41db1e286a8165f13822ff2ad00`.
- Independent review: `tasks/agent-loop/history/effect-permission-scheme-residual-20261102-r155-review.md`, SHA-256 `11cd345e26c17929c797b511ed37996bf6d8470d4f092bd70264a70eaf0da7dd`.

The reviewer authenticated all seven committed source hashes and reconstructed the single hunk against the baseline without offsets/fuzz. Workers and reviewer read only committed blobs and frozen artifacts; live dirty Rust and quarantined runtime paths were not read.

## Checks and limits

No Rust build, Cargo test, Lean run, source edit/application, scratch/cache/environment/worktree, staging, commit, or push occurred under this sprint. No tests were requested. Parent quantifiers, source/native correspondence, INITIAL-STATE, CONSUMER, effect hygiene, soundness, principality, termination, original A/B, and production remain **OPEN**. Dirty receiver and quarantined runtime paths remain untouched.
