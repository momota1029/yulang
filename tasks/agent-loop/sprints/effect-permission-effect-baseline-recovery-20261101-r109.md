# R109 candidate_effect baseline provenance recovery

Status: **ADMITTED** under the user's standing Rust implementation analysis/push authorization. Baseline commit: `54526ec9514b7065c7d7460702e9d6e2ecbc0842` (R108 evidence checkpoint).

## Fixed objective

Resolve the source-provenance obstruction that prevents a safe Rust feature compile: determine whether the exact pre-R106 `crates/yu-solver/src/candidate_effect.rs` bytes can be recovered from existing authenticated Git objects or already-frozen artifacts. R107 pins the baseline SHA-256 as `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` and the live dirty file as `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`. R107 says R106 admitted unscoped replacements outside its new block, so no complete pre-R106 preservation claim currently exists.

## Assignment and limits

One Luna/high implementer assignment, ≤300 seconds, sole write lease:
`tasks/agent-loop/inbox/effect-permission-effect-baseline-recovery-r109.md`.

Read-only inputs: the live `candidate_effect.rs`; R98/R104/R105/R106/R107 handoffs and outcomes; immutable commits, trees, blobs and artifact snapshots those records identify. Do not inspect any quarantined runtime path. Do not modify source, other solver files, tests, expected outputs or records outside the sole handoff.

Search existing history/artifacts for a complete byte sequence matching the full R107 baseline SHA. If found, reproduce its complete SHA and report its immutable object/artifact identity. Then compare it byte-for-byte with the live R107-pinned file and attribute every difference to an exact recorded transformation or identify each unresolved region. Establish which R106 transformation introduced the mismatch. Hash-only matches, guessed reverse edits and inferred authorship are insufficient.

If no exact complete artifact is found, stop with the exact searched immutable sources, available partial evidence, and missing-artifact obstruction. Do not fabricate a reconstruction or alter the live file. No build, Cargo, test, compiler, source materialization, checkout, worktree, repository copy, scratch file, cache, environment, Git mutation, staging or push is authorized by this assignment.

## Review and outcome

After the author freezes revision 1 and stops, a fresh `compiler_referee` reviews the exact handoff and independently reproduces any claimed byte recovery and transformation attribution. Review ≤180 seconds, read-only. PASS establishes provenance evidence only; it does not authorize source integration or compilation. Failure retains the obstruction.

Total packet ≤480 active seconds; one known writer/reviewer at a time, Astra 0, no disk/cache growth. Preserve all other dirty and quarantined paths. Luna records the reviewed result and chooses the next admitted source gate. No source or production claim follows automatically.
