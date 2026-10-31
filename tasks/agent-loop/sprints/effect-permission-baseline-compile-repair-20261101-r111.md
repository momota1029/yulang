# R111 baseline-derived Rust compile repair

Status: **ADMITTED** under the user's ongoing Rust implementation and push authorization. Baseline source commit: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` (R106/R107 source baseline; later commits in this session add records only).

## Objective and exact source component

Prepare and, only after all gates pass, compile one baseline-derived minimal feature-build repair. Candidate paths are limited to:

1. `crates/yu-solver/src/lib.rs`: the exact three independently reviewed R98 repairs, target SHA-256 `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f` from R108.
2. `crates/yu-solver/src/candidate_receiver.rs`: three exact owned-`HirOccurrenceId` dereference repairs plus the Member ownership correction, candidate target SHA-256 `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` from R107 after all four repairs. The three dereference repairs alone yield R98 intermediate `03553455bb3b0a4cb0f0ad2fb04b1b8dbf8fac00982547323fe8b6439edbb34d`; R111 also includes the Member ownership correction. Luna must verify `SourceRootId::Member` behavior against `crates/yu-hir/src/module.rs` before integration.
3. `crates/yu-solver/src/candidate_effect.rs`: only the existing `candidate_scheme::RowKey` import repair from R98, applied to committed baseline blob SHA-256 `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`. Exclude all untrusted R104/R106 observer/test deltas and the unrecovered pre-R106 dirty snapshot.

All other source bytes must come from the immutable source commit, not the live dirty worktree. No semantic, test expectation, fixture, diagnostic, or source-domain changes.

## Author and independent gate

One registered implementer, ≤300 seconds, sole report lease:
`tasks/agent-loop/inbox/effect-permission-baseline-compile-repair-r111.md`.

The author reconstructs the exact three-file patches in memory, reports base/target full hashes and exact hunks, pins every dependency/API and Cargo/toolchain input, validates the Member owner branch against the actual HIR implementation, and derives the complete Cargo workspace-loading closure from immutable trees/manifests with aggregate blob bytes, including all twelve workspace members and root Cargo inputs. No source materialization or source writes.

A fresh `compiler_referee` review ≤180 seconds independently checks all patches, dependency closure, Member behavior, protected source regions, command and storage method. **No compiler call until PASS.** If the closure exceeds 64 MiB, any dependency is quarantined/unavailable, the reconstruction differs from the pinned targets, or the storage namespace cannot enforce its cap, stop before execution.

## One compile-only invocation after review

Luna may create a disposable private user+mount namespace and one size-limited tmpfs of at most 6 GiB at a temporary mountpoint. `/dev/shm` is currently read-only, so use it only if the private namespace can mount there; otherwise a short-lived mountpoint under `/tmp` may be used and must be removed after namespace exit. If the platform cannot create and verify this hard aggregate cap, do not materialize or compile. Precompute the exact all-twelve-member workspace-loading closure, root Cargo inputs, selected locked registry archives/index entries and their byte totals before extraction. Local workspace source must be ≤64 MiB. Place source, temporary CARGO_HOME/cache, Cargo target, logs and all writable state inside the capped tmpfs; existing global caches are read-only inputs. No worktree, clone, persistent target, disk-backed source copy, global config or toolchain install. Record hashes/versions of cargo, rustc, clang and mold from the installed executables; do not silently install or switch toolchains.

Use one Cargo invocation only:
`cargo test --no-run --locked --offline -p yu-solver --features shadow-apply-candidate`

CPU affinity 0, timeout 180 seconds, RSS ≤2 GiB, target and source view together ≤6 GiB by tmpfs mount size. No test execution, no retry. Preserve stdout/stderr, exit/resource receipt and exact source hashes. A failed gate closes with the exact first failure.

After verified Cargo process/group cessation, leaving the private namespace must release its tmpfs. Luna verifies the namespace is gone and no `/dev/shm` mountpoint/artifact remains. If cessation/cleanup is uncertain, quarantine the exact root and do not retry.

## Integration and push

Compilation alone proves only this exact repair compiles. After fresh post-run receipt review and source/diff review, Luna may stage the three exact candidate blobs through the Git index without overwriting any live dirty source, plus the R111 records. Inspect the exact outbound range; commit and push only the reviewed source patch. Preserve all remaining dirty/untracked and quarantined paths. If any gate fails, push only a separately reviewed evidence checkpoint and leave source unintegrated.

Parent theorem, source/native correspondence, effect hygiene, original A/B claims and production remain open. No forced push. Total active packet ≤1,200 seconds; Astra 0.
