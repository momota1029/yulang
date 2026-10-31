# R108 Rust compile-repair reconstruction and Lean module validation

Status: **ADMITTED** under the user's standing Rust/Lean authorization.
Parent goal, original source scope, Simple-sub A/B claims and quantifiers,
semantic authority, expected outputs and production gates stay fixed. Baseline:
`070cc8d2fc8ae519fa9f3eb2d1b872bcb485fba8` (R107 evidence checkpoint).

## Gate inputs

R107 closed as reviewed evidence only. Its Rust compiler-referee review
independently reconstructed the exact three R98 `lib.rs` repairs to hash
`6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`; the
review explicitly did not approve source integration. The four-repair receiver
also reconstructs, but `Member` ownership behavior needs its own source gate.
The dirty `candidate_effect.rs` remains untrusted: stripping the R106 test block
did not recover the R105 pinned bytes. Do not widen R108 into observer or
receiver source integration.

R107 Lean protocol review passed as a failure-protocol report. Installed Lean
source does not prove native temporary naming, publication or crash cleanup.
R108 may use only a conservative, reviewed per-module output guard and must
preserve that limitation. The R106 execution allowance is exhausted; R108 is a
new, separately admitted batch with a new output root.

## Rust reconstruction lane

Registered implementer; sole write lease:
`tasks/agent-loop/inbox/effect-permission-lib-repair-r108.md`.
Read-only immutable baseline: `crates/yu-solver/src/lib.rs` at R107 baseline
blob SHA-256 `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.
The current dirty live `lib.rs` SHA-256 at R107 close was
`429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` and is
read-only during the reconstruction assignment.

Reconstruct, in memory only, exactly the three R98 line repairs against the
immutable base; provide a minimal patch, one-match-per-replacement receipts,
full resulting file hash, and unchanged-region evidence. Pin every direct
source/API dependency required by the changed expressions. The producer must
separate the three-hunk candidate from any dirty observer logging in live
`lib.rs` and must not guess missing bytes.

Fresh `compiler_referee` review, 180 seconds, independently validates the exact
patch, base/result hashes, dependency closure and whether one feature-build
command exercises these lines without consuming the untrusted observer delta.
If that cannot be established, report the exact source obstruction and run no
compiler. If it passes, Luna may authorize one compile-only Cargo invocation
against a separately reviewed source materialization. No test execution.

Provisional execution envelope only after review PASS: exact frozen command
`cargo test --no-run --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests::`, CPU affinity 0, hard timeout 180 seconds, RSS ≤2 GiB, one Cargo process. Use only the existing checkout with `CARGO_TARGET_DIR=/dev/shm/yulang-r108-rust-target` capped at 6 GiB; do not create a worktree, repository copy, persistent target or global config. Before launch, Luna must prove the exact candidate source state and preservation/restore plan for every pre-existing dirty byte. If the command would compile an unreviewed dependency or cannot isolate the three-hunk candidate, stop without spending the call. One call maximum; no retry.

## Lean module-validation lane

Registered `lean_prover`; sole write lease:
`tasks/agent-loop/inbox/effect-permission-module-validation-r108.md`.
Use only the unchanged R105 13-module cone and R107 protocol findings. Freeze
all source and executable hashes, the topological module order, exact command
argv, per-call active-module output allowlist (including the observed
`.olean.tmp.7` class as a guarded hypothesis), aggregate byte accounting,
race-aware monitor behavior, process-group cessation, owned-root identity and
cleanup receipt. No Lean/Lake/checker/version/compiler invocation and no
generated output during authoring.

Fresh independent pre-execution review is required. Only after PASS may Luna
run one batch of at most 13 module compilations, stopping on the first failure,
using Lean 4.35.0, `-j1 -M1024`, CPU affinity 0, 60 seconds per call and 1,200
seconds aggregate active time. Output root:
`/dev/shm/yulang-source-owner-module-validation-20261101-r108`, maximum 2 GiB;
no persistent cache. Require verified writer cessation before deletion; if
uncertain, quarantine and do not retry. Acceptance requires all 15 actual R105
declaration types and complete axiom audits, not just module compilation.

## Shared envelope and integration

Total active work ≤2,400 seconds, at most four known assignments, Astra 0.
Serialize Cargo and Lean. Each author ≤300 seconds, each reviewer ≤180 seconds,
Luna reconciliation ≤240 seconds. No other build/test, dependency update,
worktree, persistent environment, source-domain change, semantic change or
expected-output edit. Keep quarantined paths and unrelated dirty/untracked files
untouched.

Fresh post-execution receipt review must check source/dependency hashes, exact
commands, exit/resource results, artifact inventory, cessation and cleanup.
Compiler success establishes only the exact compile repair; Lean kernel success
establishes only checked declaration claims. Parent proof, source/native
correspondence, effect hygiene, A/B and production remain open. Luna alone
materializes or integrates exact source, stages explicit paths and pushes a
coherent reviewed range. No force-push.
