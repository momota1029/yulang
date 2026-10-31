# EFFECT-PERMISSION-RUST-OBSERVER-COMPILE-REPAIR/20261101-R98

Status: ADMITTED by Luna under the user's standing Rust/Lean goal continuation.

## Fixed outcome and boundary

Recover a complete durable compiler diagnostic for the frozen R97 source bytes, restore every protected assertion in the original nonrecursive regression, repair only compiler errors owned by the exact leased files, then run one final feature-correct focused test and obtain a fresh independent review of the complete intended source diff.

This is diagnostic/test-only work. It does not change solver semantics, effect permissions, memoization, expected outputs, refusal/recovery, source domain, SCC qualification, Lean definitions, semantic approval, or production authority. Original Simple-sub A/B claims, quantifiers, and source/native obligations remain OPEN. Any error whose required repair lies outside `candidate_effect.rs` or `candidate_receiver.rs` stops implementation until Luna admits the exact owner. A failed invocation is not retried.

Success requires: (1) complete stdout/stderr and resource receipts for the diagnostic-only build; (2) exact restoration of HEAD's protected nonrecursive fixture, `SupportView` expectation, distinct `source_row`, negative-root/capture trace connection, operation-bearing transaction, scratch restoration, and empty-domain/permission assertions; (3) compiler repairs limited to the leased files without changing comparison meaning; (4) one final focused test PASS on frozen bytes; and (5) fresh independent review PASS over all intended source files, including inherited `candidate_scheme.rs` and `shadow_apply.rs` changes.

## Baseline and exact files

Branch `yulang3`; HEAD and upstream are `fd97f480fd1090f686907a44072ba736649ac5e5`.

Writable implementation leases after diagnostic-owner confirmation:

- `crates/yu-solver/src/candidate_effect.rs`, initial SHA-256 `6a3ba6dfad67c4a511dee38b58a47f47883f001f7c7f1c5f8b72c94a666a87a3`
- `crates/yu-solver/src/candidate_receiver.rs`, initial SHA-256 `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`
- `tasks/agent-loop/inbox/effect-permission-rust-observer-compile-repair-source.md` (single implementer handoff)

Read-only complete-review inputs:

- `crates/yu-solver/src/candidate_scheme.rs`: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

R97's failed source candidate is documented in `tasks/agent-loop/history/effect-permission-rust-observer-repair-20261101-r97-outcome.md`; its source bytes are not approved by this contract. All unrelated dirty, quarantined, and untracked paths remain outside the assignment and must not be read, changed, or staged.

## Ordered work and verification

First, Luna runs exactly one diagnostic-only invocation on the frozen R97 source bytes, before implementation edits:

```text
CARGO_TARGET_DIR=/dev/shm/yulang-effect-observer-rust-repair-20261101-r98-target
CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=1
timeout 180s taskset -c 0 /usr/bin/time -v cargo test --locked --offline --no-run -p yu-solver --features shadow-apply-candidate candidate_effect::tests::
```

Retain complete stdout, stderr, exit status, timing/RSS, source/dependency hashes, exact argument hash, and target size in these primary-owned files: `tasks/agent-loop/history/effect-permission-rust-observer-compile-repair-20261101-r98-diagnostics.stdout`, `.stderr`, and `-outcome.md`. Logs are written directly under the repository history path, not the temporary target. If the complete output identifies an additional source owner, stop and get an exact lease decision before any edit.

After the diagnostic map is adjudicated, the implementer restores the protected assertions and makes only owner-local compiler repairs. Writes stop and all final source/handoff hashes are frozen before the second and last authorized Cargo invocation:

```text
CARGO_TARGET_DIR=/dev/shm/yulang-effect-permission-rust-observer-compile-repair-20261101-r98-target
CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=1
timeout 180s taskset -c 0 /usr/bin/time -v cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1
```

The final command writes complete stdout/stderr and timing to primary-owned `tasks/agent-loop/history/effect-permission-rust-observer-compile-repair-20261101-r98-verification.stdout`, `.stderr`, and the outcome receipt. The single test invocation has no retry. It must run in the versioned existing `/dev/shm` tmpfs target, offline/locked, one CPU, at most 180 seconds, at most 2 GiB RSS, and at most 8 GiB temporary artifacts. First verify write/execute access in the actual command context; request exact-path escalation if required. No persistent-storage fallback and no remount. Wait for all descendants, preserve the compact repository receipt, then remove only the exact temporary target.

## Lanes, review, and stop conditions

Implementer: registered Luna/high lane, at most 900 seconds, only the two Rust paths and one handoff above. No build/test, Cargo target, Git, or descendants. The implementer receives the first durable diagnostics before edits. If additional owners or semantic changes are needed, STOP and return the exact evidence.

Reviewer: fresh compiler referee, read-only, at most 500 seconds; no build/test or Git. Review final hashes, restored protected assertions against HEAD, compile repairs, observer transparency, complete intended diff including inherited `candidate_scheme.rs`/`shadow_apply.rs`, both execution receipts, and explicit non-claims. Accepted BLOCKING/major findings must close before a source checkpoint.

Primary: at most 1,000 seconds, including both serial Cargo invocations, output/hashes, independent review, adjudication, state, and primary-only Git. Sprint total at most 2,400 seconds; Astra 0. Stop on missing dependencies, timeout, resource cap, incomplete logs, diagnostics outside exact leases, test failure, reviewer rejection, or changed upstream. No third Cargo invocation under this contract.

Only Luna stages explicit intended paths, inspects every staged hunk and the complete outbound range, and makes a non-forced push after verification and independent review PASS. If a gate fails, keep the source candidate uncommitted and report the durable evidence. This sprint closes no theorem or production gate.
