# EFFECT-PERMISSION-RUST-OBSERVER-COMPILE-REPAIR/20261101-R98-v2

Amendment 1 to [R98 revision 1](effect-permission-rust-observer-compile-repair-20261101-r98.md), admitted by Luna under the standing user-authorized Rust/Lean goal continuation. Revision 1 remains immutable and records its original two-owner boundary. This amendment adds exactly one owner after the complete diagnostic receipt established the required edits.

## New evidence and fixed source owners

The R98 diagnostic invocation exited 101 before tests. Its complete stderr and resource output are durable in `tasks/agent-loop/history/effect-permission-rust-observer-compile-repair-20261101-r98-diagnostics.stderr` (SHA-256 `cb3151741b93846210e48afb78d99727ce55d9367aa09c70f2484732e44c426d`). The errors identify one compile-blocking component across these exact owners:

- Writable `crates/yu-solver/src/candidate_effect.rs`, current SHA-256 `6a3ba6dfad67c4a511dee38b58a47f47883f001f7c7f1c5f8b72c94a666a87a3`.
- Writable `crates/yu-solver/src/candidate_receiver.rs`, current SHA-256 `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`.
- **New writable lease** `crates/yu-solver/src/lib.rs`, current SHA-256 `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.
- One implementer handoff: `tasks/agent-loop/inbox/effect-permission-rust-observer-compile-repair-source.md`.

The `lib.rs` source is clean at the pinned baseline with no competing lease or known writer. Its only authorized edits are: replace the two unavailable `exhausted` references at lines 11763 and 11770 with the existing `SolveAvailabilityError::IdentityExhausted` result; replace the private `candidate_source::SourceRootId::Definition` path at line 18372 with the already imported `SourceRootId::Definition`, preserving the predicate. Do not export helpers or alter error classification.

The implementer may also resolve the reported `RowKey` name-resolution errors in `candidate_effect.rs` at lines 461/562/568 by importing the existing `candidate_scheme::RowKey`, and the three reported owned/reference comparisons in `candidate_receiver.rs` at lines 4186/4385/4628 by preserving the same `HirOccurrenceId` equality. No other owners or diagnostic locations are authorized. Restore every protected nonrecursive fixture assertion named in R98 revision 1, including operation declaration, consumer variant, source row, negative-root/capture trace, rollback, scratch, and empty state assertions.

## Unchanged gates and resources

R98 revision 1 remains binding except for this exact additional writable source path and this error map. Baseline remains branch `yulang3`, HEAD/upstream `fd97f480fd1090f686907a44072ba736649ac5e5`. Read-only full-review inputs remain `candidate_scheme.rs` (`bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`) and `shadow_apply.rs` (`c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`). The requested-model/observed-model split, unknown-writer quarantines, all unrelated edits, no-production boundary, and source/native/proof non-claims remain unchanged.

One of two authorized Cargo invocations is consumed by the diagnostic run. Exactly one final focused `cargo test` invocation remains after edits, with stdout/stderr durably captured, locked/offline dependencies, a fresh versioned `/dev/shm` target, one CPU, <=180 seconds, <=2 GiB RSS, <=8 GiB artifacts, and no persistent-target fallback. No retry or third invocation. Existing totals remain: implementer <=900 seconds, fresh independent reviewer <=500 seconds, primary <=1,000 seconds including both Cargo calls and primary-only Git, aggregate <=2,400 seconds, Astra 0.

The complete review component now contains five source files: the three writable owners above and read-only `candidate_scheme.rs`/`shadow_apply.rs`. Only a final successful focused gate and fresh independent review PASS permit Luna to stage explicit intended paths, inspect the whole outbound range, and non-forced push. Any error outside the three writable owners, semantic change, resource failure, test failure, or review rejection stops the packet. This amendment closes no theorem or production gate.
