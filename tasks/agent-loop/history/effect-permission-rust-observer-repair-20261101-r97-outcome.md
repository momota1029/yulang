# R97 primary verification outcome

Sprint: `EFFECT-PERMISSION-RUST-OBSERVER-REPAIR/20261101-R97`
Contract SHA-256: `7a7d82f2699c964bddc08757f300480bc50865f79bfe489583193351fff45392`

## Frozen source identity

- `crates/yu-solver/src/candidate_effect.rs`: `6a3ba6dfad67c4a511dee38b58a47f47883f001f7c7f1c5f8b72c94a666a87a3`
- `crates/yu-solver/src/candidate_scheme.rs`: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

## Execution

One authorized invocation ran with `CARGO_TARGET_DIR=/dev/shm/yulang-rust-observer-repair-20261101-r97-target`, offline/locked dependency resolution, one Cargo job, CPU affinity 0, a 180-second timeout, and one test thread:

```text
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1
```

Exit status: **101**. Compilation stopped before any test ran. The visible output reported nine `yu-solver` compile errors in groups `E0308`, `E0425`, `E0433`, and `E0603`. Two visible `E0308` sites were `candidate_receiver.rs:4385` and `:4628`, comparing `HirOccurrenceId` with `&HirOccurrenceId`. The complete compiler output was truncated by the tool and the temporary execution directory was removed with the command's execution context; no complete log remains. The exact command ran, but a separate argv digest was not recorded before launch.

`/usr/bin/time -v` reported 28.87 seconds elapsed and 643,004 KiB maximum RSS. The target directory peaked at 390 MiB, below the 8 GiB cap. No test result or behavioral verification is claimed. No retry was made. The temporary target no longer exists.

`python3 tools/agent_sprint.py check` passed as a static consistency check; it is not build or review evidence.

## Independent review and adjudication

Reviewer `/root/r97_fresh_review` returned **REJECT** after checking the complete intended three-file diff against HEAD. All three pinned source hashes matched. The protected nonrecursive regression still omits the distinct `source_row` assertion, trace evidence connecting its negative domain to capture publication, and the original scratch/empty-domain/permission assertions. Its consumer expectation was widened from `SupportView` to also accept `Contribution` and `OperationInterfaceMember`; its transaction fixture uses a bare `act io` declaration rather than the original operation-bearing declaration. Assertions retained in the separate recursive helper do not preserve the nonrecursive case's contract. The reviewer separately confirms that `Memo.constructor: Option<u64>` fixes the identified shared-memo observer assumption, but this local fix does not clear the blockers.

Adjudication: retain the source candidate uncommitted. The implementation gate failed before tests and the protected test assertions remain incomplete. The Cargo diagnostic output was not retained in full, so the compile errors cannot yet be assigned to exact owners. R97 is closed as failed before execution coverage; no semantics, proof, or production gate is promoted.

## Disposition

R97's execution gate failed, so no source checkpoint is authorized by this contract. The three source files and all unrelated dirty/quarantined paths remain untouched and unstaged. R97 closes no effect-hygiene theorem, source/native bridge, original A/B claim, Lean obligation, semantic gate, or production gate. The already-pushed R97 admission commit is separate from this failed source candidate.
