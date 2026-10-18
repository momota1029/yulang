# Unreviewed test-only worktree delta archive

Primary reconciliation from branch HEAD `658bb759f459acfffadd61fffaf56c595bd328e2`.
The two tracked worktree diffs were present before R50 and outside its source
lease. Their author and exact originating assignment are UNKNOWN in the current
state. This archive preserves the exact delta before returning those tracked
files to the committed baseline.

## Frozen patch

- Patch: `notes/progress/2026-10-19-unreviewed-test-only-worktree-delta.patch`
- Patch SHA-256: `5e3280b99998e1e513a408bdb360104843b6a1a79edda60a1289133facc4d332`
- Contents: test-only additions in `crates/yu-solver/src/shadow_apply.rs` and
  `crates/yu-solver/tests/candidate_local_self_recursion.rs`.
- `shadow_apply.rs`: committed baseline SHA-256
  `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`;
  observed worktree SHA `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137`.
- `candidate_local_self_recursion.rs`: committed baseline SHA-256
  `33912833281b73fc53fd0de3a34741fc778ac46f4eeb5d9064c6ca3a9193f020`;
  observed worktree SHA `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55`.

The recursive fixture overlaps a historical R36/R37 test-only candidate whose
reviews blocked execution and integration. The ordinary Call result assertion
has no matching frozen assignment located in the audited records. Both are
preserved as unreviewed candidates only. No test, build or runtime check was
run here. The archived patch grants no code, test or semantic authority and is
not to be applied without a new exact contract and fresh review.

After verifying the patch hash, Luna restored only the two named tracked files
to their committed baseline. No other tracked path was reset, cleaned, stashed
or modified as part of this reconciliation.
