# Sprint NATIVE-INTEGER-COMPARISON-EVIDENCE-REPAIR-20261026/r43

Status: READY; Luna owns fresh bounded capture and conditional integration; one fresh reviewer after freeze.
Branch: `research/simple-sub-intrusion`
Baseline: `9c104326a8ee688ec98a1f26bb5f700ad3fa85ca`

## Fixed outcome

R42 remains `FAILED / EVIDENCE_CONTRACT_BLOCKER`, without mathematical-failure attribution. Its exact 23-declaration audit and isolated default-root build passed, but its invocation-1 duration is UNKNOWN and invocation-3 full output was not retained. R43 supplies fresh process evidence for the identical frozen candidate, then obtains a new independent review of the combined candidate, exact audit, R42 root-build transcript, and fresh focused-build capture. Only a CLEAN review permits copying the exact candidate and one-line root import into the primary worktree. Do not rewrite or relabel R42.

This can close only the signed-decimal comparison/readback slice. Full source/native execution, remaining producers/primitives, inference A/B, whole executor and production remain OPEN.

## Frozen inputs

- Candidate `notes/theory/lean/YulangClosure/NativeIntegerComparison.lean`: `2352602b7047611e9f9722d788ed1acdf9f4960d178c48f6a08b1a7054f93e79`.
- R42 complete audit source embedded in receipt and isolated file: SHA-256 `eb3fcc52c652f87f598ea9136271eea3364a4eaedb0948bf941610ee8d75d573`.
- R42 primary verification receipt (audit output and default root build output): `tasks/agent-loop/inbox/native-integer-comparison-r42-primary-verification.txt`, SHA-256 `33a61dc2e2efcb0d811b77f0213f8cfc9a44769c7b1f7579cde15ff537f80834`.
- R42 independent review: `tasks/agent-loop/inbox/native-integer-comparison-r42-review.md`, SHA-256 `9fe02ad3d00694e804c677eaebea1f75fc7ec3302bdd5404dc671547e2a481df`.
- R42 isolated root file with exactly one import added: SHA-256 `b4b04a6a3b2cc0c7c330e93195539f7344612347c9b51b7f2dc8cf0be4994454`; diff from pinned baseline root is only `import YulangClosure.NativeIntegerComparison`.
- Root base hash `aeb4b99af2a786363446c49a07cf1df4ac631c411c93305b110f6868078b8641`; manuscript/readback/producer/Rust/HIR/toolchain dependency pins are inherited exactly from the R42 contract at `tasks/agent-loop/sprints/native-integer-comparison-audit-integration-r42.md` (hash `b51ca46a58ce5a8f5f5242bc382340da4b1585e0a61e303c5b064d34d79a8a33`). Reconfirm them in the fresh worktree before invoking Lake.

## Fresh capture and integration

Create a new detached worktree at the exact baseline above under `/tmp/yulang-r43-native-integer-20261026`; do not reuse R40/R42 `.lake` caches. Copy only the hash-matched candidate into its module path. Keep the root file at baseline for focused build. Capture command argv, cwd, UTC start/end, monotonic elapsed nanoseconds, exit status, and raw stdout/stderr bytes directly to dedicated files using a primary-owned subprocess wrapper; verify each log hash. The wrapper must not truncate or summarize output.

Luna may invoke Lean/Lake at most twice, sequentially, with <=60 cumulative checker seconds and 60 seconds per call:
1. pinned native Lake `--version`;
2. pinned `lake build +YulangClosure.NativeIntegerComparison` in the fresh worktree.

No retries, diagnostics, or third call. Stop on first mismatch, failure, timeout, capture error, or budget limit. The R42 audit and default-root build outputs are reused only as their existing exact artifacts; R43 makes no claim that they were rerun. Compare candidate/audit/root/toolchain hashes before and after capture.

After the two captures succeed, freeze the combined evidence and start a fresh compiler_referee. It reviews only the candidate, R42 complete audit source/output, R42 root-import/build transcript, R43 exact command logs/manifest and source/spec correspondence. No checker/build/test/Git calls by reviewer; report path is `tasks/agent-loop/inbox/native-integer-comparison-r43-review.md`, max 180 seconds. Any blocking/major finding prevents integration.

After a CLEAN review only, Luna may copy the byte-identical candidate and the exact R42 root file (one import only) to the main worktree, record the combined evidence and close R43. No additional Lean invocation in the main worktree. Preserve the R42 failure record. Pending question directories remain unstaged.

## Leases, budget and stop state

Luna leases this contract, `tasks/agent-loop/current.json`, `notes/theory/lean/YulangClosure/NativeIntegerComparison.lean` (copy only after CLEAN), `notes/theory/lean/YulangClosure.lean` (copy only after CLEAN), `tasks/agent-loop/inbox/native-integer-comparison-r43-primary-verification.txt`, the wrapper/log/manifest under the isolated checkout, and its dedicated `.lake/build`. Reviewer leases only `tasks/agent-loop/inbox/native-integer-comparison-r43-review.md`.

Fresh grant: Luna 600 active seconds, max two Lean/Lake calls, max 60 checker seconds; reviewer max 180 seconds, checker 0. R42 and R40 grants are not carried. On session stop, record actual worker cessation or retain UNKNOWN/quarantine. No Git operation is delegated.

Success requires two complete fresh process captures, unchanged pinned candidate and dependencies, reuse of R42's complete audit and successful root build evidence, a CLEAN independent delta review, and Luna's exact-byte integration receipt. R42 remains FAILED / EVIDENCE_CONTRACT_BLOCKER throughout.
