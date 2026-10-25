# R25 adjudication — FAILED_CHECK

Sprint: `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r25`, contract r4 SHA-256 `808a4fee292cb6af1aac68dde7bf750c22d6d0a4adb850eb15a2f44a3dac658c`, baseline `70c3d29f76fa54f209fe8271e2ca25f079f26acf`. R25 was admitted after source-hash verification, fresh worker availability, exact leases, and commit `6b74f92a8`.

## Frozen evidence

The source gate passed on manuscript `:694–719`, `:1024`, `:1109`. The worker added a mapOperation computation-typing constructor with the unchanged body result type, exact operation declaration/witness equalities, and both adapter derivations; it added the common arbitrary-σ transport case and an upper inversion/iff module. R24 files were unchanged.

The first focused build, `lake build +YulangClosure.PaperMapOperationIntegration`, failed at `PaperExecutionTypingSubstitution.lean:471`. The constructor application inferred the original `source`, but `sourceEq'` proves equality for `OperationInstance.subst σ source`. This is a Lean construction mismatch, not a source counterexample. No repair, retry, audit, or primary verification ran under the first-failure rule. Three literal calls consumed; 20.684965 seconds; pinned Lean 4.35.0. Axiom audit is NOT_RUN, so none of the new declarations are accepted proofs.

Frozen worker handoff: `tasks/agent-loop/inbox/paper-typing-subst-r25.md`, SHA-256 `d31aff1170c0219c851c349c420a788a4a941071a38cf6182bf21e69eca54056`.
Frozen complete checker log: `tasks/agent-loop/inbox/paper-typing-subst-r25-worker-checks.txt`, SHA-256 `0da3d9820e2d635b7ab7fe7dbfb076491dfeabcc9ac7829da636ff7292a52a92`.

The isolated worktree `/tmp/yulang-r25-mapop` retains the failed candidate only. Frozen SHA-256 values:

- `PaperExecutionSyntax.lean`: `eec31d92375ea700061ff6b0a8c5ac7742db5fe77aa96dd28bc75ad7c93fc2dd`
- `PaperExecutionTypingSubstitution.lean`: `6e8c1b8d1cf62736d6df172430bf20e44d35b6d527d468b07dc80ebe7ce736f3`
- `PaperMapOperationIntegration.lean`: `98e78766e2d2671d6d4aae6250fbe001c3eb8e9825df1aac62e5c97efcf1851f`

## Decision and remaining gates

Adjudicate R25 as `FAILED_CHECK`, not as proof or counterexample. Keep the failed source out of the active branch. Preserve the isolated files and partial `.lake/build` unchanged. A plausible next repair is to pass mapped source/target instances explicitly to the constructor, but that remains an unexecuted hypothesis requiring a new, bounded packet and checker budget.

No parent obligation closes. R23 source-context gate, R18 variant correspondence, full mapOperation substitution, execution preservation, inference/executor, original A/B, source/native/Rust correspondence and production remain OPEN. `NO_SAFE_CODE_SLICE` remains. The primary returns the exact failed premise to the sprint dispatcher before authorizing any further checker work.

Worker `/root/r17_forall` supplied an actual writes-stopped receipt: no active process or descendant; no commit. Only the failure's already spent 3 calls/20.684965 seconds count. The unused budget is not transferred or reset.
