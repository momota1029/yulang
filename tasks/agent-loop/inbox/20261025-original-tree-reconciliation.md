# Original checkout reconciliation — 2026-10-25

Status: USER_AUTHORIZED_GIT_INTEGRATION, no new research/semantic gate.
The user explicitly requested commit/push of the original checkout after the
reviewed isolated result had been fast-forwarded into the remote research branch.
Root: /home/momota1029/rust/yulang. Branch: research/simple-sub-intrusion.
Primary performs this one-time original-tree integration; no producer work,
background process or new compiler/proof change is authorized by this record.

## Exact preserved history

Checkpoint: 6f67c7971c589d10a96894d51aa794d5dc7cd36a, parent
0132d07ca7e149b59f529469d1479a1c8cfa577a. It contains all six original files
byte-for-byte, plus the explicit research-only provenance manifest
`20261025-original-tree-preservation.md` (SHA-256
 d7405dadec6532bc7ca2077e5d7b90756e45e0b9504a9e0d886d707756ea68f1).
The source variants remain NOT_CHECKED / NOT_INDEPENDENTLY_REVIEWED. The stale
proof handoff does not authenticate the foreign proof. No old review or author
is reassigned to different bytes.

Reviewed merge parent: 5aac4fcfdec690d1432e200baa0a455f800b2555, already published
on origin/research/simple-sub-intrusion. The containing merge retains both
parents. Retrieve any original file with:

```sh
git show 6f67c7971c589d10a96894d51aa794d5dc7cd36a:notes/theory/lean/YulangClosure/SourceGeneratedInteraction.lean
```

Substitute any of the six exact paths in the preservation manifest to retrieve
its original bytes. Both historical variants and final reviewed files remain
reachable after ordinary push; there is no squash or history rewrite.

## Conflict decisions

Exactly four conflicts occurred. Before resolution, each stage2 blob matched
the checkpoint hash and each stage3 blob matched the published parent hash.
The two nonconflicting handoff/contract files matched both versions exactly.

| Path | Final decision |
| --- | --- |
| SourceGeneratedInteraction.lean | Exact reviewed16952fef6ea505cce0d7f8afa6bf39cd3609119626f7857d6beaa88737c5b003; Type1 candidate17566524… remains in checkpoint |
| source_generated_interaction_20261025.rs | Exact reviewedaea1caf0b88bbce6479050ebff4989cbc3afb784e50dad228a4af70bfa3df005; seed42/immediate118 candidate4a8ac875… remains in checkpoint |
| 20261025-source-generated-native-r1.md | Exact published227c601d2bb26186196b421933be91f0e0f78d2c77c8d4df0bd9b8ae0cf0517b, matching the published review chain; foreignf4c0ab7d… remains in checkpoint |
| current.json | Published completed/reviewed state plus this original-tree integration metadata; historical RECONCILE bytes remain in checkpoint |

All other published files are unchanged. Relative to5aac4fcfd, this integration
adds the preservation/reconciliation records and changes only compact scheduling
metadata. No compiler, Lean theorem, example behavior, expected output, question
bundle, manifest, lockfile or governing rule is changed in the final tree.

## Ownership, checks and limitations

A bounded60-second read-only dispatcher recommended this checkpoint-then-merge
strategy and returned STOP without tools/writes/children. Prior research budgets
remain ended. All six bytes were checked against the premerge snapshot, fresh
intake snapshot, staged index and preservation commit. Git conflict stages were
verified before exact-path resolutions; no blanket stash/reset/clean was used.
The user-directed intake does not prove cessation of historical unknown writers.
All eight UNKNOWN observations and unrelated quarantines remain recorded; no
new research writer receives those reservations. Unexpected new writes would
reopen reconciliation rather than silently enter this merge.

Verification for this task is Git/content integrity and compact-state static
validation only. No Lean/Cargo/native execution or test rerun is claimed. Final
source bytes retain the reviews and verification evidence in5aac4fcfd. The
unreviewed candidates retain their separate future primary proof/source intake.
Full-paper/native correspondence and original Simple-sub A/B remain OPEN.

Git completion requires the containing merge to be pushed normally to
research/simple-sub-intrusion, remote/local HEAD equality and a clean original
worktree. Primary reports actual commit/push receipts after those operations;
this record does not predeclare their success.
