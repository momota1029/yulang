# R110 local pre-R106 snapshot recovery

Sprint: `effect-permission-local-snapshot-recovery-20261101-r110`.
Assignment: `/root/r110_local_snapshot_recovery`, original revision 1; Luna correction, revision 2.
Requested model/effort: `gpt-6-luna` / high. Observed model/effort: UNKNOWN.
Outcome: **NOT RECOVERED**. No source file was written or materialized.

## Search and result

Target complete-file SHA-256:
`fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5`.

- Path-specific `git log --all --reflog` and `git rev-list --objects --all --reflog -- crates/yu-solver/src/candidate_effect.rs` covered 71 distinct reachable/reflog path blobs. All 13,778,709 candidate bytes were hashed in memory; none matched.
- Stash metadata was checked path-specifically. The two current top stashes contain no change for this path; no stash was applied or inspected beyond that path check.
- `git fsck --unreachable --no-reflogs --no-progress` reported 371 unreachable commits. Their trees contain 12 blobs at the exact source path; all 2,499,357 bytes were hashed in memory; none matched.
- Unreachable object metadata reported 717 blobs / 59,148,401 bytes total. To bound content inspection and avoid unrelated data, only 16 unreferenced blobs in the plausible 250,000–450,000-byte source range were read and hashed (5,641,616 bytes total); none matched. This does not establish that arbitrary unreferenced blobs outside this range are irrelevant.
- The live dirty file was read without modification: 381,143 bytes, SHA-256 `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`; it is not the target.
- The cited R104–R106 source records, outcomes and handoffs were inspected. They preserve the target hash and report that removing the R106 test block yields a different SHA, while revision 1 used generic unscoped replacements. No exact revision-1 patch or complete pre-R106 bytes are present in those artifacts. Unreachable commit trees contain no prior version of the R106 source handoff or sprint contract. The R109 recovery handoff/outcome confirms only the committed R107 baseline blob (`20c1635c7c3974a22ff14b62916cad76062e256c`), whose full-file SHA is `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`, not the target.

The exact evidence gap is the missing complete pre-R106 snapshot or authenticated revision-1 patch. This search cannot attribute the reported outside-test replacements. Per the contract, historical snapshot recovery stops here; no reverse edits are inferred. A fresh baseline-derived source component requires a separately admitted source gate and a feasible verification method.

## Bounds and hygiene

The author reports completion within 300 seconds; wall time was not independently measured. Candidate content read totaled 22,300,825 bytes, below the 256 MiB cap. Peak RSS was not recorded, so compliance with the 1 GiB RSS limit is unverified. No checkout, stash application, object creation, scratch, copy, worktree, fetch, GC/prune, source write/materialization, build/test/compiler, cache, Git mutation, staging or push occurred. Quarantined paths were not read. No known disposable scratch was created. The only new path is this leased handoff.

Writes stopped; **STOP**. This report is not independent review, source validation, or authorization to integrate the live file.


Revision 2 correction by Luna after independent compiler_referee review: the original wording overstated verification of the RSS limit. No search was rerun and no source, candidate, or bound was changed; only the resource-evidence statement was qualified.
