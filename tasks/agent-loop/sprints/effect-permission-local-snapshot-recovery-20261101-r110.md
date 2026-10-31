# R110 local pre-R106 source snapshot recovery

Status: **ADMITTED** under the user's standing Rust implementation analysis/push authorization. Baseline commit: `23a968dc9` (R109 reviewed evidence pushed).

## Target

Recover either complete `candidate_effect.rs` bytes matching the pre-R106 dirty SHA-256 `fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5`, or an authenticated R106 revision-1 patch sufficient to reconstruct those exact bytes and attribute the unscoped transformations.

R109 independently recovered the committed R107 baseline (`1c80c55c…`) but confirmed it is not this pre-R106 dirty snapshot. R106 block removal produced a distinct SHA from the target, and its author recorded generic replacements outside the newly added test block. The exact R106 source snapshot/patch remains missing.

## Assignment and limits

One Luna/high implementer, ≤300 seconds, sole write lease:
`tasks/agent-loop/inbox/effect-permission-local-snapshot-recovery-r110.md`.

Read-only scope: path-specific refs/reflogs and existing stash/object database; R104–R106 records and source snapshot/patch artifacts identified by those records. Do not inspect quarantined paths, unrelated personal/session data, or broad external filesystems. Keep every dirty path untouched.

First inspect path-specific reachable/reflog candidates and referenced artifacts; then, within the bound, plausible unreachable blobs. Hash candidate bytes in memory. Report search coverage, immutable identity and complete hash; if none matches, specify exactly what was searched and the remaining evidence gap. A filename, approximate diff, or committed baseline is not sufficient. No checkout, stash application, object creation, `--lost-found`, copies, scratch, worktree, fetch, GC or pruning.

Resource bounds: one lightweight process at a time, ≤1 GiB RSS, ≤256 MiB candidate content inspected, ≤300 seconds. Stop immediately at any bound. No build/Cargo/test/compiler, source materialization/edit, cache/environment, Git mutation, staging or push.

A fresh `compiler_referee` review ≤180 seconds must independently reproduce any claimed target hash and protected-region comparison. PASS authorizes only provenance use in a later separately admitted source gate. If no exact artifact is recovered, stop historical recovery as the active method; do not admit an equivalent repeat search. Luna must plan a fresh baseline-derived source component with independently reviewable changes and a feasible verification method.
