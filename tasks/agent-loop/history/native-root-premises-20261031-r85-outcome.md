# R85 bounded outcome — conditional lifecycle audit passed, native bridge open

Sprint: `EFFECT-PERMISSION-NATIVE-ROOT-PREMISES/20261031-R85`  
Contract: `tasks/agent-loop/sprints/native-root-premises-20261031-r85.md`  
Baseline: `c4e594fc64d72dba30a73c64fcbf258eaebdfc32`

## Result

The exact flattened Lean audit passed after the single Amendment 03 reduction repair. Slot 2 used 115,884 bytes with SHA-256 `bac29ad18bd16e9a5af0422ea4d3416e049a61951d6b1545c8ba35a0548cbc79`, ran the pinned Lean v4.35.0 executable with `-j1 -M1024 --stdin` and `LEAN_NUM_THREADS=1`, exited 0 without timeout in 7.866 seconds, and emitted 63,692 bytes of stdout (SHA-256 `686bf27a6570b2c9f7009b4622cc1593c50bc64bec0b58992429030bec804918`) with empty stderr. Peak child RSS was 925,468 KiB. The complete receipt is retained in `tasks/agent-loop/inbox/effect-permission-native-root-premises-r85-review.md`.

All eleven R85 theorem types and axiom reports were printed and independently audited. `pending_nil` depends on no axioms; the remaining ten depend only on `propext`. No errors, `sorryAx`, project axioms, `Classical.choice`, or native evaluation shortcuts appeared. The R85 conditional lifecycle therefore proves that every modeled reachable Origin remains attached to an incomplete drain, rejects `checkedRootGate`, and blocks the unchanged R84 `Primitive` on the same records.

This accepts the conditional finite Lean model for the exact flattened stdin only. It does not establish that the lifecycle model exhausts Rust initialization and sibling-module transitions, that the producers supply a successful checked root, that R57's relation-ID selector entails R84's occurrence/route selector, or that original Simple-sub A/B is closed.

## Source evidence and remaining obstruction

The frozen source handoff `tasks/agent-loop/inbox/effect-permission-native-root-premises-r85-source.md` (SHA-256 `06f55710a9cbee24e6171435f7062b938d07afca5f079b5fb369bf7d15fcb8b9`) found that the inspected producer attaches a `completed=false` drain receipt to an Origin, then stores a completed clone separately. `checked_internal_use_root` requires the Origin-attached receipt itself to be complete. The audited producer path therefore does not provide that checked root under the inspected assumptions.

The source inventory is not exhaustive: `pub(super)` fields permit sibling mutation and actual initialization/resumption paths remain outside the admitted source slice. No source-reachable successful-root counterexample was proved. The R57 selector uses state/relation ID while R84 uses occurrence/route selection; global relation-ID uniqueness remains unproved. These are the exact open premises for the next bounded source/proof step.

No Rust/compiler changes, builds, tests, Lake/Cargo work, scratch, cache, target, installation, worktree or new environment were used. The two-call audit cap is exhausted (2/2). Slot 1 remains rejected because its recovered reduction theorem depended on `sorryAx`; only the repaired slot-2 theorem reports are accepted.

## Review and integration

The fresh independent reviewer approved the diagnostic-directed one-line repair before execution and independently audited the complete slot-2 receipt afterward. Reviewer: `/root/r85_review` (`compiler_referee`), STOPPED, read-only. Revision-2 candidate and proof handoff hashes, exact input, authorization and raw result are pinned in the R85 review receipt and synchronized input manifest.

The exact-input authorization was committed and pushed before execution as `0bebbdf7d1f64460d9235b4e096af3086d597e42`. The audited revision-2 candidate, handoff, raw result receipt, synchronized input manifest and this outcome are integrated in the primary checkpoint commit.
