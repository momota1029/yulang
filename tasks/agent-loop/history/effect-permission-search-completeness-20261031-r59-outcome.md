# R59 outcome — bounded model completeness PASS

Sprint: EFFECT-PERMISSION-REACHED-SLOT-COMPLETENESS/20261031-R59
Contract SHA-256: `90278c103db56eaea91a65491241aec55e111db20bbfa2a71c85cc82b155e9b3`
Baseline: `3c103d8d1`; R59 admission: `78a1a2ed3`.

## Result

The initial-state candidate converse and exact result membership equivalence are proved in the unchanged R58 operational model. For every original `Checked` target branch, every successful complete initial `Run` contains it in `results`; conversely, successful results are exactly checked target candidates. The converse assumes no queued-target, frontier-coverage, uniqueness or all-readers-success premise.

The frontier invariant tracks an already-found goal, queued prefix continuation, or explicit remaining original Support-member/physical-cell continuation. It is initialized from the checked derivation, preserved through arbitrary mixed prefixes and every `Move` case, and eliminated at successful exhaustion. The complete model preserves LIFO ordering, branch-local seen pruning, and absorbing reached failures.

Adversarial applications show: the R2 omitted-candidate state is unreachable from initialization; competing distinct checked targets prevent successful Run without claiming an error priority; repeated endpoints are pruned by freshness; a mixed physical-to-Support candidate has both an original checked derivation and an explicit complete initialized model run. A finite existing-consumer application retains its separate `LocalDecode` premise.

## Lean evidence

Frozen module: `notes/theory/lean/YulangClosure/ReachedSlotCompletenessR59.lean`, SHA-256 `d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab`.

Frozen proof handoff: `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-proof.md`, SHA-256 `830b01128716055f4b3b54e2c650e865af97bc2ff1f5d54efcd34a78e07501e9`.

Pinned Lean 4.35.0 Audit5 exited 0 with no warnings/errors/diagnostics. It records all 220 roots across the exact nine-module cone, including all 43 R58 roots and 28 new R59 roots, with complete printed theorem types and transitive axiom audits. R59's 28 roots use `[propext]` (15) or `[propext, Quot.sound]` (13); none uses `Classical.choice`, project axioms, `sorryAx` or native evaluation. The full cone has 91 `[propext]`, 120 `[propext, Quot.sound]`, 7 axiom-free roots and 2 existing R57 roots using `[propext, Classical.choice, Quot.sound]`.

Audit5 input SHA-256: `7c52418564b19f395af278b11f5610ae1c32f7e69d64edc4f8680fa2babd6113` (314187 bytes). Output SHA-256: `5e065d48d3dee887025e73ceb34f032dbabe78dddcb9a0a45766c3b69c1940b2` (310971 bytes). Stderr empty. Wall 13.052817701s; peak RSS 1068816 KiB. All five raw audit triplets and exact bytes are preserved in the handoff.

## Source mapping and review

Rust handoff: `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-rust.md`, SHA-256 `bc35f40e1ed7de957634472ea91e3fbb6cb040e4dfdf99e4b872edf2bd11e45c`. No Rust source change was needed. The frozen mapping covers Support decoding/scheduling, LIFO order, branch-local cycles and the early `relations.len() > 65,536` ancestry guard. `candidate_receiver.rs` and `candidate_context.rs` match the pinned hashes.

Independent review: `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-review.md`, SHA-256 `59658c916da9d5cf6f766568045b1de7f1dc3348fec0076118ab81d3c9a694b3`. Verdict: BOUNDED PASS, no blocking/major/minor finding. The reviewer authenticated the R58 R1-to-R2 delta (all 43 roots and 18 audit archives) and R59 final cone (all five archives and 220 roots), checked every new theorem type/axiom result, the frontier proof, source mapping, omitted-state reachability, competing targets, cycle pruning and mixed physical-to-Support witness. R58 R1's separate review remains intact; its minor handoff omission of the oversized ancestry guard is now explicit in the R59 source map.

## Limits

This closes only initialized successful-search candidate completeness in the R58 model. It does not prove successful Run existence or termination, a concrete same-owner Rust reader encoding, general `LocalDecode`, Rust-to-Run simulation, inner ancestry visitor/resource correspondence, caller extraction/final rereads, complete Context/R50 interpretation, original parent A/B, inference soundness, principality, termination of the compiler, full hygiene or production. No semantic or Rust source change was made. No build, test, Cargo, Lake or typecheck was run; only the pinned Lean stdin audits and the repository-mandated static sprint checker ran.

All authors/reviewer STOPPED; writes stopped. This is a bounded research checkpoint, not parent-theorem closure or production authorization.
