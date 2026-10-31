# EFFECT-PERMISSION-LOCAL-DECODING/20261031-R60 outcome

Status: **CLOSED_BOUNDED_PASS_RESEARCH_ONLY**. This is a conditional, bounded research result. It grants no production authority and closes no parent theorem.

## Accepted result

From one constructed native input, R60 builds concrete `rows`, `views`, and `physical` readers and proves both fields of `LocalDecode` without assuming reader soundness. The physical receipt derives its facts from current-slot, emission, readback, admission, and relation checks in source order. Support equations come from the retained view/member/closed-tail inventory. Ancestry policy stays separate from physical reads. On the same constructed inputs, R59's initial-success candidate converse yields candidate membership and the existing R49/R57 consumer refinement without an extra decoder premise. Successful `Run` existence remains a hypothesis.

The frozen implementation is the private borrowed reader in `candidate_receiver.rs`; ordinary search, forwarding, ancestry policy, and the existing certified lower paths remain unchanged. The malformed atom-lane `EffectRow` returns unavailable because R47 uses atom-lane keys. The proof's finite falsifiers cover foreign state, crossed owner/view, swapped lane/index, stale readback, duplicate emission precedence, wrong relation, reordered Support member, canonical-row substitution, malformed atom row, and open Support tail at the existing search guard.

## Proof and independent review

Lean 4.35.0 Audit8 exited 0 with no warnings/errors. It authenticated 245 roots and complete final types/transitive axiom reports over the ten-module cone. The 25 new R60 roots use `[propext]` (16), `[propext, Quot.sound]` (8), and no axioms (1). The full cone has 107 `[propext]`, 128 `[propext, Quot.sound]`, 8 empty, and 2 preexisting R57 roots with `[propext, Classical.choice, Quot.sound]`. No R60 root adds `Classical.choice`; no project axioms, `sorryAx`, or native evaluation dependency occur.

The new proof module SHA-256 is `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`; its handoff SHA-256 is `161b792dca1920b7ba8d78725af9f42277efb4d20771e6c51ef133a0490f2f81`. Final audit input/stdout hashes are `b24c47d0171b8eade6831a3242d1479947267d1e5ae90f8ca27229fc7d6a30b0` and `e933c4e481ebfc001de7441a544fc04f7b33213ab0c4f93c98ac666c32f5a988`; stderr was empty. Eight raw audit triplets were preserved/authenticated by the producer and independently reconciled by the reviewer.

Fresh independent reviewer `/root/r37_inventory_review` returned **BOUNDED PASS**, no blocking/major/minor finding. The review report returned to the primary has SHA-256 `8d80bf7049829d0d713d2a67d072cf2cf8be9f415538100d847ab7e815f08d5d`; the primary placement is `tasks/agent-loop/inbox/effect-permission-local-decoding-r60-review.md`. Rust and Lean frozen hashes and all pinned dependencies matched. The reviewer also reconstructed the exact admitted receiver baseline in memory by removing only the new private decoder block.

## Exact frozen source artifacts

- Rust `candidate_receiver.rs`: `0b25ddde51ee77cfdc558ad4384ce827e9f48880bd598f1640f5323a102672de`.
- Rust handoff: `744014a3ec186e16e82cca0ba3497f53a08d2eb5bd5f60fe7f41ae8461b46730`.
- Lean `NativeLocalDecodeR60.lean`: `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`.
- Lean handoff: `161b792dca1920b7ba8d78725af9f42277efb4d20771e6c51ef133a0490f2f81`.
- R59 model and review: `d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab` and `59658c916da9d5cf6f766568045b1de7f1dc3348fec0076118ab81d3c9a694b3`.
- R58 model: `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`.

## Remaining OPEN boundary

The next seam is interpreting the pointer-anchored Rust owner and retained records as one R57 `Native` with a `Nat` state tag. Distinct Rust `State` pointers have not been proved to map injectively to distinct tags. Agreement between the model's `Cell.target` callback and Rust's row/lane/index-derived target during real worklist expansion remains part of the Rust-to-Run bridge. Inner ancestry/resource correspondence, full Context/R50 extraction, publication/runtime, original parent A/B, inference soundness, principality, termination, complete hygiene, and production remain OPEN.

No Rust build, tests, Cargo, formatter, typecheck, Lake, new environment, or worktree was run/created in R60. The required sprint static checker passed after state synchronization. Source and Lean authors are STOPPED/WRITES STOPPED; independent reviewer is STOPPED/WRITES STOPPED. Existing unrelated dirty and untracked work, all UNKNOWN worker observations, and all 12 quarantined leases were preserved.
