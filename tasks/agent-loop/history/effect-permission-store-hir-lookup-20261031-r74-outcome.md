# R74 outcome — store-owned admitted HIR lookup

**Disposition: `CLOSED_BOUNDED_SOURCE_REPAIR_ACCEPTED`.** Fresh independent review accepted the limited Rust source repair with no blocking, major, or minor finding. This closes R73's missing-`ConstraintStore`-method source blocker only. It does not close the R73 Lean/native bridge, the parent theorem, or production.

## Implemented repair

`ConstraintStore::hir_position_for_occurrence` now returns `Option<(usize, &Arc<HirModule>)>` from the same store's admitted `hirs` inventory. It accepts a valid indexed owner hit; otherwise it selects the first full-artifact owner in that inventory. A misleading or out-of-range map index cannot authenticate an occurrence. `require_owned` is unchanged.

Both receiver paths use the returned inventory coordinate: projection validation checks the coordinate, borrowed slot and full occurrence ownership; provenance reification stores that coordinate directly rather than finding an unrelated pointer position. Existing `BoundMismatch` and `SearchLimit` mappings remain. No inference, constraint, propagation, routing, execution, or HIR transformation semantics changed.

The Rust author pinned the pre-edit `lib.rs` and receiver hashes from the R74 input manifest and enumerated the exact receiver edits in the frozen handoff. The reviewer independently inspected the current files but could not byte-compare against the uncommitted pre-R73 receiver; acceptance therefore retains the writer's preservation receipt as an explicit provenance dependency. The cumulative checkout diff includes pre-existing R73 receiver changes.

## Evidence and review

- Rust `lib.rs`: SHA-256 `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745`.
- Rust receiver: SHA-256 `6452e18c32bd55e49b31a2dcd474d39140ca97b73ce71a0f4fede07d32b4840e`.
- Rust handoff: SHA-256 `9b4b5a1a5f3ba0c3bc2df06005a6882db74a4c6f376479816ce631e146382124`.
- Source/Lean correspondence note: SHA-256 `3ac2c7ac7771462187488f09750abdc0cb4ec4fe11422e5700d755a28b95863c`.
- Independent review: SHA-256 `34f8fb8e9448d6e6463e4d85a418f8ccc30823a639aca66f54428a8a65dc3267`.
- Review contract: `e20477f1fea775ca9bd2cadc32dfff883d03833a0a68d8d08974486c1d63c1c1`; inputs manifest: `12411b44a6fa42cd6f86030df9baf8318900ede3fc96ced3588b50afe0a0d676`.
- `git diff --check` passed for the leased source files and state/review records. `python3 tools/agent_sprint.py check` passed; it is static state validation, not live-execution or compiler evidence.

No compiler, Cargo, build, test, formatter, Lean/Lake, executable probe, cache, target, scratch, environment, or worktree was used in R74. Rust type checking and runtime remain unverified. The correspondence note is conditional on faithful physical artifact identity and ordered extraction; it does not prove those premises. No new Lean theorem or axiom audit was claimed.

The accepted R73 Lean artifact remains accepted only within its finite conditional model. Physical pointer/Arc/registry/slice/map/allocator extraction, complete native readbacks, genuine R66 `Root`, original A/B, whole-language hygiene/soundness/principality/termination and production remain OPEN. R72 attempt-1 remains UNKNOWN/unrefunded; unrelated UNKNOWN/quarantines, R24 capacity authority and all 32 pending items are unchanged.

## Git disposition

R74 admission, author launch, proof handoff, reviewer launch, and the reviewed source checkpoint were committed and pushed on `yulang3`:

- `5ed00e1c3` admit R74;
- `0c21b8c45` record live Rust/proof launch;
- `dd636b4dc` record frozen source correspondence;
- `89fe216f9` record independent-review launch;
- `53bc36f91` implement and integrate the reviewed store-owned lookup.

No force push. Only the two leased Rust files and their R74 handoffs/state receipts were staged for the source checkpoint; unrelated dirty files were left untouched.
