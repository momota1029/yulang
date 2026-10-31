# R74 independent review

**Verdict: ACCEPT for the bounded source lookup repair. No BLOCKING, major, or minor correctness finding.** Compilation, runtime, physical Rust-to-Lean extraction, and parent theorem closure remain unverified.

Reviewer: `/root/r74_review`. Sources and contract were inspected before reading the authors’ explanations. Review remained read-only; the primary must persist this report. No author contact, descendants, files written, Git mutations, compiler, Cargo, tests, formatter, Lean/Lake, executable probes, environments, worktrees, caches, targets, or scratch.

## Cause and ownership

The change repairs the missing owning method: `ConstraintStore::hir_position_for_occurrence` now exists at `crates/yu-solver/src/lib.rs:3897`, returning `Option<(usize, &Arc<HirModule>)>` from that store’s inventory. Both receiver calls target this method. No `InferenceSession` inventory substitution supplies the answer.

Static type inspection finds consistent receiver, result, and borrowing types. The method’s output borrow follows `&self`; indexed `get` and fallback `iter().enumerate().find` both return a borrowed `Arc<HirModule>` slot with its corresponding inventory index. The descendant `candidate_receiver` module can access the private ancestor method. This is source reasoning, not compiler acceptance.

## Ownership and alternate paths

For arbitrary finite `hirs` and map contents:

- A valid indexed owning hit returns that exact index and borrowed slot.
- A missing map entry, out-of-range position, or indexed artifact that fails ownership falls back to the first owning artifact in the same inventory.
- If no admitted artifact owns the occurrence, the accessor returns `None`.
- With duplicate admitted entries, a valid indexed hit retains its selected position; fallback chooses the first matching position.

Thus accessor success has the same predicate as unchanged `ConstraintStore::require_owned` at `lib.rs:3887`: existence of an owning artifact in this store’s inventory. The complete `lib.rs` diff adds only the 11-line accessor and leaves `require_owned` unchanged.

`HirOccurrenceId` equality/hash retain both ordinal and artifact token (`crates/yu-hir/src/module.rs:1438`); `HirModule::owns_occurrence` tests artifact-token pointer identity (`:2103`). Equal local ordinal zero from independently minted artifacts cannot authenticate ownership. Shared artifacts across sessions remain admissible when present in the selected store; session origin alone is not grounds for rejection. No name, path, spelling, or content comparison enters this lookup.

At `candidate_receiver.rs:1573`, reification stores the accessor’s returned `artifact_index` beside the original full occurrence. At `:1053`, validation retrieves the admitted inventory slot, calls the store accessor, checks the returned coordinate directly, checks full ownership and borrowed-slot pointer equality, and retains the `require_owned` check. The prior selected-owner and slice checks at `:936` bind that admitted inventory to the selected experiment’s actual store. Shared immutable borrows keep selection and validation stable.

Missing ownership/coordinate evidence maps to `BoundMismatch`; occurrence-row overflow remains `SearchLimit`. The repair adds no store mutation, publication, recovery, inference, propagation, routing, execution, or HIR transformation behavior.

## Conditional proof correspondence

The unchanged R73 definitions were read directly:

- `requireOwned` at `OwnerExactCompletedInstanceR73.lean:374` expresses admitted artifact membership.
- `Readbacks` at `:399` checks occurrence positions against the selected owner’s ordered inventory.
- `decodeOwner` at `:422` authenticates completed-view/experiment pairing before using owner rows.

The retained source coordinate supports the modeled inventory-position conjunct under faithful artifact identity and ordered extraction. Source validation additionally requires the accessor-selected coordinate; Lean permits any coordinate containing the matching artifact. Duplicate entries therefore introduce no contradictory uniqueness premise.

This does not establish physical pointer/registry extraction, complete native readbacks, resource correspondence, or a genuine R66 `Root`. Original A/B, whole-language results, and production remain OPEN. No Lean execution or fresh axiom audit occurred.

## Frozen evidence and delta boundary

Independently observed SHA-256 values:

| Artifact | SHA-256 |
|---|---|
| R74 `lib.rs` | `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745` |
| R74 receiver | `6452e18c32bd55e49b31a2dcd474d39140ca97b73ce71a0f4fede07d32b4840e` |
| Unchanged HIR module | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| Unchanged R73 Lean module | `afed53ee5ebb82bbe87c171c6ac2808919976046df4cb2e0fdeb774f618a6e87` |
| R74 Rust handoff | `9b4b5a1a5f3ba0c3bc2df06005a6882db74a4c6f376479816ce631e146382124` |
| R74 correspondence note | `3ac2c7ac7771462187488f09750abdc0cb4ec4fe11422e5700d755a28b95863c` |
| R74 contract | `e20477f1fea775ca9bd2cadc32dfff883d03833a0a68d8d08974486c1d63c1c1` |
| R74 input manifest | `12411b44a6fa42cd6f86030df9baf8318900ede3fc96ced3588b50afe0a0d676` |

The four unchanged R73 handoff/review/outcome input hashes also match the manifest. `git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/candidate_receiver.rs` passed.

**Exact receiver delta limitation:** R73’s receiver was an uncommitted input, and the primary reports no authenticated retained old bytes or Git object. Its pre-edit hash is recorded, and the Rust author’s authenticated preservation receipt supplies the pre-edit comparison. I independently checked the current source and described changed call paths, but cannot independently byte-compare the R74 receiver against those old uncommitted bytes. The checkout Git diff includes R73 changes. Acceptance therefore carries this explicit provenance dependency; it must not be reported as an independent byte-for-byte R74 delta audit.

Relevant existing artifact-isolation and occurrence-identity tests were read, not run. Zero executable probes were used.

**Reviewer STOPPED / WRITES STOPPED.**
