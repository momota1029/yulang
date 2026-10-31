# R121 independent review — primary-recorded read-only report

The independent `compiler_referee` returned the report below. Its role is read-only, so the reviewer did not write a file; the primary recorded the returned report here without attributing authorship to the primary.

## Decision

**PASS for bounded research records only. `NO_AUTHENTICATED_LOCAL_TRACE` upheld.** No new blocking, major or minor defect was found in the R121 handoffs. This reduces a local membership consequence's premises but does not close Rust-to-Lean correspondence.

## Frozen inputs authenticated

Fresh SHA-256 reads matched:

| Input | SHA-256 |
| --- | --- |
| R121 contract | `0544d0f08716328e016906544e4b3b9f4c556c7fb71a4a123d1f04f6cba419c6` |
| R121 source handoff | `b016a0249755607b698c20c0516821b1119d01dd44f7daf1c4d5d9cf18fb09f1` |
| R121 proof handoff | `c9d331b6b4aa5f25892fe2041821a5c7eb9330241c955b2746a6858ca580b575` |
| R120 source / proof / review | `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e` / `2ce7eaba1483c4f9d5c190977421717125aa55b37c5764ee75b7b834d2da9415` / `ab6b4daa848196610986f62eebb7b5bbc3a32ba8bbdee0973954785b51ccc50b` |
| R119 Lean / R118 Lean | `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f` / `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` |
| R119 patch | `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a` |

The final virtual receiver `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470` is inherited from the frozen, independently reviewed R120 composition; R121 did not reconstruct it.

## Findings

- **Short circuit:** Source handoff lines 44–56 correctly require control to continue beyond the entire rejecting guard. An earlier true disjunct skips the member expression and returns `None`, so that path supplies no successful-read premise. The converse is rejected.
- **Same record and equality:** Source handoff lines 38–56 distinguish the inventory record pointer check from the `Option<&SourceEffectId>` value comparison. An equal payload at another address cannot replace the pointer premise. The indexed read uses `self.catch.permission.concrete`; the separate pointer guard binds that captured record to the unique selected inventory record. The slice-start comparison is not promoted to a length or provenance theorem.
- **Uniqueness and coordinates:** Registration-keyed uniqueness and packed-slot equality remain separate. Registration 7 at slot 0 does not identify storage slot, native member, concrete index or family.
- **Duplicates:** In `[4,9,9]`, changing index 1 to 2 preserves the local family comparison. This refutes inferring first-match from that guard while preserving membership. Both handoffs avoid claiming that the changed witness is reachable through safe capture. `None`, empty, out-of-range and unequal indexed values cannot satisfy the displayed `Some(f)` equality.
- **Lean specialization:** `PermissionMemberWitnessR119.lean:57` takes an indexed-read equation and concludes membership. The proposed specialization accurately omits search, registration, decoder and extraction premises for this local list consequence. If the read names another family, the required equality is retained. The handoff distinguishes written source from unchecked elaboration and axiom results.

## Existing blocker and preserved scope

The Rust comparison has not been shown to yield the exact Lean indexed-read equation for the interpretation of that actual record, vector, index and resolved family. An equal-looking Lean list would leave the premise assumed. Minimum closure is an established same-record interpretation deriving that equation from the actual Rust `Option`/`get`/equality, then theorem checking and a complete axiom audit. Another conditional membership lemma does not supply it.

Full `.position` and projection/request transport correspondence remains open. R39 PRE-state registration absence, R45 owning reads/extraction, R114 transport, R111 compilation, parent soundness, effect hygiene and production remain open. R121 introduces no model or axiom.

Review was read-only and had no build, test, compiler, Lean, checker, source execution, Git operation, recomposition, environment/storage probe, descendant or filesystem write. This report is a primary-recorded transcript; the independent review itself produced no file hash.
