# R119 independent static review

Verdict: **revision required — one major artifact defect**. No additional BLOCKING, major or minor compiler-correctness defect established in the intended Rust delta or conditional Lean statements. This is static candidate review, not compilation, kernel acceptance, source integration or production approval.

Assignment `/root/r119_review`, bound ≤180 seconds, no descendants. Applied the yulang-lean-proofs premise/source review discipline; the packet's explicit execution prohibition overrides its normal checker workflow. Initial conclusions used the contract, patch, Lean definitions and immutable baseline, not the implementer's self-explanation. Author handoffs were read afterward to audit their claims.

## Frozen identities

Independently recomputed SHA-256:

- R119 patch: `da385246bc86fdeb6737acef40d8f6f9afddfdeb6fbf5606a842917da6d34ed0`.
- R119 Rust handoff: `fb587997d39e45ec5e83eec4e8339b7a5806feeaaffdee540e92ce391afe7306`.
- R119 Lean candidate: `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f`.
- R119 proof handoff: `cd7f488faa9bc3ae5670fa3dfc3ab050a19e0ec8f772a5003f0125bf6b891c6d`.
- Frozen R117 patch: `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`.
- Frozen R118 Lean: `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab`.

Read root operating instructions, design authority, the R119/R118/R117 contracts, Authoritative annotation-effect hygiene policy §§1–1.2, exact R39/R45/R116 definitions and R118 decoder, frozen R117/R118 reviews and handoffs. Immutable Rust reads used only `git show d177c46ec61fcadd70a3d587c2f8934f6bc91f46:crates/yu-solver/src/candidate_receiver.rs`, following the primary's explicit clarification that exact baseline reads are permitted and Git mutations are forbidden. Relevant capture, consumption, request assembly and existing tests were read. No dirty Rust or quarantined source was read.

## Finding

**major — the submitted unified diff has invalid hunk lengths and overlapping advertised regions.** Exact locations: `tasks/agent-loop/artifacts/effect-permission-member-witness-r119.patch:34` and `:55`.

The capture hunk declares `@@ -5145,8 +5150,10 @@` but contains **13 old / 19 new** payload lines. Its final hunk declares `@@ -5155,7 +5164,7 @@` but contains **8 old / 8 new** payload lines. The other four hunk counts agree with their headers. These counts were independently calculated by reading line prefixes in memory, without applying the patch. A unified-diff reader using the declared lengths reaches further context/addition lines where another hunk/file header is required. The artifact cannot reliably deliver the intended source delta. Merely increasing the first lengths would also expose overlap with the following advertised old region; the two adjacent capture edits should be represented coherently together.

Violated contract: R119's fixed outcome requires an unapplied Rust **patch** based on the frozen R117 candidate; its research-only status removes application/compiler evidence requirements, but does not make malformed patch syntax a valid source candidate. The Rust handoff correctly says application is UNKNOWN; that disclosure does not repair the malformed artifact.

Minimum closure: issue a sequential frozen revision with correctly counted, nonoverlapping capture hunks, preserving the reviewed code changes; independently recount every hunk and match old context against the pinned baseline plus R117. No patch application, compiler run or environment probe is needed to close this syntax finding. Refresh exact artifact/hash references and delta-review the repaired bytes. Do not promote the current hash as a deliverable patch.

## Intended Rust behavior and adversarial traces

The intended change retains evidence at the responsible lookup owner: capture records the concrete vector position, request assembly transports it, and the existing successful observer consumer checks `get(index)` on the same borrowed permission. It does not reconstruct permission provenance from family coincidence or alter suppression downstream.

- Registration selects the record by its registration field in R117; packed permission storage is separately retained in `permission_index`; R119's `permission_member_index` selects within that record. Native endpoint member remains another coordinate. Registration 7 at packed slot 0 with concrete `[4,9,9]`, native member 0 selecting family 9, yields permission member 1. No numeric-namespace equality is required.
- The earlier capture guard still searches for the schema provider family and rejects absence. Baseline capture at 5092–5107 binds the owner-view member to `owner.schema.operation.id.family`; R117 additionally equates full provider/declaration/arm operation identities. Therefore the later search for `provider_family` is for the same family on a successful capture. Changing `.any()` to `.position().is_none()` retains equality-test order and early termination. The additional search is read-only.
- Empty concrete vectors reject at the existing capture guard. Duplicate equal families return their first position, and indexed consumption sees that equal value. A missing/out-of-range optional member rejects locally through `None != Some(provider_family)`; no unchecked indexing or panic was added.
- Different permission payloads cannot substitute merely because registration and family are equal: R117 consumer checks the selected payload pointer against the captured permission, and capture checks retained annotation/owner fields and concrete allocation pointer. Missing/duplicate registration fails uniqueness. Foreign owner/state/batch is checked by the existing owner chain and R117 pointer guards. R119 does not erase those guards.
- Full operation identities are still independently checked by R117. A same-family distinct operation can satisfy the finite Lean membership lemma, but cannot satisfy the complete Rust projection's full operation/declaration guards. This difference is explicitly outside the partial theorem's claim.
- New fields are consumed on the existing mandatory observer assembly path. The delta changes borrowed reads/local evidence only; no inference state, AST/CST, solver IR, rollback journal, suppression action, error diagnostic or recovery owner is changed. Optional observer failure is not promoted into ordinary solver failure.

Read pinned receiver tests at 5704 onward: exact signal suppression, same-spelling write forwarding, grouped scrutinee and private-envelope rejection with ordinary candidate admission retained. They substantiate existing sibling expectations, not executable validation of this candidate. No tests were run or changed.

## Lean claims and limits

All declarations in `YulangClosure.PermissionMemberWitnessR119` remain **CONSTRUCTED/UNCHECKED**. Printed types, elaboration, kernel results and complete axiom lists are UNKNOWN. The static proof surface contains no introduced axiom, sorry/admit or checker bypass; this observation is not a transitive axiom audit.

- `search_index_read` (37–54) constructs the actual indexed equality from successful ordered recursive search for arbitrary decidable identities and arbitrary lists/indices. Empty and duplicate cases are represented.
- `indexed_read_member` (57–69) derives list membership by list/index induction from a successful indexed read.
- `same_record_search_read` (74–82) joins search and read at one permission value and one index, deriving consumed/searched identity equality and membership. It assumes neither membership nor a generic faithful-decoder law.
- `selected_retained_member` (88–106) additionally requires the actual supplied R118 native and registration-keyed reads. Its conclusion preserves the separate registration/storage/member coordinates. It does not authenticate list ownership, pointers, state/batch or full operation identity.
- `certificate_member_if_extracted` (110–125) retains R45 extraction as an explicit premise and correctly transports to that exact output permission through `accepted_payload`. It constructs neither extraction nor R39 preparation.
- `distinct_coordinates_and_duplicates` (132–138) is a finite example of distinct coordinate roles and first-match selection. Its `by decide` has not executed.

Supplying an equal-looking foreign list/permission value can satisfy this mathematics, because it contains no Rust pointer model. That is a disclosed interpretation boundary, not a proof of foreign-owner rejection. Actual `iter().position`, `get`, immutable borrowing, same-record transport and complete owner/operation checks still require operational correspondence. No successful Rust execution is established by these equations.

R39's PRE-state remains a separate open obligation: `Valid` requires registration absent from `retainedRegistrations`, whereas retained POST-state contains the published registration. Search/index evidence cannot reconstruct the earlier Action, source annotation row, constructor inputs, `prepare` or `permissionFor`. R116 still requires those exact equations plus selected-source/operation premises; R45 extraction remains explicit. The submission does not claim otherwise. Original source domain, shared witnesses, inference soundness, complete hygiene, principality, termination, native correspondence and production remain OPEN. No semantics change or source-scope reduction is justified.

## STOP

Only this review receipt was written. No patch application, Rust/Lean execution, checker/compiler/build/test, environment/storage probe, scratch/cache/worktree, Git mutation or descendants. Static hunk counting and SHA-256/read commands completed successfully. Writes STOPPED; return to primary for finding adjudication. Receipt hash reported separately.

## Sequential narrow rereview — corrected patch

Primary authorized a ≤60-second delta review of the corrected patch and Rust handoff. Independently authenticated corrected patch SHA-256 `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a` and corrected handoff SHA-256 `731cc66eacc5f271bdf1d70054b8430ac0641ac55ac07281123f9fe5645e8e98`. The handoff at line 40 names that exact corrected patch hash.

Recounted all six hunks: old/new payload lengths are `5/6`, `4/5`, `7/9`, `4/5`, `13/19`, `8/8`, each agreeing with its corrected header. Old half-open ranges are `[237,242)`, `[610,614)`, `[1878,1885)`, `[4880,4884)`, `[5145,5158)`, `[5158,5166)`; new ranges are `[237,243)`, `[611,616)`, `[1880,1889)`, `[4884,4889)`, `[5150,5169)`, `[5169,5177)`. They are ordered and nonoverlapping, including the now-adjacent final pair.

An in-memory reversal of only the two corrected hunk headers reproduces the original patch SHA-256 `da385246bc86fdeb6737acef40d8f6f9afddfdeb6fbf5606a842917da6d34ed0`. This authenticates unchanged semantic payload; no source or patch application was used.

**Disposition: the one major malformed-diff finding is RESOLVED for the corrected patch hash. ACCEPT as an unapplied, uncompiled research candidate only.** Original finding and target hashes above remain preserved. The unchanged handoff revision marker is 1, so the primary must identify the corrected snapshot by its explicit hash rather than treating the changed same-revision bytes as idempotent intake. All original operational, kernel, source/native and parent-proof limits remain in force. No additional semantic review or execution result is inferred from this correction.

Only this receipt was updated; narrow read-only Python counting/hash checks and patch/handoff reads were used. No source reads, application, tests, builds, checker/compiler execution, scratch/cache/worktree, Git operation or descendants. Writes STOPPED again; corrected receipt hash reported externally.
