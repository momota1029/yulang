# R47 independent review — bounded PASS

Reviewer: /root/r37_inventory_review. Both authors were confirmed STOPPED before review. This report was returned read-only for primary placement.

**PASS for the private current-emission ownership construction and conditional Lean characterization.** No BLOCKING, major or minor correctness finding remains open. Concrete query success on a running instance remains unobserved. Provider arrival, Catch/residual correspondence and whole-parent closure remain UNRESOLVED.

## Source construction and ownership

candidate_receiver.rs:56–116 obtains R45’s actual Internal certificate for the experiment’s unique complete DefinitionUseId, checks relay/answer owners, and retains the same borrowed permission. Its entry_effect supplies the raw entry identity.

At lines 74–105, the wrapper obtains the indexed retained emission, requires its physical owner to be that exact raw entry, and restricts the lane to EffectLowerRow or EffectLowerAtom. It then reads the actual current vector at the addressed row/index: effect_bounds[row].direct_lower_rows[index] or effect_bounds[row].exact_non_variable_lowers[index]. It reconstructs the oriented positive BoundKey from that current item. Historical constructor readback is not substituted, and no canonical-row lookup selects the entry.

candidate_context.rs:2904–2960 follows the emission’s explicit admission ID into the owning admission vector. It checks emission/admission/current/readback bound equality and physical/readback slot equality. A second retained emission at the same complete physical slot rejects the lookup. Reverse uniqueness—one emission per admission—is correctly not required.

The selected admission must retain a relation whose exact stored pair equals bound_pair(admission.bound). The source root is selected by the same use occurrence/slot and R45 fact-derived pair, before receipt validation. Duplicate matching Origins reject rather than allowing malformed candidates to disappear during filtering.

The selected SourceDrainReceipt must be completed and agree on origin index, created seed, selected relation, cause occurrence and task pair, with no incoming relation or replay acknowledgement. Endpoint equality is only one equation within an independently anchored source chain.

require_relation_ancestry, lines 2962–3017, follows actual retained dependency parents, including both Replay parents. It validates relation references and bounds work and allocation. Missing ancestry, invalid references or exhausted search returns an explicit unavailable reason. This establishes the requested ancestry join; it does not infer ownership from graph reachability alone.

The resulting CurrentInternalEmission borrows both the same R45 incidence and checked admission/emission records. There is no provider-origin query, new route admission, propagation, permission consumption or suppression.

## Adversarial cases and lifecycle

The guards reject missing or swapped indexed records, changed physical/readback slots, changed current contents, duplicate physical-slot ownership, wrong raw entry/lane, absent or foreign relation pairs, ambiguous source roots, invalid receipts and absent ancestry.

Equal contents recreated at a physical slot are not independently distinguished by a generation/ABA theorem. The accepted source scope is the current borrowed state and completed experiment lifecycle. Shared borrowing prevents mutation during use of the returned references. The API does not certify a historical event supplied from another state or generation.

Existing evidence rollback truncates admissions/emissions, and context rollback removes relations/dependencies/Origins. The query adds no persistent state or rollback owner. Transient search containers are fallible and bounded; allocation failure returns unavailable. Rust execution, injected rollback and compilation were not performed.

## Exact delta and frozen hashes

Independently removing only the new query/type blocks in memory reconstructs both admitted source baselines exactly:

| Source | Reconstructed baseline SHA-256 |
|---|---|
| candidate_context.rs | 030fcb4b6571c0db8a670d12a8d67fe8fcf465484502fe5b11b6d057e8026c38 |
| candidate_receiver.rs | f5bff0d8aa7a20551fb2c5ad60b7b2b41907f471a55068a9ec1ae61ceba02911 |

This establishes the bounded additive delta without Git and without normalizing unrelated dirty bytes.

| Artifact | SHA-256 |
|---|---|
| R47 contract | af75bcc2dcf6103fe3e3cabfb33f4ce0de91c516acacbe09f74af3a6dfe58d70 |
| R47 admission | 0de99112d82388c050acfe10799d7e0d1af51ed8960a81f4d893519055db4b64 |
| candidate_context.rs | 184f09e91221f8ae0969d1dbc792b7707ef5571ff56d96e276467641215bf32e |
| candidate_receiver.rs | 1426526cad48d4bc02984e0a5967e30e50cd188cb01fbeb71bc6f15442e59448 |
| Rust handoff | 6a8e7c60a6bf45733524b457c8cffb43d4ebae5101bb8a526fd9ca0f60a1f8de |
| R47 Lean | d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c |
| Proof handoff | ce27378fe9dbc6c25ede25869a238bbf59af14ffe9a64202d3aeb520947a08e1 |

Unchanged dependency pins matched, including candidate_effect.rs 2a86befde95581dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631; candidate_scheme.rs bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631; lib.rs 25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4; copied-bound owner 80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61; R45 Lean 9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f; and R46 Lean 3429aef705d2c059c23c8ec0a33dd1e4a6dcb75c9461e90f4380df679146f3c3. R39, R45/R46 handoff/review, governing design, toolchain, project configuration and audit-helper pins also matched, subject to the authenticated R46 erratum below.

## Lean correspondence and theorem census

All twelve actual declarations, statements, proof bodies and final printed types were inspected. The model reconstructs current bounds from row vectors and physical lanes. Rust accepts its exact lower-entry subset. Indexed admission ownership, singleton physical-slot ownership, relation-pair consistency and same-use root checks correspond to the source guards.

The mathematical ancestry checker validates an explicit finite path. Rust searches reverse parents with resource limits. Search completeness, allocation success and acceptance on a concrete runtime instance are not proved.

Root Fact observations are derived extraction observations. Neither Origin nor SourceDrainReceipt directly stores a FactId. Source anchoring comes from R45’s actual fact plus the exact occurrence/cause, singleton Origin and completed task-pair checks. Omitted administrative receipt fields remain part of the source interpretation, not silently proved by the model.

apply_to_internal requires successful R45 extraction, successful local R47 checking, and exact same-use, same-fact and same-raw-entry equations. It preserves the same whole permission and concrete list, current physical bound, raw entry owner and retained ancestry. It assumes no aggregate arrival or ownership predicate.

Every theorem in namespace YulangClosure.CurrentEmissionOwnershipR47 has complete transitive axioms [propext, Quot.sound]:

1. ancestry_sound
2. accepted_iff
3. accepted_current_slot
4. accepted_unique_event
5. accepted_same_use_entry
6. accepted_root_fields
7. mismatch_rejected
8. swapped_or_stale_rejected
9. foreign_use_or_entry_rejected
10. apply_to_internal
11. concrete_current_event_witness
12. concrete_swapped_stale_foreign_rejected

No final project axiom, Classical.choice, sorryAx, native-evaluation assumption, proof hole or checker bypass was found. Finite examples establish model inhabitance and rejection cases, not Rust execution.

## Retained checker receipts

No checker was rerun. All thirteen preserved stdout blocks independently reproduce their recorded hashes. Source-aligned final batches 8–13 support the final correspondence census and contain exactly the twelve declarations in source order with matching markers, complete types and axiom reports.

Final source-base SHA-256: 447d600a80a3c34635315bd84f0e78c677361560d61c7011671ac6c825649246

| Batch | Verified stdout SHA-256 |
|---|---|
| 8 | fce0c36b3d158537fce2991c8edde771728c5b54d1c3a9e5d37e30651cd369fc |
| 9 | 44d5d04a89970061eb1ee855487e87aeb08b287e55f6b655ea6b4b1a76758349 |
| 10 | e9601b0effbb00eeb319b32d35654989946a1ce8110098252b82ac3cf514886b |
| 11 | 2e5a6b9dfa5ba684f30d45470dbd09fb2ca2ff42365c06b137d1bd8e0f3bf5a8 |
| 12 | 7fcde00f2c69ea621e05c80f5bbc623087a67a7d4a1a02a158c449a5f6575a68 |
| 13 | fb2047a931d3a87248ba2c55ed36ee9d601c0223cd2c374cecb514e5e6cc35c4 |

Receipts report pinned Lean 4.35.0, read-only stdin, -j1 -M1024, 120-second invocation limits, exit 0 and no final warnings. Reported total proof wall time is 46.632704 seconds; maximum RSS is 1,039,080 KiB. These are retained producer measurements, not fresh reviewer measurements.

## R46 dependency erratum

Erratum record SHA-256: 7b901ab3aaac22387a91cc3d5974ba5269da2b9b9b6a516bf9987cb212f2614f

Using the primary-supplied exact baseline transcription, replacing only the corrected context hash in the current R46 review reconstructs contract-pinned review hash 7fbaed174bee5cae7a92874ddd795b9b80ec1bc8cd7f18acc30e6dedfde7c56e. Reversing only the outcome’s review-hash reference reconstructs 512e2afbe9f5f6ac12279b587fb6c2453f78bed1254ba4eff33fd69ea3395f14.

This verifies the content correction as hash transcription/reference maintenance, with unchanged reasoning and verdict. Baseline commit membership is supported by primary/dispatcher evidence; reviewer ran no Git command.

Frozen disclosures distinguish actual consumption: Lean read the original pinned review; Rust read the corrected review and inventoried the outcome by hash. The proof imports R39/R45 only. Those historical records do not establish or alter the new source join.

## Boundary and STOP

This PASS certifies the bounded private owning-record query and its conditional mathematical characterization. It does not establish provider arrival, that a concrete instance returns a certificate, global completeness, cross-generation ABA safety, Catch selection, residual subtraction, original A/B/hygiene closure or production readiness.

Reviewer STOPPED. Read-only inspection and in-memory hash/delta verification only. No writes, checker/compiler/build/test reruns, Cargo/Lake, Git, scratch files, new environment/worktree/cache/target, descendants or persistent processes. No quarantined runtime path was accessed; no lease or quarantine was released.
