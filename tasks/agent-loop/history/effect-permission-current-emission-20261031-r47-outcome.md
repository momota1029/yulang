# R47 outcome — CLOSED_BOUNDED_PASS

Sprint: EFFECT-PERMISSION-CURRENT-EMISSION / 20261031-R47
Contract: tasks/agent-loop/sprints/effect-permission-current-emission-20261031-r47.md
Baseline: 8017b53f5
Review: bounded PASS, no open correctness findings; reviewer STOPPED before Luna integration.

## Original bounded outcome

Construct a private, borrowed source query joining the actual retained BoundEmission to its owning admission, current physical owner/lane/index read, and retained relation ancestry rooted in R45’s complete Internal DefinitionUseId and same raw entry. The alternate success was a source-qualified exact missing owner transition. The sprint did not authorize provider, routing, consumer, propagation, Catch, subtraction or semantic changes.

## Result and evidence

The private receiver wrapper obtains the same R45 Internal certificate and permission, checks the raw entry identity, requires the emission’s physical owner and lower lane to match it, then reads the current indexed lower bound from the addressed effect_bounds vector. It reconstructs the oriented positive bound and rejects missing, changed, swapped or duplicate physical-slot ownership.

The context query follows the emission’s explicit admission ID, checks bound and physical/readback slot equality, validates the admission relation’s exact observed pair, and selects a unique source root for the same use occurrence/slot and R45 fact-derived pair. It validates the completed SourceDrainReceipt and traverses retained dependency ancestry, including both Replay parents, with bounded fallible search. Missing or ambiguous evidence returns unavailable. The resulting record borrows the checked emission/admission and the same R45 incidence.

Independent review reconstructed both admitted Rust source baselines by removing only the new query/type blocks in memory. It found no BLOCKING, major or minor defect. The source paths and review details are in the frozen review receipt.

Lean module YulangClosure.CurrentEmissionOwnershipR47 contains 12 accepted declarations: ancestry_sound, accepted_iff, accepted_current_slot, accepted_unique_event, accepted_same_use_entry, accepted_root_fields, mismatch_rejected, swapped_or_stale_rejected, foreign_use_or_entry_rejected, apply_to_internal, concrete_current_event_witness, and concrete_swapped_stale_foreign_rejected. Each complete transitive axiom set is [propext, Quot.sound]. The parent application uses the same R45 permission and explicit same-use, same-fact and same-raw-entry equations; it assumes no aggregate arrival predicate.

Final source-aligned Lean audit batches 8–13 report exit 0, complete types and axioms, no warnings, and final source-base SHA-256 447d600a80a3c34635315bd84f0e78c677361560d61c7011671ac6c825649246. Final Lean SHA-256: d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c. Proof handoff SHA-256: ce27378fe9dbc6c25ede25869a238bbf59af14ffe9a64202d3aeb520947a08e1.

Rust source hashes: candidate_context.rs 184f09e91221f8ae0969d1dbc792b7707ef5571ff56d96e276467641215bf32e; candidate_receiver.rs 1426526cad48d4bc02984e0a5967e30e50cd188cb01fbeb71bc6f15442e59448. Rust handoff SHA-256: 6a8e7c60a6bf45733524b457c8cffb43d4ebae5101bb8a526fd9ca0f60a1f8de.

Independent review report SHA-256: 2f2fc7568b67058cd1e3aac50635206687a9c5bfcaf3a4d36065aab01287bc40. R46 dependency erratum is recorded at tasks/agent-loop/history/effect-permission-entry-arrival-20261031-r47-r46-dependency-erratum.md, SHA-256 7b901ab3aaac22387a91cc3d5974ba5269da2b9b9b6a516bf9987cb212f2614f.

## Authors, reviewer and STOP receipts

- Rust implementer /root/r43_rust froze the exact source and Rust handoff hashes above, reported no build/test/Git or out-of-lease writes, and STOPPED. Runtime telemetry was UNKNOWN.
- Lean prover /root/r43_proof froze the exact Lean and proof handoff hashes above and STOPPED with no Lean process. Final source-aligned batches 8–13 passed; total proof-call wall time 46.632704 seconds, final script CPU 15.927591 seconds, maximum RSS 1,039,080 KiB. No build/test/scratch/Git activity.
- Fresh reviewer /root/r37_inventory_review confirmed both authors STOPPED, returned the bounded PASS receipt read-only, and STOPPED. No checker/build/test/Git/scratch/environment/worktree activity.
- R47 exact write leases are resolved by this outcome; no descendant or quarantined path was reclaimed.

## Verification limits and remaining parent work

The Lean results characterize the checked finite observations; they do not prove source extraction completeness, reverse-search completeness, allocation success or that a concrete running query returns a certificate. The reviewer notes no cross-generation ABA theorem. Runtime execution and rollback injection were not performed.

Provider arrival, Catch selection, residual subtraction, original A/B and hygiene claims, whole-language soundness, principality, termination and production remain OPEN. R47 closes only its owning-record join milestone.

No build, Rust test, Cargo, Lake, scratch, cache, target, worktree or environment was created or run for this sprint. Static agent-state check passed; it is not proof or independent review.

## Frozen artifact identities

| Artifact | SHA-256 |
|---|---|
| Rust source: candidate_context.rs | 184f09e91221f8ae0969d1dbc792b7707ef5571ff56d96e276467641215bf32e |
| Rust source: candidate_receiver.rs | 1426526cad48d4bc02984e0a5967e30e50cd188cb01fbeb71bc6f15442e59448 |
| Rust handoff | 6a8e7c60a6bf45733524b457c8cffb43d4ebae5101bb8a526fd9ca0f60a1f8de |
| Lean module | d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c |
| Proof handoff | ce27378fe9dbc6c25ede25869a238bbf59af14ffe9a64202d3aeb520947a08e1 |
| Independent review | 2f2fc7568b67058cd1e3aac50635206687a9c5bfcaf3a4d36065aab01287bc40 |

