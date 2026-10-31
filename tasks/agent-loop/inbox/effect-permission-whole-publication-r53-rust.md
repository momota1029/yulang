# R53 Rust handoff — whole-publication residual observation

Sprint / contract: `EFFECT-PERMISSION-WHOLE-PUBLICATION/20261031-R53`, revision 1, SHA-256 `78321147638d3847c1073c6c24a7050a068c4a5142cc7c8e8206232c6ea4926e`.
Amendment acknowledged: `tasks/agent-loop/sprints/effect-permission-whole-publication-20261031-r53-amendment-01.md`, SHA-256 `b1cad22e75c360ae8b217b9671cf52f066afab916ef67435117733f0e4b46636` (corrects only the R52 contract digest).
Assignment / worker: R53 Rust author, actual worker `/root/r52_rust`, active continuation session; current row RUNNING was confirmed by Luna.
Requested / observed model and effort: Luna/high / UNKNOWN.
Baseline: admitted integrated R53 base `21d95ed3f2ffefb6dbbfdfb2872804a00abb96cd`; contract code baseline `fe5c872e5722f5a2a56ac99ab4f08eabed2e9f3d`.

## Outcome

Candidate source/native evidence. `ReceivingResidualExperiment` now retains one `WholePublicationObservation` rather than a disconnected call-vector plus identity. The observation owns the unique publication identity, relay and answer owners, Catch and edge-scrutinee occurrences, original `ConstraintOccurrence`, upper/result row, complete ordered `CompleteResidualPlan` including authenticated Suppress decisions, ordered per-call R52 records for Forward decisions, initial lower-row/lower-atom snapshots, and final lower-row/lower-atom snapshots.

Before forwarding, the optional observer captures the exact initial row vectors with fallible capacity reservation. After each actual `constrain_live_effect` return, existing R52 logic records that call's identity and original plan index, exact task/fact/cause, origin/completion/emission cuts and ends, completion, slot state, drain, and physical bound evidence. Whole-publication capture then checks original fact/catch coordinates, plan-to-terminal order, exact Forward-only call projection and identity/index order, absence of calls at Suppress positions, monotone cut composition, unchanged initial prefixes, and a final suffix whose ordered entries correspond exactly to `NewlyEmitted` evidence. `AlreadyPresent` calls add no suffix entry. Any unavailable record, identity, snapshot, final read, or failed check leaves the whole observation unavailable; it does not change an otherwise successful forwarding result.

No write was needed in `candidate_context.rs`: its existing R52 read-only producer accessors supply the completion and physical-emission evidence. This remains private research evidence with no permission consumer or production cutover.

## Source/native correspondence and evidence reused

- Source constructor/owner: `assemble` retains relay/answer roots, Catch and selected edge-scrutinee occurrences, provider and selected-arm evidence. `execute_receiving_assembly` selects the original fact at `edge_scrutinee` local slot 51, validates the unique module use, and builds a canonicalized, deduplicated terminal inventory.
- Plan/propagation: `complete_residual_plan` turns that inventory into the full indexed decision plan. Suppress decisions retain authenticated provider-entry evidence. In original order, only Forward decisions invoke `constrain_live_effect(endpoint, pending.upper, fact.id, fact.cause)`.
- Native result: the R52 call bridge uses `candidate_context` origin, drain-completion, admission, emission and physical-readback records around each individual call. The new whole view preserves the pre-call lower-row/atom vectors and verifies the final vectors against the exact ordered New-emission suffix.
- Reused evidence: R52 Rust source and handoff, accepted R52 per-call review, R52 Lean model, R51 frame/call predicates, and R50 complete indexed plan model, all with the hashes in the frozen R53 contract (including the corrected R52 contract digest in amendment 01). R52's accepted Audit 6 byte receipt was not rerun.
- Rejected substitute: no publication-wide cut and no post-hoc search by equal endpoint, occurrence, task or cause selects a call. A call is matched by retained publication identity and original plan index, then its other fields are checked.

## Frozen outputs and checks

- `crates/yu-solver/src/candidate_receiver.rs` SHA-256 `c13aa8543fcf5acb281951badd2edaddfc954c2697d14b701aab337f6b3490fd`.
- `crates/yu-solver/src/candidate_context.rs` unchanged, pinned SHA-256 `c9deb23ebb2b7762f6404c6529231f3581e9959082ee301e03eb1c0895d111eb`.
- Read-only `crates/yu-solver/src/lib.rs` unchanged, pinned SHA-256 `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- Contract and amendment hashes as above. R52 Rust handoff `2183c859ec7b1ce8b75aaf0b93efe4af1c9fdc8012b162833079af03ba8d7cf3`; R52 proof handoff `da53deb52aed9447c61ef46fb27288cc53e569167221ade7bae5a77d6e58ea6a`; R52 review `b11d7b3151fd6d3cd718848875203e54c0d5d751955db7a8ecf465211d054ae0`; R52 outcome `68f0cf47a3e4635a07d6cd39006458260496d91decc355ab0a9b392d665727dd`.
- `git diff --check -- crates/yu-solver/src/candidate_receiver.rs crates/yu-solver/src/candidate_context.rs` passed. Source inspection only; no tests, build, compiler, Cargo, Lake, formatter, cache, scratch output, worktree or environment was used.
- Approximate active wall time: 21 minutes; within the 1,500-second assignment limit. No descendants or generated paths.

## Limits and remaining premises

The Lean lane is still constructing/auditing the R53 whole-publication theorem. Its author reports that relay/answer/current-state extraction into the same R50 context remains an explicit source premise; this record alone does not discharge that premise. Fresh independent R53 review is pending. No Rust compilation/runtime evidence was authorized or obtained, and this handoff does not close the original Simple-sub A/B claims, `SourceProblem.InferenceSoundness`, soundness, principality, termination, full effect hygiene, or production authority.

TODO R53-RUST-PROOF-01: parent R51/R52 whole-publication source bridge; first missing evidence is extraction of the retained original fact, owners, plan/call records and pre/post vectors into the same formal source/native context; source owner is the `candidate_receiver` observation path; proposed output is the conditional theorem application with exact premise retained; falsifier is a missing/foreign/reordered call, non-monotone cut, changed prefix or unexplained suffix.
TODO R53-RUST-REVIEW-01: independent review of these frozen bytes; attack repeated endpoints/tasks, shifted indices, Suppress/no-call, foreign identity/fact/owner, cut ordering, AlreadyPresent, changed prefixes, extra/missing/reordered suffix, and observer loss while forwarding succeeds.

Worker state: STOPPED writing; no descendant leases. This handoff is frozen at revision 1; primary owns review, adjudication, integration and Git. No commit-ready or production claim is made.
