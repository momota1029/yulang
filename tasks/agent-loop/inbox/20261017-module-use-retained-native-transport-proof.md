# Module retained native transport proof handoff

Sprint-ID / contract revision / SHA-256: `module-use-retained-native-transport-20261017` / 2 / `b193043d56e60af7bfea4f8de7310a1230ae39546df70455bc4fa4b788184604`.

Assignment-ID / handoff revision: `MODULE-USE-RETAINED-NATIVE-TRANSPORT-PROOF-20261017` / **2 (Luna equation correction)**.

Parent: original Yulang inference/execution theorem; unchanged A/B claims, quantifiers and source domain. Application only to native field-map readiness contract sections 2/5 remap-retention prerequisite. Original theorem conditions closed: **0**.

Baseline: sprint `9f8a03bdf`; frozen repaired implementation `candidate_scheme.rs` SHA-256 `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494`; implementation handoff revision3 `7537cd9744d77ca2d100b7996237daaa858123ae0f84c2ded35d00eacfd12a28`. All contract input pins and launch pins matched; full direct source/dependency pins in proof section6.

Role / worker / receipt: prover `/root/module_freshuse_retention_proof`, current session, actual assignment received after implementation STOP and Luna PASS check receipts. Requested Sol/high; observed effective model/effort UNKNOWN. Sole proof author; no descendants. Implementation author remains `/root/module_freshuse_retention_implementation`; this proof does not independently certify that implementation.

Outcome class: **candidate source-native evidence/proof**, awaiting independent review. The actual module helper returns the exact constructed FreshUse. Its move split retains rows plus every non-row field and all three nested scope maps with the exact Graph and actual module use ID. Capacity identity `FreshUse.bytes = row_capacity_bytes + retained_maps.bytes` and the checked transfer of captured Graph bytes plus FreshUse bytes (`G+F`) leave the caller scratch unchanged and count each moved capacity once. Owner recount enumerates each surviving map payload once and charges inline headers/scalar through route-vector capacity. Capacity units exclude unmeasured allocator overhead and physical peaks.

Lifecycle qualification: route-vector ownership persists until route removal or GraphState drop. Transaction rollback truncates appended route entries and drops Graph/rows/maps, then recounts surviving owners; vector capacity can remain allocated. Successful session finalization moves GraphState into FrozenInferenceData and CandidateSolvedResult, so session consumption can transfer ownership rather than drop it. Dropping the final GraphState owner drops the routes. Referenced native IDs require their own valid live-owner/read-version premises; retaining the crosswalk supplies no historical snapshot or validity protocol.

Failure boundary: before push, error drops private local Graph/maps and publishes no route. Push remains tentative through final sample; transaction error rolls back its suffix. Failed rollback propagates availability failure and grants no permission to continue an inconsistent attempt. No full capacity restoration or scope inventory reclamation theorem. Compatibility `freshen_candidate_graph -> (Term,Vec<RowKey>)` and projection/drop behavior are retained; retained helper is module-private.

Actual path: route_incoming transaction -> candidate graph recapture -> prepare_candidate_fresh_use -> actual ordered bound restoration -> retained FreshUse -> capacity precharge -> existing route admission/constraint propagation -> FreshRoute move -> transaction commit; error -> existing rollback/truncate/recount. No new consumer, classifier or source certificate.

Artifact frozen for review:
`notes/theory/2026-10-17-module-use-retained-native-transport.md`
SHA-256 `11fb8ad1dd099f998acc7d4ac72d61c79cec9ce8879a53cd7174741ab53cae3b`.

Reused: local retained record/split and direct-map versus dereferenced-value distinction under actual premises. Rejected: local source semantics as module semantics, native rows as source field classes, retained evidence as EventProof, implicit Published/Mono choice, full Phi_u or parent closure.

Checks: Luna reran `cargo check -p yu-solver --features shadow-apply-candidate --tests` after the accounting repair (PASS, 3.26s) and the focused test `module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting` (PASS, 1/1, 8.71s). The test executes the cfg(test) scratch equality assertion immediately before the prepublication resource sample. `git diff --check` PASS on the corrected proof/handoff integration. These checks do not cover failed-transaction capacity behavior beyond the source argument.

Remaining premise / owner: HINTRO-OWNER-u_id requires authentic source-handle introduction from actual source rule/publication environment. MODULE-NATIVE-FIELD-MAP additionally requires source Sig/field producer/ownership, allocation classes and all witness/operand incidences. No total Phi_u, root/Call, F1/FK1, N-Transport, soundness, principality or termination conclusion.

Mutual TODO `MODULE-RETAINED-MAP-INTAKE-20261017`: Luna obtains independent reviews of frozen code+proof. Falsifier: discarded FreshUse field, mismatched move capacity, missing route owner, or failed transaction retaining an appended successful route. Next semantic task remains authentic HINTRO-OWNER-u_id; no new lease or semantic choice requested by this proof.

Revision 2 corrects the equation from the actual post-capture scratch entry: S caller scratch, G captured Graph bytes, F=R+M FreshUse bytes, E=S+G at retained-helper entry, and `(E+F)-(G+F)=S` after the checked transfer. The code reviewer found the previous formula left G in scratch while also adding G to retained bytes. Luna applied this proof-only correction after the implementation author and initial proof author STOPPED. The initial proof author remains STOPPED; the two proof paths are frozen for fresh independent review. Original theorem conditions remain 0.
