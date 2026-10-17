# Module retained native transport proof handoff

Sprint-ID / contract revision / SHA-256: `module-use-retained-native-transport-20261017` / 1 / `1cdbd0706203b0d34c13aa0f7e7342e3413dbc3fbd90b40e335b294bdbe820c2`.

Assignment-ID / handoff revision: `MODULE-USE-RETAINED-NATIVE-TRANSPORT-PROOF-20261017` / **1**.

Parent: original Yulang inference/execution theorem; unchanged A/B claims, quantifiers and source domain. Application only to native field-map readiness contract sections 2/5 remap-retention prerequisite. Original theorem conditions closed: **0**.

Baseline: sprint `9f8a03bdf`; frozen repaired implementation `candidate_scheme.rs` SHA-256 `2c334b62c61285954a6dfdb6639f81016fabb045ab0df6414ba03b86ab8e7407`; implementation handoff revision2 `cee5c9770483b41c1660b7ede3448e2865a87a8802368ed8c14a88ba21ae1790`. All contract input pins and launch pins matched; full direct source/dependency pins in proof section6.

Role / worker / receipt: prover `/root/module_freshuse_retention_proof`, current session, actual assignment received after implementation STOP and Luna PASS check receipts. Requested Sol/high; observed effective model/effort UNKNOWN. Sole proof author; no descendants. Implementation author remains `/root/module_freshuse_retention_implementation`; this proof does not independently certify that implementation.

Outcome class: **candidate source-native evidence/proof**, awaiting independent review. The actual module helper returns the exact constructed FreshUse. Its move split retains rows plus every non-row field and all three nested scope maps with the exact Graph and actual module use ID. Capacity identity `FreshUse.bytes = row_capacity_bytes + retained_maps.bytes` gives checked scratch-to-retained transfer with no payload counted twice. Owner recount enumerates each surviving map payload once and charges inline headers/scalar through route-vector capacity. Capacity units exclude unmeasured allocator overhead and physical peaks.

Lifecycle qualification: route-vector ownership persists until route removal or GraphState drop. Transaction rollback truncates appended route entries and drops Graph/rows/maps, then recounts surviving owners; vector capacity can remain allocated. Successful session finalization moves GraphState into FrozenInferenceData and CandidateSolvedResult, so session consumption can transfer ownership rather than drop it. Dropping the final GraphState owner drops the routes. Referenced native IDs require their own valid live-owner/read-version premises; retaining the crosswalk supplies no historical snapshot or validity protocol.

Failure boundary: before push, error drops private local Graph/maps and publishes no route. Push remains tentative through final sample; transaction error rolls back its suffix. Failed rollback propagates availability failure and grants no permission to continue an inconsistent attempt. No full capacity restoration or scope inventory reclamation theorem. Compatibility `freshen_candidate_graph -> (Term,Vec<RowKey>)` and projection/drop behavior are retained; retained helper is module-private.

Actual path: route_incoming transaction -> candidate graph recapture -> prepare_candidate_fresh_use -> actual ordered bound restoration -> retained FreshUse -> capacity precharge -> existing route admission/constraint propagation -> FreshRoute move -> transaction commit; error -> existing rollback/truncate/recount. No new consumer, classifier or source certificate.

Artifact frozen for review:
`notes/theory/2026-10-17-module-use-retained-native-transport.md`
SHA-256 `fa8c54fd83e43b6a98f148ac0f8c8240fa5a530679291d061cd3488614f753e2`.

Reused: local retained record/split and direct-map versus dereferenced-value distinction under actual premises. Rejected: local source semantics as module semantics, native rows as source field classes, retained evidence as EventProof, implicit Published/Mono choice, full Phi_u or parent closure.

Checks: this author only inspected exact source/authority and SHA-256 pins. Luna supplied cargo check PASS, focused `module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting` PASS1/1, diff whitespace check PASS on repaired freeze. No tests/builds/probes/Git by this author. Budget ≤300s; exact active telemetry unavailable, conservatively charge300s. No scratch files.

Remaining premise / owner: HINTRO-OWNER-u_id requires authentic source-handle introduction from actual source rule/publication environment. MODULE-NATIVE-FIELD-MAP additionally requires source Sig/field producer/ownership, allocation classes and all witness/operand incidences. No total Phi_u, root/Call, F1/FK1, N-Transport, soundness, principality or termination conclusion.

Mutual TODO `MODULE-RETAINED-MAP-INTAKE-20261017`: Luna obtains independent reviews of frozen code+proof. Falsifier: discarded FreshUse field, mismatched move capacity, missing route owner, or failed transaction retaining an appended successful route. Next semantic task remains authentic HINTRO-OWNER-u_id; no new lease or semantic choice requested by this proof.

Exact/all written paths: proof artifact above and this handoff only. **STOP: writes ceased after revision1 freeze; no descendants or outstanding generated outputs.** Commit-ready only as unpromoted research evidence pending Luna review/adjudication.
