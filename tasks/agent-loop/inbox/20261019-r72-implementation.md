# R72 Luna source-owner handoff — revision 1 (frozen for independent review)

Sprint/contract: `third-owner-prefix-20261019-r72`, revision 2, SHA-256 `7a5d49d2c5eb05f839020f89debedd440e9909658cdff676ef8be0b6e9f29883`.
Baseline: `4916ef65306af1acec50df4cdab1d28f9ab0fa9f`; 27 direct pins matched at activation and were rechecked by the proof worker at its start receipt.
Owner: `/root`, Luna/high, session `current-conversation-2026-10-19-r72-preparation`.
Exact outputs: `notes/progress/2026-10-19-r72-third-owner-prefix-owners.md`; this handoff.

## Fixed path and current correspondence

Contract source is the single annotated recursive `helper(y:[io] int) = loop y` case nested in `loop(x:[io] int)`, with sibling `direct = loop x`, use `helper x`, and outer `loop q`. Full source and outcome contract remain in the pinned sprint file.

Static owner chain:

1. `local_source.rs` lowers named formals to Lambda/Parameter identities, Apply tails to callee/argument nodes, and Names via lexical resolution; `source_annotation.rs` resolves source effect declarations and annotation rows.
2. `CandidateInference::solve` selects ordinary candidate mode `(false,false)`. `candidate_source.rs` builds formal registrations, initializer/install levels and actions for formal computation Names, recursive active-initializer Links, installed Local uses, and Apply endpoint records. `shadow_apply.rs` authenticates/admit candidate Apply facts. `candidate_call.rs` owns the retained formal/Apply record schema.
3. `term.rs` owns Function endpoint children; `candidate_value_graph.rs` builds resolved-Name source SCCs and qualifies events; `candidate_scheme.rs` owns default ordinary fresh-use remap and local capture/routing.
4. `candidate_intrusion.rs` owns occurrence-scoped parent retention, PairGroup construction and representative merge. `lib.rs` owns the two candidate extrusion dispatch sites. `candidate_extrusion.rs` owns `Work::Bound`, physical slot readback and copied-bound/evidence transfer.
5. The authentic consumer/provider lineage is not established by those candidate records alone and remains a required proof step.

The map explicitly separates candidate action execution, candidate production-owner dispatch, and source-level reachability. It does not claim the exact input was admitted, a group activated, a merge happened, or a later copy reached the consumer.

## Preliminary proof-lane message and status

The proof worker's interim static finding: `e_direct=(direct,loop)` is unqualified; `e_helper=(helper,loop)` and `e_use=(loop,helper)` are qualified; outer call is unqualified. Its first annotated-helper negative Function is reported with children `Y+`, `n_y+`, `C_h−`, `U_h−`, with `n_y` as the exact FormalNameEffect endpoint. The first group has exactly four parents `Y+`, `n_y+`, `C_h−`, `U_h−`, all originally level 3 to target level 2, and one selected `Work::Bound` copies `K=(Y,+,Int+)`. Formal entry `t_y3` is absent because equal-level `t_y↔n_y` stores two negative-side bounds, not a positive row bound on `n_y`. Settlement merges each fresh copy to its original parent and lowers originals. Third-owner `K_t=(t_y,−,n_y)` at `EffectUpperRow` index 0 retains raw item `n_y`; `(n_y,−,copy(n_y,+))` is owned by the merged class, not a third owner. Worker is tracing whether Local/Lambda admission or later capture adds a copy. This exact-prefix exclusion is interim and not a completed A/B/C result.

Later proof-lane audit reports helper `RE` is born at current `Y=2`, while original entry `t_y` stays 3; helper Local boundary 2 freshens `t_y` and shares `n_y`, `U`, `RE` at level 2. FreshUse restoration alone is not a production `Work::Bound`. The remaining seam is Local restoration/replay → loop Lambda replay against both prior demands → loop Local boundary 1, including memo recapture and independent consumer-fiber need.

Outcome remains **OPEN / UNFINISHED**. In particular, the identified initial third-owner slot is not yet joined to a qualified alias-changing merge covering that owner, a later production Work::Bound lookup/copy of it, or independently justified consumer lineage. Do not infer B/C from this unfinished reachability derivation.

## Implementation decision

**NO_SAFE_CODE_SLICE.** I inspected `shadow_apply.rs`, `candidate_extrusion.rs`, `candidate_intrusion.rs`, and source/call owners. These show conditional candidate handling and exact-key evidence movement; the unresolved question is joint source reachability and consumer correspondence. No proof-independent bug or authorized code repair follows from the static owner map. Compiler, test, expected-output, and semantic changes are outside this lease.

## Checks, resources, and next action

- No tests, builds, probes, parser/solver execution, measurements, instrumentation, or code changes ran.
- Source reads and static line-owner mapping only. `git diff --check` and static sprint check remain for final integration; they are not compiler tests.
- R72 owner-map allocation is 500s and the proof grant is 600s, both fully charged by the sprint grant. Proof completion/stop receipt was received; proof and Luna outputs are frozen for independent review.
- Next in-scope step: fresh independent compiler/source and spec reviews of the frozen six-output packet; then Luna adjudicates whether to close this bounded attempt unresolved and route `R72-LATER-OCCURRENCE-1`.
- Parent computation-forwarding theorem and Simple-sub A/B remain OPEN 0→0. R50 remains NOT_ADOPTED. R70/R71 results remain conditional and their open targets are not discharged here.

## Pins, artifact hashes, and freeze receipt

The contract SHA and 27-item source manifest are frozen in the sprint contract; all 27 baseline Git blobs and live bytes MATCH at Luna verification. Luna outputs are frozen for independent review. Their final SHA-256 values are stored in `tasks/agent-loop/current.json` with the freeze receipt.

Proof outputs: theory `504abc36cd877407b57b744484640c3fb2f8e12d09f08bfe90188dc700ee18a5`; inbox `8e30e80a5e382fe6e3a88a65933ac5eb787e5b7773bae72657f3eb2348668401`. Static sprint check and `git diff --check` pass; these are static/tooling checks, not compiler evidence.
