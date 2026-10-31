# R125 outcome — same-graph PRE projection

Contract: `tasks/agent-loop/sprints/effect-permission-same-pre-20261102-r125.md`, SHA-256 `e064495d96385942c79cfacdec5ce7be6b060db7be4f820c79a1096fcc9862cb`. Baseline: `bf83716eea816536f3cc1d68b323d1567712dd38`. Frozen source and R39 inputs are pinned in the admitted manifest.

## Result

**PASS for the bounded same-graph PRE mapping and existing R39 application.** At the successful guard, `Inputs.retainedRegistrations` and `State.permissions` are both projections of the same owned, ordered `formal_entry_permissions` Vec (`map registration V0` and `map P V0`). This is a shared witness, not two equal-looking snapshots. The mapping keeps the complete native identity coordinates, preserves concrete row order and duplicates, and distinguishes physical index, registration and recipe. The local append is `map P V2 = map P V1 ++ [build …]`.

The guard's domain keys and permission Vec come from the same graph at t0 and correspond to existing R39 `Valid` and `prepare_exact`. Applying `constructed_entry_publication` to those premises is justified. The generated `State.links` remains a constraint trace; external `State.inflow` remains separate from lower storage.

## Independent review

Fresh independent compiler referee: **PASS, no blocking, major or minor findings**. Reviewer independently authenticated eleven source/theory blob hashes and both handoff hashes, then confirmed the same-Vec projection, full native identity, duplicate-preserving row copy, local append, and faithful treatment of links/inflow. No new Lean declaration or execution was used.

- Source handoff: `tasks/agent-loop/inbox/effect-permission-same-pre-r125-source.md`, SHA-256 `0fc58726d0db552c99714926533080d0238cb913f3d898f1b12430b3057e84a3`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-same-pre-r125-proof.md`, SHA-256 `23ac34427928c0f9e6a4060018391b0083de2da3c19381667950e763a9013387`.
- Source, proof and reviewer workers are STOPPED: `/root/r125_same_pre_source`, `/root/r125_same_pre_proof`, `/root/r125_same_pre_review`.

## Open boundaries and disposition

This closes the concrete PRE projection, not full symbolic publication correspondence. A successful symbolic drain still needs to establish permission preservation (`V1 = V0`); the retained direct-request trace and actual inflow interpretation also remain open. `candidate_receiver.rs` consumer-read correspondence remains a later separate gate. R111's verification-resource gate, parent soundness, full effect hygiene and production remain OPEN. Rust code integration remains **NO_SAFE_CODE_SLICE** under the current authority; no compiler source was edited.

Close R125 conditionally and continue the standing Rust/Lean goal at the next admitted bounded source/proof seam. No builds, tests, Lean/checker execution, environment/storage probes, dirty/quarantined reads or source edits occurred. `python3 tools/agent_sprint.py check` passed as static consistency only, not as proof or independent review.
