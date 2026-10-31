# R127 admission — reviewed Rust patch composition candidate

At the R126 close boundary, the read-only selector recommended a source-candidate composition as the closest safe step toward the user's Rust implementation goal. R126's conditional outcome remains unchanged. The parent soundness/effect-hygiene goal and all quantifiers remain open.

## Admission decision

Admit `EFFECT-PERMISSION-INTEGRATION-CANDIDATE/20261102-R127` for exact in-memory composition of the R111 three-file compile-repair target with the R117 and R119 receiver patches, followed by a source-to-proof-premise audit. The result can establish complete candidate bytes or an exact composition conflict. It is not source integration, compilation or production evidence.

R111 rev3 remains the controlling source gate: no source materialization or compiler call until fresh independent review and Luna's storage gate pass. Its private aggregate 6 GiB namespace was unavailable, no configured remote verifier was found, and its single Cargo allowance is still unused. R111 explicitly bars repeating environment experiments or reconstructing its standalone candidate without a resource/policy change. R127 reuses its already reviewed immutable target and only attempts the new R117/R119 composition in process memory; it does not repeat those experiments or claim R111's execution gate passed. If the authorized unique-context composition cannot be established, stop without a candidate.

## Frozen pins and assignments

- Contract: `tasks/agent-loop/sprints/effect-permission-integration-candidate-20261102-r127.md`, SHA-256 `aa6cb58fb8c728ff021a87b9e86ea9ce2251142bee283928816e97848317996a`.
- Manifest: `tasks/agent-loop/sprints/effect-permission-integration-candidate-20261102-r127-inputs-r1.json`, SHA-256 `04566bb0f82e2d34bf4f6e843aa0534c193d37f1a87326066c298e2cabec9cce`.
- Current baseline: `b5f4df2509ad9c8dba311a6139354bc3f7d33404`; R111 source baseline: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. Luna verified identical base blobs for all three target files.
- R111 rev3 contract SHA `d1461c3204bacf59783d918e2c6ebc6ec1776693ecf814ed5d31dda938597976`; rev3 handoff SHA `54a79a1b4f49d75b78bd3c3e96ff2c317941c57e24dfbad6e2c441309f131d9d`; outcome SHA `a0ed59f783f4b1b06504a66aa3c6e7bf55039a8038352860434de760d75e26a0`.
- R117/R119/R120 patches, source/proof/review records and outcomes are individually hashed in the manifest. R120's already reviewed receiver result is `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470`; R127 must derive the combined target rather than assume that hash survives R111 repairs.
- Implementation handoff only: `tasks/agent-loop/inbox/effect-permission-integration-candidate-r127-implementation.md`, 300s cap. Registered `lean_prover` proof handoff only: `tasks/agent-loop/inbox/effect-permission-integration-candidate-r127-proof.md`, 300s cap. Both may work in parallel on their independent inputs; the proof lane waits for the exact implementation target before asserting target-specific properties.
- Fresh compiler referee after both freeze: 180s. Primary integration: 240s. Total ≤1,020s; Astra 0.

No code edits, tests, builds/compiler, Lean/checker, patch application to files, scratch/cache/copy/worktree, environment/storage probe, dirty/quarantined read, Git mutation or source push is authorized. Luna owns any later R111 resource admission and source integration decision. A reviewed handoff may be pushed only as a research candidate; it is not an uncompiled Rust implementation.
