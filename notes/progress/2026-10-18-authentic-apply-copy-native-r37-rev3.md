# R37 revision 3 native identity relation

## Outcome and parent application

The test-only join now carries capture-time `requested` and stored `representative` separately from reconstruction-time `captured` and current `source_representative`. For every row, the retained `Capture` owns the request-to-stored-row edge; the route-owned reconstruction observation must capture that stored row and records its current representative. The helper checks the current representative against the indexed retained C/D Parent copy/parent, without requiring the historical stored representative to equal the present representative. Each route's image remains independently checked.

For `canonical_rows_hit`, the helper requires the retained `existing_image` to equal the route image, a strictly earlier first-entry row to own that same image, and (when the image differs from the current source representative) that first row to record fresh allocation. A hit itself is not fresh allocation. Non-hit/nonallocated rows still require representative reuse. Downstream assertions now preserve the same distinction and accept a retained prior fresh image. The exact indexed Parent, forged-parent rejection, nonvacuous missing-event control, structural trigger comparison, exact signed C/D parent/polarity coordinates, and both actual helper routes remain in the candidate.

This is native test evidence only. The source/proof result remains the bounded obstruction report: ordinary Call result description, complete ordered telescope and typed `NativeInterface.result` correspondence are missing; `TypedPortRef(R)`, `CopyScope(C/D)` and typed publication remain unconstructed. Parent theorem conditions remain `0 -> 0`; no semantic adoption or production promotion follows.

## Source/native correspondence and reused evidence

Inspected `GraphBuilder::row` in `candidate_scheme.rs`: it records both the requested key and its representative at capture time, while storing that representative in `Graph.rows`. Inspected `prepare_candidate_fresh_use`: it records the captured row, then-current intrusion representative, map-hit flag, `existing_image`, first-entry graph row, fresh-allocation flag and final route image. The revised predicate composes these owner records with `state.intrusion.parents[parent_index]`, rather than treating current canonical identity as capture-time identity.

Reused rev2's indexed Parent authentication, actual `loop y` Apply and checking event, exact active trigger comparison, C/D rows and two `FreshUse` routes, forged-copy rejection, and nonvacuous missing-event control. Rejected the rev2 capture/current equality assertions and final nonfresh-image-equals-source assertion identified in the frozen review receipt. No source expectation, diagnostic, semantic rule, production code, or integration test changed. No Simple-sub bypass was restored.

## Frozen artifacts, checks and boundary

- Contract SHA-256: `b19c4131f79476f787b8ef424e46f38a396598234dab5400215025938bd0d250`.
- Candidate `crates/yu-solver/src/candidate_scheme.rs`: SHA-256 `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e`.
- Production prefix remains 119639 bytes / SHA-256 `bc809becb6dc89149e2d00057f1d65b879121668f5485fef9d6a493d64f08a18`.
- Integration test was not changed; SHA-256 `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55`.
- `git diff --check -- crates/yu-solver/src/candidate_scheme.rs` passed. No Cargo, build, test or probe ran. No generated or scratch path was created.
- Fresh compiler/spec delta reviews have not run; focused Cargo is still gated on both clean reviews and Luna's separate launch receipt. The actual lawful prior-fresh-image fixture incidence is not claimed without execution. The output remains provisional pending independent reviews and gated execution.

Assignment: `/root/r37_native_repair_r3`, requested Luna/high, observed model/effort UNKNOWN/UNKNOWN; no descendants. Grant 240 seconds; full 240 seconds charged (bounded assignment receipt; exact active elapsed unavailable). Writes stopped after freezing this candidate, progress note and handoff. Luna owns independent review, adjudication, launch receipt, and integration.
