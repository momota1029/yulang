# Sprint contract — MODULE-SUPPLIER-NATIVE-SLICES-PAGEPACK-REVIEW/r2

Status: **ACTIVE; read-only package review only.** Baseline `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. No source/proof semantic lane is authorized.

## Goal and boundaries

Fresh nonauthor review of the corrected r2 immutable page package after r1 review rejection. Determine whether the named admitted source slices and consumer are safe for a later bounded producer grant. The prior unreviewed r2 page attempt and all r1 artifacts remain preserved and are excluded from this review. Do not infer source semantics or close supplier, source/native, parent, or production gates. Preserve `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE`, UNKNOWN reservations and quarantines.

## Exact pins

- Governing r1 source-slice contract `tasks/agent-loop/sprints/module-supplier-native-slices-20261028-r1.md`: `6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435`.
- r2 preparation receipt `tasks/agent-loop/history/module-supplier-native-slices-r2-page-preparation.md`: `d1f06be5a996170d7d07086e42d85df7c7b2a30c842fe60f3297c8a4a35b8ed6`.
- r2 page manifest `tasks/agent-loop/sprints/module-supplier-native-slices-r2-pages/manifest.json`: `4c5db2314c74ac5f42a81ef05eda17be4524de970f90baaf4a6ba842669676fe`.
- r2 generator `tasks/agent-loop/sprints/module-supplier-native-slices-r2-pagegen.py`: `9e555f3f83d9f7153ad1972dbd5e8f66e951317fb41e0ae78da49f4dffc27d4a`.
- r2 consumer `tasks/agent-loop/sprints/module-supplier-native-slices-r2-pagecat.py`: `41a350c97634b2025d8b4dcd98643e9c3938a720e2acbc57089f43fcbf2c0ff0`.
- Four owner SHA pins are recorded in the manifest; independently authenticate each.

Review output: `tasks/agent-loop/inbox/module-supplier-native-slices-r2-page-pack-review.md`.

## Review procedure

Independently authenticate all five pins above and the four owners. Verify all 18 page hashes, headers, body/emitted lengths, owner pins, byte offsets, line spans and continuation. Reconstruct each declared range from original pinned bytes and pages; prove no gaps, overlaps, duplication or substitution. Confirm named complete functions/closed arm/declarations have complete exact boundaries. Ensure `lib.rs` ranges at 1054–1108, 1400–1478 and 19179–19187 are explicitly context fragments only. Verify `instantiate_candidate_graph` includes its closing brace and `definition_use` includes full declaration. Inspect generator for all-pin/range/overlap/cap validation before staging, staging validation before atomic publication, and fail-closed handling. Inspect consumer path selection, manifest-page membership, hash/size/header checks before output, and output cap. Execute the prescribed consumer with >=8192 output tokens on the largest page and record exact returned bytes/hash/ending.

Read only declared slices, immutable page files and generation/consumer scripts. No semantic source facts or supplier conclusions. No edits, tests, builds, Cargo, Lean/Lake, Git, descendants or background work. If an unexpected failure prevents complete adjudication, STOP and report exact coverage.

## Budget and gates

Fresh review **150 seconds**, primary adjudication/record **50 seconds**. Charge full **300 seconds** for preparation100 + review150 + primary50. Prior ledger **5,150/7,200 seconds**; full disposition **5,450/7,200**, leaving **1,750 seconds**. No contingency and no producer grant. A pass only makes the page pack eligible for a later selector decision and a separate bounded semantic grant. All research gates remain OPEN.
