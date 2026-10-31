# Sprint EFFECT-PERMISSION-TRANSPORT-REACHABILITY-20261028/r1

Status: ADMITTED by Luna after the prior sprint closed incomplete and the selector recommended a backward slice from `effect_rep(r)` to its qualified representative write. This continues the user's unchanged inference/executor goal under the standing autonomous-continuation rule. Branch: `yulang3`; committed baseline: `bc2a0836ec`, plus the exact dirty overlay pinned below.

## Objective and semantic boundary

Find an existing representative-changing path for an effect row created by the permitted ordinary source construction, or record the exact first missing transition/guard. The prior two ordinary-source runs yielded only `r=q`; they do not prove unequal transport is unreachable. Separately repair the delegated site association: annotation-context position and nested effect-row position are distinct coordinates and must be related through their actual source occurrence/tree, not required to be numerically equal.

Preserve original quantifiers, source scope, effect-hygiene meanings, expected outputs and production semantics. Do not synthesize a representative, weaken strict assertions, reclassify an internal fixture as ordinary-source evidence, or infer impossibility from absence in a bounded search. Parent/source-native/A/B/hygiene/principality/termination/production gates remain OPEN.

Prior closed outcome: `tasks/agent-loop/history/effect-permission-canonical-export-20261028-r1-outcome.md`, SHA-256 `f3c634072dd5affadc720af11ed3b6b5ec653d370cbc34cf929520323a84bbc5`. Integrated review: `tasks/agent-loop/inbox/effect-permission-canonical-export-final-review.md`, SHA-256 `4961ea42bb3ad09579ecf0bff2899af1b2d229cb4067d86dfcbc3d9508c687d8`.

## Frozen starting overlay and source pins

The working tree is the exact prior frozen overlay plus unrelated dirty/quarantined paths; no reset/stash/clean. Rust write inputs re-leased only after prior writers STOPPED:

- `crates/yu-solver/src/candidate_effect.rs`: `75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1`
- `crates/yu-solver/src/candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`

Read-only source cone individually pinned:

- `crates/yu-solver/src/candidate_intrusion.rs`: `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `crates/yu-solver/src/candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- checked `FormalPermissionExportWitness.lean`: `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`
- conditional `FormalPermissionExportWitnessNative.lean`: `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1`

Keep all previous raw receipts, source hashes, review and outcome immutable. Scratch root: `/tmp/yulang-effect-permission-transport-reachability-20261028-r1/{rust-target,lean-project}/` only.

## Rust lane — registered implementer, Luna/high

Write leases only:

- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/effect-permission-transport-reachability-rust.md`

Read only the pinned source cone above and governing effect-hygiene/source-preservation sections cited in the prior contract. First perform a bounded backward slice: identify the exact `effect_rep(r)` lookup, the actual merge/write and its qualification guards, then trace an already existing approved source route/regression toward that guard. Record source classification and exact transition. The existing ordinary-source recursion/merged-row readback may be examined, but do not assume it selects an Effect row. An internal test that manually merges rows is not an ordinary-source witness.

Only after an authentic ordinary-source route is identified, make the smallest test-only instrumentation/assertion repair. Preserve `r` independently from the materialized graph row `q`; preserve polarity, node, capture, origin concrete metadata, wrapped owner, occurrence, nested row position, enclosing annotation occurrence/path and actual returned port. Keep annotation position and effect-row position separate and connect them via the actual source tree/site. Do not change solver behavior, public API, recovery, source preflight or expected outputs. If no guarded route is established within the source slice, stop without speculative fixture or source edits and return the precise missing transition/guard; do not call it impossible.

Up to two feature-correct Cargo invocations sharing 180 seconds, serialized. Invocation 1 only after source and fixture classification freeze; invocation 2 only after diagnosed failure and changed frozen source. Each preflight must verify exact hashes/argv, no competing cargo/rustc, >=4 GiB free memory, CPU0, one Cargo job, <=2 GiB RSS, <=180s; retain separate raw streams/status/time/input manifest/argv. Use the two selected `formal_permission_constructor_` tests and one test thread. Both slots expire if the backward slice finds no real candidate route; do not spend a build merely to probe guesses.

## Lean lane — registered lean_prover, after Rust freeze

Write leases only:

- `notes/theory/lean/YulangClosure/FormalPermissionTransportInstance.lean` (use only if an attributable native unequal-transport observation and position mapping freeze; otherwise do not create a self-supplied fixture)
- `tasks/agent-loop/inbox/effect-permission-transport-reachability-proof.md`

Keep both prior decoder modules and all audited dependencies immutable. Independently classify source vs internal fixture and audit the annotation-position/effect-row association and representative witness. If real data freezes, instantiate the existing decoder only from those observations and explicit mappings; retain exact declaration types and transitive axioms. If it does not, record the missing native premise and do not fabricate IDs/rows or run a meaningless audit. Maximum one Lean invocation, 120s, one CPU, <=1GiB RSS, isolated pinned project.

## Independent review and close

After Rust and proof artifacts freeze, a fresh non-author read-only compiler_referee verifies the exact guarded write path, source classification, full owner/capture/export/port join, nested source-site mapping, all five falsifiers, frozen hashes/raw receipts and any conditional Lean audit. No build/test/Lean rerun by reviewer. Max two producers, zero Astra. Total envelope 1,500 seconds: Rust600, proof300, review250, Luna150, selector50, contingency150. Stop at changed pins, another owner, unsupported transition, falsifier or resource/budget boundary.

At end freeze outcome and compact current without dropping UNKNOWN reservations/quarantines or unresolved pending items; run `python3 tools/agent_sprint.py check`; consult selector. Only Luna integrates/stages explicit reviewed research paths and commits/pushes after exact-range review. All attempts in prior sprint are already spent; any new invocation is governed only by this contract.
