# R29 Rust implementation handoff — frozen source-only candidate

Sprint/contract: `EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R29`, revision 1, SHA-256 `8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f`.
Assignment: Rust implementation lane, registered Luna/high implementer request. Observed model/effort metadata: UNKNOWN. No runtime routing metadata was available to this worker.
Baseline: admitted W archive from baseline commit `dd3d5ee22b8622f22e8db87382edaec0a466e7fd`; byte verification and four named overlays are pinned by inputs manifest SHA-256 `8022d3e6462012f4a8bbf3124d6c286683976f259fe8b5bd084dfaf8ac4cf83f`.

## Frozen candidate and owner map

- `isolated/ep-native-callback-grant-r29/project/tools/inference-playground/src/runtime/machine.rs` — SHA-256 `b50efa79045fbe00529cc72efbc0bff78552b2febecbcacc967a7c4d26bb3ed0`.
- `isolated/ep-native-callback-grant-r29/project/tools/inference-playground/src/runtime/receiving.rs` — SHA-256 `1c650336b2cf5834c94be8fb75a4a09eadc4b5a838500eb57b0d39aa6ee69a48`.
- `isolated/ep-native-callback-grant-r29/project/receipts/r29-source-mutation-design.md` — SHA-256 `2397e7c5cc1b10cc418cca5b22dcff6588541805d728ce2a14d0e75783ef553b`; source-only design receipt, not execution evidence.
- Fixed schema: `tasks/agent-loop/sprints/effect-permission-native-callback-grant-20261030-r29-schema-r1.json`, SHA-256 `b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379`.

Native owner path: `Receiving::observe` assigns the ordinal and constructor-time bound; the bound field and initializer are now `cfg(test)`. `Machine::propagate_request` selects the actual live Catch frame, validates its `HandlerInstallation`, and evaluates local Grant on the request-owned observation vector. The exact result is passed to test-only evidence. `RequestConsumerEvidence` independently retains that request vector. Receiving joins the selected observation tuple against this snapshot and the execution table, reconstructs local Grant from the snapshot, and keeps callback entry, direct Name receipt, typed callback use, result receipt, and execution occurrence distinct. Catch JSON now uses the selected `HandlerInstallation.occurrence` for `handler_id`; the Catch source site stays in `handler_source_site`, and installation owner/selected arm are checked against separately retained source evidence.

The selected-main assertions remain callback `1` and companion `23`. No source fixture, inference/solver/HIR behavior, schema, expected output, dependency or lockfile was changed. The companion owner/template/frame/write request checks remain on their R28 seed path, separate from callback Grant evidence. No Lean correspondence is claimed by this Rust handoff.

## Changed-target mutation plan and receipts

The focused test is renamed to the exact R29 gate name and contains seven callback mutations: wrong dynamic installation identity; altered request-snapshot construction bound; wrong invocation owner; wrong formal/receipt; wrong typed use/result view; wrong event/origin; wrong resolved effect identity. It retains seven companion mutations: wrong positive node, missing boundary, borrowed/fresh disposition, disconnected write lineage, changed no-op target guard, wrong request occurrence, and dropped replay boundary. Every case passes through `rejected_mutation`, which requires target-present, before/after difference and validator rejection before creating the runtime receipt row.

Only the design/source receipt exists at this freeze. No target was executed and no `owner-certificate.json` runtime mutation receipt exists yet. The altered bound is chosen as `observer + 2` and the harness requires it to remain plausible under the old `bound <= next_observer` check, so its rejection depends on exact snapshot equality.

## Checks, budget and stop

Read-only evidence: contract, README, sprint rules/skill, fixed schema/inputs, effect-policy design, original source-preservation theorem, R28 Rust seed, R28 handoff and exact-hash independent R28 source review. Rejected R28 defects were the source-occurrence Catch ID, duplicated-evidence observation check, production `Observation` storage change, and missing mutations; all were treated as defects, not accepted evidence.

No Cargo, rustc, tests, runtime/compiler command or source checker ran. No compilation, JSON schema conformance, actual mutation receipt, selected-main result, or source/native theorem is claimed. Exact author active seconds were not instrumented; work remains bounded by the 1,200-second author cap, with zero Cargo seconds of the 360-second allowance used. No new scratch path was created; the only new path is the source mutation design receipt above. `project/build-target/` was not written.

Status: candidate frozen; writes stopped. Compilation remains blocked pending a fresh independent exact-hash Rust/schema source ACCEPT and a separate Luna stage receipt. After both, the already bounded next step is the one-job locked/offline library compile, focused R29 certificate/mutation test, then callback and companion selected-main routes, within the 360-second Cargo cap and one-heavy-process rule. Stop on any failed source review, compile/runtime mismatch, absent/no-op mutation, changed output, production-layout difference, or need for another path.
