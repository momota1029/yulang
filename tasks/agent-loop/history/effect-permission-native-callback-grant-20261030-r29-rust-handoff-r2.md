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

---

# Sequential repair addendum — revision 2

Handoff ID: `r29_rust`, revision 2. This addendum follows R1 without changing its contents. R1 is preserved verbatim at `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-rust-handoff-r1.md`, SHA-256 `509572eac5b45a720277efb9e119306a43ed7388f76d41306c80a1c2f6d5749c`. The independent R1 review remains REJECT at `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-review-r1.md`, SHA-256 `cfd65b4674402bc21a670b81468fcea78e96c5124545a035f22d22a847d0b08e`.

## Frozen R2 source candidate

- `isolated/ep-native-callback-grant-r29/project/tools/inference-playground/src/runtime/machine.rs` — SHA-256 `391210906e4d6c8e103bfb7aef357f2447a6ee5904e82b411adc807e823f7278`.
- `isolated/ep-native-callback-grant-r29/project/tools/inference-playground/src/runtime/receiving.rs` — SHA-256 `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.
- `isolated/ep-native-callback-grant-r29/project/receipts/r29-source-mutation-design.md` — SHA-256 `75a408c3cd4f0a8b95a156fb5687cf577d9a927e0a9667c3dd704d154c18c5c2`.
- Fixed schema remains SHA-256 `b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379`; inputs manifest remains SHA-256 `8022d3e6462012f4a8bbf3124d6c286683976f259fe8b5bd084dfaf8ac4cf83f`.

## R1 findings repaired in the candidate

1. **Query-time Grant:** immediately before the actual local Grant query, test-only code retains a clone of the actual invocation descriptors and a separate `(invocation_id, active)` guard snapshot. Both are request-owned fields on `RequestConsumerEvidence` and are passed as arguments separate from the candidate certificate. The validator checks the candidate query guard against both snapshots and recomputes Grant using the retained query-time invocation state. The unchanged positive route asserts the query guard is active and the post-`ReceiverReturn` live invocation is inactive; owner deactivation is retained.
2. **Selected dynamic Catch source:** after the actual `HandlerInstallation` succeeds in `validate_handler_installation`, test-only code records its occurrence, Catch source site, owner, resolved operation, selected arm and live-frame authentication in a separate `Machine.selected_catch_installations` vector. The candidate contains only an index to that vector plus emitted candidate fields. The validator receives the independent selected-source record separately and compares candidate handle, source site, authentication, owner, operation and arm against it. Serialized `handler_id` is the selected installation occurrence; source site remains a separate field.
3. **Construction-time observation snapshot:** test-only request evidence retains the request observation vector's execution tuple, ordinal, construction bound and event independently from certificate observations. The mutation changes only candidate bound and leaves the request snapshot untouched. The harness adds a genuine later observation in the same authentic `Receiving` using the selected execution. If selected observer is `n`, its original construction bound is `n+1`; the later observation receives ordinal `n+1` and advances `next_observer`/its own construction bound to `n+2`. Candidate bound is changed to `n+2`, making the former plausibility test true (`n+2 <= n+2`), while exact comparison with the untouched request snapshot rejects the candidate.

## Changed-target mutation design

The source candidate contains 11 callback mutations and 7 companion mutations. Each is routed through `rejected_mutation`, which requires a present target, changed before/after values, and validator rejection before emitting a receipt row. Callback cases cover invocation owner, formal/receipt, typed result/use, event/origin, effect identity, coordinated dynamic identity plus occurrence, coordinated owner fields, coordinated arm fields, resolved operation, request-snapshot bound, and query-time guard. The coordinated identity, owner and arm values remain internally consistent with each other; each is rejected against the separately retained selected source. The seven companion mutations are retained from R28: wrong positive node, deleted required boundary, borrowed/fresh disposition, disconnected write lineage, changed no-op target guard, wrong request occurrence, and dropped replay boundary.

These are applicable source-level mutation constructions, not executed receipts. No `owner-certificate.json` runtime receipt exists in this source-only stage. Selected-main assertions for callback `1` and companion `23` remain in the focused test but have not been executed.

## Source owners and Mutual TODOs

- Rust owner map: `Receiving::observe` owns observer ordinal and bound construction; `Machine::propagate_request` owns the actual request vector, live `HandlerInstallation`, query-time invocation guard and actual Grant result; the separate `Machine.selected_catch_installations` vector owns selected live Catch source evidence; `Receiving::validate_callback_route_evidence` joins request observations, execution table, query-time Grant state and callback entries/uses/receipts. Added bound/evidence/snapshot/mutation state and the separate selected-installation vector are `#[cfg(test)]`; production `Observation` and runtime decisions retain their behavior.
- Lean lane must map `NativeObserved` together with separate construction-bound side evidence; the exact request-owned observation vector; the query-time invocation/Grant guard snapshot; the live selected dynamic installation snapshot; and the exact callback source/Name/use/execution joins (annotation, formal entry, Name read, typed callback use, result receipt and authentic execution). The proof lane must recheck R29 candidate `NativeCallbackGrantBridge.lean`, previously identified at SHA-256 `e49a320fbb148712b59e27a57cde57072e2192cdcdd84c936b10175f3a6ce6e0`. No Lean source or proof handoff was edited here.
- First remaining source/model premise: the projection from these concrete Rust owners into the formal source model must authenticate construction-time observations, the complete query-time invocation guard and the selected live dynamic Catch installation. Even if these joins map, source-to-constraints propagation/execution and the original full A/B obligation remain open; this handoff claims no theorem closure.

## Checks, resources and stop

R1's review text is preserved unchanged. The three repaired findings and positive baseline route were inspected by source read only. No Cargo, rustc, test, runtime, compiler or source-checker command ran; no mutation or selected-main result is claimed. R1 author time remains conservatively charged as 600/1200 seconds; R2 used part of the remaining 600-second repair cap, but exact active seconds were not instrumented. Cargo remains 0/360 seconds. Requested role/model/effort: Luna/high; observed runtime model/effort: UNKNOWN. No new path beyond the already leased source mutation design receipt was created, no build-target content was written, and no scratch output was created.

Outcome: source candidate and this single sequential handoff are frozen; writing is stopped. Compilation remains blocked until a fresh independent exact-hash source ACCEPT and a separate Luna stage receipt. The author stops here and does not self-certify the repairs.
