# R28 Rust lane — frozen source-construction handoff

Assignment: `/root/r28_rust`; R28 fixed source/certificate packet. Status: source candidate constructed, uncompiled and unexecuted. This lane stops pending exact-hash review ACCEPT plus separate Luna authorization for Cargo.

## Frozen inputs and current hashes

W: `isolated/ep-owner-certificate-r28/project`, HEAD `c9e315208cb04bcc4fe8c3595d929fb76538f1cd`.

- `tools/inference-playground/src/runtime/machine.rs`: SHA-256 `015db9d7adf57b2c9ca628b5908c7c58f50c279b26b19cafb2f082ba33cec86a`
- `tools/inference-playground/src/runtime/receiving.rs`: SHA-256 `632e9a23951d2791d4638400a5f93815bbb1c9831f388ddae4a8a0e806470ddb`
- Frozen proof bridge: SHA-256 `7089b047821ed82e715b4230c47e36f5fec231bf431ec6d26501137f8a358c18`
- Read-only R26 overlay: SHA-256 `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`
- Unchanged dependencies: `continuation.rs` `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`; `program.rs` `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`; package manifest `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56`; `Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`; companion fixture `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7`.

The callback source hash is the fixed manifest value `163fb480ec7ecaed2c341253066a7c6cc3af1a0cf5499c384f0cad4952c64e18`. Baseline receipt at this inbox path: SHA-256 `a381771b04c964855c26550ea25fb2f6271824461eac7ebd3bf016bf75d24b59`; callback baseline was reused only after matching the R27 command/source/manifest pins (status 0, stdout `1`). The companion selected-main baseline ran with locked/offline package resolution and one job (status 0, stdout `23\n`; Cargo build 42.69s). No source changed during that baseline.

## Source-to-native contribution implemented

All new collection and validator code is `cfg(test)`. The production Grant decision is unchanged.

- Source-owned callback annotation enters through `CallbackResultSchema::from_parameter` and its concrete `families`, lambda site and formal. The certificate builder encodes the resolved effect as its HIR declaration index plus module/declaration identity; it does not use display-name equality.
- `callback_entry_for_apply` remains the sole direct-parameter-Name gate. On success, test-only evidence records its actual entry, owner, value/view, Name receipt, formal absence and source site. `callback_grant` does not redo these Name checks. The gate checks source root and occurrence; native code does not establish byte-span equality, so no such theorem is claimed.
- The receiving-store projection joins the actual callback entry/formal receipt, direct Name receipt, callback use, result view/receipt, execution-table slot, request observation, active owner at query, `callback_grant`, and the `local_grant` result at the request’s selected Catch. Permission and actual incoming view are separate fields; callback-entry view coverage is copied from incoming view, and no permission is inserted into actual inflow.
- The machine’s Catch-side request record preserves the emitted event, resolved operation identity, payload, request owner, handler/arm source identities and selected result. Callback JSON contains no template/frame coordinates.
- Companion evidence reuses the R27 test-only Owner replay and frame lineage construction. Its captured signal template/root/replay coordinates remain in the companion route; the distinct write request, payload and Catch consumer are recorded separately as a surviving contribution.
- The focused test constructs five callback mutations (invocation owner, Name/formal receipt, result view/use, event/origin execution and resolved effect identity) and retains R27’s applicable companion mutations for wrong positive node, required boundary deletion, borrowed/fresh disposition, disconnected write lineage and changed no-op target. Each uses the target-present/change/rejection guard.
- The test writes the schema-v1 combined JSON to the leased `receipts/owner-certificate.json` only when it is eventually run. It has not been generated: candidate execution is still gated.

## Evidence reused and rejected

Reused the R27 final frozen Rust candidate only as an unreviewed implementation seed: machine SHA `bf5a2819d256658ef3d93cc73a0adee467113e83f3126ebaa9247f54f8378241`, receiving SHA `c843f27f7e5c74e50434f15e00544f5e07054efdc993a8327b200c51266e158b`. The three `ReceiptHandle.0` reads were changed to the test-scoped `index()` accessor. R27 had no candidate JSON, no post-repair compile, and no accepted exact-hash review; none is treated as evidence here. The R26 rejected candidate/archive remains rejected. The R26 Lean overlay is only the abstract conditional dependency; the R27 unchecked Lean artifact is not used as proof. The R28 stage-1 Lean bridge is constructed but unchecked, as its handoff states.

## Checks, omissions, and stop boundary

- No Cargo, rustc, compile, candidate runtime, focused test, formatter, or Lean process was started in this resumed source stage. No process remains. A static format-placeholder/argument-count audit passed for the new JSON builders; it is not a Rust compile check.
- `receipts/owner-certificate.json` does not exist. The focused assertions have not run, so no native Grant, Catch result, mutation rejection, or source-to-output correspondence is authenticated yet.
- Full original A/B quantifiers, complete History, RootComp reachability, arbitrary effect type arguments/symbolic rows, computation-formal route, source formation, propagation/freshening/extrusion, source-to-constraint generation, principality, termination and production remain OPEN. The bridge’s constructor implications remain unchecked and do not establish native/source equivalence.
- Provisional boundary: observations and mutation validators are test-only. They do not authorize semantic cutover or prove the theorem. No source fixture, expected result, solver semantics, dependency, lockfile or production decision changed.

## Paths, budget, and next authorized step

New/edited Rust source paths: only the two exact W leases above. Root inbox handoff: `tasks/agent-loop/inbox/effect-permission-owner-certificate-r28-rust.md` (this file). `build-target/` is the existing leased baseline build output from stage 1; disposable by primary-only hygiene after the sprint. The stage-1 isolated-copy handoff remains preserved. No candidate JSON, scratch path, new dependency or manifest path was written. No Git operation occurred.

Requested model/effort: `gpt-6-luna/high`. Observed model/effort: unavailable in this runtime receipt (`UNKNOWN`); no fallback is claimed. The assignment reserves 250 seconds for baseline/prior coordination; the resumed construction remained below its 900-second cap. Conservative total accounting is at most 700/1,150 seconds, leaving at least 450 seconds; no Cargo time beyond the 42.69-second stage-1 baseline was charged.

Next related in-envelope step: after an independent reviewer ACCEPTs these exact two source hashes and Luna separately authorizes execution, run only the pinned one-job locked/offline library test compile (<=90 seconds), check that result, then the focused R28 certificate test (<=60 seconds), subject to the 360-second aggregate Cargo ceiling and one-heavy-process rule. Freeze the generated JSON and source hashes for fresh Lean instantiation/review. Do not run either command before both gates.
