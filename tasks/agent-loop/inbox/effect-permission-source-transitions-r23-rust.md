# R23 Rust handoff — correction revision 2, frozen for independent preflight

Sprint: `CALLBACK-SOURCE-TRANSITIONS/20261030-R23`  
Assignment / handoff: `CALLBACK-SOURCE-TRANSITIONS/20261030-R23/RUST-CORRECTION-1`, revision 2  
Claim class: provisional source/runtime instrumentation and test harness; no theorem, native execution, cutover, or production claim.  
Baseline: `9a74a70a32ebda716a00c7203d8e606343cf442a`.  
Contract: `tasks/agent-loop/sprints/effect-permission-source-transitions-20261030-r23.md`  
Input manifest: `tasks/agent-loop/sprints/effect-permission-source-transitions-20261030-r23-inputs.json`

## Frozen source and validator hashes

| Exact leased path | SHA-256 | Baseline SHA-256 |
| --- | --- | --- |
| `isolated/ep-source-transitions-r23/project/tools/inference-playground/src/runtime/machine.rs` | `0116f875bc5df81f1321c4f13ca49e7745b67d02c52976fc216dabbfc7c7aab6` | `4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d` |
| `isolated/ep-source-transitions-r23/project/tools/inference-playground/src/runtime/receiving.rs` | `cfac5fcbc875f24172cc9027ace1169a2901614f25d1822f5f922e206ac7dd2e` | `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd` |
| `isolated/ep-source-transitions-r23/project/tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` | same |
| `isolated/ep-source-transitions-r23/project/receipts/source-transitions.json` | `bc1bdb6f4c840c1cf2cc602adf8de5ccaf92d121a0c89b2c700fce54140303fb` | newly created |

The revision 1 handoff's `consumer_step < request_step` check was removed from the operation-v1 receipt validator. Machine step remains captured separately; it is not used to order nested hooks. The test-only observation ordinal is monotonically minted at the actual Consumer, Request and committed Catch-selection hooks.

## Source-owner path and corrected harness

The transition table remains derived from the committed baseline. `program.rs::CallbackResultSchema::from_parameter` constructs the permission schema from the source Lambda/formal. `Frame::ValueEntry` and `receiving.rs::callback_entry` mint a distinct entry view and formal receipt. The operation Consumer observes the actual direct `Name(Observe)` and calls `callback_entry_for_apply`, which checks schema/formal, Name receipt, invocation owner and view. `callback_use` records the body Apply separately and mints the result view/use receipt. The Consumer creates its execution view before executing the returned Request. `execute_with_substitution` mints the Request event; `propagate_request` checks the active Catch, operation, payload and grant before selecting its source arm.

The corrected `cfg(test)` harness is inside the leased `machine.rs`. For each unchanged source it first calls the public `crate::execute` entry point, then runs a candidate-backed `Machine` through the same `prepare_with_world → RuntimeProgram::from_candidate_world → start_source_schedule` path so the test-only owner hooks can be inspected. The callback literal includes the final newline and has the approved source SHA-256 `163fb480ec7ecaed2c341253066a7c6cc3af1a0cf5499c384f0cad4952c64e18`. The companion uses `include_str!("../../examples/original-suffix-outer-receiver.yu")`, SHA-256 `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7`.

The test is authored to assert:

- Callback formal entry, Name read, body Apply, Consumer, Request and Catch have separate source/arena coordinates. Invocation/view joins are checked; formal and Name receipts must remain distinct; the body Apply (`cb()`) is not equated with the operation Request (`signal::ping`).
- Consumer ordinal < Request ordinal < Catch ordinal. Consumer and Request are expected to share a machine step because they run as nested hooks in `Frame::OperationResultConsumer`; the independent ordinal expresses their actual order.
- The unchanged callback source completes through its local Catch with integer `1`; the Catch observation separately records shallow suffix discard.
- The unchanged companion source completes with integer `23`; its `write::ping` Request joins by event, operation, payload and owner to the separate outer `catch pending` selection. The signal Catch and write obligation remain separate.

This is authored coverage only. No test has run; neither source's acceptance/output/trace behavior is yet observed. If either ordinary route rejects, the first exact failure must be preserved without changing source semantics or runtime guards.

## Exact proposed command and gate

```text
cargo test --locked --offline -p yu-playground --lib source_transition_ordinary_runtime_reaches_callback_one_and_outer_write -- --nocapture
```

No Cargo, Rust compiler/test, Lean/Lake, checker, or formatter was run. There is no native event trace or raw execution output. The command is locked/offline, one Cargo attempt, and remains blocked on fresh nonauthor ACCEPT of these exact hashes plus Luna's separate fresh-session resume. Any edit invalidates this freeze and needs renewed review.

## Semantics and prior evidence

- Contravariant `[signal]` remains permission; it adds no signal to an empty inflow. The callback's actual Request is a separate contribution. The owning Catch alone handles signal. The companion's independently sourced `write` remains a separate obligation for the outer receiver.
- R22's rejected observer was not overlaid. Its known mistakes (post-Request use observation, conflated lambda/Apply identity, reversed order, missing payload/arm/formal receipt) are covered by owner-local hooks or the new source test assertions. The R22 result remains failure evidence only.
- No expected output, source domain, diagnostics, inference semantics or root source file changed.

## Remaining premises and limits

- Exact behavior is unknown until the reviewed focused command runs. The current test may reveal that either unchanged source route rejects; do not patch semantic guards or infer a successful trace from the test source.
- The test captures selected arm identity from the Catch constructor and checks its source handler plus result, but no separate Lean application exists yet. Parent theorem/source-native, hygiene, soundness, principality, termination and production gates remain OPEN.
- No program.rs change was needed; it is frozen at its admitted baseline hash. Root dirty/quarantined `machine.rs` and `receiving.rs` were not read or used as baselines.

## Runtime and cessation

- Requested role/model/effort: `implementer`, Luna/high (pinned).
- Observed model/effort: UNKNOWN; worker runtime exposes no model telemetry.
- Active elapsed: UNKNOWN (no worker monotonic start/stop telemetry). The primary's authenticated bound remains the session-level budget basis: prior upper-bound charge 455s; correction-session cap <=700s; <=240s reserved for post-ACCEPT Cargo and <=5s handoff reserve; cumulative Rust grant remains 1,400s with no renewal.
- Worker state: STOPPED after this handoff. No Cargo/Rust/Lean process or descendant was launched; no process remains active.
- Git operations: none. New paths: the leased `source-transitions.json` and this handoff. `build-target` was not written; no disposable scratch or generated path was created.

STOP: these bytes are frozen. Wait for Luna's exact-hash preflight result. No Cargo invocation is authorized before ACCEPT and an explicit fresh-session resume.
