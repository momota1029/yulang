# R31 Rust correspondence handoff — frozen source-only proposal

Assignment: `/root/effect_permission_r31_rust`; exact outputs are this handoff
and `tasks/agent-loop/artifacts/native-callback-grant-r31.patch`. Sprint:
`EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R31`, contract and input
manifest pinned by Luna. Requested lane: Luna/high. Observed model and effort:
UNKNOWN. Active seconds were not instrumented; the assignment remains bounded
by its 1,600-second cap. No model-routing or runtime claim is made.

## Result and exact proposed change

The patch replaces the R29 fixture's one inequality over Debug-derived Strings
with an inequality over the retained typed operation IDs:

```rust
assert_ne!(consumer.operation_identity, template.declaration.id,
    "the consuming write request is distinct from the captured request");
```

This is a source proposal only. Neither the patch nor runtime source was
applied. It was not compiled or executed, and it is not independently reviewed.
It therefore does not establish that these two typed IDs compare unequal in
the fixture. A typed equality failure on application/execution is a stop and
must be reported as a real typed collision; do not synthesize identity changes
to make the assertion pass.

The proposed assertion is narrowly about operation identity. Existing adjacent
fixture checks remain unchanged: the request family is `write`, the operation
spelling is `ping`, and the request and captured source occurrences differ.
These checks are separate observations, not substitutes for the typed ID
comparison.

## Source-owner mapping inspected

Inputs: the R30 archive was streamed without extraction. Archive SHA-256 is
`5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`;
the candidate `machine.rs` member is
`b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`, and
`receiving.rs` is
`55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.
The typed identity definitions are pinned in the manifest:
`source_annotation.rs` SHA-256
`409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` and
`full_parse.rs` SHA-256
`dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`.

| Native owner | Concrete source fields / operation | Correspondence limit |
|---|---|---|
| Structural operation identity | `SourceOperationId { family: SourceEffectId, declaration: SourceNodeKey }`; family is `{ module: Arc<ModuleId>, declaration: SourceNodeKey }`. Both ID types derive `Eq`/`PartialEq`. `SourceNodeKey` compares parse `Arc` identity, green-node allocation identity, and source start. | `Debug` for `SourceNodeKey` omits all identity fields. The R29 assertion compared `consumer.operation` and `capture.operation`, both `format!("{:?}", id)` strings. That failure is not evidence of typed equality or a typed collision. The patch compares the actual retained `consumer.operation_identity` with the captured template's `declaration.id`, preserving family/module/declaration identity. |
| Request-owned observations and local Grant | `PendingRequest.observations` is the request vector. `Machine::propagate_request` selects/authenticates the live `HandlerInstallation`, snapshots `invocations` and `(id, active)` immediately before `Receiving::local_grant`, and stores a separate `request_observation_snapshot` on `RequestConsumerEvidence`. | `Receiving::validate_callback_route_evidence` joins candidate observation fields to the request snapshot and reconstructs local Grant from that snapshot and the retained query-time invocation descriptors. This is the candidate's source-to-runtime permission check; it is test evidence, not a proof that every source annotation reaches the runtime query. |
| Invocation guard | The cloned `request_invocations_snapshot` and `request_query_guard_snapshot` are taken at the actual Grant query point. The validator checks the callback route's query owner and active bit against both; the harness also checks the owner becomes inactive after `ReceiverReturn`. | The snapshot records the query-time state and later deactivation check. No new guard or runtime semantics are proposed here. |
| Selected dynamic Catch | After a real selected live frame passes installation validation, `Machine::propagate_request` appends `SelectedCatchInstallationEvidence` with request event, Catch source site, installation occurrence/owner, resolved typed operation, selected arm and `authenticated_live_frame`. `RequestConsumerEvidence` points to that independent record by index. | `validate_dynamic_catch_consumer` joins request event, handler/installation occurrence, source site, authentication, owner, typed operation and selected arm against the selected record. Human-readable Debug fields remain presentation only. |

Together, the inspected native path is source HIR operation resolution →
request creation and observation ownership → actual live Catch candidate and
request-local Grant query → request-owned snapshots and selected Catch record
→ callback route validation and selected arm execution. R31's Rust delta
repairs only the typed-identity assertion at the existing fixture boundary; it
does not add constructor fields, constraints, propagation code, or a new
execution path. The broader mapping from source annotations into these runtime
premises remains an open source/proof obligation.

## Evidence reused, rejected, and checks

Reused the exact R30 archive member hashes and manifest-pinned source identity
definitions; inspected the candidate assertion, `RequestConsumerEvidence`,
`SelectedCatchInstallationEvidence`, the `propagate_request` Grant query and
evidence construction, `Receiving::validate_callback_route_evidence`, and
`validate_dynamic_catch_consumer`. Reused R29's source-level owner/mutation
map only as a guide to the concrete fields; it is not runtime evidence.

Rejected the R29 inference that a Debug-string collision establishes a
`SourceOperationId` collision. The typed equality assertion was never run.
Also rejected any claim that the existing test-only snapshots establish the
full source-to-constraints/proof correspondence: they establish concrete
candidate source owners and joins only.

Focused read-only checks: confirmed the archive and pinned member/source
hashes; inspected both sides of the unique proposed assertion and the concrete
field types, construction points, and validator joins listed above. No Cargo,
Rust compiler, test, runtime, Lean, Lake, or Git command ran. No compiler or
runtime certificate exists. No temporary extraction, project copy, worktree,
target, cache, or helper artifact was created.

## Open premises, boundaries, and handoff

The original A/B source-preservation claims, finite structural-identity
encoding/injectivity for Lean, source-annotation-to-runtime correspondence,
and whole-language hygiene remain OPEN. A reviewer must inspect the frozen
patch against the pinned source and the proof lane's exact Lean artifact. If
accepted, any apply/compile/runtime step still needs Luna's separately recorded
stage authority; the current contract forbids source edits and Cargo/tests.
No production behavior, effect policy, expected output, diagnostic, or source
domain was changed. No provisional runtime instrumentation was added.

Frozen handoff ID: `effect-permission-native-callback-grant-r31-rust`,
revision `r1` (local assignment handoff; Luna owns intake/adjudication).
Outputs and hashes are listed in the stage receipt supplied to Luna. Writes
are stopped. No disposable scratch path exists.
