# Sprint EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R28

Status: ADMITTED by Luna; no child work starts before the admission checkpoint is pushed.
Revision: 1. Baseline commit: c9e315208cb04bcc4fe8c3595d929fb76538f1cd.

## Original goal and fixed semantics

Original parent: YulangClosure.SourceProblem.InferenceSoundness and the source-preservation claims in notes/theory/2026-10-13-intrusion-source-preservation-proof.md §§1, 3, 5. The active user goal remains Yulang inference/executor soundness, effects, principality and termination, with effect hygiene emphasized.

Use the selected annotation policy in notes/design/2026-10-10-annotation-effect-hygiene-integration.md §§1.1–1.2 and 3–5. A contravariant [signal] permission belongs to the resolved formal/port/invocation boundary. It does not add signal to actual inflow. The actual Catch handles the matching signal contribution; permission does not impose a closed [signal]-only upper bound. Preserve unrelated contributions and symbolic dependencies. Do not infer permission from family-name equality, equal row roots, callback output, or companion-route evidence.

The source domain is fixed: the approved callback program in the R27 input manifest returns 1, and tools/inference-playground/examples/original-suffix-outer-receiver.yu returns 23 through its selected main. Preserve both sources, expected outputs, supported language, production behavior, dependencies and lockfile. No solver semantics or production code changes are authorized in this packet.

## Fixed outcome

Produce one reviewed provisional source-to-model checkpoint, or an exact first-failure receipt, with these joined parts:

1. The callback route records the actual source-owned annotation, invocation/formal callback entry, parameter-name receipt, callback use, result execution, emitted request/event, resolved signal identity, local Grant result and selected Catch consumer. Each identity is read from its owning runtime store/constructor. A Lean projection from source-faithful native records derives the callback branch of the accepted R26 conditional model's PortReady and, where the recorded consumer establishes every premise, CatchReady. Instantiate the projection with the authenticated callback certificate. Do not assume UseReady, PortReady, native Grant, an authenticated History, or the desired result as the bridge conclusion's premise.
2. The companion route preserves an independent owner/template replay and complete retained-frame/request-consumer certificate. Keep its frame/template coordinates separate from callback records. Record the surviving write request/contribution separately from the signal Catch.
3. Negative mutations target present records, change the intended field, and are rejected by the validator. Cover wrong invocation owner, formal/receipt, result view, event/request identity, and resolved effect identity on callback evidence; cover the existing wrong-positive-node, missing-boundary, borrowed/fresh disposition, disconnected-write and no-op-target cases on companion evidence. Report a mutation as inapplicable when its target is absent; never count a no-op as rejection evidence.
4. A fresh independent reviewer accepts exact Rust sources, the generated certificate, the Lean declarations/audits and the application of those declarations to the recorded callback route.

The callback bridge is the decisive hygiene target. The companion certificate is supporting native evidence and cannot supply callback facts. Full History construction, RootComp reachability, arbitrary symbolic/type-argument rows, the computation-formal route, propagation/freshening/extrusion, the original joint source strategy, principality, termination, and production remain OPEN unless proved by their actual owners.

## Source, proof and evidence lanes

### Rust implementation lane

Owner: registered implementer, Luna/high. Work only in fresh detached worktree W=isolated/ep-owner-certificate-r28/project, based on the committed baseline above. First run the unchanged companion selected-main baseline route; reuse the authenticated R27 callback baseline result only after checking its exact command/source pin. Then combine the R27 companion certificate repair with test-only callback observation at the actual receiving/machine constructors. Preserve the R27 final frozen candidate and R26 rejected candidate/archive as read-only references; do not copy an unreviewed claim forward as accepted. Keep instrumentation under cfg(test), and do not modify request, handler, Grant or solver runtime decisions.

Freeze the observation schema and inputs before worker launch. The callback certificate must preserve resolved identities and separate permission, actual inflow/request, execution, Grant and Catch consumption. It must not attach capture/template coordinates to callback records merely to share the companion format. Emit raw command output, the structured certificate and all positive/mutation checks in W/receipts/owner-certificate.json. Stop on changed baseline output, a native true Grant that does not project to the required R26 premises, an inapplicable mutation claimed as evidence, a compile failure, a new source path, or a source transition that cannot be authenticated.

### Lean proof lane

Owner: registered lean_prover, leaf. Reuse the exact R26 CallbackHygieneCorrespondence.lean overlay unchanged. Construct NativeCallbackGrantBridge.lean from the actual constructors and store joins in receiving.rs and machine.rs. First stage is at most 350 seconds against frozen source/schema: define source-faithful records and prove the generic constructor-success implications; then stop writing and stop charging while Rust produces authenticated records. Resume only with a fresh current-session receipt after the JSON hash is frozen. Use at most the remaining 650 seconds to instantiate the bridge on actual callback records, make at most two pinned Lean audits totaling 120 seconds, inspect every theorem type and full transitive axiom report, and record omitted cases. Do not wait in RUNNING state for Rust or for a heavy-process window.

Build/check only in the isolated project with Lean 4.35.0. No root import edits, global tool changes, new dependencies, sorry/admit/project axioms, checker bypasses, or definitions that assume the parent conclusion. A generic constructor theorem or R26 conditional result is not source/native or parent closure.

### Independent review and execution gates

One fresh read-only compiler_referee reviews the exact frozen Rust/Lean hashes and generated evidence. Authors cannot review their own work. Reviewer rejects any wrong owner/formal/view/event/family join, callback Grant unsupported by source-owned records, companion evidence substituted for callback data, omitted mandatory boundary, no-op mutation, or theorem whose native constructor premises are merely assumed.

Only after exact-hash ACCEPT and a separate Luna stage record may the Rust owner run the targeted library test compile and, after its result is checked, the focused certificate test. Cargo commands are serialized, offline/locked, one job, at most 360 aggregate seconds. The compile is bounded by 90 seconds and the focused execution by 60 seconds. At most one heavyweight process runs across Cargo, Lean and Lake. A changed source revision invalidates review and all later execution gates.

## Exact leases

Rust writes only:
- isolated/ep-owner-certificate-r28/project/tools/inference-playground/src/runtime/machine.rs
- isolated/ep-owner-certificate-r28/project/tools/inference-playground/src/runtime/receiving.rs
- isolated/ep-owner-certificate-r28/project/receipts/owner-certificate.json
- isolated/ep-owner-certificate-r28/project/build-target
- tasks/agent-loop/inbox/effect-permission-owner-certificate-r28-rust.md

Lean writes only:
- isolated/ep-owner-certificate-r28/project/notes/theory/lean/YulangClosure/NativeCallbackGrantBridge.lean
- isolated/ep-owner-certificate-r28/project/notes/theory/lean/.lake
- isolated/ep-owner-certificate-r28/lean-scratch
- tasks/agent-loop/inbox/effect-permission-owner-certificate-r28-proof.md

Read-only overlay: isolated/ep-owner-certificate-r28/project/notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean, copied byte-for-byte from the accepted R26 conditional artifact. Review writes only tasks/agent-loop/inbox/effect-permission-owner-certificate-r28-review.md. Luna owns the contract, schema, input manifest, admission/active/outcome receipts, current.json and Git.

All root runtime, solver, Lean and existing worker paths retain their current hashes/owners/states. In particular, tools/inference-playground runtime paths quarantined to UNKNOWN_WRITER remain untouched; the dirty/frozen root candidate_effect.rs, candidate_scheme.rs and shadow_apply.rs remain untouched. The R27 worktree and unchecked R27 Lean artifact are frozen archival inputs, not writable leases.

## Fresh finite envelope and stops

Total 7,200 seconds: Rust 1,150; Lean 1,000; fresh independent review 1,200; Luna 3,850 including a 500-second closeout reserve; Astra 0. Rust gets at most 360 aggregate Cargo seconds. Lean gets at most two audits/120 seconds total. Assignments use finite stages and exact paths. Reserve review/integration capacity and serialize all heavyweight processes. No R27 remaining allocation transfers to R28.

Stop and consult the dispatcher on a semantic mismatch, source counterexample, repeated failed premise, material dependency/path/schema/authority change, inadequate resources, or integration seam. Close incomplete with exact source hashes, theorem types actually checked, resource receipts and remaining owner/premise when any required bridge fails. Do not promote this provisional packet to compiler semantics, full-language hygiene, soundness, principality, termination or production readiness.
