# R26 Amendment 02 — additive observation schema R2

Status: **APPROVED BY LUNA** for one sequential, test-only R2 candidate. This is a versioned amendment to the R26 contract; R1 and the rejected R1 candidate remain immutable. It preserves the original objective and source routes.

## Frozen parent and reason

Base contract: `/home/momota1029/rust/yulang/tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26.md` SHA-256 `8b2fcc72995472465b23fc397f257d07a035b0b1ba15f8f62ee31ae705dc11e5`. Base input manifest: `/home/momota1029/rust/yulang/tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-inputs.json` SHA-256 `ec31c06563e6835101647272ce46930be55230481862621d8757b1193387e97d`. Prior resource-only amendment 01 remains in force and unchanged. R1 schema digest `686c96c8f8b5417b075a18954f773ad4071996e51e809d65040a87441c342c3c` and R1 rejected candidate hashes are preserved in the R26 active history and inputs-r2 manifest.

The exact R1 candidate was rejected because `ContinuationApply.owner == retained write Request.owner` is not an existing runtime invariant, and the outer receiver/control chain is not part of the inner signal Catch's saved suffix. The author confirmed that R1 has no observation for the actual `TemplateNode::Owner` resolution and cannot authenticate the distinct retained surrounding chain. Reusing R1 fields would misstate identity or event time.

## Authorized additive delta

Adopt the additive test-only observation schema R2 defined at `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-schema-r2.json` (canonical schema digest `118319c84980812e0a2bf5f5f4c968ddd4fba2fd08cdac0a65ca841510c0f9e7`, raw file SHA-256 `e767fb0c71752691c4ca953621105a1c7a1f4b3f5809423a71c30588d2d1a5ee`). R2 adds only:

1. `TemplateOwnerResolution`, recorded at the existing `TemplateNode::Owner` branch after the runtime has resolved and selected its existing borrowed or fresh owner, before the existing `current_owner` assignment. It records template/node, original owner, control-resolved owner, prior owner, actual selected owner and `BorrowedActive`/`FreshInvocation`, with the existing `OwnerOpen` record linked when fresh.
2. A distinct `ContinuationCapture.outer_control_chain` snapshot of the actual retained receiver/control boundary frames at capture time, with exact frame indices/order and existing `ReceiverReturn`, `OwnerReturn` and `CatchReturn` identities. Keep this separate from `ContinuationCapture.suffix`; do not add outer frames to suffix evidence.

The validator must link the exact continuation application to its later owner-resolution event, then link the retained write Request/Catch through the captured outer handler/control chain and actual owner. Keep the response value/view lineage separate and join both to the same write request. Add rejection mutations for substituted/missing owner-resolution identities and dispositions, mismatched outer boundary/handler/order, and disconnected write event. Preserve every earlier required mutation and both exact route-result assertions.

## Preserved invariants and authority

R1 stays byte-for-byte frozen. Every existing R1 transition and field retains its meaning. This amendment does not reinterpret `ContinuationApply`, `ContinuationCapture.containing`, `OwnerOpen` or suffix owners. The observer changes are under `cfg(test)` only. Runtime owner selection, `resolve_control`, active-owner reuse, freshening, current-owner transitions, receiving/grant behavior, source semantics, dependency versions, source domain, fixtures and expected results remain unchanged. No production authority is added. R2 evidence does not close native Grant or RootComp image/receipt reachability. The reviewed R1 Lean module is unchanged; do not run another Lean audit.

## Existing exact leases and resource plan

No worker path, dependency, capacity or production lease is added. The same six Rust leases remain the only write paths. The same Rust author resumes only after this amendment, schema R2, inputs-r2, and the ACK are committed and pushed. Correction/freeze cap: **400 seconds**, within the 627 seconds left in the prior 700-second sequential packet and the 1,037-second total Rust remainder. The bounded path through correction, one compile-only command (≤120s after a fresh exact-hash ACCEPT), up to two runtime invocations (≤120s each, ≤240s combined, after a separate fresh ACCEPT), and handoff (≤40s) is at most 800s, within the current Rust envelope; remaining time is not implicitly transferred.

No compiler/test/formatter invocation is authorized by this amendment. The same nonauthor reviewer has 313/1,000 seconds charged, 687 seconds remaining: only **170 seconds** remain in the current compile-candidate review allocation; preserve the later 300-second runtime and 200-second final-applicability allocations. If fresh exact-hash review does not ACCEPT within its cap, stop without compile. The Lean lane has 497/600 seconds charged and remains frozen. Luna has 1,470/3,600 seconds charged; retain the 500-second closeout reserve. Astra remains 0.

Before R2 writing resumes, Luna must authenticate this amendment, schema and inputs-r2 hashes, record the unchanged exact leases and fresh ACK, then reopen those same paths. Any schema/semantics/source-scope/resource need outside this delta stops for a new Luna decision. No inference from this approval grants compile, runtime, source/native, parent-theorem or production closure.
