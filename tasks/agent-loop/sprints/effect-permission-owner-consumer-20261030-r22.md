# Sprint EFFECT-PERMISSION-OWNER-CONSUMER/20261030-r22

Status: ADMITTED; conditional source/runtime and proof evidence only
Branch baseline: `fcd38f02a33cb28b2c5c56dc6f1a48b8838e1dc4`
Authority: continuing Yulang Rust/Lean inference, executor soundness, effect hygiene, principality and termination goal
Decision: R21 sprint-end selector recommendation, admitted by Luna
Decision: R21 sprint-end selector recommendation, admitted by Luna

## Parent and fixed source domain

The original Simple-sub A/B claims, source quantifiers, accepted semantics and all existing parent gates remain unchanged. This sprint observes and reasons about existing callback-result runtime constructors and their consumer. It grants no compiler-semantic or production authority.

The first source is the exact approved callback example in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1.1:

```yu
act signal:
    our ping: () -> int

my relay(cb: () -> [signal] int) = catch cb() {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping
```

Use that exact text as its own source occurrence. The distinct companion is `tools/inference-playground/examples/original-suffix-outer-receiver.yu`: an inner `relay` Catch consumes `signal`, and its separate `write` contribution proceeds to the outer `receive`. The examples are independent occurrences. Neither may provide identity, permission, owner or event premises to the other.

R21's test did not execute. Its two reviewed instrumentation blockers (substring owner lookup/repeated caller labels; assertions passable with empty permission/contribution records) are historical failure evidence and are prohibited as R22 observation methods.

## Exact outcome

Authenticate each source independently through source annotation/schema formation, actual invocation ownership, callback entry/use/result view and receipt, operation request, exact local Catch selection and returned result. The callback permission and the actual `signal` contribution are separate facts; matching event families alone is insufficient. For the companion, separately authenticate inner `signal` consumption and the same source invocation's distinct `write` request reaching the outer `receive` consumer.

The trace must use structured typed ordered records. Bind each to a unique probe ID, source hash and actual source root/occurrence; record runtime IDs at the transitions that mint them, including invocation, callback-entry/use, view, receipt, event, and Catch installation/selection owner. A caller-supplied group label, debug-name substring, graph-family equality or final result does not establish identity. The validator must reject a sibling invocation/view, missing permission or contribution, failed export/selection, premature view/receipt retirement, the wrong handler owner, or lost `write` residual.

Relevant pinned runtime transitions include `program.rs` construction of `CallbackResultSchema`; `machine.rs` invocation creation, callback entry/use, `OperationResultConsumer`, request propagation and committed Catch selection; and `receiving.rs` entry/use/execution/grant validation. The trace must correspond to those actual owners and transitions. A candidate inventory or a modeled trace with no concrete Rust instance does not meet this outcome.

Success is an authenticated constructor-to-consumer trace plus a checked Lean invariant applied to those observations, or the exact first failed runtime transition with an honest incomplete proof result. The callback case must record the local branch returning `1`; the companion must retain its distinct `write` request through the inner relay to the outer receiver. No expected-output or fixture changes.

## Rust lane and pre-execution review gate

Create a detached isolated worktree from the baseline above. Copy only these exact source inputs from that commit; do not overlay the dirty or quarantined main-tree `machine.rs` or `receiving.rs`:

- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/src/runtime/program.rs`

All source edits must be test-only/provisional observation code in those isolated copies. The test reads the exact approved callback text above and the pinned companion file without changing either. Do not change Cargo manifests, lockfiles, fixtures, examples, expected output or main-tree sources.

Before the single Cargo invocation, freeze the three exact Rust source files and send their hashes plus a brief transition-to-event mapping to Luna. Luna assigns the fresh `compiler_referee` to check owner/invocation identity joins, event ordering and explicit rejection conditions before execution. Cargo may run only after Luna records ACCEPT for those exact frozen source hashes. Any source change invalidates that pre-execution ACCEPT and requires another review within the same 300-second review envelope. A rejection means no Cargo run until a reviewed revision exists.

One locked/offline invocation only:

```text
cargo test --locked --offline -p yu-playground --lib r22_callback_owner_consumer_trace -- --nocapture
```

No retry. Record complete argv, raw stdout/stderr, exit status, elapsed time, CPU and sampled memory, test result and machine-readable trace in the single JSON receipt. Invocation limit: 180 seconds, one CPU, at most 2 GiB process-tree RSS, and at least 4 GiB available RAM before launch.

Exact Rust write leases:

- `isolated/ep-owner-consumer-r22/project/tools/inference-playground/src/runtime/machine.rs`
- `isolated/ep-owner-consumer-r22/project/tools/inference-playground/src/runtime/receiving.rs`
- `isolated/ep-owner-consumer-r22/project/tools/inference-playground/src/runtime/program.rs`
- `isolated/ep-owner-consumer-r22/project/receipts/owner-consumer-receipt.json`
- `tasks/agent-loop/inbox/effect-permission-owner-consumer-r22-rust.md`
- `isolated/ep-owner-consumer-r22/project/build-target`

No directory-wide lease, Git operations or descendants.

## Lean lane

Write only:

- `notes/theory/lean/YulangClosure/CallbackResultOwnerConsumer.lean`
- `tasks/agent-loop/inbox/effect-permission-owner-consumer-r22-proof.md`
- `isolated/ep-owner-consumer-r22/lean-scratch`

Prove owner/lifetime invariants for the exact callback-entry/use/execution/grant and request-consumer transitions, then apply the invariant to authenticated Rust observations when present. Keep permission, actual contribution, event identity, owner/scope, Catch selection and residual `write` as separate premises/results. A generic projection theorem, arbitrary event-list model or assumed Rust-to-Lean bridge does not satisfy the outcome.

The pinned R21 audit failed in the unleased `FormalPermissionSourceTransport.lean`. Do not edit or lease it by inference. Import or repair it only if the proposed proof genuinely requires a theorem from that dependency; stop and return the exact dependency request to Luna before any such change. No Lean/Lake audit until the sole Cargo invocation is terminal. Use Lean 4.35.0, at most two serialized audits total (each ≤90 seconds, together ≤120 seconds, ≤1 GiB RSS and one CPU). Capture complete theorem types and full per-root axiom reports. A failed dependency build or absent concrete trace leaves the corresponding theorem/application OPEN.

## Review, resources and boundaries

The pre-execution source review and final frozen-evidence review use one fresh nonauthor `compiler_referee`, for a total of at most 300 seconds. After the test and proof lanes freeze, the reviewer checks source hashes, runtime identity joins, rejection cases, both source occurrences, exact trace order, Lean statements/application, complete axiom reports and resource receipts. Luna authenticates, adjudicates and records the result; only Luna stages, commits and pushes.

Total envelope: 2,400 active seconds (Rust 900, Lean 900, reviewer 300, primary 300); zero Astra; at most two concurrent producers. One serialized Cargo invocation ≤180 seconds; at most two Lean audits ≤120 seconds combined. No production repair, fixture/expected-output change, semantic revision, original-parent closure or cutover follows from this packet.

Keep original A/B, source/native correspondence, effect hygiene, soundness, principality, termination and production gates OPEN unless this packet proves its exact assigned premise. Stop on any identity falsifier, missing lease/dependency, material semantic ambiguity, resource limit, STOP, or exhausted budget.
