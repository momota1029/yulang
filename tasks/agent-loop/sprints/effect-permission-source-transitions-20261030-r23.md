# Sprint CALLBACK-SOURCE-TRANSITIONS/20261030-R23

Status: ADMITTED, serial Rust source-transition lane first; all evidence remains conditional
Branch baseline: `9a74a70a32ebda716a00c7203d8e606343cf442a`
Authority: continuing Yulang Rust/Lean inference, executor soundness and effect hygiene goal
Decision: next_action_selector sprint-start recommendation; Luna validates and admits

## Parent, semantics and source domain

Preserve the original Simple-sub A/B claims, quantifiers, accepted semantics and source domain. The unchanged original parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`; the selected language behavior is governed by `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` and the approved level-SCC design. This packet supplies conditional source/runtime and mathematical evidence only. It grants no semantic revision, parent closure, production promotion or cutover.

Keep these distinctions explicit throughout the observer, validator and Lean model:

- Contravariant `[signal]` on a callback formal grants permission to the caller; annotation alone does not add `signal` to inflow.
- Actual callback execution may contribute a `signal` request. Only the owning `Catch` consumes that request.
- Removing handled `signal` from an actual inflow leaves a separate `write` contribution intact; it cannot create a contribution in an empty inflow or erase unknown variables/dependencies.
- The callback example and the companion `write` example are distinct source occurrences with independent owners and obligations.

The callback source is exactly the §1.1 text in the governing hygiene document:

```yu
act signal:
    our ping: () -> int

my relay(cb: () -> [signal] int) = catch cb() {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping
```

The companion source is the unchanged `tools/inference-playground/examples/original-suffix-outer-receiver.yu`. Its inner relay handles `signal`; its distinct `write` request must remain available to its outer `receive` consumer. Do not combine identity, permission, event, owner or result evidence across the two sources.

## Exact outcome and method

Derive one source-transition table from committed baseline code, then derive both the provisional observer and validator from that same table. Trace the actual constructor-to-consumer route: callback schema construction in `runtime/program.rs`; invocation creation, callback entry/use, operation-result consumer, request propagation, Catch installation/selection, normal return and shallow-handler discard in `runtime/machine.rs`; and callback entry/use/execution/grant validation in `runtime/receiving.rs`.

For every transition record the owning source occurrence and the identity minted by that transition. Keep lambda definition, formal binder, Name read, body Apply, invocation, callback entry/use, view, formal receipt, request payload, selected arm, Catch owner, event and consumer coordinates separate. Equality may be asserted only where the source transition actually carries or derives that identity. Do not infer identity from debug formatting, substring lookup, graph-family membership, supplied group labels, equal source occurrences for different syntax nodes, or equal final results.

The validator must check provenance, required transition order, owner/lifetime, exact payload and selected arm, schema/Name agreement, and distinct normal-return versus shallow-discard branches. It must reject absent records and mutations that swap invocation, entry, use, Name view, formal receipt, request payload, arm, Catch owner or event; mismatched schema/Name; an invalid event order; and a lost companion `write`. Permission evidence and actual contribution evidence are separate required facts.

Success is either (a) a fresh independently reviewed source table/observer/validator, an authenticated constructor-to-consumer execution for each unchanged source, and a pinned Lean 4.35.0 theorem with complete type and axiom report applied to those authenticated records; or (b) the exact first failed source transition with a reviewed and checked conditional invariant, if available. A modeled trace without a concrete Rust instance is not execution evidence. The callback trace must reach the local branch returning `1`. The companion must preserve its separate `write` through the inner relay to the outer receiver. Expected outputs and fixtures remain byte-identical.

## Rust lane and pre-execution review gate

The baseline source blobs were checked against the inherited R22 pins. A detached worktree at `isolated/ep-source-transitions-r23/project` must be initialized at the baseline commit. Do not read, copy, overlay, or use the dirty/quarantined root `machine.rs` or `receiving.rs` as a baseline. Only provisional, behavior-neutral, test-only observation changes are allowed in these three isolated files:

- `isolated/ep-source-transitions-r23/project/tools/inference-playground/src/runtime/machine.rs`
- `isolated/ep-source-transitions-r23/project/tools/inference-playground/src/runtime/receiving.rs`
- `isolated/ep-source-transitions-r23/project/tools/inference-playground/src/runtime/program.rs`

The Rust lane may also write only:

- `isolated/ep-source-transitions-r23/project/receipts/source-transitions.json`
- `tasks/agent-loop/inbox/effect-permission-source-transitions-r23-rust.md`
- `isolated/ep-source-transitions-r23/project/build-target`

Before execution, freeze all three source files and the transition table/validator, report exact hashes and the proposed Cargo argv. A fresh nonauthor `compiler_referee` must review those exact bytes and explicitly ACCEPT identity joins, event order, provenance/ownership, rejection coverage, source/fixture immutability and resource plan. No Cargo before Luna records that exact-hash ACCEPT. Any correction invalidates ACCEPT and receives a bounded re-review from the same referee. Up to two reviewed invocations are permitted only for a reviewed source correction or an exact failed first transition; combined Cargo elapsed time <=240 seconds, each <=120 seconds, one CPU, <=2 GiB process-tree RSS and >=4 GiB available memory before launch. Capture complete argv, raw output, status, elapsed time, CPU/memory sample and machine-readable records. Serialize Cargo and Lean processes; never run concurrent heavy processes.

No Cargo manifest, lockfile, fixture, source example, expected output, main-tree source, or quarantined path may change. No candidate inventory or graph projection may stand in for the concrete runtime path.

## Lean lane, sequential admission

Admit the registered `lean_prover` only after the Rust writer is STOPPED and the frozen source table, reviewed validator and any authenticated records are available. Write only:

- `notes/theory/lean/YulangClosure/CallbackSourceTransitions.lean`
- `tasks/agent-loop/inbox/effect-permission-source-transitions-r23-proof.md`
- `isolated/ep-source-transitions-r23/lean-scratch`

Use the pinned Lean 4.35.0 toolchain. Define the smallest source-shaped branching transition system that retains owner-produced IDs and provenance. Prove accepted transitions preserve the callback-owner/lifetime invariant and handle normal return and shallow-handler discard separately. Model permission, actual inflow contribution, Catch subtraction, event identity and the companion residual independently. Apply the theorem to authenticated Rust records when present; never assume a Rust-to-Lean identity equation or use an arbitrary event list as whole-source evidence. Capture complete theorem types and full per-root axiom reports. At most two serialized audits, <=120 seconds combined, each <=90 seconds, one CPU and <=1 GiB RSS. An unavailable dependency or absent execution leaves the relevant application OPEN; do not edit an unleased dependency.

## Review, leases, capacity and stop conditions

One fresh nonauthor `compiler_referee` is reserved for both the pre-execution gate and final frozen evidence review, total <=1,000 active seconds (up to 500 for source/preflight revisions and 500 for final). Review is read-only and returned to Luna by message. Keep only one R23 child assignment active/reserved at a time: current state has three pre-existing non-stopped assignment reservations and two review/integration slots remain reserved. Rust must stop before the referee begins; stop the referee before Rust resumes; Rust must stop before Lean is admitted; Lean must stop before final review. Reuse the same child identities only through explicit fresh-session resumption receipts. Do not release UNKNOWN capacity reservations or reuse the R17 handoff.

Total sprint envelope: 4,200 active seconds (Rust 1,400; Lean 1,400; reviewer 1,000; Luna 400); zero Astra. No descendants. Keep exact current-state leases; no directory-wide lease. Stop at a changed authority/dependency/semantic premise, identity falsifier, missing or mismatched lease, resource/time limit, unavailable pinned toolchain, unresolved reviewer rejection, or STOP. Preserve failure evidence; do not reinterpret it as closure.

Original parent, source/native correspondence, effect hygiene, soundness, principality, termination and production remain OPEN except for the precise premise this packet independently proves. A checked conditional theorem, source review, successful test or checkpoint is not whole-language closure.
