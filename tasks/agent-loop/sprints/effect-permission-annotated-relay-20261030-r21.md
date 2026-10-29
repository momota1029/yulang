# Sprint EFFECT-PERMISSION-ANNOTATED-RELAY/20261030-r21

Status: ADMITTED; conditional source/native evidence only  
Branch baseline: `4bb23ea31e5bb434313e073df1d68f477b54326f`  
Authority: continuing Yulang Rust/Lean inference, executor soundness, effect hygiene, principality and termination goal  
Decision: R20 sprint-end selector recommendation, admitted by Luna  

## Parent and fixed scope

The original Simple-sub A/B claims, source domain, quantifiers, accepted semantics and all existing parent gates remain unchanged. This sprint targets one approved callback annotation path and its approved computation-form companion. It grants no compiler-semantic or production authority.

The selected callback case is the exact policy example in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1.1:

```yu
act signal:
    our ping: () -> int

my relay(cb: () -> [signal] int) = catch cb() {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping
```

The approved companion is `tools/inference-playground/examples/original-suffix-outer-receiver.yu`: a `[signal]` annotated computation is handled by `relay` while a distinct `write` contribution flows outward to `receive`. It is a separate source occurrence and may not supply callback identity or permission premises to the callback case.

## Exact outcome

Authenticate the concrete chain for each selected source independently:

1. The source annotation occurrence and resolved owner/formal/path construct the actual permission object.
2. The same source call transports the actual `signal` contribution through the correct function/callback or computation effect port.
3. The exact `signal` event reaches the exact local `Catch` under the same relay invocation and owner; matching by family/type alone is insufficient.
4. The callback case returns its approved `1`. In the companion computation case, `signal` is handled locally and the same distinct `write` contribution reaches the outer `receive` path rather than being removed by the inner relay.
5. Apply existing Lean source/hygiene/transport results to these authenticated constructors. Prove permission, inflow, owner/scope, selection and surviving contribution separately. If a constructor or consumer edge is absent, return that exact first missing edge and leave the corresponding theorem premise OPEN.

Do not join events from different sources, calls, arenas or handler owners. Do not infer flow from equal rows, families, values or expected results. Tag every trace event with a unique probe ID, source hash, source occurrence, invocation ID and relevant owner/event IDs; validate ordered typed records, not whole-log string searches. The probe must reject an event from a sibling invocation even if its family matches. The R20 finding about unobserved `Session::take` is outside this packet's journal model; do not infer a journal transition here.

Independent falsifiers: wrong annotation/formal owner or structural path; permission not projected at the claimed endpoint; an event not descended from the supplied callback/computation; an event associated with another invocation; a Catch selected by same-family substitution; `signal` not consumed by the selected local Catch; `write` disappears before the outer consumer; or a Lean theorem assumes a compiler/source bridge not authenticated by the trace.

## Rust lane and exact outputs

Use the isolated worktree `isolated/ep-annotated-relay-r21/project` at the baseline above. It is initialized from that commit; the three frozen main-tree inputs `candidate_effect.rs`, `candidate_scheme.rs` and `shadow_apply.rs` are overlaid byte-for-byte to provide a build-coherent source snapshot. All edits and the one execution stay in this worktree. Main-tree files and quarantined paths remain read-only.

Test-only or otherwise provisional instrumentation may record source/action identity, annotation/formal permission construction and projection, the callback/computation effect contribution, local Catch construction/selection and the surviving outer contribution. Keep each event structured and linked to the same invocation. Preserve complete argv, stdout, stderr, exit status, resource measurements and machine-readable traces in the single JSON receipt. The one Cargo invocation must exercise the approved callback source and the companion write-residual source through the ordinary candidate path; it may not change fixtures or expected output. No Cargo retry.

Exact Rust write leases:

- `isolated/ep-annotated-relay-r21/project/crates/yu-solver/src/candidate_effect.rs`
- `isolated/ep-annotated-relay-r21/project/crates/yu-solver/src/candidate_scheme.rs`
- `isolated/ep-annotated-relay-r21/project/crates/yu-solver/src/candidate_source.rs`
- `isolated/ep-annotated-relay-r21/project/crates/yu-solver/src/lib.rs`
- `isolated/ep-annotated-relay-r21/project/crates/yu-solver/src/shadow_apply.rs`
- `isolated/ep-annotated-relay-r21/project/crates/yu-solver/src/term.rs`
- `isolated/ep-annotated-relay-r21/project/receipts/annotated-relay-receipt.json`
- `tasks/agent-loop/inbox/effect-permission-annotated-relay-r21-rust.md`
- `isolated/ep-annotated-relay-r21/project/build-target`

No directory-wide lease is granted. Manifests, lockfiles, tests/fixtures and all other source files are read-only. No Git operations or descendants.

## Lean lane and exact outputs

The Lean lane uses Lean 4.35.0 in `isolated/ep-annotated-relay-r21/lean-scratch`, reuses pinned existing theorems without weakening them, and writes only:

- `notes/theory/lean/YulangClosure/FormalPermissionAnnotatedRelay.lean`
- `tasks/agent-loop/inbox/effect-permission-annotated-relay-r21-proof.md`

Construct a relation for the exact owner/source/event chain and apply existing results only after their actual hypotheses are established. Use the frozen source trace only after the Rust lane freezes it. A projection theorem without a concrete instance, or an assumed callback-to-Catch bridge, fails the outcome. Capture complete theorem types and per-root axioms. At most two serialized Lean audits total, each ≤90 seconds and ≤120 seconds combined, with ≤1 GiB RSS each.

## Review, resources and boundaries

After both lanes freeze, a fresh nonauthor `compiler_referee` reviews all source deltas, receipts, trace identities/event order, proof statements, theorem application and complete axioms. The primary authenticates hashes, adjudicates, updates `current.json`, writes outcome/evidence and alone stages, commits and pushes a coherent checkpoint.

Total envelope: 2,400 active seconds (Rust 900, Lean 900, review 300, primary 300); zero Astra; at most two concurrent producers and one later reviewer. One serialized locked/offline Cargo test invocation ≤180 seconds, one CPU, ≤2 GiB RSS and ≥4 GiB available RAM. No production repair, expected-output change, original-parent closure, semantic revision or cutover follows from this packet.
