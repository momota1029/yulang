# Sprint EFFECT-PERMISSION-ARENA-EVENTS/20261029-r16

Status: admitted by Luna under the unchanged ongoing Simple-sub inference/executor goal after the R15 `CLOSED_COMPLETE_CONDITIONAL` result and sprint-end selector recommendation.

## Baseline and authority

R15 provides the conditional `with_term_events` control model and a successful Lean 4.35.0 audit of 38 roots. Its artifact is pinned at SHA-256 `73bface0963c65eb76933ff8116594b161e78f1733b66e6be25cc174d1eb2dd7`; its aggregate audit receipt is `02eca0b48d30dd438a696cab015975bdcc89cc997e6e41df1108b453cb28378b`. R12/R13 declarations and the original inference/executor goal remain unchanged. R16 adds a checked source-directed event derivation for only live-variable and positive/negative function constructors. It does not modify Rust behavior or establish the original parent theorem.

Pinned source handoff: `tasks/agent-loop/inbox/effect-permission-arena-events-r16-source.md`. Relevant current source hashes and the unresolved initial-buffer, allocator, sampler, and execution premises are recorded there. `candidate_effect.rs` is read-only and differs from HEAD; this remains an input provenance/Git blocker, not authority to alter or stage it.

## Fixed outcome

Create `YulangClosure.FormalPermissionArenaEvents` as a source-directed derivation of the ordered events that the R15 control model consumes for the three named constructor families. The model must derive events from constructor mode, cache hit/miss, route-journal presence, page-needed status, capacity-change outcomes, and failure stage. It must preserve an explicit preexisting event prefix. It must not accept an arbitrary final event list or assume that the buffer starts empty.

Prove the exact append order and bound: at most six newly appended events, and `prefix.length + appended.length ≤ 6` for executions that do not overflow the source's fixed event buffer. Reserve capacity changes are recorded before reserve error propagation. PageBacking is recorded only after successful page creation/publication. Cache hits and function-child validation failures emit no new events. Constructor failures preserve all earlier events. State precisely which allocator, snapshot, buffer-provenance, page-identity, sampler, and actual-execution facts remain assumptions.

Audit the inherited 38 R12/R13/R15 roots together with every new public theorem root, printing fully qualified theorem types and complete axiom reports. Do not treat the conditional R15 roots as source/execution closure.

## Lanes and exact permissions

- Proof owner: one fresh registered `lean_prover`, 600 seconds. Write only `notes/theory/lean/YulangClosure/FormalPermissionArenaEvents.lean` and `tasks/agent-loop/inbox/effect-permission-arena-events-r16-proof.md`.
- Source owner: primary Luna, read-only on Rust/Lean sources; write only the frozen R16 source handoff above. Source analysis is complete.
- Independent review: fresh nonauthor `compiler_referee`, 250 seconds, only after the complete pinned audit passes; write only `tasks/agent-loop/inbox/effect-permission-arena-events-r16-review.md`.
- Primary Luna: 150 seconds for contract/manifest/evidence, at most two primary audits, review adjudication, and closeout.
- Total sprint envelope: 1200 seconds. Zero Astra and zero descendants.

The proof worker may not alter theorem scope, source inputs, the R15 artifact, Lean configuration, Rust code, or audit roots. No tests, Cargo, runtime instrumentation, package updates, or Git staging/commit/push are authorized in this sprint.

## Audit and resource limits

Use the pinned Lean 4.35.0 toolchain in a fresh isolated project copy under `/tmp/yulang-effect-permission-arena-events-20261029-r16/`. Keep one primary-owned build/cache and run serially with `-j1`; cap each of at most two separate audits at 90 seconds and their combined wall time at 120 seconds. Preserve exact input-copy receipts, complete stdout/stderr, exit status, resource record, fully qualified root types, and transitive axiom lists for every invocation. No third audit or diagnostic probe is permitted.

## Falsifiers and stop conditions

Stop and return the exact counterexample/obstruction if the derivation omits or reorders an event, loses an event retained on a failed reserve, records PageBacking before publication, assumes an empty initial buffer, hides fixed-buffer overflow, or needs an invented native identity. Also stop if the exact proof paths conflict, the worker/audit budget expires, or an inherited root fails. A failed audit is not itself a mathematical counterexample.

The primitive reserve/allocation behavior, snapshot availability, initial buffer provenance, sampler execution and native authenticity remain explicit. Rust execution correspondence, source-to-generated call correspondence, the original parent, hygiene, consumer residual, soundness, principality, termination, and production remain OPEN.
