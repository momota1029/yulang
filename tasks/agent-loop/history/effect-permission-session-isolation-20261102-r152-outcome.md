# R152 outcome — session-owned permission binder

Sprint: EFFECT-PERMISSION-SESSION-ISOLATION/20261102-R152, contract revision 1.
Disposition: ACCEPT the reviewed candidate for checkpoint as an unapplied research artifact only. No source file was applied or promoted.

## Before

The frozen three-file diff at baseline `225c5519943fc490c3d5620683918674f4f6afd5` removed the session-owned binder boundary. Its independent route/store/state/registration arguments admitted a conditional cross-session join when source IDs and local numeric ordinals coincide. Separately, dirty `candidate_receiver.rs` changes remove owner/batch/live-state, provider/arm/operation and permission-origin checks; that diff remains excluded. Dirty runtime files remain quarantined.

## Candidate and review

The corrected candidate restores the session-owned scheme wrapper and preserves registration, context-origin, exact Lambda/recipe, source HIR, raw-entry, canonical representative, and mapped native-row checks. It removes the unconditional provider-equals-constructor-owner predicate only where the exact registration/source-Lambda construction witness supports returned/local Function ownership. The candidate does not assign handler/provider/Catch-arm authority.

- Frozen input patch: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152-input.patch`, SHA-256 `643d75e8e8435253a8606af7800134c28ce8eb74c86b1880ab169d5b8891bd1a`.
- Candidate patch: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152.patch`, SHA-256 `3a5a2f73b75cd3caaecae7fbb0f36c60b9c33492502fe531f3e7237fdb9838c4`.
- Source handoff: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152-source.md`, SHA-256 `a18dc477d33e639b002cd22d4825e56640c7ab6c25b0a1f4eebc61974c58094c`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152-proof.md`, SHA-256 `ac040d9ad233fce3ac29b9e5fe3b092261d30a7003bf41238f96e151fe9c0b39`.
- Independent review: `tasks/agent-loop/history/effect-permission-session-isolation-20261102-r152-review.md`, SHA-256 `06d4aef333b67986454ce234a7a57c335549394c5b5fb90ab6a1e6f150ac2914`.

The fresh compiler referee found no blocking, major or minor compiler-correctness issue in the exact candidate and accepted checkpointing it as an unapplied research artifact. Review was static and used committed baseline blobs. No build, tests, Lean, scratch, cache, environment, checkout, worktree or Git operation was run by proof, implementation or review lanes.

## After and remaining boundary

The prior cross-session argument-joining interface is removed from this candidate. The patch is not applied, compiled or tested. R152 does not close complete source/native correspondence, returned/local source coverage, INITIAL-STATE, CONSUMER, soundness, principality, termination or original A/B obligations. The excluded receiver diff still needs a separate owner-preserving analysis and review. No theorem or production readiness is claimed.

The next in-scope action is assigned at the R152 boundary after checking the fresh dispatcher result. Luna remains sole Git integrator and must inspect the exact outbound range before push. Only the listed R152 contract, admission, frozen input, candidate and handoffs, review, outcome, current state and current navigation card are intended for this checkpoint; unrelated dirty and untracked files remain untouched.
