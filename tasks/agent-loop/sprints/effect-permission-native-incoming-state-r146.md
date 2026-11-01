# R146 — native incoming state and allocator invariant

## Fixed goal

Starting at pushed baseline `3560df97dab02744da10e897c73c1cf94118f4ee`, investigate the two R145 source-application premises: (1) the global allocator/support invariant that keeps relevant IDs below each FreshUse pre-copy cut, and (2) the actual consumer state corresponding to `NativeScopeTransformer.State`, including whether the same map renames that state. Identify the earliest missing owner or a reachable production counterexample. No production repair is authorized by this packet.

R145's exact result and limitations are in `tasks/agent-loop/history/effect-permission-fresh-map-support-20261102-r145-outcome.md`; its finite-support candidate remains unchecked.

## Exact scope and source boundary

- Source lane follows every relevant committed producer and propagation path for scope/input IDs: initial demand/release creation, FunctionPort conversion, composition/replay, previous copies, FreshUse callers, and failed-attempt handling. Determine whether all transformer/demand coordinates at entry lie below inventory counts and where the invariant is or is not enforced. Include `candidate_intrusion.rs` and `lib.rs` where they own construction or rollback. Inspect `shadow_apply.rs` only from the baseline Git object: its observation API evaluates from an empty state and is research-only, so it cannot stand in for the real Catch/effect consumer.
- Source/proof lane identifies the real consumer state, its relation to the native `State`, and whether that state is transported using the same FreshUse map. Distinguish empty observer input, accumulated transformer prefix, demand, and `use_instance`. Do not introduce a new state model or add another unchecked Lean file. If no corresponding state exists, name that boundary precisely. A baseline locator found `candidate_apply_effect` in `candidate_extrusion.rs`, called by the admitted context executor; inspect that actual handoff and only the effect operations/Catch handling it invokes in `candidate_effect.rs`. Determine whether scope/input IDs, transformers, and protections reach actual effect decisions or Catch subtraction, and where same-map transport and allocation bounds would be required. This is a narrow input amendment: `candidate_effect_kernel.rs` is absent at baseline, and `candidate_receiver.rs` is not needed absent a demonstrated path through it.
- Use only immutable source objects at the baseline commit, especially for dirty working-tree `candidate_scheme.rs`. Source searches must be baseline-qualified (`git show <baseline>:<path>` or `git grep <baseline> -- ...`); do not search working-tree source with `rg`, `sed`, or equivalent.
- Relevant committed files: `candidate_source.rs`, `candidate_context.rs`, `candidate_scheme.rs`, `candidate_scope.rs`, `candidate_intrusion.rs`, `lib.rs`, `shadow_apply.rs`, `candidate_extrusion.rs`, and the reached portions of `candidate_effect.rs`; `NativeFreshScopeTransport.lean`, `NativeScopeTransformer.lean`, the R145 candidate/handoffs, and the governing compose construction note.
- No source edits, speculative guards, environment/checkouts, scratch/cache, Rust/Cargo/tests/builds, or Lean/Lake execution.

## Deliverables and ownership

1. Luna/high source lane, max 600 seconds: `tasks/agent-loop/inbox/effect-permission-native-support-invariant-r146-source.md`.
2. `prover` source/proof lane, max 600 seconds: `tasks/agent-loop/inbox/effect-permission-native-state-correspondence-r146-proof.md`. Identify the authentic incoming-state consumer and its map correspondence or state the precise absence; no assumed model.
3. One fresh independent reviewer, max 240 seconds, after both writers stop: `tasks/agent-loop/history/effect-permission-native-state-support-20261102-r146-review.md`. Reviewer must first hash the admitted frozen inputs, then read only committed baseline source. Any input-boundary deviation means stop with no verdict.
4. Luna adjudication, outcome, compact state, and push only a coherent reviewed checkpoint.

## Falsifiers and limits

Concrete counterexamples include a supported production path that carries an ID at or above the pre-copy cut into transformer/demand/state support, mixes allocation cuts/maps, reuses stale IDs after failure, or omits a real state-side rename. Abstract numeric examples alone are insufficient.

This packet cannot close the original Simple-sub A/B claims, the full source/native theorem, or production readiness. Keep all those gates OPEN unless their full governing contracts are met.

## Resource and Git rules

- Source: 600 seconds. Proof: 600 seconds. Review: 240 seconds. Total cap: 1,620 seconds; no budget reset for prior work.
- No Astra, Cargo, Rust/Lean execution, build, tests, scratch/cache, new environment, checkout or worktree.
- Preserve all dirty/quarantined working-tree paths. Primary stages explicit paths only, verifies the full outbound range and performs normal fast-forward push only.
