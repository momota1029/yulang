# R149 outcome: member state and decoder repair

## Accepted checkpoint

R149 is **bounded pass** for the proof-term repair and conditional source-characterization contract. The independent review found no major or minor correctness finding against those bounded claims.

The R118 patch changes only two proof terms in `NativePermissionDecoderR118.lean`; it leaves definitions, theorem types, assumptions, imports, and axioms unchanged. The targeted R118/R119 build passed on Lean 4.35.0. The complete axiom audit reports:

- R118 `contains_member`, `read_family_exact`, `read_permission_exact`, `unequal_coordinates`: `[propext]`.
- R118 `decode_member`, `post_state_is_not_prepare_input`: `[propext, Quot.sound]`.
- R119 `selected_retained_member`: `[propext]`.

The R119 result includes its explicit native-read, retained-permission-read, ordered-search, and consumer-indexed-read premises. It is a finite decoder theorem receipt, not source/native or parent-theorem closure.

## Source boundary

The concrete Support expansion executes under the exact active `RelationId`; it is a plausible owner for relation-qualified member state. A View-wide mutable field would merge distinct paths. The source contract also preserves combined inventory bounds, same-map FreshUse transport, replay ordering, attribution, collisions, failure behavior, and independent protections.

Two required source premises remain OPEN:

1. **INITIAL-STATE:** the pinned source has no constructor establishing each actual member's incoming inputs/protections, including latent operation members and Contribution paths.
2. **CONSUMER:** the reached allowance decision reads family membership only; it does not consume evaluated protections to suppress a Catch or continuation.

The independent reviewer accepts the conditional obligations but explicitly says they are not a complete implementation-ready construction. No Rust patch or semantic claim is promoted by R149. A reachable source counterexample was not established.

## Resources and gate

One targeted build took 4.441 seconds and the separate theorem audit passed. Existing `.lake` grew from 48,734,666 to 49,408,795 bytes (+674,129); fifteen generated files were authenticated and none deleted. No new environment, checkout, worktree, Rust build, or test was created or run.

Original H/A/B, full effect hygiene, source/native correspondence, whole-language soundness, semantic adoption, and production remain OPEN. Next work must establish the source-owned initial-state rule and actual protection-sensitive consumer before an exact Rust implementation lease is admitted.

Review: `tasks/agent-loop/history/effect-permission-member-state-decoder-20261102-r149-review.md`.
