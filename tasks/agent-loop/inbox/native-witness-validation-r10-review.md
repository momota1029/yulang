# NATIVE-WITNESS-VALIDATION/r10 review

Verdict: **CLOSED_INCOMPLETE.** Accept the final Lean conditional artifact; reject Rust witness success.

**BLOCKING — exact Rust fixture fails before witness assertions.** Frozen `isolated/native-witness-frame-repair-r9/crates/yu-solver/src/candidate_scheme.rs:8019` unwraps `session.execute()`, which returns `ReceiptMismatch`. Retained Cargo output establishes exactly one test execution: 0 passed, 1 failed. Restoration, transport mutation and rejection assertions are never reached. This violates R10’s required fixture completion/pass predicate. The observed failure alone does not identify its deeper cause.

Minimum closure: separately authorize diagnosis at the actual receipt owner, preserve the exact fixture and assertions, independently review frozen repair bytes, then obtain fresh successful execution. R10 authorizes no retry.

Final Lean revision `5e44687e7d59f1ccac2da6361befe66bc7a19ed3744d0dc4bc029ea9c48e61f6` repairs constructor ambiguity at lines 199, 208, 215, 217, 225 and 261 through explicit `Effect.sink`. Byte comparison confirms unchanged definitions, effect ordering, prefixes, seven theorem statements/bodies, `WriteAll` and exact `extract`.

All seven fully printed declarations under `YulangClosure.NativeExternalEffectFrameR8` passed complete transitive audits:

| Declarations | Axioms |
|---|---|
| `effect_frame`, `effect_keeps_replay_undo`, `effects_frame`, `every_prefix_frame` | None |
| `callback_frame`, `observed_capacity_frame`, `native_frame_conditional` | `[propext]` |

Final Lean exit 0, 2.8162s, sampled RSS 606,412,800 bytes. Lean-1 remains failure evidence: exit 1, ambiguous `.sink` at line 208, three downstream `sorryAx` audits.

Cargo exit 101, 42.3974s, sampled RSS 1,866,809,344 bytes. Both checks used the exact contracted commands and stayed within resource limits.

Authentication completed before source body reads: contract `280fb2e5c37c18e55ae139a449994791605fd20a83442a88b6a91676f5bc9e65`, manifest `36e54c93c486fb15ba1a01af15104216031335f5bd6c39d6b62c624e1513e9bd`, 89 entries / 69 unique paths, zero mismatches. All 89 pins were reauthenticated before both initial gates. Final Lean/handoff hashes and all 12 R10 log hashes match the primary’s frozen values.

No additional major or minor compiler correctness finding. The local Rust binding repair addresses its compilation cause, but does not repair the newly observed execution failure. `extract`, std I/O realization, native/source correspondence, original `InferenceSoundness`, effect hygiene and production remain OPEN.

Reviewer `/root/native_witness_validation_r10_review` STOPPED read-only; no edits, checks/builds, Git, scratch outputs or descendants. Primary persists this receipt.
