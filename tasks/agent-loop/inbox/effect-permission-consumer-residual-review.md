# Independent review — EFFECT-PERMISSION-CONSUMER-RESIDUAL-20261028/r1

Reviewer: `/root/effect_permission_consumer_residual_review` (`compiler_referee`), distinct from both authors. Read-only receipt; no files, Git, builds, Cargo, tests, Lean/Lake, or descendants.

## Verdict

**Do not accept Rust handoff revision 1's outcome class “fixture expectation defect.” Retain outcome (4): the source-demand/provider and extraction bridge is not established.** The exact fixture passes a stateful callback to `f` and syntactically demands `left 0`, but does not establish that the result bound to `left` is that input callback. `case` projects the result of `f (...)`; the function body recursively calls `f pair`. The source path therefore does not yet join the input provider to the returned result. This is not a proof that the expectation is false, that a solver defect exists, or that the callback effect is absent.

The Rust handoff cites `notes/design/2026-10-10-local-self-recursive-binding.md`, which governs a *local* binding/HirLocalId. The fixture's `my f` is module-level and exported through `SourceRootId::Definition`; the cited local rule alone cannot authenticate this recursive route. `candidate_source.rs:1444–1488` constructs tuple-pattern bindings from the scrutinee endpoint, while `candidate_source.rs:1869` records Apply argument and result endpoints separately. Establishing the exact module-definition recursion/call correspondence remains open.

## Native and proof evidence

- Independently rehashed all six supplied artifact pins: contract `a2d8b9a7aef7a142559370d9f5bd10d8fe0ee6d68f9bb4938d4167a11a86da7e`; candidate source `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`; unchanged candidate scheme `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`; Rust handoff `c873113f179634be7f9e29e90eea95f717bd50f4ceb314c239379e488ce8b1fe`; proof handoff `7437b723ac103af620dd35dd348ec78fbd82c176eb9893b4acf0578da9b817db`; prior conditional Lean source `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84`.
- Invocation 1 inventory `a1785f08ca2fc0a2fbdae0e1dd1d1345e41c8d2db36180bc912f163def7560f0` contains 280 unique files; zero missing paths or size/hash mismatches. Frozen argv, launcher, stdout, stderr, status, and time hashes match the handoff.
- The test reached the unchanged consumer assertion at `candidate_effect.rs:3428`; the new test-only census reports `consumer-returned-effect-forms=[]`. Exit 101; wall 59.64s; peak RSS 1,671,032 KiB; zero swaps. This proves only that this observation found no `CandidateGraphEffectOperand` forms in this exported answer graph. It does not interpret absent operands as absent source effects.
- The original `r != q` assertion remains in the original unequal test. The isolated entry selects the same fixture with that assertion skipped and leaves the original consumer predicate in place. The census is inside `#[cfg(test)]`; this review did not authenticate the full source delta against the pinned predecessor hash.
- The fixture has no Catch/handler. `formal_effect_permissions` exports formal Permission metadata; it does not perform subtraction. Adopted N-Subtract-Elim requires actual demand/input, same-contribution transport, a typed local subtraction consumer, scope/eligibility, and selecting/removing evidence. Those operands are not established here.
- The proof handoff appropriately constructs no new Lean theorem and performs no Lean invocation. The cited `OriginalEffectHygiene` results concern publication/replay provenance, not contribution inflow or residual preservation. The inspected projection audit receipt records prior `sorryAx` failures and an unexecuted repair; no accepted residual theorem was shown.

## Review limitation

**Major provenance limitation:** no separate baseline byte file was available. In-memory reversal of the isolated entry, census/state-ID lookup and helper flag split did not reproduce pinned predecessor SHA `6f20ac00deb2f5a84f57a0cf54cf9ceb64f2de5a90d15cc371240d9de68dfa3b`. The reviewer therefore cannot certify the whole source delta as test-only or make a complete source-diff assessment. This is unresolved provenance, not evidence of a production-path change.

No new solver or source-language defect is established. Original parent/H/A/B, consumer hygiene, source/native, termination, principality, and production remain OPEN. Preserve the handoff and raw failure; do not change the protected expectation. The next proof/source step is the exact module-level recursive Definition/Call/result-to-pattern route plus a same-contribution extraction interpretation, or an exact first missing transition.
