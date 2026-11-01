# R145 — FreshUse shared-map support

## Fixed goal

At baseline `f634b2f426b6aef3e2dd602dab0a6dce3e1ad0dd`, determine whether the real `prepare_candidate_fresh_use` boundary supplies the pre-copy support and one shared scope/input remap needed to instantiate the existing native rename law for a single FreshUse. This is a source/proof bridge investigation, not a production repair.

## Exact scope

- Inspect `candidate_source.rs::ScopeInventory::fresh`, `candidate_context.rs` scoped-flow creation and acceptance, and the committed immutable blob for `candidate_scheme.rs::prepare_candidate_fresh_use`.
- `candidate_scheme.rs` has dirty quarantined working-tree content. Read it only as `git show HEAD:crates/yu-solver/src/candidate_scheme.rs`; do not inspect its working-tree bytes or diff.
- Establish the exact allocation cut and map domain/range; identify transformer, demand, and required incoming-state support; authenticate which single map reaches each coordinate and whether any allocation/re-entry/replay can intervene.
- Trace repeated FreshUse, replay, and failure boundaries. Do not treat `scope_origins` equality as evidence of injectivity.
- State the exact finite-support rename premise that follows, or the first missing owner/premise. Do not assume the source premise or close the parent theorem.
- Check for relevant additional production callers only in clean committed source paths.

## Deliverables and ownership

1. Luna/high source lane: `tasks/agent-loop/inbox/effect-permission-fresh-map-support-r145-source.md`.
2. Registered `lean_prover` lane: candidate `notes/theory/lean/YulangClosure/NativeScopeFreshMapR145.lean` and handoff `tasks/agent-loop/inbox/effect-permission-fresh-map-support-r145-proof.md`. Localize global injectivity to the union of transformer and incoming-state support; apply it only if the frozen source result proves its premises. Label the candidate unchecked.
3. One fresh independent review after both writers stop; review source ownership, allocation cut, finite-support theorem type and premise match. The initial reviewer violated the immutable-input boundary before reading this contract and froze a no-verdict deviation receipt at `tasks/agent-loop/history/effect-permission-fresh-map-support-20261102-r145-review.md`. It is not an acceptance artifact. The replacement reviewer’s sole output is `tasks/agent-loop/history/effect-permission-fresh-map-support-20261102-r145-review-r2.md`; the reviewer must read this contract and hash the frozen inputs before inspecting source, and must use only baseline committed blobs for source search.
4. Luna adjudication, outcome record, compact current-state update, and push only a coherent reviewed checkpoint.

## Limits

- Each author lane: at most 600 seconds. Independent review: at most 240 seconds. Total sprint cap: 1,620 seconds.
- No Cargo, Rust build/test, Lean/Lake invocation, generated artifacts, scratch/cache, new checkout/worktree, or environment creation.
- No edits to production source. Do not read, stage, or modify any dirty/quarantined paths. No speculative guard or repair.
- Keep original A/B claims, quantifiers, and whole-language gates OPEN. This packet cannot promote production behavior.

## Falsifiers and stop conditions

Stop with the first concrete source counterexample: an actual combined support colliding under the shared map, inconsistent maps/allocation cuts across coordinates, missing state-side rename, or an uncovered real caller. An abstract two-ID example alone is not a source counterexample.

If no source premise authenticates the required support inclusion, report that exact owner and do not apply the conditional theorem as a source result. No new repair is authorized without a specific defect and separate gate.

## Checkpoint rule

Commit only the exact contract, admitted records, frozen source/proof/review handoffs, and outcome. Recompute hashes after review; stage explicit paths only. Push a coherent normal fast-forward range. Do not claim execution, kernel checking, source refinement, or parent-theorem closure without the corresponding evidence.
