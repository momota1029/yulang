# R271 — retain Tuple children in the source Value graph

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 playground goal; R149 Types/Console are the current end-to-end increment, not the whole goal.
Baseline: `37c1745bc8716e4b2bb4a534aaaa435af75dae84` on `research/simple-sub-intrusion`.
Authority: approved ordered product semantics in `notes/design/2026-10-20-r149-types-console.md`; source-owner obstruction in `notes/theory/2026-10-21-r256-tuple-source-runtime-obstruction.md`; R270 tuple candidate path.

## Outcome

Make the candidate Value-reference graph retain references beneath every source Tuple, including nested Tuple elements, so source reachability and SCC/intrusion input agree with the LocalSource tree. Preserve exact semantic Value identities and nested-initializer owners. Keep traversal iterative and linear in expression nodes plus tuple edges.

Success evidence: direct and nested tuple expressions expose all child Name references through expression-fragment reachability; nested local initializer owners remain separate; recursive/reference SCC behavior includes tuple-contained uses; focused source Value-graph and tuple solver tests pass.

Falsifiers: a tuple child Name is absent or attributed to the wrong owner; nested tuples flatten into another expression's fragment; source order changes; SCC membership changes when the tuple constructor is merely traversed; resource accounting omits newly retained edges/fragments.

## Exact write paths

- `crates/yu-solver/src/candidate_value_graph.rs`
- this contract
- `notes/theory/2026-10-21-r271-tuple-value-reference-graph.md`
- `tasks/agent-loop/inbox/20261021-r271-tuple-value-reference-graph.md`
- primary-owned `tasks/agent-loop/current.json`

No public type, parser/HIR semantics, runtime, import resolver, fixture, production promotion, or parent-proof closure in this packet. It repairs a necessary solver input before tuple lifting to public schemes/runtime.

## Method and limits

The current `retain_source` traversal assigns source expression owners and edges direct Name references. Its fragment graph composes Name, Apply, If and Sequence references, but omits Tuple in both child traversal and fragment composition. Add ordered child work using the existing `LocalSourceIndex` vector and compose the Tuple expression fragment with child fragments. Preserve the block-initializer owner boundary. Do not create a source Value or SCC vertex merely because a tuple constructor exists unless existing expression identity rules require it.

Budget: 600 seconds, no carryover, one heavy Cargo process. The user requires solo work, so no sub-agents or independent reviewer will be used; keep all evidence primary-only and provisional. Commit and push a coherent checkpoint. Public closed schemes, runtime ordering, authentic library resolution, host continuation, R149 samples, Simple-sub/evaluator A/B, soundness, principality and production remain OPEN.
