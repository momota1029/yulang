# R274 — ordered Tuple candidate graph rendering

Status: provisional diagnostic-rendering packet; unreviewed. R149's public type display and all sample/proof gates remain OPEN. Contract revision 1 adds compatibility handling for the legacy F5 closed-scheme adapter after the public Tuple view variants exposed non-exhaustive matches.

## Parent application

R270/R271 retain ordered Tuple structure in the candidate graph; R273 adds ordered positive and negative Tuple constructors to the closed-type API. `tools/inference-playground/src/render.rs` still traverses only fixed Function children, so direct Tuple nodes and nested children are not shown by the candidate graph renderer.

This packet makes that existing diagnostic view expose retained Tuple structure in source order. The graph retains unresolved row/effect premises and is not a public closed scheme. The F5 adapter now walks Tuple children but returns its explicit unavailable error at Tuple reconstruction; it does not flatten or fabricate a term. No source typing, principal type, R149 Types pane or production claim follows.

## Evidence

Verification: `cargo test -p yu-playground --lib candidate_graph_renderer_exposes_nested_tuple_children_in_order -- --nocapture` passed (1 test; package compiled). `git diff --check` passed. Existing `yu-hir` and `yu-solver` warnings appeared during the build and are outside this packet's ownership. The renderer remains provisional and unreviewed under the user's solo-work instruction.

## Implementation result

`render.rs` now interns and prints Tuple children in their observed order, preserving nested Tuple nodes. The focused regression covers direct and nested source tuples. `yu-solver/src/lib.rs` now visits positive and negative Tuple children in the legacy closed-scheme adapter and returns `SolveAvailabilityError::IdentityExhausted` when reconstruction reaches a Tuple, since F5 has no approved product-of-alternatives constructor. The public solved-root summary reports a Tuple as `Unknown`.

This closes only the R274 diagnostic renderer implementation slice. R149 Types/Console, Yulang2 sample execution, F5 Tuple reconstruction, source/native correspondence, proof and production remain OPEN.
