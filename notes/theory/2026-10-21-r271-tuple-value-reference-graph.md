# R271 — Tuple references in the candidate Value graph

Status: implementation investigation in progress; provisional and unreviewed.

## Parent application

R270 now visits tuple children for candidate constraint generation and captures/reconstructs ordered Tuple nodes. R256 independently located another source-owner gap: `candidate_value_graph::Graph::retain_source` does not descend into Tuple children and its expression-fragment graph has no Tuple fragment. A Name under a tuple can therefore be absent from the source Value-reference relation used by SCC/intrusion decisions, even when candidate type constraints retain it.

This packet repairs that prerequisite only. It does not make the candidate solver a public type checker or close any R149/sample/proof gate. No independent review was performed under the user's solo-work instruction.

## Implementation and evidence

`Graph::retain_source` now visits each Tuple child in reverse worklist insertion order, so the LIFO traversal processes children in source order and assigns the same owner that the parent expression received. The fragment graph allocates an auxiliary fragment for each Tuple expression and connects the expression result to that fragment, then the fragment to each child fragment in source order. It does not flatten nested Tuple identities.

- `tuple_fragments_retain_direct_and_nested_name_references` passes for `(a, (b, a))`; both outer and inner expression fragments reach the exact parameter Values `{a, b}`.
- `tuple_child_references_keep_nested_initializer_owner` passes for a local tuple initializer. Its local Value reaches `x`, while the enclosing module root reaches only the local Value.
- `tuple_contained_module_reference_contributes_to_semantic_scc` passes for `f = (g,)` and `g = f`; after sealing, the module Values for `f` and `g` are in the same semantic SCC.
- New fragment vertices use the existing auxiliary adjacency storage and `edge()` accounting; `Graph::bytes()` already includes those capacities and edge deltas.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib tuple_` passes (9 tests), including the R270 capture/effect/FreshUse cases and R254 ordered comparison/index diagnostics.

## Limits

No public scheme, runtime, import, host request, sample, soundness, principality, or production evidence follows from a Value-graph repair. Full solver-suite evidence is not claimed. R149 and all parent proof gates remain open.
