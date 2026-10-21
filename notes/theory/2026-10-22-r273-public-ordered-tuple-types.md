# R273 — public closed ordered Tuple nodes

Status: provisional `yu-types` implementation checkpoint; primary-only and unreviewed. R149 and all end-to-end sample/proof gates remain OPEN.

## Design correspondence

R149 requires arbitrary finite positional products. The unified design plan §3.3 calls for one ordered product constructor across constraint generation, capture, public types and evaluation; R254 fixes exact arity and same-index child correspondence in the live solver. `yu-types` currently exposes only scalar/function constructors plus union/intersection child ranges, so closed scheme views cannot yet name a product.

This packet adds a distinct positive and negative Tuple constructor across the existing closed arena pipeline. Tuple child spans reuse the established checked ordered child lanes, but remain semantically distinct from Union/Intersection. This is an API/value-construction slice only; it does not connect candidate graph export into this arena.

## Implementation and evidence

`IndexedPositiveNode` / `IndexedNegativeNode`, draft constructors, planned/permanent arena nodes, and positive/negative borrowed views now carry distinct ordered Tuple spans. The existing child lanes retain checked reservation, length validation, commit ordering, rollback, and byte accounting. Indexed traversal visits every tuple child before publishing the parent. `alpha_eq` compares tuple children positionally and preserves arity.

- `indexed_positive_and_negative_tuples_preserve_order_and_arity` verifies both polar views, heterogeneous ordered children, reordered and one-element non-equivalence, and malformed-span rejection.
- `draft_tuple_constructors_preserve_nested_positive_and_negative_views` verifies nested 3-element/2-element structures in both polarities.
- `cargo test -p yu-types --lib`: 41 passed, including existing indexed failure injection, atomic rollback/retry, capacity accounting, and small-stack depth tests.
- `cargo check -p yu-types` passes. `python3 tools/agent_sprint.py check` and `git diff --check` pass. Only the existing two `yu-hir` provenance warnings appeared in these package checks.

Public type display from accepted Yulang source, candidate graph export into this arena, source/native correspondence, soundness, principality, R149 sample outputs and production remain OPEN. No independent review under the user's solo-work instruction.
