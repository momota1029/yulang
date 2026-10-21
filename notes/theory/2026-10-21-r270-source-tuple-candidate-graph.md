# R270 — source tuple candidate inference result

Status: provisional implementation checkpoint; primary-only and unreviewed.

## Implemented

`LocalSourceForm::Tuple` now retains its ordered child endpoints and each child's computation-effect component in one candidate recipe. Admission creates a positive native tuple term, constrains it against the expression's negative value component, and records one effect edge per child into the tuple expression's effect row. Tuple effect fact slots use checked `u32` IDs so their namespace does not stop at 255; existing byte-sized source slots remain supported.

Candidate graph capture records tuple polarity and ordered child node indexes in a separately accounted backing vector. Fresh reconstruction walks those children in order and rebuilds a positive or negative native tuple term. Graph inspection exposes tuple children as a non-allocating exact-size iterator. The term storage resource assertion now accounts for tuple backing capacity and payload separately from the six fixed Term lanes.

## Evidence

- `shadow_apply::tests::source_tuple_is_retained_as_ordered_candidate_graph_node` passes for source tuples of arities 1, 2, and 3. The arity-2 and arity-3 values pass through polymorphic `id`, exercising graph freshening. The nested `(1, (true, "x"))` export contains both tuple nodes, and the outer tuple's second child row reaches the inner tuple bound. A direct `(1, true)` export also ties the first child row to `IntPositive` and the second to `BoolPositive`, detecting dropped or reordered source child constraints.
- `candidate_scheme::authentic_demand_capture_tests::tuple_fresh_use_reconstructs_each_captured_child_in_order` passes. It inspects the retained terms created by an actual module Name FreshUse route and checks each reconstructed tuple term's elements against the corresponding captured child-node term at every offset; both nested tuple nodes are reconstructed.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib tuple` passes (6 tests), including ordered tuple term polarity/duplicates, R254's indexed mismatch/arity behavior, candidate tuple source/effect/export and nested FreshUse evidence.
- `shadow_apply::tests::source_tuple_child_effect_is_admitted_to_tuple_computation_row` passes for `(io::tick(), 1)`. The first tuple child's retained provenance has Effect terms on both sides of its relation into the tuple computation row.
- Existing `f5b_ordered_tuple_comparison_keeps_positions_and_reports_arity_mismatch_at_root` passed during the full feature-enabled run before that process encountered a stack overflow.
- Focused feature-enabled source tuple tests and `cargo check -p yu-solver --features shadow-apply-candidate` pass.
- `python3 tools/agent_sprint.py check` passes. `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'` passes (57 tests).
- `git diff --check` passes.

## Static source-order correspondence audit

The source-to-graph order path is explicit in the current implementation:

1. `yu-hir` constructs `LocalSourceForm::Tuple.elements` by iterating the syntax children in their retained order. Its existing source-carrier test checks the child values, ranges, and occurrence ordinals in increasing source order.
2. `candidate_source` iterates those `LocalSourceIndex` values without sorting. At each index it appends the corresponding `endpoints[element]` and `positions[element].effect` to parallel vectors. The retained tuple recipe therefore carries one value endpoint and one computation-effect endpoint per source position.
3. `shadow_apply` builds the positive tuple term by iterating `elements` in vector order. The per-child effect constraints use the same `element_effects` order, with checked local slots `index + 1`.
4. Capture reads the ordered tuple term view and writes child node indexes at `start + offset`. FreshUse reads exactly that stored range and rebuilds the positive or negative tuple by iterating the range in order.

This closes the implementation-level ordering correspondence for the stored tuple term and child-effect edges. The source child index itself is not retained as a separate field after endpoint selection; the parent occurrence plus the ordered endpoint/effect vectors encode that correspondence.

The first nested-export assertion exposed an actual omission: the source `Visit` worklist handled sequences, applications and grouped expressions, but had no Tuple arm to visit tuple children. The outer candidate recipe still referenced child components, which made shallow arity checks pass while nested tuple recipes and child expression constraints were never emitted. Adding the Tuple arm schedules children in reverse onto the LIFO worklist, so they are processed in source order before the parent's `Finish`. The strengthened export test now observes both nested tuple nodes and verifies the outer second-child row is bounded by the inner tuple. This is a concrete nested-shape receipt. The direct heterogeneous-literal assertion now joins source order to the exported ordered child rows, and the FreshUse test joins each graph child node to the same-offset reconstructed native term. The graph API still does not retain an explicit source index field on each exported child; the identity correspondence is instead established by the LocalSourceIndex-preserving collection loop, the distinct child-row bounds, and the exact term-by-offset FreshUse assertion.

## Limits and remaining work

This is evidence for the candidate native path only. It does not establish source/native proof closure, public closed `yu-types` tuple schemes, runtime tuple values, or Types/Console playground execution. The graph export tests check arities, nested shape and ordered heterogeneous child constraints; the FreshUse test checks native term reconstruction against the captured graph child at every index. Source index is not exported as a separate field, but its correspondence is audited from HIR occurrence order through endpoint selection and per-offset reconstruction. Effect evidence checks the retained child-to-parent fact, not whole-program effect publication or runtime handling. This packet remains a provisional candidate-path result and does not establish the full proof companion connection, public Tuple scheme, runtime tuple value or playground execution.

The complete feature-enabled `yu-solver` test process failed with a stack overflow in an unnamed worker thread after numerous tests had passed. A serial retry was stopped after over two minutes while one test remained CPU-bound without new output. These are unresolved full-suite receipts, not attributed to this patch. `cargo fmt --all -- --check` also reports extensive formatting differences across pre-existing repository files; no whole-repository formatting was applied.

No independent review has occurred. R149 sample execution and production promotion remain open.
