# R270 — source tuple candidate inference result

Status: provisional implementation checkpoint; primary-only and unreviewed.

## Implemented

`LocalSourceForm::Tuple` now retains its ordered child endpoints and each child's computation-effect component in one candidate recipe. Admission creates a positive native tuple term, constrains it against the expression's negative value component, and records one effect edge per child into the tuple expression's effect row. Tuple effect fact slots use checked `u32` IDs so their namespace does not stop at 255; existing byte-sized source slots remain supported.

Candidate graph capture records tuple polarity and ordered child node indexes in a separately accounted backing vector. Fresh reconstruction walks those children in order and rebuilds a positive or negative native tuple term. Graph inspection exposes tuple children as a non-allocating exact-size iterator. The term storage resource assertion now accounts for tuple backing capacity and payload separately from the six fixed Term lanes.

## Evidence

- `shadow_apply::tests::source_tuple_is_retained_as_ordered_candidate_graph_node` passes for source tuples of arities 1, 2, and 3. The arity-2 and arity-3 values pass through polymorphic `id`, exercising graph freshening. A nested tuple source is also admitted by the same candidate solve.
- `shadow_apply::tests::source_tuple_child_effect_is_admitted_to_tuple_computation_row` passes for `(io::tick(), 1)`. The first tuple child's retained provenance has Effect terms on both sides of its relation into the tuple computation row.
- Existing `f5b_ordered_tuple_comparison_keeps_positions_and_reports_arity_mismatch_at_root` passed during the full feature-enabled run before that process encountered a stack overflow.
- Focused feature-enabled source tuple tests and `cargo check -p yu-solver --features shadow-apply-candidate` pass.
- `python3 tools/agent_sprint.py check` passes. `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'` passes (57 tests).
- `git diff --check` passes.

## Limits and remaining work

This is evidence for the candidate native path only. It does not establish source/native proof closure, public closed `yu-types` tuple schemes, runtime tuple values, or Types/Console playground execution. The graph export test checks tuple arities; it does not yet authenticate every exported child against its source occurrence or a tuple-specific fresh-use receipt. The nested source currently has a successful candidate solve but lacks an exported nested-shape assertion. Effect evidence checks the retained child-to-parent fact, not whole-program effect publication or runtime handling.

The complete feature-enabled `yu-solver` test process failed with a stack overflow in an unnamed worker thread after numerous tests had passed. A serial retry was stopped after over two minutes while one test remained CPU-bound without new output. These are unresolved full-suite receipts, not attributed to this patch. `cargo fmt --all -- --check` also reports extensive formatting differences across pre-existing repository files; no whole-repository formatting was applied.

No independent review has occurred. R149 sample execution and production promotion remain open.
