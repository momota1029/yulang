# R253 — native ordered Tuple term and comparison

Status: ACTIVE; no result yet. Baseline `5596b1598`.

## Parent application

The unchanged Yulang2 Types sample needs arbitrary finite positional products. R168 requires same-polarity ordered Tuple terms, exact arity comparison before child traversal, and one constraint for every corresponding position. The sample remains blocked until source admission, candidate/capture/scheme transport, closed-type export and runtime evaluation also preserve those positions.

## Contract

See `tasks/agent-loop/sprints/ordered-tuple-native-terms-20261021-r253.md`. This packet is limited to the native term and live solver comparison owners M5–M7. It makes no public Tuple or sample support claim. R149 and original proof gates remain OPEN.

## R253 result

The branch-owned native term algebra now has distinct positive and negative Tuple nodes backed by shared immutable ordered children. Construction rejects zero arity (kept distinct from Unit), foreign handles, wrong kind and wrong polarity before publication. Structural hash/equality preserves order and duplicates; interning reuses equal tuples. Tuple payload bytes and the Arc-slot vector are included in branch retained-byte snapshots and independent lane accounting; checkpoints truncate payloads on rollback. `TermView` exposes the ordered children and value endpoint extraction retains term plus arity.

Evidence: `cargo check -p yu-solver` passed after the new endpoint arms. The focused `term::tests::ordered_tuple_terms_preserve_arity_order_duplicates_and_polarity` passed. It covers arities one through three, order, duplicates, interning, invalid handles/polarity, retained-byte reconciliation and route rollback.

The full solver library test was inconclusive. Default parallel execution aborted on stack overflow. A serial retry reached an existing failure at `f5c_normalization::tests::transferred_member_outputs_have_a_simultaneous_index_peak`, then spent the packet cap in the 4k bounded-cycle scaling test and was stopped. The serial run did not finish; the newest arity-shape test added during that run was not part of its compiled binary. No sample uses Tuple yet.

Parent application: M5 is implemented provisionally and remains unreviewed. Exact equal-arity child propagation, source candidate admission, capture/scheme transport, public closed types and runtime remain OPEN. R149 and all source/native proof gates remain OPEN.
