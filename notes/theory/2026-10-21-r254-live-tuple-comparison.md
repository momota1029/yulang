# R254 — live ordered Tuple comparison

Status: RESULT_PARTIAL; provisional native implementation evidence, solo primary, no independent review. Baseline is the R253 worktree and commit `5596b1598`.

R253 added provisional native term storage and endpoint shape identity, but did not attach Tuple to the live structural worklist. This packet targets R168 M6–M8: exact same-arity positional constraints with indexed context, honest arity/shape failures, and rollback/resource evidence. Public sample support and R149 remain OPEN.

## R254 result

`dispatch_live_item` now checks Tuple arity before reading children, then constructs one value pair for every same-index child. It records diagnostic edges with their exact tuple indices. Candidate graph execution owns an explicit Tuple continuation, admits each child through a `TuplePort` dependency carrying its source index, and can resume after rollback without losing the saved continuation. Candidate source dependency observations expose the TuplePort index, and solver-facing value endpoint observations retain the term plus arity.

The equal-arity test compares `(Int, Bool, Bool)` with `(Int, Str, Str)`, confirms all three diagnostic edges retain indices `0,1,2`, and reports the first mismatch at index `1`. A 3-to-1 comparison reports `Tuple(3)` vs `Tuple(1)` at the root and creates no child edges. A candidate graph test drives repeated child handles through rollback and resume and observes all three TuplePort indices after completion.

Evidence: `cargo check -p yu-solver --features shadow-apply-candidate` passed. `cargo test -p yu-solver --features shadow-apply-candidate --lib tuple` passed all three matching tests. `python3 tools/agent_sprint.py check` and `git diff --check` passed. `cargo fmt --check` shows repository-wide drift from HEAD, so it was not applied across the repository. The full solver suite was not rerun because R253's capped attempts were inconclusive and the observed scaling test consumed the prior packet budget.

The isolated normalization failure was rerun on both the modified worktree and a detached baseline worktree at `5596b1598`. Both failed at the same `unwrap()` with `IdentityExhausted`; this is a baseline failure, not evidence against the Tuple change.

R168 M6–M8 proof and source/native correspondence remain OPEN. In particular, the native worklist step does not establish source tuple construction, extrusion/capture/freshening, candidate schemes, closed public types, runtime ordering, Console support or either R149 sample. No independent review has occurred.
