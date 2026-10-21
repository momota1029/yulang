# R273 primary handoff — public closed ordered Tuple nodes

Contract: `tasks/agent-loop/sprints/public-ordered-tuple-types-20261022-r273.md`.
Baseline: `eeaa516ee`.
Status: implementation checkpoint complete; provisional, primary-only and unreviewed.

Parent: unchanged Yulang2 examples and proof-backed compiler/evaluator. R272 adds provisional runtime Tuple construction; R149/R168 require arbitrary ordered products across public types. The current `yu-types` public views have scalar, function, union and intersection forms but no Tuple constructor.

Exact scope completed: ordered positive/negative Tuple constructors now flow through indexed and draft inputs, checked child spans, final arena commit, public views and alpha-equivalence in `crates/yu-types/src/lib.rs`. Nested heterogeneous values preserve order and arity; malformed spans reject. Solver candidate export remains unwired, and no inference/source-native proof gate or R149 sample is closed.

Checks: `cargo test -p yu-types --lib` (41 passed), `cargo check -p yu-types`, `python3 tools/agent_sprint.py check`, and `git diff --check`. Existing `yu-hir` provenance warnings remain. No independent review under the user's solo-work instruction.
