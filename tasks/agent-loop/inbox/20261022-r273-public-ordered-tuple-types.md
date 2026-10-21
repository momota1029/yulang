# R273 primary handoff — public closed ordered Tuple nodes

Contract: `tasks/agent-loop/sprints/public-ordered-tuple-types-20261022-r273.md`.
Baseline: `eeaa516ee`.
Status: primary implementation in progress; provisional and unreviewed.

Parent: unchanged Yulang2 examples and proof-backed compiler/evaluator. R272 adds provisional runtime Tuple construction; R149/R168 require arbitrary ordered products across public types. The current `yu-types` public views have scalar, function, union and intersection forms but no Tuple constructor.

Exact scope: extend indexed and draft closed-type construction, positive/negative public views, checked child spans, final arena commit, and alpha-equivalence in `crates/yu-types/src/lib.rs`. Preserve order and arity. This does not wire solver candidate export, close inference/source-native proof, or make the R149 samples pass.

Checks: focused `yu-types` tuple/finalization tests, `python3 tools/agent_sprint.py check`, and `git diff --check`. No independent review under the user's solo-work instruction.
