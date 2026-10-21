# R214 — resumed playground and parser verification

## Outcome

After the user resumed the standing inference/evaluator and sample goal, the
existing R187 sample/parser changes were verified against the current worktree.
No Web sample bytes changed.

`RUSTC_WRAPPER= cargo test -q -p yu-playground` passed. This package run
exercises the six `web/playground/examples/` fixtures through their ordinary
integration tests: identity, ordinary islands, repeated choice, escaping
closure, and the two intentional diagnostic examples. The ordinary-islands
fixture covers all four public definitions and expected outputs.

`RUSTC_WRAPPER= cargo test -q -p yu-syntax` passed: 1,422 passed, 1 ignored,
and 9 integration tests passed. This includes the parser and recovery coverage
for braced conditional arms.

`RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate
local_source_observation` passed on the pushed readback implementation: 1 test
passed, 731 filtered out. This reproduces the source-local Capture readback
used by the R213 candidate witness; it does not independently certify the
model or its source/native correspondence.

The two pre-parenthesized Catch test inputs were also run directly through the
current CLI and produced syntax diagnostics. The updated test inputs wrap the
braced conditional scrutinee in parentheses, making the Catch boundary
explicit. The full playground suite passes with those inputs.

## Limits

This verifies executable sample and parser behavior only. It does not close the
Simple-sub/F5 proof, source/native correspondence, the R213 candidate frontier
witness review, or production inference gates. The original theorem remains
OPEN; no inference algorithm change is claimed.
