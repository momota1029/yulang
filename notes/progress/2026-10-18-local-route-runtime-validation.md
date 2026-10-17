# Local route runtime validation

## Rev2 scoped selection repair

`CandidateInference::source_call` now selects `observe_scoped` from the retained
`candidate_graph.intrusion.effect_algebra.context.scoped_enabled` bit initialized
by `start_candidate_graph`. The fact-admission authentication guard remains in
place. This fixes the compile-time field mismatch without changing the route
authentication behavior.

## Runtime command record

The first focused command failed before running tests:

```text
timeout 120s cargo test --offline --manifest-path crates/yu-solver/Cargo.toml --features shadow-apply-candidate --lib candidate_graph_call -- --test-threads=1
```

Exit status: 101. Compiler error E0609 at `shadow_apply.rs:417`: `FrozenInferenceData`
has no field `candidate_source`. No tests executed.

Rev2 authorized at most two additional commands after fresh CLEAN review, each
at most 120 seconds and preceded by a capacity remeasurement of at least 120
seconds: retry the exact focused command once; if it passes, run the unchanged
receive/choose fixture with `YU_CALL_REPLAY_OBSERVER=1`. Any command failure
stops validation; there are no further retries. The focused retry compiled;
both preexisting tests passed, while the three new tests failed at lines 328,
350, and 374. The receive/choose fixture was not run.

## Rev3 regression source repair

The three new regressions now lower through `lower_module_with_local_source`,
with syntax diagnostics and structural recoveries asserted empty. Legacy
`candidate_call_hir()` and the two preexisting tests are unchanged. No tests or
builds were run for this edit.

## Rev3 runtime results

The LocalSource-specific harness repair received CLEAN independent review at
the exact frozen test hash before these commands. Both commands were
remeasured against the rev3 budget and run once as authorized.

Focused regression:

```text
timeout 120s cargo test --offline --manifest-path crates/yu-solver/Cargo.toml --features shadow-apply-candidate --lib candidate_graph_call -- --test-threads=1
```

Exit 0. Five tests passed, zero failed, 718 filtered; test execution finished
in 0.80s. This includes later-argument Local route retention, annotation and
ascription refusal, unscoped record-cap noninterference, and the two existing
candidate-call regressions.

Unchanged receive/choose fixture:

```text
YU_CALL_REPLAY_OBSERVER=1 timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit 2. The harness reported `parse.structural_recoveries=[]`, then stopped at
`missing module binding received`. HIR reports `UnsupportedItem` at range
80..130 and `UnsupportedExpression` at ranges 147..162 and 328..356. No
`YU_CALL_REPLAY_OBSERVER` Replay row appeared before this obstruction, so this
run establishes neither a demand-bearing Replay nor source acceptance.

The fixture SHA remains `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`;
the example SHA remains `d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28`.
No fixture, expected output, or production source changed after CLEAN review.
Rev3 command allowance is exhausted. Original theorem conditions remain OPEN;
closed count is 0.
