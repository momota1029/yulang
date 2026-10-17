# Implementation handoff: Local route runtime validation

The scoped `source_call` selector reads the retained candidate graph's
`intrusion.effect_algebra.context.scoped_enabled` flag, initialized by
`start_candidate_graph`. It retains the `observe_scoped` authentication path;
fact admission still runs `authenticate_scoped_apply`.

The attempted focused command failed with exit 101 before tests ran:

```text
timeout 120s cargo test --offline --manifest-path crates/yu-solver/Cargo.toml --features shadow-apply-candidate --lib candidate_graph_call -- --test-threads=1
```

E0609 at `shadow_apply.rs:417`: `FrozenInferenceData` has no `candidate_source`
field. Rev2 allows one retry of that exact command and, only on success, one
unchanged receive/choose fixture command with `YU_CALL_REPLAY_OBSERVER=1`;
each is capped at 120 seconds and requires a fresh capacity measurement of at
least 120 seconds. Any failure ends command validation. On the Rev2 focused
retry, compilation succeeded, the two preexisting tests passed, and the three
new tests failed at lines 328, 350, and 374. The receive/choose fixture was not
run. Rev3 switches only the three new regression cases to the
`lower_module_with_local_source` path, asserts no syntax diagnostics or
structural recovery, and leaves `candidate_call_hir()` plus the two preexisting
tests unchanged. No tests or builds were run for this edit.

Rev3 review was CLEAN. The exact focused command then passed all five
`candidate_graph_call` tests (0 failed, 718 filtered; 0.80s). The unchanged
fixture command with `YU_CALL_REPLAY_OBSERVER=1` exited 2 at
`missing module binding received`, after HIR reported `UnsupportedItem` at
80..130 and `UnsupportedExpression` at 147..162 and 328..356. No Replay row
appeared before that obstruction. The fixture and harness remain unchanged.
The rev3 command allowance is exhausted; do not claim source acceptance,
demand-bearing Replay, or original NPAIR closure from these results. Parent
remains OPEN; original conditions closed 0.
