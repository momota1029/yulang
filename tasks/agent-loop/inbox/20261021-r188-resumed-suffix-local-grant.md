# R188 result — resumed-suffix local Grant owner

Status: RESULT, candidate-only; original parent/A/B/source-native/production remain OPEN.
Contract: `tasks/agent-loop/sprints/resumed-suffix-local-grant-20261021-r188.md`, SHA-256 `2cc2d73da2e698a5e5bc45598928f7b197202d9d3418f3fd93c55d3ac8a676ab3f`.
Baseline: `183d69ef36cf45753980a83b7eecefd303421650`.

## Before/after evidence

The unchanged `runtime_unmatched::unmatched_request_preserves_original_suffix_across_outer_handling` fails at the resumed `other 23` request with `Unavailable(HandlerEvidence)` at the inner Catch source range `87..123`.

Temporary read-only trace of the existing positive path showed:

- event 0: local Grant query owner `Invocation(0)`; observations `(view 2, receipt 2)` and `(view 5, receipt 5)`;
- event 1 after suffix resumption: query owner `Invocation(4)`; observations `(view 2, receipt 2)` and `(view 5, receipt 5)`;
- retained RootComp boundary receivers are `[0, 1]`, so `Invocation(4)` has no direct boundary;
- retained receipts include `(Invocation(0), view 2, formal)`, `(Invocation(1), view 5, formal)`, and corresponding observer receipts for those exact views.

A temporary candidate added continuation owner lineage `Invocation(4) -> Invocation(1)` and allowed the current event's authenticated observations to join the original receiver boundary and receipt. It made the positive `runtime_unmatched` test pass, but also made the sibling regression `runtime_resume::fresh_owner_reentry_does_not_resurrect_an_expired_receivers_grant` pass unexpectedly; that test requires `Unavailable(HandlerEvidence)`. Both tests have the same two receiver views, retained boundaries `[0, 1]`, and the same event-1 owner projection. Their source shapes differ in names, request payload constants, and arm result expression, none of which is a justified Grant premise.

I rejected and removed the candidate repair. No Grant condition, source expectation, or test output was changed. `receiving.rs` and `machine.rs` were restored byte-for-byte to their contract pins:

- `receiving.rs`: `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`
- `machine.rs`: `7187abd78ca13efaeebf4cb70837c98360c0024d082a59af331da41169d3409b`

Post-restore `cargo test -q -p yu-playground --test runtime_unmatched --test runtime_resume` confirms the 19 `runtime_resume` tests pass, including the expired-owner guard, while `runtime_unmatched` still fails on the positive resumed suffix. The alias candidate makes the opposite pair fail/pass, so it is not an acceptable implementation.

## Related goal evidence and boundary

The explicit Yulang2 CLI tests passed:

```text
cargo test -q -p yu-playground --test cli_ordinary_islands --test cli_demo_identity --test cli_yulang2_diagnostic_examples
```

The Web playground build and WASM smoke passed with cached wasm-bindgen 0.2.125: inference, 13 execution examples, three Yulang2 identity definitions, and two Yulang2 diagnostic examples. `python3 tools/agent_sprint.py check` passed as static workflow validation only.

No source-qualified rule currently distinguishes the two event-1 cases without consulting unrelated payload values or arm bodies. The next evidence must explain this distinction from the original source/native computation-forwarding obligation or establish that the existing test expectations conflict. Do not infer a Grant from an old receiver receipt alone. No production admission or theorem promotion follows from these tests.

R188 work stopped within its fresh cap; charged time: 240s, remaining reserve: 1560s, no carryover. No child workers were launched. Independent review remains unavailable under the user's solo-worker constraint. The focused Cargo run used the dirty shared worktree; solver/parser dependencies were not re-pinned, so this result remains provisional and is not a commit-ready checkpoint.
