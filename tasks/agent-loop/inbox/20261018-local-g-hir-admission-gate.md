# R20 runtime HIR admission gate — frozen target

Sprint/contract: R20, `tasks/agent-loop/sprints/operation-v1-fieldbound-prefix-authentic-use-consumer-20261018-r20.md`, rev2 SHA-256 `8486608b0e7f891223da836ecfdf02cb6148b60e6fcc6c3a23188256c4ce353f` (rev1 snapshot retained in sprint history).

Assignment: runtime HIR admission gate, handoff revision 2. Parent remains `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN / closure 0. Baseline recorded by contract: `8e1ad99fd`; R19 runtime source and machine dependencies remain pinned to hashes `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` and `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN. Astra: 0. Exact write lease: `tools/inference-playground/tests/runtime_resume.rs` and this handoff only. Worker: `/root/r19_local_binding_runtime`; current-session launch metadata beyond this active-work receipt is not available to this worker. Writes are stopped at this frozen target.

## Outcome and owner boundary

The test now checks HIR error admission before calling the unchanged `CandidateInference::solve_operation_v1_research` receipt gate. The check derives only existing candidate-mode owner paths:

- `SourceEffectDeclaration.placeholder_errors` owns declaration placeholders. Each must be `UnsupportedItem`, `Lowering` origin, match its declaration range, and be attached to a direct root `HirItem::Error` containing the same ID.
- For a binding with local source, the source placeholder set is exactly the terminal `ResolvedExpr::Error` reached through its outer Lambda chain, matching `retain_placeholder_errors`.
- For a binding on candidate mode's fallback path, only IDs attached to `Apply` nodes can enter the permitted set, matching `preflight_expression`'s error collection. These must be `UnsupportedExpression` and attached to that binding's `Value` owner.
- Duplicate IDs, missing/extra owner IDs, wrong origin/kind/attachment, and every unowned ID fail closed. The diagnostic is bounded to at most 16 errors and prints each ID, derived owner, origin, kind, attachment, and range.

No HIR IDs or runtime error classifications are claimed as observed: the bounded diagnostic and focused target have not run. The first unverified boundary is whether the current valid local-g source's actual HIR errors are entirely within the declaration and source-carrier/fallback Apply owners above. The tests retain syntax validity, unchanged static candidate-receipt assertions, local-g runtime lineage assertions, and the balanced shadowed-sibling static acceptance plus runtime rejection control.

## Checks, status, and limits

At the rev1 freeze, no test, build, formatter, or diagnostic command had run. The initial independent review was BLOCKING because fallback Apply IDs were individually admitted but omitted from `expected_ids`. R20 rev2 repaired only that set construction, then received CLEAN independent delta review before verification. Static source inspection compared the helper with `CandidateInference::solve_mode`, `retain_placeholder_errors`, fallback `preflight_expression`, and HIR declaration placeholder creation. The focused test passed, establishing that this specimen's observed HIR errors satisfy the exact owner checks and unchanged candidate receipt gate. Successful test output did not preserve the bounded diagnostic lines, so concrete HIR IDs are not claimed here.

Claim class: provisional implementation/test gate. Runtime lineage alone does not establish FieldBound Capture, FreshUse, a native consumer, source/native correspondence, or any theorem. Original parent remains open. No solver, HIR, runtime program, or machine files were changed.

## Frozen artifact hashes

- `tools/inference-playground/tests/runtime_resume.rs`: SHA-256 `686d9a88cc4c36693ac63edb54bd74258e329f1ea971e80162501ac0fd71eb8c`.
- This handoff: final hash reported with the frozen submission message.
- Frozen unchanged runtime dependencies: `program.rs` SHA-256 `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`; `machine.rs` SHA-256 `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`.

R20 rev2 result: independent delta review CLEAN at `runtime_resume.rs` SHA-256 `3902e5071d9d2bc8bede6cc03fe74e224cf12627de7bcfc147ec850b9fd560bd`; the one authorized `cargo test -p yu-playground --test runtime_resume` run passed 18/18. The owner gate, unchanged static receipt, local-g runtime path, and sibling controls all passed. Parent theorem remains OPEN / closure 0; this runtime/test result establishes no FieldBound-to-FreshUse connection.


## R20 rev2 verification receipt

The only rev2 source change was `.chain(fallback_apply_errors.keys().copied())` in
`expected_ids`; all error-owner checks, unknown rejection, and final set
equality remain. The frozen delta received CLEAN independent review. Luna ran
`cargo test -p yu-playground --test runtime_resume` exactly once: 18 passed, 0
failed. The test target emitted only compile warnings for unused/dead fields and
`unused_mut`; no failing diagnostics or test errors occurred. This confirms the
R20 runtime HIR admission gate and local-g runtime case for this specimen,
conditional on this candidate test. It does not close any original parent
condition or prove a receive/FieldBound/FreshUse theorem.

Final rev2 hashes:

- `tools/inference-playground/tests/runtime_resume.rs`:
  `3902e5071d9d2bc8bede6cc03fe74e224cf12627de7bcfc147ec850b9fd560bd`.
- This handoff: recorded in the R20 closeout commit.
