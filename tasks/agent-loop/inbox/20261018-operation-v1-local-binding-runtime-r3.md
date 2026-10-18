# Frozen R19 local-binding runtime test repair handoff

- Sprint: `operation-v1-local-install-use-lineage-and-capture-20261018-r19`, repair revision 4; contract SHA-256 `d65e86aadd85f814b69b6ba4648330ddb50ef9571ed89b854eedbe8d9da8276d`.
- Assignment ID: `r19-local-binding-runtime`, handoff revision 3. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN/closure0 with original domain and quantifiers.
- Baseline runtime implementation frozen at rev3 hashes below. Root checkpoint at assignment start: `4dfe91d24c229a96b57837881ee71102715eb972`.
- Role/session: `/root/r19_local_binding_runtime`, current session. Requested model/effort Luna/high; observed model/effort UNKNOWN/UNKNOWN.
- Exact write paths: `tools/inference-playground/tests/runtime_resume.rs` and this new handoff only. `program.rs` and `machine.rs` were not edited. No Git mutation.

## Test-only repairs

The sibling source replacement now retains the Catch's closing brace before adding the nested shadowed `g` block. The existing test assertions still require parse/HIR success, no HIR errors, unchanged `solve_operation_v1_research` acceptance, conflict-free evidence, and exactly one consumed FieldBoundV1 receipt for both the positive and sibling source before the runtime assertion.

The sibling result is matched by reference, so the diagnostic formatting can borrow the full result afterward. The sibling runtime assertion still requires rejection at `runtime unavailable: InvalidSourceReference`.

These source/static/runtime assertions are **NOT RUN** pending the same compiler referee's CLEAN test-only delta review. Static acceptance and the exact runtime rejection therefore remain unobserved. If static acceptance fails, the first failing assertion is the boundary to report; runtime behavior remains NOT_RUN/failed. No source, solver, runtime implementation, receipt schema, expected output, or test gate was changed.

## Frozen hashes and checks

```text
ea4579c34b0c01a8e109a6b26cb426ac1fb337a87d7ff4af66a4969010a784db tools/inference-playground/tests/runtime_resume.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs (frozen; not edited)
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs (frozen; not edited)
```

- Tests/builds/formatters: **NOT RUN**, pending same-reviewer CLEAN delta review.
- Resource: prior R19 grant remains spent. Rev4 adds exactly 120 seconds for this repair; actual elapsed/CPU/RSS/tokens UNKNOWN. Astra 0.
- Review: same independent compiler referee's test-only delta review pending. Author does not self-review. Writes stopped after this freeze.

The runtime lineage remains provisional and does not establish FieldBound Capture, FreshUse transport, a native consumer, or any original parent condition. Known pre-existing quarantined/disposable paths remain untouched: `notes/theory/2026-10-18-replay-constructor-lineage.md`, `notes/theory/2026-10-18-replay-constructor-separate-test.md`, `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-proof.md`, and `tools/__pycache__/`.

Next step: same reviewer's CLEAN delta review. Only after CLEAN may Luna run once the authorized `cargo test -p yu-playground --test runtime_resume` target and integrate its result.
