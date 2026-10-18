# Frozen R19 local-binding runtime repair handoff

- Sprint: `operation-v1-local-install-use-lineage-and-capture-20261018-r19`, repair revision 3; SHA-256 `9002cc81daf3a6bde262fcf8390dfdc6a48f6145106327fb00236ed9f38b6cfe`.
- Base contract revision 1 SHA-256: `75eba332166f8ffece47fe2ccbe6513058b151cc76fa74545ba56c3ca70977fd`.
- Assignment ID: `r19-local-binding-runtime`, handoff revision 2. Parent remains `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN/closure0, original source/native domain and quantifiers unchanged.
- Baseline: root checkpoint `f8b035526a8fa362074a13e6795fa39e12b7eddb`; original R19 implementation target and BLOCKING review remain immutable at their pinned hashes.
- Role/session: `/root/r19_local_binding_runtime`, current session. Requested Luna/high; observed model/effort UNKNOWN/UNKNOWN. No separate runtime launch receipt available.
- Exact write paths: `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/tests/runtime_resume.rs`, and this new handoff only. Git was not used for mutation.

## Repair delta

1. R18 keeps its original direct Catch-result Apply discovery when there is no matching local-`g` initializer. For the local route, `operation_v1_local_lineage` now constructs the response invocation from the source chain: the exact request lies under a local `g` initializer Catch; an Apply's callee is a Name resolved to that exact `HirLocalId`; and that Apply is the unique matching use. It rejects missing, ambiguous or sibling-resolved uses. It does not make Name generally transparent.
2. The actual `g` Apply is allowed to be the response-closure invocation. `response_invocation_apply` is set to that exact Apply in the local route. This single call remains distinct from the continuation `k response` Apply and callback-body operation Apply. Existing runtime closure-handle/environment and invocation-owner checks apply to this same invocation; no second owner is demanded. The machine implementation required no repair delta and remains byte-identical to the original frozen R19 target.
3. The sibling control is balanced and adds a nested shadowing `g` initialized from the outer `g`. Both positive and sibling sources first pass explicit parse/HIR checks and unchanged `solve_operation_v1_research`, conflict-free, exactly-one-consumed-FieldBoundV1 receipt checks in the test. The sibling runtime entry then expects the exact source-lineage gate to reject the shadow binder.

The test gates and source are frozen but **NOT RUN** pending the same reviewer's CLEAN delta. Therefore parse/HIR acceptance, unchanged static candidate/receipt acceptance, actual local execution, and the specific sibling rejection remain unobserved. If static acceptance fails after review, freeze the first failing assertion/source boundary and report local-runtime success NOT_RUN/failed; no source or solver semantics rewrite is authorized.

## Hashes and checks

```text
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs (unchanged from original R19 frozen target)
679c21fb6810b636791374ddeff19b131952e53567533f6f48d7d7dae9187a8b tools/inference-playground/tests/runtime_resume.rs
```

- Tests/builds/formatters: NOT RUN before the same reviewer's CLEAN delta review, as contracted.
- Solver/source code and receipt schema: unchanged. Pinned direct dependencies rechecked unchanged: candidate_scheme `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd`; candidate_effect `6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0`; candidate_source `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`; candidate_context `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca`; playground lib `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b`; continuation runtime `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`.
- Resource: prior 600 seconds remain spent. This repair grant is exactly 360 seconds; actual elapsed/CPU/RSS/tokens UNKNOWN, no prior budget reset or carryover. Astra 0.
- Review: same independent compiler_referee delta review pending; author does not self-review. Writes stopped after freezing this handoff.

## Scope and evidence limits

The intended runtime chain is exact source initializer Catch -> `HirLocalId` -> resolved Name -> `g` Apply -> runtime initialized local cell/value/environment -> Name read of that same cell/value -> the same Apply's invocation owner -> callback operation/request under that owner -> R18 live outer handler arm -> `Completed(42)`. This is a candidate implementation path pending review and focused execution.

Reused evidence: R18 rev4 direct-path implementation and reported `runtime_resume` 17/17; the original R19 frozen source/runtime target and its review findings. The R18 result does not establish this local route. Rejected: spelling/type/family equality, a same-family callback, a copied static receipt, or a sibling cell as lineage evidence.

Runtime lineage alone does **not** establish FieldBound Capture, FreshUse transport, a use-specific native consumer, or any original parent condition. `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN/closure0. No provisional result authorizes cutover.

Known pre-existing quarantined/disposable paths remain untouched and outside this lease: `notes/theory/2026-10-18-replay-constructor-lineage.md`, `notes/theory/2026-10-18-replay-constructor-separate-test.md`, `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-proof.md`, and `tools/__pycache__/`.

Next related step: same reviewer's CLEAN delta review of these exact bytes. Only then may Luna run the single authorized `cargo test -p yu-playground --test runtime_resume` and integrate/update state. No test is claimed here.
