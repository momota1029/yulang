# R113: unmatched expression request and withheld selected definition

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW**. Primary and sole Git integrator:
Luna `/root`. This sprint rotates from R112's method/role source gap to the
unmatched outward-request plus suffix effect-hygiene front, while bringing one
existing source recipe through the public CLI.

## Fixed exact source and result

Use the exact source from
`runtime_module_expressions.rs::expression_request_retains_original_provenance_and_pending_suffix`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
io::tick 99; my main = 7
```

Source is 83 UTF-8 bytes, SHA-256
`f80549d67af6ffb8d402e5f469c7b3e7c22c7ec971377de47c2cb6c469d33f63`,
without final LF. Preserve the source byte-for-byte.

Primary adjudication of the pre-review finding: for this exact program,
`my main = 7` is not a later `ExecutionRoot`. The scheduled computation is the
expression `io::tick 99`; after its `Frame::ExpressionReturn { root, next }`
cursor reaches schedule exhaustion, the live Machine retains its distinct
selected-definition fallback for `main`. This packet proves that the
unmatched request saves the expression-return cursor and that the terminal
request stops execution before the fallback can evaluate/publish `main = 7`.
It does not claim a nonempty remaining execution-root list or general suffix
preservation.

Constructively trace the authentic first expression root, operation `io::tick`
and payload 99, original expression-root provenance and HIR-backed `SourceSite`,
the exact `ExpressionReturn` frame and `next` cursor, unmatched request
propagation, and saved continuation. The continuation must retain that
expression-return control point; positive depth alone does not establish its
identity. At the public stdin CLI boundary, `--run main --steps 30000 -` must
fail with empty stdout and the existing unhandled-runtime-request diagnostic,
whose range expectation is derived from the Machine's original HIR-backed
`SourceSite`. No hand-written span is allowed.

## Evidence boundary and falsifiers

Reuse the existing runtime test assertion only at its actual premises: it
observes an `Expression` SourceRootId and positive `continuation_depth`; depth
alone does not prove the identity of the saved frame/cursor. The proof must
inspect the pinned production path from mixed HIR root order through
`ExecutionRoot` scheduling, `Frame::ExpressionReturn { root, next }`, original
operation `SourceSite`, request propagation, `stop_unhandled_request`, saved
continuation construction, and CLI publication. Identify schedule exhaustion
at `next`; separately identify the live selected-definition fallback for
`main`. Show that the request stops before that fallback evaluates or publishes
7. Keep source occurrence/range derived from original HIR construction, not
byte arithmetic.

Do not invoke R99's fresh-receiver law or alter receiving semantics. The
approved authorities are the module-expression source-owner decision and the
initialization-order/global-effect decision. Their source-order and
escaping-effect policies do not by themselves prove whole-program admission,
initialization adequacy, or arbitrary suffix preservation. No theorem for all
source programs, all effects, or all saved continuations is authorized.

Falsifiers include wrong definition-root attribution, changed operation
identity/payload/source range, loss or misidentification of the saved
`ExpressionReturn` cursor, execution/publication of 7 after the terminal
request, CLI success, stdout containing 7, preparation failure, or any outcome
different from the fixed finite prediction. Do not falsify against a nonexistent
remaining execution-root entry after `io::tick 99`; the textual `main` binding
is the separate selected-definition fallback described above. Any mismatch consumes the one attempt and
stops without repair or retry.

This packet makes no production edit or semantic change. It does not close
R99's earlier fresh-receiver question, module initialization/materialization
adequacy, the original Simple-sub/evaluator claims or A/B, F1/FK1, six-front
effect hygiene, R100-P2/P3/P4, R85 adoption, or production authority.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| Existing source/runtime assertions `tools/inference-playground/tests/runtime_module_expressions.rs` | `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f` |
| Approved module-expression ownership `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| Approved initialization/effect order `notes/design/2026-10-16-initialization-order-global-effects.md` | `e2f70f535319522261cc6f52592d62b491d9d0e9d32e14310ac5d9fb81ee1bb6` |
| Runtime expression-root theorem `notes/theory/2026-10-16-runtime-module-expression-roots.md` | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| Module-expression carrier correspondence `notes/theory/2026-10-16-module-expression-carrier-correspondence.md` | `600391db278adf29c955b407e3586b2e351994d7a8a7aa5003349fe72209d39a` |
| HIR module owner `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| HIR LocalSource owner `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| Runtime program and schedule `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| Runtime machine and request frames `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| Saved continuation `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| Public prepare/execute result mapping `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| Public stdin CLI `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| Atomic output/error handling `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| Existing child-process convention `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| Test target and package `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

All pins and the literal source hash must match. A new required owner or pin
mismatch stops the packet; no source-domain expansion.

## Lanes and outputs

- Proof, Sol/high, cap 600 seconds; exact writes only:
  `notes/theory/2026-10-19-r113-module-request-suffix.md` and
  `tasks/agent-loop/inbox/20261019-r113-proof.md`.
- Test-only implementation, Luna/high, cap 300 seconds; exact writes only:
  `tools/inference-playground/tests/cli_module_request.rs` and
  `tasks/agent-loop/inbox/20261019-r113-implementation.md`. Add one test
  `outward_expression_request_preserves_suffix_and_withholds_cli_result`.
  It must combine a direct Machine provenance/payload/nonempty-suffix
  observation with one public stdin CLI child. No production edits.
- Fresh pre-edit review of rev2: `tasks/agent-loop/inbox/20261019-r113-pre-spec-review-rev2.md`.
- Fresh post-output spec and compiler/source reviews:
  `tasks/agent-loop/inbox/20261019-r113-post-spec-review.md` and
  `tasks/agent-loop/inbox/20261019-r113-compiler-review.md`.
- Luna owns current state, the exact one-shot command, review adjudication,
  closeout `notes/progress/2026-10-19-r113-module-request-suffix.md`, and
  explicit-path Git integration.

After both outputs freeze and both post-output reviews are CLEAN, Luna alone
may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_module_request outward_expression_request_preserves_suffix_and_withholds_cli_result -- --exact --nocapture
```

No alternate command, standalone build, formatter, direct CLI invocation,
retry, or repair is authorized. A command failure or predicted-outcome mismatch
consumes the attempt. Workers do not run tests, builds, compiler/runtime/CLI,
formatter or Git commands.

## Resources and breadth

Total ceiling: 1,500 seconds: proof 600, implementation 300, pre/post spec
120, compiler/source 180, command 120, closeout 180; Astra 0. The original
rev1 review time counts against the existing shared review allocation; no
resource reset. R111 unknown
resource use remains charged and its FROZEN_UNVERIFIED test remains quarantined
without retry. Preserve the three inherited UNKNOWN identities, board
quarantine, R104 historical lease and legacy slot reservation.

R113 covers one finite unmatched-outward-request/captured-cursor path and one
public CLI observation. It does not displace the other five hygiene fronts,
method/role proof, runnable source breadth, original A/B, or semantic/adoption
gates. At the next boundary choose another under-covered obligation; do not
repeat this fixture or continuation storage analysis by default.
