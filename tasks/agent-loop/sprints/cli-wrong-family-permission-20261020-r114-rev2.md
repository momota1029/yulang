# R114 continuation: authentic family identity and public Web example

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW**. Luna is primary and sole Git
integrator. This continues, without replacing, R114 rev1's fixed source,
quantifiers, outcome, and exclusions. Rev1 remains
`CLOSED_INPUT_BOUNDARY_PARTIAL_REVIEWED`; its proof and test stay immutable
until this exact continuation is reviewed and granted.

## Fixed parent and finite outcome

The parent is R114's exact 195-byte source and finite claim in
`cli-wrong-family-permission-20261019-r114-rev1.md` (SHA-256
`7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`). The
source remains byte-for-byte SHA-256
`91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`.
Retain every original hypothesis, falsifier, and non-goal. In particular,
`HandlerEvidence` is a finite missing-positive-certificate observation, not
language rejection or proof of forwarding; no general hygiene or production
claim follows.

The missing premise P-ID is that the exact `signal` and `other`
ActDeclaration nodes receive distinct authentic `SourceNodeKey`s, and hence
distinct `SourceEffectId`s. Prove this using the source-key constructor and
the identity equality owner below, then apply it to the unchanged conditional
R114 source-to-runtime argument. If another direct owner is required, a key
does not preserve parse/node/start identity, or exact source preparation
differs from rev1, stop and report the obstruction; do not expand pins or
change the source.

## Frozen dependencies

Rev1's complete frozen table remains binding and must be revalidated. These
previously missing/direct continuation inputs are also pinned:

| Input | SHA-256 |
|---|---|
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| Rev1 proof `notes/theory/2026-10-19-r114-wrong-family-permission.md` | `447875018fee0f7a7e131658223ea9e7066b860fe8e8c3c35513877edf795f92` |
| Rev1 proof handoff `tasks/agent-loop/inbox/20261019-r114-proof.md` | `1e557c2adbcf53861701fa0a11679124fde1ebf87606a35624c923be6eba3f18` |
| Frozen unverified CLI test `tools/inference-playground/tests/cli_permission_boundary.rs` | `3efcf117612a513250a4396f5f21c15a0a3b2b89ac4ce27518979df8b3b93f13` |
| Frozen rev1 implementation handoff `tasks/agent-loop/inbox/20261019-r114-implementation.md` | `6eecb772e7ee30d7582c1f5d89b47e9310273f18a393c550f464f67960cf609e` |
| Web examples `web/playground/src/main.ts` | `b6b33cb75aa76a701c6373335f1cd823a4d807f0a23fbbaf97b878adcfaaed55` |
| Web example selector `web/playground/index.html` | `a1e098252dfae29635180fb8c3ce611c0a9e29436e177f76f408d5e4d8dbc9e3` |
| Web smoke `web/playground/smoke-test.mjs` | `6071129b561c8cae9ab1b147aaf8dd87eb2a802b51f92b187076c34c2cf5fea2` |
| Web package scripts `web/playground/package.json` | `ff870bfa1ba5cbb139a5a0b1d34673684eed9984f821548703ad648d0c9d1caf` |
| WASM Web adapter `apps/yulang-wasm/src/lib.rs` | `2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a` |

Any mismatch stops before work. No other source owner, fixture, or pin may be
added under this contract.

## Lanes, exact output leases, and gates

- **Proof, Sol/high, 240 seconds:** write only
  `notes/theory/2026-10-20-r114-source-identity-completion.md` and
  `tasks/agent-loop/inbox/20261020-r114-proof-continuation.md`. The proof must
  establish the two authentic keys are unequal from the pinned key equality,
  connect their owning declarations to distinct effect IDs, and discharge
  exactly P-ID in the frozen rev1 argument. Preserve all other open premises.
- **Implementation, Luna/high, 60 seconds:** after prospective spec review is
  CLEAN, write only `web/playground/src/main.ts`,
  `web/playground/index.html`, `web/playground/smoke-test.mjs`, and
  `tasks/agent-loop/inbox/20261020-r114-implementation-continuation.md`.
  Add the exact R114 source as a Web example and an isolated negative smoke
  case that invokes `run(source, "main", 100_000)` and catches the thrown
  `JsError`. Normalize it with the existing smoke convention `String(error)`
  and require that normalized string to include
  `runtime unavailable: HandlerEvidence(`. This accounts for the JavaScript
  `Error:` prefix while matching the adapter's runtime message. A normal
  return, parse/inference/preparation error, or any other error fails the
  smoke. Do not hard-code numeric source ranges; the CLI test separately checks
  derivation from the original Machine `SourceSite`. Keep the case separate
  from the positive example loop. Do not edit the frozen Rust test, its
  expectation, compiler/runtime code, or other Web examples.
- **Prospective spec review, 60 seconds:** before any Web/example or expected
  output edit, review this frozen contract and the proposed negative smoke
  expectation. Output only
  `tasks/agent-loop/inbox/20261020-r114-prespec-review.md`.
- **Fresh final reviews, 180 seconds total:** independent compiler/source,
  spec/authority, and regression reviewers, each at most 60 seconds, inspect
  the frozen proof, implementation, handoffs, and direct pins. Exact outputs:
  `tasks/agent-loop/inbox/20261020-r114-compiler-review.md`,
  `tasks/agent-loop/inbox/20261020-r114-post-spec-review.md`, and
  `tasks/agent-loop/inbox/20261020-r114-regression-review.md`.
- **Verification, Luna only:** after the proof and implementation are frozen,
  all three final reviews are CLEAN, and the prespec is CLEAN, run these exact
  commands sequentially, once each, stopping on any failure:

  ```sh
  CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_permission_boundary wrong_family_permission_withholds_runtime_and_cli_result -- --exact --nocapture
  timeout 120s npm --prefix web/playground run check
  ```

  The first is newly authorized only by this contract; rev1's NOT_RUN command
  has no independent retry authority. The second builds and runs the Web smoke
  through the pinned package script. Do not run alternate tests, builds,
  formatters, or direct CLI invocations.
- **Closeout, Luna, 60 seconds:** write only
  `notes/progress/2026-10-20-r114-closeout.md`, reconcile current state, and
  integrate only after successful gates and review adjudication.

## Resources, stop conditions, and authority

R114 rev1 reservations are reconciled conservatively: proof 480 seconds,
implementation 240 seconds, the completed pre-spec/compiler reviews 240
seconds from their shared review pool, and closeout 120 seconds are charged in
full. The NOT_RUN command reservation of 120 seconds is cancelled. Rev2 sets a
**cumulative R114 ceiling of 1,920 seconds**: 1,080 prior charged + 240 proof
+ 60 implementation + 60 prespec + 180 final reviews + 240 commands + 60
closeout. No budget resets; unobserved or interrupted work remains charged.
Zero Astra. At most one heavy process, and the two verification commands are
strictly serial.

Any mismatch, failed command, non-CLEAN required review, or newly needed owner
stops this packet without repair, retry, or pin expansion. Preserve rev1's
NOT_RUN history, frozen artifacts, all UNKNOWN reservations and quarantined
leases. Luna alone owns state, command execution, review adjudication, closeout,
explicit staging, outbound-range review, and non-forced Git integration.

R114 remains a finite witness only. All original Simple-sub/evaluator A/B,
adoption, effect-hygiene, source-law, and production gates remain OPEN.
