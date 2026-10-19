# R114 continuation: current-source identity and runtime correspondence

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW**. Luna remains primary and sole Git
integrator. This version continues the exact R114 parent; it does not alter
the original source, finite permission claim, expected observations, or
exclusions. Rev1 remains `CLOSED_INPUT_BOUNDARY_PARTIAL_REVIEWED`; rev2 remains
`STOPPED_INPUT_MISMATCH`. Preserve both outcomes and all frozen artifacts.

## Parent and result sought

The exact parent and source are in rev1 contract
`tasks/agent-loop/sprints/cli-wrong-family-permission-20261019-r114-rev1.md`,
SHA-256 `7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`.
The 195-byte source SHA-256 is
`91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`.
All original hypotheses, quantifiers, observations, falsifiers, and exclusions
remain binding. The target is only a finite wrong-family permission witness;
`HandlerEvidence` is neither language rejection nor proof of forwarding.

Discharge P-ID for the exact source: authentic unequal `SourceNodeKey`s for
the `signal` and `other` ActDeclaration nodes, and therefore distinct
`SourceEffectId`s. Apply this only after accounting for the current owner
deltas listed below. Then establish whether the original `[other]` annotation,
request identity, receiver construction, bypass exclusion, permission
consumer, and public CLI error withholding still correspond to the frozen
rev1 claim on current source. The rev1 argument is historical conditional
evidence; this contract does not assume it transfers automatically.

## Baseline and frozen source inventory

Baseline: commit `a96f040f4c2e07c1832e8ffca05db673da4318e5`. The complete
rev1 input table remains binding, with the following seven current-byte
overrides. The other twelve rev1 inputs matched at rev2 startup and must be
revalidated against their unchanged rev1 hashes before proof work:

| Changed direct owner | Rev1 SHA-256 | Current baseline SHA-256 |
|---|---|---|
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `crates/yu-solver/src/shadow_apply.rs` | `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb` | `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` |
| `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/primitive.rs` | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` | `da1beeb825ffe5263733a88955d3061372e34b74cd585bb4006a070f7adefc57` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |

Also pin the rev2 identity owners and frozen test/artifacts:

| Input | SHA-256 |
|---|---|
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| Frozen Rust CLI test `tools/inference-playground/tests/cli_permission_boundary.rs` | `3efcf117612a513250a4396f5f21c15a0a3b2b89ac4ce27518979df8b3b93f13` |
| Rev1 proof `notes/theory/2026-10-19-r114-wrong-family-permission.md` | `447875018fee0f7a7e131658223ea9e7066b860fe8e8c3c35513877edf795f92` |
| Rev1 implementation handoff `tasks/agent-loop/inbox/20261019-r114-implementation.md` | `6eecb772e7ee30d7582c1f5d89b47e9310273f18a393c550f464f67960cf609e` |
| Rev2 obstruction `notes/theory/2026-10-20-r114-source-identity-completion.md` | `8f2a79d5c3a4c7f458da787d18927414d747a93315ccb35356c9677bca43e925` |
| Rev2 proof handoff `tasks/agent-loop/inbox/20261020-r114-proof-continuation.md` | `2d8cfd2daf37d374dc8fe86850f25c7425a325c056fa9c9a317c5ba733a833b3` |

No mismatch is accepted by inference. Any further required direct owner,
unexpected source alteration, unpinned dependency, or mismatch stops the
affected work. No pin may be added after prospective review without another
contract revision and review.

## Leases and review/verification gates

- **Proof, Sol/high, cap 360 seconds:** exact outputs only
  `notes/theory/2026-10-20-r114-source-identity-current.md` and
  `tasks/agent-loop/inbox/20261020-r114-proof-current.md`. Revalidate all
  frozen inputs; audit the seven owner deltas only as they affect the exact
  source; prove authentic key inequality and distinct effect identities; and
  trace the original permission route through current HIR/candidate/runtime
  owners. Return a current conditional argument or precise remaining
  obstruction. Do not expand source domain or claim parent/general theorem
  closure.
- **Luna source/public-path audit, cap 120 seconds:** no compiler/test edits.
  Write only `tasks/agent-loop/inbox/20261020-r114-luna-audit.md`. Record
  whether the frozen direct-Machine/CLI test still expresses the current API
  and public path. The Rust test is byte-frozen; no edits, output changes,
  browser additions, or generated artifacts are allowed.
- **Prospective spec review, cap 60 seconds:** review this exact contract,
  unchanged frozen Rust expectation, and one-shot command before any command
  runs. Exact output:
  `tasks/agent-loop/inbox/20261020-r114-rev3-prespec-review.md`.
- **Fresh final reviews, 180 seconds total:** independent compiler/source,
  spec/authority, and regression reviews, each at most 60 seconds, of frozen
  proof, Luna audit, test, and direct pins. Exact outputs:
  `tasks/agent-loop/inbox/20261020-r114-rev3-compiler-review.md`,
  `tasks/agent-loop/inbox/20261020-r114-rev3-spec-review.md`, and
  `tasks/agent-loop/inbox/20261020-r114-rev3-regression-review.md`.
- **Verification, Luna only:** only after all required outputs are frozen and
  all four reviews (prospective plus three final) are CLEAN, run exactly once:

  ```sh
  CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_permission_boundary wrong_family_permission_withholds_runtime_and_cli_result -- --exact --nocapture
  ```

  This is the first R114 execution attempt. Stop on any failure or predicted
  outcome mismatch. No alternate command, build, formatter, direct CLI call,
  Web edit/build, or retry is authorized.
- **Closeout, Luna, cap 60 seconds:** exact output
  `notes/progress/2026-10-20-r114-closeout.md`; retain all open parent gates.

## Resource reconciliation and stop conditions

Preserve **1,440 seconds charged**: rev1 proof 480 + implementation 240 +
completed pre-spec/compiler review pool 240 + closeout 120; rev2 prospective
review 60 + proof grant 240 + no-edit implementation grant 60. Rev1's NOT_RUN
command reservation was cancelled. Rev2's unstarted final review (180),
verification (240), and closeout (60) reservations were cancelled on STOP.

Rev3 cumulative ceiling: **2,340 seconds**, comprising 1,440 prior charged +
360 proof + 120 Luna source/public-path audit + 60 prospective review + 180
final reviews + 120 command + 60 closeout. This is a finite 420-second
extension over rev2's 1,920-second cap, granted by Luna after
dispatcher reconciliation. No other budget resets; unknown/interrupted assignments keep
their complete reservation. Astra 0; one heavy process maximum; no nested or
parallel verification.

Any mismatch, new required owner, non-CLEAN review, failed command, or changed
expected outcome stops without repair, retry, or theorem promotion. Rev1 and
rev2 evidence remain historical and immutable. Preserve all UNKNOWN
reservations and quarantined leases. Luna alone owns current state, review
adjudication, execution, closeout, explicit staging, outbound review, and
non-forced Git integration. Original A/B, adoption, effect-hygiene, source-law,
and production gates remain OPEN.
