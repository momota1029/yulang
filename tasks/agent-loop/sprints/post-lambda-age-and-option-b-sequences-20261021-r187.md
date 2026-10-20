# R187 — post-Lambda age proof and Option B sequences (candidate rev8)

Status: **rev8 sequential review pending**. Rev6 activation and rev7's parser expectation/scratch lease were CLEAN. Isolated parser checks found one further stale pending-boundary expectation for an unclosed braced `else` body; rev8 gates that exact matrix adjustment and malformed-body recovery assertion behind fresh review.
Baseline branch: `research/simple-sub-intrusion`; baseline HEAD `d314168e12e2e5138c7d45f84767f5e6eb39edbc`.
Preparation-start current-state SHA-256: `f5d7e8ec24c0fd18eca318dd253b093a65fa5b71e824be9bcabe9fcb46b244aa`.

## Goal and authority

Preserve the active user goal unchanged: proof-backed inference/evaluator implementation and broad execution of unchanged Yulang2 Web demo samples; Luna alone integrates and pushes. Prioritize making the sample work end to end while retaining the proof/source correspondence obligations. R147 rev2 Option B is provisionally adopted; do not request its approval again.

R186 closed CLEAN scoped unfinished. Independent review established a local bare-Name finite Catch/finish compensation under successful ordered-input premises: negative demand extrusion lowers the formal Value endpoint and original Name effect together; the Lambda return takes the now-shared Value level; Capture restores the same-use suffix. It did not prove universal post-Lambda exposure/age or Group facade coverage. Keep `R186-POST-LAMBDA-NAME-AGE-1`, `R186-GROUP-SAME-USE-1`, original A/B/source-native and production gates OPEN. Exact receipts: R186 closeout SHA `2f82f1c08deb5ce3bcc3c6ebe5671d966527039eefa8a47e6f99ef83fc5d92c2`; proof note `84a235ad62c8ee980c3d71f96bf24496d4e9941ea13d4bca2c33eee44bc0a4ae`; proof handoff `8776b1a2cf3bb7777479c2eb165b00221d526ba4b6fd6409c9909b93c0748a2d`.

The R186 implementation contract rev1 review found MAJOR because “every selected child” could weaken the primitive certifier's universal retained-object invariant. Corrected R186 rev2 explicitly requires every retained definition, arm, dependency and sequence child; it remains unreviewed. R187 gives that corrected exact contract a fresh review allocation before any code activation.

Frozen authority pins:
- R147 decision `notes/design/2026-10-20-braced-if-compatibility-r147.md`: `2dbbf05c2c74810c4684a71d81933d4b6b4a9be2067dcc60b943bb090ff64f12`.
- R147 approval packet `tasks/agent-loop/sprints/braced-if-approval-packet-20261020-r147-rev2.md`: `87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281`.
- Corrected R186 design `notes/design/2026-10-21-r186-option-b-implementation-contract.md`: `4e59c25947f3e3ea5acc746ca3e4483f7c4225028f93ad9ec54db3035c2117d9`.
- Corrected R186 handoff `tasks/agent-loop/inbox/20261021-r186-implementation.md`: `d4ad8e9bfbe15a49d99de7759b20e6d99f7a768774b03f254d5350cd733fb3dd`.
- Original parent `notes/theory/2026-10-15-computation-forwarding-preservation.md`: `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
- Unchanged Web fixture `web/playground/examples/yulang2-ordinary-islands.yu`: `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`; required existing result remains `countdown_result -> 8`.

## Exact source baseline pins

Only after CLEAN initial review, source reads are limited to these 50 committed blobs at `d314168e12e2e5138c7d45f84767f5e6eb39edbc`. Hash is SHA-256 of blob bytes; third column is Git mode. Never inspect dirty worktree bytes or external Yulang2 worktrees.

| Source owner | SHA-256 | Mode |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/if_expr.rs` | `509af68c34e11a2a2d5538df8bab84c599d68154a3f03d57c304bbfb04d8cd39` | `100644` |
| `crates/yu-syntax/src/expression/mod.rs` | `05d874dd4c2874eb7b24038467c8a74b22fa6f7821a3980f3348683ad02743f1` | `100644` |
| `crates/yu-syntax/src/expression/delimited.rs` | `e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95` | `100644` |
| `crates/yu-syntax/src/syntax_kind.rs` | `26d2a0ddbe1862c95c503420ded0b0d35217bee5ba9f350be9163c065c6b488d` | `100644` |
| `crates/yu-syntax/src/sequence.rs` | `1a68331e5d16d46471545e673226541dc848123d1c3e286260359cecf41adcd2` | `100644` |
| `crates/yu-syntax/src/rule/expression_list.rs` | `e30e915dca56c9609709280e9f053c151e16e1f9619340a56abd470241b545f5` | `100644` |
| `crates/yu-syntax/src/expression/tails/colon.rs` | `df37d747f396e8b27c53b6785e4a26f5210162b14e65b4648d449495bf8f5982` | `100644` |
| `crates/yu-syntax/src/expression/tails/with_body.rs` | `4fdf57e9a19b8897871d666ab5ec8adaa7c9219fc775d6c54cddc4555f61c058` | `100644` |
| `crates/yu-syntax/src/tests/if_expr.rs` | `5133fec3401b849662ef0e9155eb82ebbd69544a448484ec07c3262191db503d` | `100644` |
| `crates/yu-syntax/src/tests/delimited_recovery.rs` | `8e80d66b36ae390a803edf27dbe9485bb4797f8a48dfb639dd31c64fcad082ce` | `100644` |
| `crates/yu-syntax/src/tests/expression_recovery.rs` | `e744ebbbd07c7ccfb53c452e0db13d0bf5f984567cc4df7dc768dc2a23567a1a` | `100644` |
| `crates/yu-syntax/src/tests/braced_statement_recovery.rs` | `4bb110be9f307dd98fba277e35069b9d9ead051406fccce384dd47c081b7fca8` | `100644` |
| `crates/yu-syntax/src/tests/rule_expression_list_recovery.rs` | `3c3f03de751af147232096c74bd2034495300df4a0d93633321e9000dd98a367` | `100644` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` | `100644` |
| `crates/yu-syntax/src/syntax_diagnostic.rs` | `b3c5e959e646ad3d557c4f60c367d80731bf6a8e616a08326827f687e9077714` | `100644` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` | `100644` |
| `crates/yu-hir/src/module.rs` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` | `100644` |
| `crates/yu-hir/src/module/local_source.rs` | `d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442` | `100644` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` | `100644` |
| `crates/yu-hir/src/shadow.rs` | `ae5f40a9b1d34d08938eb23b8bc3d1756411d146b5c83ba73b7294f5d332a654` | `100644` |
| `crates/yu-hir/src/tests/shadow_source_core.rs` | `d2a0c4464e46cd697efae9b4e374a152069fd1226cc8624742880d7e72d83ebd` | `100644` |
| `crates/yu-solver/src/candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` | `100644` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0` | `100644` |
| `crates/yu-solver/src/candidate_context.rs` | `ac1375954d0d310bbeaaccb09625dc4701dd1c25a050a67f1f203d91e9456b06` | `100644` |
| `crates/yu-solver/src/candidate_effect.rs` | `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1` | `100644` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` | `100644` |
| `crates/yu-solver/src/candidate_unit_tests.rs` | `d9679812bcbb08b53b494768c8b1bdc21bb89b9c2db59d705f1747c388451e13` | `100644` |
| `crates/yu-solver/src/lib.rs` | `99dc39e970b35f2d06a900826bf686ee5a76795430a3e4167ac5c64184da6af6` | `100644` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` | `100644` |
| `tools/inference-playground/src/runtime/machine.rs` | `875213902660c06ffa393c8fef001c4e67d229486fed6ef8773c6abd9a3b23f1` | `100644` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` | `100644` |
| `tools/inference-playground/src/runtime/mod.rs` | `64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b` | `100644` |
| `tools/inference-playground/src/lib.rs` | `a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473` | `100644` |
| `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` | `100644` |
| `apps/yulang-wasm/src/lib.rs` | `2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a` | `100644` |
| `web/playground/src/main.ts` | `f4e8dfaf3f089fbee63abac9cc69506cfdd280ad5bdcb980096dbfa83e689a5b` | `100644` |
| `web/playground/smoke-test.mjs` | `4abce089ada2822578df4dcefa023d0ad83929b2d7188fe4527ee29f80b47d9a` | `100644` |
| `web/playground/examples/yulang2-ordinary-islands.yu` | `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487` | `100644` |
| `crates/yu-types/src/lib.rs` | `c6587027612157c070a1b27b297a9f5aeec066422cf550eb78e3ec4828f0aa6b` | `100644` |
| `crates/yu-solver/src/term.rs` | `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60` | `100644` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225` | `100644` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332` | `100644` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` | `100644` |
| `tools/inference-playground/src/render.rs` | `86dba831366995d4c36e2446c9b8e6847f7bff524d5e7e7b6d12d02ff337fc66` | `100644` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` | `100644` |
| `crates/yu-solver/src/shadow_apply.rs` | `13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5` | `100644` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | `100644` |
| `crates/yu-hir/tests/conditional_local_source.rs` | `1a271192071dc3c690080802c69ad63246f631f7a9039b4200c40fbffb139c40` | `100644` |
| `crates/yu-solver/tests/ordinary_expression_source.rs` | `c223c913fcf8a9101fbc527979bbd104db68c1191ab53bf2f3c47dcd2fa53918` | `100644` |
| `tools/inference-playground/src/runtime/primitive.rs` | `da1beeb825ffe5263733a88955d3061372e34b74cd585bb4006a070f7adefc57` | `100644` |

## Lanes and gated scope

1. **Proof / Sol-high / 1200s.** Continue `R186-POST-LAMBDA-NAME-AGE-1`: source-position/level induction for a later authentic positive Name exposure after Lambda return allocation. Prove the existing mapped same-use suffix is always retained, or give a source-authenticated finite history that loses it under original quantifiers. Use the direct-Name R186 compensation as a lemma. Keep Group facade separate under `R186-GROUP-SAME-USE-1`; do not use Group to refute the narrower parent §1 whole-actual-argument-as-resolved-Name fragment. Exact outputs:
   - `notes/theory/2026-10-21-r187-post-lambda-name-age.md`
   - `tasks/agent-loop/inbox/20261021-r187-proof-result.md`
2. **Implementation-contract design / Luna-high / 480s.** Refresh the R186 sequence-slice contract against the current exact baseline and source owners. Define parser child order/recovery, unique occurrence conservation, HIR ordered direct children, last-value typing, cumulative effects, no-else Unit, continuation exact-once suffix behavior, unchanged Web route, and focused verification. Preserve colon/inline/indented forms. Keep record-shaped empty/field/spread/duplicate/override/lookup/rendering and mixed spread rules explicitly OPEN/deferred. Primitive certification must retain the universal condition over every retained definition, arm, dependency and sequence item, including unused retained code; selected-path coverage is insufficient. Exact outputs:
   - `notes/design/2026-10-21-r187-option-b-implementation-contract.md`
   - `tasks/agent-loop/inbox/20261021-r187-implementation.md`
3. **Conditional code / Luna only / 1200s remaining envelope.** Rev6 activation was recorded after CLEAN. Rev7 and rev8 each transfer 120 seconds from the remaining code allowance for independent spec review. Continue only on the already listed source paths; do not change the newly identified recovery expectation until rev8 is CLEAN.

Conditional candidate paths:
- `crates/yu-syntax/src/expression/if_expr.rs`
- `crates/yu-syntax/src/expression/mod.rs`
- `crates/yu-syntax/src/expression/delimited.rs`
- `crates/yu-syntax/src/syntax_kind.rs`
- `crates/yu-syntax/src/sequence.rs`
- `crates/yu-syntax/src/expression/tails/with_body.rs`
- `crates/yu-syntax/src/tests/if_expr.rs`
- `crates/yu-syntax/src/tests/delimited_recovery.rs`
- `crates/yu-syntax/src/tests/expression_recovery.rs`
- `crates/yu-syntax/src/tests/braced_statement_recovery.rs`
- `crates/yu-syntax/src/tests/rule_expression_list_recovery.rs`
- `crates/yu-hir/src/lib.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/source_identity.rs`
- `crates/yu-hir/tests/conditional_local_source.rs`
- `crates/yu-solver/src/candidate_value_graph.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/tests/ordinary_expression_source.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/primitive.rs`
- `tools/inference-playground/src/runtime/continuation.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/tests/cli_ordinary_islands.rs` (new)
- `web/playground/src/main.ts`
- `web/playground/smoke-test.mjs`

The unchanged fixture is read-only. Dirty `crates/yu-solver/src/candidate_context.rs`, `candidate_scheme.rs`, `lib.rs`, `shadow_apply.rs`, and `tools/inference-playground/src/lib.rs` remain excluded. If a required consumer depends on an excluded path, stop for exact sequential revision; preserve current dirty bytes. Do not write code or tests before activation.

Verification-only lease: `/tmp/yulang-r187-validation-r7`, owned by Luna. Build the temporary tree from the pinned baseline archive, then overlay only R187 changes from the exact candidate path set. Keep Cargo output under its `target/`. Do not copy dirty excluded files, create Git metadata, or implement in this tree. Remove it after isolated checks and final review.

Focused verification, only after activation: targeted parser/HIR/solver/CLI/Web-WASM paths; assert source order, each item once, final child value, all item effects, continuation suffix through suspension/resumption, no-else Unit, recovery behavior, universal primitive-certifier coverage over unused retained objects, existing outputs, unchanged fixture SHA and `countdown_result -> 8`. No broad expected-output changes.


## Sequential repair after rev1 review

Rev1 was NOT CLEAN: its design named the new CLI test without leasing that path in this governing candidate, and it required every old parser expectation to remain unchanged even though the approved braced-arm syntax supersedes one brace-rejection expectation. Rev1 review and pins remain recorded in current-state receipts.

Rev2 added lease for `tools/inference-playground/tests/cli_ordinary_islands.rs` as a new file without claiming a baseline blob hash. Its first exact pre-write delta removes only `"if x { body }"` from `if_c6_keeps_non_companion_and_shallow_newline_outward`, preserving both colon cases, and adds the braced input to accepted `IfArm` parsing; that delta received CLEAN review. Rev7 adds a second delta: remove `("if x { body }", "if x ", 5, " body }")` from `if_completed_condition_missing_introducer_owns_ordinary_gap_only`; that delta also received CLEAN review. Rev8 addresses only the `suffix == " { rest"`, `head == "if x: a else"`, no-error case in `if_inline_boundaries_preserve_pending_payload_leading_and_successor`: remove that tuple combination from the old pending-boundary matrix and cover it in a dedicated malformed-braced-else recovery test. Keep comma, paren, newline, CRLF and all other brace cases unchanged. Assert recovery and HIR refusal to publish the partial sequence. No other parser expectation or Web output is waived; fixture bytes and `countdown_result -> 8` stay pinned.

## Budget and gates

Fresh cap **6000s**, no carryover. Current **3540 charged** (prior 3300, rev7 review120, rev8 review120) + **2460 reserved** (code1200, focused checks600, final review300, closeout360) = 6000. Both incremental reviews transfer from the code reserve. R187 proof and proof-review charges are included in the prior 3300. R186's 2690s are closed and not reset. No Astra; descendants 0; unknown legacy leases remain quarantined. No parallel heavy test/build process.

Rev6 activation is already recorded. Rev7 review approved its parser expectation and validation-only scratch lease. Rev8 covers the newly identified malformed-else recovery case; do not edit that test expectation before CLEAN. If a gate fails or does not fit its allocation, stop that gate with no borrowing/renewal. All original theorem and production gates remain OPEN unless separately closed.

Rev2 review was NOT CLEAN on stale budget fields and a stale handoff pin. Its pre-write spec review approved the exact single brace expectation change above. Rev3 synchronizes candidate/design/handoff/current pins and resources; no tests have been edited.

Rev5 review was NOT CLEAN on resource interpretation and stale code grant. Rev6 separates consumed charges from future reservations and records the last recheck grant as charged. Earlier review grants are not repeated in reservations. Prior NOT-CLEAN review receipts and the CLEAN pre-write expectation ruling remain preserved.

Rev4 review was NOT CLEAN on reserved/charged interpretation and stale handoff code grant. Its exact expected-output ruling remains CLEAN. Review history archive: `notes/progress/2026-10-21-r187-contract-review-history.md` SHA-256 `b18aca005fe9b670dc8c2d9e1e556fd10a89b53e90ea58dc70112377aa755850`. Rev5 separates spent charges from remaining reservations and reduces code to1440s to fund one final240s bundle recheck.

Rev6 returned CLEAN for activation with minor record corrections; rev7 returned CLEAN for its parser delta and scratch lease. Isolated `yu-syntax if_` verification found one additional stale malformed-else pending-boundary expectation; rev8 freezes its exact adjustment and keeps malformed HIR publication rejected.

Review charge identity map: the 720s historical contract-review allocation is three 240s runs: `/root/r187_contract_review` (initial rev1), `/root/r187_contract_review_rev2` (rev2), and `/root/r187_contract_review_rev4` (third run, first reviewing rev3 and then its repaired rev4 follow-up). Rev4 is not a fourth run; rev5 is a primary artifact revision, not an assigned review. Rev6 is a separate 240s run. Current live resource totals include the completed 1200s proof charge.
