# R186 — source emission and staged Option B implementation (candidate)

Status: **prospective review only**. No semantic source reads by workers and no
code writes are active under this candidate. Baseline branch
`research/simple-sub-intrusion`, HEAD `ef15618375343b5bfef0ba4aa3a7fbfbe5606d74`.
Preparation-start current-state SHA-256
`8039b4216461a92e071c0ef4cd1002c312c2701634f4e95ddec69c7960fb5bb5`.

## Fixed goal and end-to-end outcome

Continue the user goal unchanged: proof-backed inference/evaluator and broaden
unchanged Yulang2 Web sample execution; Luna alone integrates and pushes.
R185 closed CLEAN scoped research, not its original parent theorem. Preserve
`R183-FRONTIER-COVERAGE-1`, original quantifiers/source domain, A/B,
source/native, implementation and production gates as OPEN unless their own
proofs close.

R147 rev2 Option B is the provisionally adopted direction recorded in the
current state. This sprint advances the concrete expression-sequence path that
unblocks the unchanged `web/playground/examples/yulang2-ordinary-islands.yu`
countdown body. The staged sequence slice is not a claim that all of Option B
is complete: record-shaped/empty/spread behavior remains separately pending
where the selected semantics or existing representation is not yet supported.
Do not silently discard items or invent field/duplicate/spread/lookup/rendering
rules. Preserve existing colon arms and no-else Unit.

## Frozen authority/evidence

- R147 decision draft: `notes/design/2026-10-20-braced-if-compatibility-r147.md`,
  SHA-256 `2dbbf05c2c74810c4684a71d81933d4b6b4a9be2067dcc60b943bb090ff64f12`.
- R147 rev2 packet:
  `tasks/agent-loop/sprints/braced-if-approval-packet-20261020-r147-rev2.md`,
  SHA-256 `87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281`.
- R185 closeout: SHA-256 `8dc8691026478973054bee05f1ff3feb941fa4fef05951b6d1cd8cd0aee5a0d1`.
- R183 source-to-Capture proof: SHA-256
  `0fe3afdc4ddfd1d3b8979bf34497e395bef06836a199cb6735a39eb84c43a28d`.
- R185 rev1 local proof: SHA-256
  `8e102bfa1badaba2578eaef3cf6e76100d52bdb9b312b22e2368dbc570c47161`.
- R185 rev2 admission bridge: SHA-256
  `929390664ca527725661fbc434c4a24d5d64d37db6f718a436a92e17dc8ce780`.
- R185 Option B map: SHA-256
  `9f858110df227709a2b4fc30bc7941f6172cec9c8c40486efc37874d49faebca`.
- Unchanged Web fixture SHA-256
  `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`.

R147's accepted direction gives ordinary non-record braced arm expression
lists source-order sequence behavior; record-shaped empty/field/spread meanings
remain distinct and mixed non-record spread is explicitly rejected. Preserve
all existing Web expectations and require the unchanged fixture result
`countdown_result -> 8`. R186 does not change the fixture.

## Exact committed source manifest

After prospective CLEAN and activation, semantic reads are limited to these 50
committed blobs at the exact baseline above. Hash is SHA-256 of blob bytes; mode
is Git mode. Dirty worktree bytes and external Yulang2 worktrees are excluded.

| Source owner | SHA-256 | Mode |
|---|---|---|
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

## Lanes and exact write authority

1. **Proof / Sol-high / 1200s.** Continue
   `R185-POSITIVE-N-EMISSION-1`: construct an authenticated actual source history
   for positive-n provider exposure or prove the source-position/level invariant
   that excludes it or supplies a compensating same-provider mapped path. Use
   actual Apply polarity/slots and Formal/Name association, not another
   constructor inventory. Preserve the R185 local premises and original theorem
   quantifiers. A conditional abstract mixed frontier is not a counterexample.
   Exact outputs:
   - `notes/theory/2026-10-21-r186-positive-name-emission.md`
   - `tasks/agent-loop/inbox/20261021-r186-proof-result.md`
2. **Implementation-contract design / Luna-high / 600s.** Complete an exact
   sequence-slice constructor-to-runtime contract using only the manifest above.
   Define occurrence identity, ordered children, final-result typing, cumulative
   effects, continuation/resumption, no-else Unit, malformed and record-shaped
   stop cases, unchanged fixture path and focused coverage. Enumerate every
   exact code/test path and consumer; no code, tests, builds or execution in this
   lane. Record semantics with no approved rule remain OPEN and out of this
   slice. Exact outputs:
   - `notes/design/2026-10-21-r186-option-b-implementation-contract.md`
   - `tasks/agent-loop/inbox/20261021-r186-implementation.md`

These producer output leases are disjoint. The conditional code write list is
predeclared below; it becomes active only after Luna freezes the implementation
contract, a fresh independent prospective contract review is CLEAN, and Luna
records activation. It must be an exact subset of this list. Any added file,
semantic premise or consumer owner requires sequential revision and review.

### Conditional Luna code write paths — not active at candidate time

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
- `tools/inference-playground/tests/cli_ordinary_islands.rs` (new file)
- `web/playground/src/main.ts`
- `web/playground/smoke-test.mjs`

The fixture, `tools/inference-playground/src/lib.rs`, and dirty solver owners
`candidate_context.rs`, `candidate_scheme.rs`, `lib.rs`, `shadow_apply.rs` are
not write paths. If the exact source/runtime path requires them, STOP for a
sequential dependency/lease revision; preserve the current dirty bytes.

Focused verification, only after code activation: targeted parser, HIR, solver,
playground CLI, and Web/WASM smoke checks for the unchanged fixture and all
existing expectations. No full workspace suite by default. No tests/builds/
probes are authorized before code activation.

## Gates, budget, and stop conditions

Original parent/A/B/source-native gates remain OPEN. A completed proof lane is
reviewed separately and cannot certify itself. Code can be developed as an
approved independent sequence increment while provider-frontier proof remains
open; no result is promoted as a complete inference or evaluator theorem.

Fresh cap 6000 seconds, no carryover: preparation plus initial prospective
review 240; proof 1200; implementation-contract design 600; conditional code
implementation 2400; focused verification 600; independent reviews 600; closeout
360. Reviews split exactly: 120 prospective implementation-contract review
before code activation; 180 independent proof-witness review; 300 final code/
source/check review. The code allocation stays unavailable until the 120-second
prospective review is CLEAN and Luna activates. Verification stays unavailable
until code freezes. If a gate does not fit its allocation, STOP that gate; do
not borrow, renew or claim approval. Astra 0; descendants 0.

The initial candidate remains inactive until a fresh exact-pin/authority/lease
review is CLEAN and Luna records activation. Before then only candidate and
hash/mode review are allowed. No source-semantic reads, tests, code edits,
compiler/sample execution, Git staging/commit/push, or external Yulang2 reads.
After activation, all lane writes remain on the exact paths above. Only Luna
integrates and performs Git actions.
