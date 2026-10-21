# R184 — Option B source-owner map (revision 3)

Status: prospective-review candidate; no additional source inspection is active.
This is a bounded read-only mapping extension to active R183. It preserves the
R183 source-to-Capture proof and all original theorem claims. Branch
`research/simple-sub-intrusion`; source baseline commit
`1ec02864dccccffa9617705b0ddbeaa64176aff5`.

## Objective and authority

Produce a complete, reviewable source-owner matrix for the provisionally
adopted R147 rev2 Option B end-to-end route: dedicated braced-arm CST and
recovery; occurrence-preserving HIR sequence and record representation; source
constraint construction, transport and consumers; evaluator continuation,
effects and order; CLI/WASM/Web route; focused parser/HIR/inference/runtime and
Web regression owners. For each row report the constructor, all relevant
consumers, exact source definition, existing representation, required edit
surface if absent, directly applicable proof premises, and falsifier. This
result is an owner map, not an implementation contract or code permission.

User intent provenance stays as recorded by R183: the user directed provisional
adoption and continuation; Luna interprets that as Option B from the previously
reviewed R147 proposal. The user did not name B. Preserve all R147 shape cases:
ordinary non-record expression lists evaluate left-to-right; empty records,
inline fields and at most one operand-bearing record spread retain record
meaning; malformed lists, duplicate spreads and non-record mixed spreads are
rejected explicitly. No source item may disappear silently. The unchanged Web
fixture must eventually yield `countdown_result -> 8`; this mapping does not
execute it.

## Parent and fixed dependencies

R183 rev3 contract:
`tasks/agent-loop/sprints/source-to-capture-and-sample-readiness-20261021-r183-rev3.md`,
SHA-256 `6380fedea2dad3e302fd8ed2ce99a010c61eff493b7010c17476020afa028dd8`.
R183 Option B preparation result:
`tasks/agent-loop/inbox/20261021-r183-braced-if-implementation.md`, SHA-256
`6d0bcd380914aaac37e4a5885d5a094701a6db4ecf27ade0cb52a98329f8d67d`.
R183 reviewed design:
`notes/design/2026-10-21-r183-braced-if-implementation.md`, SHA-256
`17f73daf42b32452c544965aff7c85d31950b89ae7d9397dca03e1a2180c3513`.
R183 readiness handoff SHA-256
`29398ce0f258ebb9bab824b7bd66c18f1807eb9276d2e990634fe13e9e76cc08`.
The current-state baseline at R184 preparation start was the committed
`tasks/agent-loop/current.json`, SHA-256
`6af9eb8d3ada3feef7b5f4bbb6b6675bf98bc1cc63001cf20dc22d035b994a5b`.

R147 reviewed proposal bundle and final review remain governed by R183 rev3;
the decision design itself is SHA-256
`2dbbf05c2c74810c4684a71d81933d4b6b4a9be2067dcc60b943bb090ff64f12`.
Fixture identity is SHA-256
`f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`.
R167 `R167-CASE-FETCH-1` and R149 module/type/initialization obligations stay
separate. They do not automatically block the selected-definition countdown
route.

## Immutable source manifest

Read only these committed Git blobs at the exact baseline above. Hashes below
are SHA-256 of the blob contents; modes are Git modes. The live worktree has
uncommitted edits in solver files; those bytes are excluded. Do not read the
dirty external Yulang2 worktrees or infer owners from them. A required owner
outside this manifest is a stop-and-report dependency request to Luna, not an
implicit expansion.

| Owner candidate | SHA-256 | Mode |
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

## Assignment and output leases

After prospective CLEAN and Luna activation, Luna/high performs a read-only
constructor-to-consumer audit and writes exactly:

- `notes/design/2026-10-21-r183-option-b-owner-map.md`
- `tasks/agent-loop/inbox/20261021-r183-option-b-owner-map-result.md`

The matrix must enumerate every accepted/rejected shape and follow its source
occurrences through parser recovery, HIR identity/order/scope, constraints and
record/list choice, effects, solver consumers, runtime continuation and order,
CLI/WASM/Web selection, and focused regression owners. Distinguish proven direct
owners from unresolved owners. State every missing evidence item and a concrete
falsifier. If these inputs do not establish a complete mapping, return
`NO_SAFE_CODE_CONTRACT` with the exact missing path and propose a sequential
manifest revision. No extra source reads, scratch, generated files or children.

R183 proof worker `/root/r183_source_to_capture_proof` has STOPPED. Its exact
theory and handoff outputs remain frozen under their existing paths pending
independent review; the worker has no active reservation. Charge its assigned
1200 seconds. The reported mixed shared/local frontier remains a static
falsifier unless an emitted source history and same-provider/use route are
established. The original parent, quantifiers, and source/native correspondence
remain open.

## Resources, review and gates

R183 has 2400s charged after the proof writer stopped (the prior 1200s plus
its conservatively charged 1200s assignment) and 600s still reserved under
its 3000s cap. Extend the combined cap to 4800s by a separately recorded
1800s addition for owner-map
preparation 240s, mapping 1200s, independent review 240s, and closeout 120s.
No carryover or reset. Astra 0; compiler execution/tests/builds/probes 0;
descendants 0. Unknown legacy workers and leases stay quarantined.

Prospective review must verify the original R183 authority and frozen proof
result are preserved, the new source manifest is exact and rooted in the
committed HEAD, worktree edits remain excluded, outputs are disjoint from proof
artifacts, and resource arithmetic is consistent. A fresh source/compiler reviewer inspects
the frozen mapping before Luna can prepare the full implementation contract.
That later code contract still requires its own CLEAN prospective review and
activation. Mapping review grants no code, test, build or execution rights.

Stop on a manifest mismatch, any required unlisted source owner, authority
ambiguity, counterexample or resource boundary. The proof worker has already
stopped; do not relaunch it. Luna alone owns central state, sequential
revisions, adjudication and Git.
