# R185 — source-history coverage and Option B representation design (candidate)

Status: prospective review only. No source-semantic reads or worker assignments
are active under this candidate. Baseline: branch `research/simple-sub-intrusion`,
HEAD `1ec02864dccccffa9617705b0ddbeaa64176aff5`. The live current-state input at
preparation start was SHA-256 `ee6733027062ed7a8132621028f63ed202a2e269dac7da02fd4daad903604e54`.

## Original goal and outcome

Continue the active goal: proof-backed inference/evaluator and broaden unchanged
Yulang2 Web samples, with Luna sole Git integrator. R183 remains unfinished:
`R183-FRONTIER-COVERAGE-1` and original parent/A/B/source-native gates stay
OPEN. R184 owner mapping ended with a MAJOR review finding, not code readiness.

R185 has two bounded read-only lanes after activation:

1. **Proof (Sol/high, 1200s):** apply R183's reviewed local Capture/FreshUse and
   independent-demand results to the original source-history obligation; prove
   reachability excludes the abstract mixed shared/local cutoff, or construct
   an accepted source-qualified counterexample with the same provider/use.
   Keep the original quantifiers and source domain.
2. **Representation design (Luna/high, 1200s):** produce an exact constructor-to-
   consumer design for provisional R147 rev2 Option B, repairing R184's exact-
   path gap. The mapping must state current definitions versus missing owners,
   record semantic premises not established by repository evidence, occurrence
   and order preservation, solver/effect/continuation obligations, and the Web
   fixture falsifier. This is design only, with no code/tests/builds/execution.

The unchanged fixture must eventually produce `countdown_result -> 8`; R185 will
not run it. Preserve no-else Unit, all R147 accepted/rejected cases, every
existing Web expectation, R167/R149 separation, and all open proof gates.

## Frozen evidence and review findings

R183 proof note SHA-256
`0fe3afdc4ddfd1d3b8979bf34497e395bef06836a199cb6735a39eb84c43a28d`; result
`e9dfe4353a92a933a9aa282960e827cc92f4bb530ad06bb93f80b025936b3d8e`. It is
reviewed CLEAN scoped, with `R183-FRONTIER-COVERAGE-1` still open.

R184 contract rev3 SHA-256
`a49e651c2efc17837f7feee4e5d2f24e10d997f0ae1d5746ac2e8c95f97c881d`; owner-map
note `f38e913e7e0eda6558dac293714176b9d6d1bd8f66e2a28e4bf7e69cda2a6f9f`; result
`267a64103fd9c40f81f760c4f4a72e367293a6aa6c0c8fb453c39d6d755f0bcc`. Fresh
review found MAJOR: the map must name concrete missing paths and distinguish
existing owners. The exact newly required path is
`tools/inference-playground/src/runtime/receiving.rs` (machine and continuation
import `ExecutionView`/receiving state, and `runtime/mod.rs` declares the module).
The already-pinned `tools/inference-playground/src/lib.rs::execute` owns selected
definition scheduling and output formatting at lines 167–201; do not request it
again as an unknown owner. Additional exact candidate owners in this revision
are the type representation, term and candidate scheme/extrusion/intrusion, and
playground render paths below. They are candidates to inspect, not findings about
their contents.

## Immutable source manifest

After prospective CLEAN and Luna activation, inspect only these committed blobs
at the exact baseline above. SHA-256 is over blob bytes; mode is Git mode.
Uncommitted worktree source and external Yulang2 worktrees are excluded.

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
| `crates/yu-types/src/lib.rs` | `c6587027612157c070a1b27b297a9f5aeec066422cf550eb78e3ec4828f0aa6b` | `100644` |
| `crates/yu-solver/src/term.rs` | `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60` | `100644` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225` | `100644` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332` | `100644` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` | `100644` |
| `tools/inference-playground/src/render.rs` | `86dba831366995d4c36e2446c9b8e6847f7bff524d5e7e7b6d12d02ff337fc66` | `100644` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` | `100644` |

## Exact leased outputs

Proof lane:
- `notes/theory/2026-10-21-r185-frontier-source-history.md`
- `tasks/agent-loop/inbox/20261021-r185-proof-result.md`

Representation-design lane:
- `notes/design/2026-10-21-r185-option-b-representation.md`
- `tasks/agent-loop/inbox/20261021-r185-implementation-design.md`

These outputs are disjoint from R183/R184 frozen artifacts and from each other.
No other writes, scratch, descendants, probes, tests, builds, compiler or sample
execution, network, Yulang2 worktree reads, code, Git staging, commit or push.

## Required evidence and falsifiers

The proof lane must identify the source constructors/admission steps that could
create shared/local transitions, prove the needed invariant across all allowed
steps, or provide a complete emitted source history and authenticated same-
provider/use consumer route. A static relation skeleton is not a counterexample.
Falsifier: an admitted history emits the mixed frontier with no compensating
mapped path.

The design lane must distinguish existing definitions from missing constructors
and consumers for braced if bodies, ordered expression sequences, empty/field/
spread records, explicit rejection, constraints, effects, rollback/scope,
runtime frames, saved continuation state, value rendering, CLI/WASM/Web sample
selection, and focused tests. It must explain source occurrence conservation
and evaluation order. Repository silence cannot decide record merge, duplicate
field, or lookup rules; retain those as explicit semantic questions. Falsifier:
any accepted source shape lacks a consumer, any item/effect is lost or reordered
on resume/replay, or the unchanged fixture's required result is unsupported.

A complete code contract is not an R185 output. Any implementation requires a
separate exact-path contract, prospective CLEAN review and activation.

## Resources, review and gates

Proposed fresh cap: 3600 seconds, no carryover: preparation/prospective review
240; proof 1200; representation design 1200; final independent review 600;
closeout 360. Astra 0; compiler execution/tests/builds/probes 0; descendants 0.
The two producer lanes are bounded and concurrent only after activation. A fresh
prospective reviewer must verify all pins, authority, lease disjointness,
resource arithmetic, R184 MAJOR correction, proof lineage and stop boundaries.
After both outputs freeze, a fresh independent final review covers proof and
design; Luna adjudicates and alone owns current state/Git.

This candidate is not active until prospective review is CLEAN and Luna records
activation. Until then, the only permitted work is reviewing this candidate and
its exact hashes/modes; no source-semantic inspection or producer launch.
