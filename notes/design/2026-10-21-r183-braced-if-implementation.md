# R183 provisional Option B implementation preparation

Status: **provisional working decision; implementation contract not yet ready
for review; no compiler edits or execution authorized.**

## Authority and scope

The user's standing goal is proof-backed type inference/evaluator
implementation and broad execution of unchanged Yulang2 Web samples. After the
R147 decision gate was raised, the user directed provisional adoption and
continuation. Luna interprets this as provisional adoption of **Option B** from
the independently reviewed R147 rev2 packet because it best fits the broad
sample-compatibility goal. The user did not name B in that message; this
contextual interpretation is recorded rather than attributed as a direct quote.

R147 rev2 exact proposal contract SHA-256:
`87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281`.
The five-artifact review receipt and hashes are pinned by the R183 rev3 sprint
contract and verified by its CLEAN prospective review. The R147 closeout's
historical “pending user decision” state predates the later provisional
instruction. No language rule is marked permanently adopted by this note.

## Provisional Option B behavior

The complete proposal keeps the original countdown sample unchanged and adds a
dedicated braced-arm path rather than reusing ordinary statement blocks:

- Preserve condition/body ownership, source order, arm scope, matching-close
  ownership, colon-form behavior, effects, and existing conditional semantics.
- Lower ordinary non-record expression lists in source order with explicit
  left-to-right sequence behavior.
- Preserve record-shaped meaning for `{}`, inline fields, and at most one
  operand-bearing record spread.
- Explicitly reject malformed lists, duplicate record spreads, and non-record
  mixed-spread forms. Never silently discard a source item.
- The unchanged `web/playground/examples/yulang2-ordinary-islands.yu` must
  eventually produce `countdown_result -> 8`; retain its three identity
  observations and all current expected outputs.

This is finite source-compatibility evidence, not a proof of the general
inference/evaluator A/B obligations. R70/R71, source/native correspondence,
parent soundness and production gates remain OPEN.

## Pinned owner map already available

R147 rev2's independently reviewed owner map identifies the initial path:

| Stage | Pinned owner | Stated role |
|---|---|---|
| Parser/recovery | `crates/yu-syntax/src/expression/if_expr.rs` | Parse `if`/`elsif`/`else` arm body boundaries and recovery |
| HIR | `crates/yu-hir/src/module/local_source.rs` | Admit arm bodies with original source identities and arm order |
| Constraint generation | `crates/yu-solver/src/candidate_source.rs` | Consume conditional source forms and combine branch values/effects |
| Runtime construction | `tools/inference-playground/src/runtime/program.rs` | Build ordered conditional execution representation |
| Runtime evaluation | `tools/inference-playground/src/runtime/machine.rs` | Consume conditional representation |
| CLI and playground API | `tools/inference-playground/src/main.rs`, `src/lib.rs` | Select and execute the unchanged definition |
| WASM and Web | `apps/yulang-wasm/src/lib.rs`, `web/playground/src/main.ts`, `web/playground/smoke-test.mjs` | Expose and exercise the unchanged sample in browser flow |

R147 pinned these direct owners, but did not define the new sequence HIR,
constraint, or continuation owners required by Option B. No contents outside
the R147 frozen bundle were inspected for this preparation result.

## Exact gaps before a code contract can be reviewed

The implementation contract needs a bounded source-mapping stage to discover
and pin the exact current owners for:

1. The CST node and parser test owners for dedicated braced `IfArm`/`ElseArm`
   ownership and recovery, including malformed/record/list sibling cases.
2. The occurrence-preserving HIR sequence representation and its constructor,
   visitor, identity, and source-range invariants.
3. Sequence/record constraint generation and the exact consumers that retain
   source occurrences, effects, received views, and branch-result typing.
4. Runtime continuation state and ordered sequence evaluation, including error,
   fuel/step, host/effect, and partial-progress behavior.
5. Focused parser, HIR/source-link, inference, runtime, CLI, WASM and Web tests,
   plus existing regression and smoke expectations.

Until this owner map is pinned, assigning code leases would risk omitting a
consumer or source identity owner. The next bounded action is an exact-pin,
read-only source-owner mapping packet over these seams. That packet must not
change semantics, code, tests, samples or expected outputs. Once its result
names all owners and direct dependencies, Luna can issue a separate complete
Option B implementation contract with atomic end-to-end leases, focused
verification, independent source/code review and unchanged-sample execution.

## Frozen input pins

- R147 decision contract: `87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281`.
- R147 decision draft: `2dbbf05c2c74810c4684a71d81933d4b6b4a9be2067dcc60b943bb090ff64f12`.
- R147 source note: `f2a9ef20bc981ba40310aaca5ff20f2c0edaff6e60f5e07e63f13fdd33e4094b`.
- Unchanged sample: `web/playground/examples/yulang2-ordinary-islands.yu`,
  SHA-256 `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`.
- R183 rev3: `tasks/agent-loop/sprints/source-to-capture-and-sample-readiness-20261021-r183-rev3.md`,
  SHA-256 `6380fedea2dad3e302fd8ed2ce99a010c61eff493b7010c17476020afa028dd8`.

No code, tests, builds, compiler/evaluator, CLI/WASM/browser or Yulang2 runs
were authorized or performed. No implementation lease is granted by this note.
