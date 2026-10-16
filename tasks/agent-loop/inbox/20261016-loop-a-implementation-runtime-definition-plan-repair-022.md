# I16-R1 runtime Definition-plan regression repair

Request-ID: 20261016-loop-a-implementation-runtime-definition-plan-repair-022
Revision: 1
From: primary Luna (runtime model/effort observation unavailable)
To: next_action_selector
Parent-gate: approved module-expression G4, `notes/design/2026-10-16-module-expression-source-owner.md` §10.3
Baseline: `881487aa8b9cbe5fed4b7e0da5dd38c840d3ad26`
Kind: implementation / focused regression

## Claim and scope

Add a test-only regression for `RuntimeProgram::start` validation of selected
and scheduled Definition IDs, duplicate Definition roots, and successful use
of the original valid plan. No production code, source semantics, effect-order
rule, omitted/reordered caller-plan rule, proof status, F5 status, or production
readiness changes.

## Prior attempt and correction

The initial I16 test used two independent lowerings with the same `FileKey`.
`yu_hir::DefId` derives equality from its module identity, spelling and
same-name ordinal, so corresponding IDs from those fixtures are equal. The
first selected-foreign-ID assertion therefore used an invalid falsifier. The
initial frozen receipt remains byte-for-byte at
`20261016-loop-a-implementation-runtime-definition-plan-validation-021.md`
(SHA-256 `4cd17abd180d6998c6f710b384d929ce083f293d4c439b867ba772be329ccc2e`).
Primary read of `crates/yu-hir/src/module.rs` confirmed this identity rule.
The repair lowers the foreign fixture through the normal path with a distinct
file key and asserts its authentic `first` and `main` `DefId`s differ from the
local IDs before checking the planned outcomes. No production defect was
established.

## Frozen inputs and output

- Approved G4 design: `notes/design/2026-10-16-module-expression-source-owner.md`,
  SHA-256 `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`.
- Reviewed runtime-root correspondence:
  `notes/theory/2026-10-16-runtime-module-expression-roots.md`, SHA-256
  `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694`.
- `tools/inference-playground/src/runtime/machine.rs`, SHA-256
  `d9a8e14bd3eda8f5c40641beabac0ad862a4c04fc1173359934376681b731e77`.
- `tools/inference-playground/src/runtime/program.rs`, SHA-256
  `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748`.
- Final test file:
  `tools/inference-playground/tests/runtime_module_expressions.rs`, SHA-256
  `e86c45f917b6e0242d952223f839f6f1b07368e3ad69f8e0001bf91ea9d69176`.
- No other file changed by this packet.

## Verification

One primary focused test command, after the bounded correction:

```sh
timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions definition_root_validation_preserves_program_ownership -- --exact --test-threads=1
```

Result: exit 0; exactly 1 passed, 0 failed, 13 filtered. Test compilation
completed in 1.51 seconds; test body completed in 0.00 seconds. One Cargo
process, jobs capped at 2. `git diff --check` passed. No broad tests, benchmark,
production edit, or performance claim.

The test uses two normal lowerings with distinct source-root file keys, checks
authentic IDs differ, verifies local roots are exactly Definition(`first`) then
Expression, and checks foreign selected/scheduled IDs return
`MissingDefinition`, a duplicate local Definition returns
`ModuleInitializationOrder`, and the original plan completes with local integer
`7`. No claim is made about arbitrary caller-plan completeness or ordering.

## Status and handoff

Requested implementation setting: Luna/high. Runtime-observed model/effort:
unknown. Source write stopped and artifact frozen for primary integration and
one M1 regression review. Review pending. The original G4 source/correspondence,
Simple-sub proof, F5, and production gates remain OPEN; this test does not
discharge them.

Suggested review: one read-only `regression_auditor` R26 review, bounded to the
literal test diff, DefId-distinct fixture construction, all validation outcomes,
preservation of prior assertions and absence of production changes. No review
tests or writes.
