# Current task: complete the CST-derived diagnostics prerequisite

Updated: 2026-09-12. Branch: `yulang3`; do not modify frozen `main`.

## Current management instruction

The user's latest instruction is temporary solo management by the primary
(Astra): establish current state and continue appropriate work, asking only for
necessary decisions. It supersedes the earlier session's subagent request;
do not spawn subagents for this pass. This is not a permanent repository-rule
change. Primary inspection and deterministic tests are not independent review,
and no still-required schema audit or approval is declared complete by them.

This handoff is M0: records/navigation only, zero reviewers, no repair round,
one focused existing Use test run, and zero benchmark samples/processes.

## Objective and governing authority

Complete Construction gate 1 of
[`2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md`](../notes/design/2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md):
the complete ordered Rowan schema for every Missing/Error/Invalid slot,
direct-CST evidence, independent audit and the corresponding public
syntax-reference slice. The document is Authoritative despite its filename.

Then follow its remaining construction gates: structural diagnostic proof,
effective-table planning, and atomic interpreter/environment-analysis/parser
ledger/API migration. Do not start a partial global collector or remove the
temporary diagnostic state while the schema remains incomplete.

- Authority navigation: [`notes/design/INDEX.md`](../notes/design/INDEX.md).
- Accepted input and recovery: [`successor recovery authority`](../notes/design/2026-09-08-successor-recovery-authority-amendment.md).
  Yulang2 is reference evidence for formally accepted input; historical local
  `grammar/` was older Yulang3, not Yulang2. Legacy recovery equality and the
  pre-Item scalar-frontier prerequisite are superseded.
- Direct Rowan and Error/Invalid topology: [`Rowan CST-only amendment`](../notes/design/2026-09-09-successor-rowan-cst-only-amendment-draft.md)
  and [`topology-ordering addendum`](../notes/design/2026-09-09-successor-error-invalid-topology-ordering-addendum.md).
  No AST, materializer, second output tree, opaque Error relexing or hidden
  recovery classifier is authorized by this work.
- Existing accepted syntax, lossless UTF-8/CRLF source ownership, current-Item
  and caller/fence handoff, effect-free rejection and nested recovery ownership
  remain binding. Retain current frozen/record behavior until atomic migration.

## Verified position at handoff

- Public successor header/root cutover and legacy-parser removal are complete
  at `dfa481c4`; see the [`cutover authority`](../notes/design/2026-09-08-successor-public-cutover-priority-amendment.md).
  Do not revive the old public-cutover queue.
- Direct Rowan construction and Error-token/structured-Invalid topology are
  implemented. The generic parser/CstOutput umbrellas are removed. Current
  owners are the direct modules in `crates/yu-syntax/src/lib.rs`;
  `cursor::recovery` still owns the temporary parser diagnostic machinery.
- The CST diagnostic interpreter and ledger/API retirement are not complete.
  `HeaderInfo` still retains recoveries, and
  `crates/yu-syntax/src/full_parse.rs::ParsedFile::diagnostics` still exists.
- Latest implementation/evidence checkpoint: `1c5fed0c` (inner group-item
  UseAlias recovery). Root, group-terminal, Glob and inner group-item aliases
  now have bounded fresh/frozen Missing, terminal Error/retry and boundary
  evidence. The inner evidence covers ordinary UseGroup and both brace/paren
  UseExclusionGroup ancestry, propagated failed-Alias exits without a fabricated
  local Close Missing, successful retry through comma/next item/actual close,
  and successful retry followed by the existing terminal Close Missing.
  Independent post-write schema audit and catalog promotion remain pending;
  broader fences and complete recursive coverage remain open.
- The focused Use module passed 59 tests at this checkpoint on 2026-09-12.
  This is fresh local health evidence, not whole-workspace certification.

## Immediate next bounded work

1. Use the reconciled evidence links in the two existing navigation layers:
   the [`slot catalog`](../notes/design/2026-09-10-successor-cst-slot-schema-catalog.md),
   especially **UseDeclaration Path, Alias and group-entry Draft**, and the
   [`source coverage manifest`](../notes/progress/successor-cst-slot-schema-coverage.md),
   especially **2026-09-12 Use navigation reconciliation**. Their
   family summaries and older exclusions are historical/partial; they are not
   a trustworthy current completion count. Check the specific row and test
   before selecting a new gap or reopening completed work.
2. The inner group-item Alias candidate now has direct evidence in
   `use_schema_inner_group_alias_direct_recovery_and_handoff`: 48 source cases,
   each fresh/frozen. The next pass is its independent post-write schema audit.
   Only after a clean audit may the Alias catalog/coverage row be promoted;
   until then this remains evidence, not an approved schema row. Arbitrary
   third/fourth Alias ordinal enumeration is not a new slot.
3. Keep component recovery under its existing parent and preserve exact pending
   Item leading. If the CST cannot distinguish required diagnostics, record the
   concrete collision and return only that owner to design; do not infer a new
   wrapper or change an expectation to match output.

## Known open boundaries and deferred work

- The global schema remains partial across expressions, Pattern, Type,
  declarations/headers, literals/Rule and statement/root/virtual contexts.
  Catalog-audited bounded Draft rows are not whole-family approval.
- TypeDeclaration header `STOP_WITH` is a recorded authority conflict between
  C15's no-DefinitionIntroducer handoff and TND's With-excluding form boundary;
  neither observed result is certified by the attachment row. Resolve the
  governing sources before changing that affected behavior.
- The source census is not a semantic-slot count or retirement proof. Its
  indirect `emit_rule_missing` publishers remain explicit exceptions. The
  previously stale mapped-Type locators were revalidated and refreshed on
  2026-09-12; consult per-row evidence before treating any old gap as open.
- Production outer Yumark document/fence integration and broader actual
  caller/header/full proof remain separate. The test-only code-cell wrapper is
  not a production document owner. Future frontend/type-walk integration is
  Construction gate 5, when that traversal exists.
- Type-attached `impl` promotion and remaining product/schema proposals retain
  their own approval boundaries; standalone `impl_tail` extraction did not
  activate them. Do not turn historical product Drafts into AST authority.

## Verification and continuity

Fresh check (180-second cap, one build job, one test thread):

```sh
timeout 180s env CARGO_BUILD_JOBS=1 cargo test -p yu-syntax --lib tests::declaration::use_decl:: -- --test-threads=1
```

Result: 58 passed, 0 failed, 0 ignored; 1,353 filtered out. No workspace build,
broad suite or performance experiment was needed for this M0 record update.
Future checks follow `rules/testing.md`; inspect resource behavior before
broadening. `cargo xtask check-graph` checks dependencies, not syntax behavior.

- Current daily record: [`2026-09-12`](../notes/progress/daily/2026-09-12.md).
- Complete pre-handoff task text: [`archived navigation`](../notes/progress/task-navigation-before-solo-handoff-2026-09-12.md).
  It preserves all 1,737 original lines, including older confirmed facts,
  rejected approaches, verification history and source locators. It is not an
  active queue or authority to resume superseded work.
- Earlier history: [`typed-recovery ledger`](../notes/progress/successor-typed-recovery-ledger.md)
  and [`pre-recovery-authority task archive`](../notes/progress/rewrite-state-before-recovery-authority-2026-09-08.md).
