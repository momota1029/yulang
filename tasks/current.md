# Current task: complete the CST-derived diagnostics prerequisite

Updated: 2026-09-15. Branch: `yulang3`; do not modify frozen `main`.

## Current management instruction

The user's 2026-09-14 instruction supersedes the temporary solo-management
restriction for this pass and permits bounded subagent delegation. An
architect assessment selected the already-recorded inner group-item Alias
post-write audit; an independent specification audit closed it cleanly. This
does not alter the repository's role, approval, or design-authority rules.

The completed audit closure was M1: one read-only `spec_auditor`, no repair
round, no new test run or benchmark process. The following record
synchronization is M0 only.

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
  and successful retry followed by the existing terminal Close Missing. Its
  independent post-write schema audit is clean, so this bounded Alias slice is
  now catalog-audited evidence-complete Draft. Broader fences and complete
  recursive coverage remain open.
- Latest M1 evidence checkpoint: the first required `Statement` below actual
  `WithBodyTail > Colon > IndentedStatementBlock` now has bounded direct Rowan
  evidence for EOF Missing, terminal Error, Error retry and accepted control.
  It is catalog-audited evidence-complete Draft only for these four alternatives;
  nested/later/fence/other-caller coverage remains open.
- Latest M1 evidence checkpoint: the first required `Statement` below accepted
  `BindingHeader Equals > BindingBody > IndentedStatementBlock` now has bounded
  direct Rowan evidence for EOF Missing, terminal Error, Error retry and
  accepted control. It is catalog-audited evidence-complete Draft only for
  these four alternatives; target/Equals, inline/wrong-indent, later/nested,
  fence and other-caller coverage remains open.
- Latest M1 evidence checkpoint: the first required `Statement` below ordinary
  `ModDeclaration Colon > IndentedStatementBlock` now has bounded direct Rowan
  evidence for EOF Missing, terminal Error, Error retry and accepted control.
  It is catalog-audited evidence-complete Draft only for these four alternatives;
  marker/visibility/header, inline/wrong-indent/braced, later/nested, fence and
  other-caller coverage remains open.
- Latest M1 evidence checkpoint: RecordPattern's direct lexical Item/Separator
  `Missing` and `Error+` slots are catalog-audited evidence-complete Draft for
  ten existing ordered-child witnesses. The row proves phase selection from CST
  order only; spreads, other trivia, repeated/boundary transitions, structured
  Invalid, foreign/local close and nested Pattern coverage remain open.
- Latest M1 evidence checkpoint: RecordPatternField's default Expression
  Missing after actual Equals is catalog-audited evidence-complete Draft for six
  witnesses. It is selected before later sequence recovery by ordered CST;
  carried-close/fence, nested defaults/Invalid, field Pattern/Expression
  internals, close recovery and exact-Equals lexing remain open.
- Latest M1 evidence checkpoint: terminal local Close Missing for
  ParenthesizedPattern, ListPattern and RecordPattern is catalog-audited
  evidence-complete Draft for empty/completed-child ordinary EOF controls,
  matching native closes and the same-offset `"({a:"` composition. Ordered
  direct Rowan ancestry selects nested Pattern then Record then Parenthesized
  close occurrences without diagnostic records. Foreign/caller/fence closes,
  sequence recovery, child interiors and broader recursion remain open.
- The focused Use module passed 59 tests at this checkpoint on 2026-09-12.
  This is fresh local health evidence, not whole-workspace certification.

## Immediate next bounded work

1. Select the next bounded unmapped schema candidate only after reconciling its
   specific catalog/coverage row, direct owner and existing tests. Do not
   expand the completed Pattern terminal-close slice into foreign/caller/fence
   closes, sequence recovery, child interiors or broader recursion without a
   distinct candidate and audit.
2. Keep component recovery under its existing parent and preserve exact pending
   Item leading. If the CST cannot distinguish required diagnostics, record the
   concrete collision and return only that owner to design; do not infer a new
   wrapper or change an expectation to match output.

The parenthesized/list post-item Separator slice is now catalog-audited
evidence-complete Draft for its 24 direct CST witnesses. Select the next bounded
unmapped candidate before further implementation.

Selected candidate: RoleDeclaration's first indented Statement after completed
Head and actual Colon, limited to EOF Missing, lexical Error, Error-to-Statement
retry and accepted control. Head/BodyIntroducer, inline/wrong-indent/braced,
later/nested/fence and other callers remain separate.

Role's first indented Statement slice is now catalog-audited evidence-complete
Draft for its four direct CST witnesses. Select the next bounded unmapped
candidate before further implementation.

Selected candidate: Impl's first indented Statement after completed Head,
completed ImplDescription and the direct second body Colon. It is limited to
EOF Missing, lexical Error, retry and accepted control; first-colon Description,
other body forms, later/nested/fence/caller paths remain separate.

Impl's second-Colon indented Statement slice is now catalog-audited
evidence-complete Draft for its four direct CST witnesses. Select the next
bounded unmapped candidate before further implementation.

Selected candidate: ActDeclaration's first indented Statement after completed
Head and actual Colon, limited to Missing, lexical Error, retry and accepted
control. Source/Head/BodyIntroducer, bodyless/attachment, inline/wrong-indent/
braced, later/nested/fence/caller paths remain separate.

Act's first indented Statement slice is now catalog-audited evidence-complete
Draft for its four direct CST witnesses. Select the next bounded unmapped
candidate before further implementation.

Selected candidate: CastBody's first indented Statement after completed
CastPattern/CastTarget and actual Equals, limited to Missing, lexical Error,
retry and accepted control. Inline/wrong-indent/braced, malformed earlier
phases, later/nested/fence/caller paths remain separate.

CastBody's first indented Statement slice is now catalog-audited
evidence-complete Draft for its four direct CST witnesses. Select the next
bounded unmapped candidate before further implementation.

## Staged-state integration and ordinary expression Missing closure

- The user selected the staged state as authoritative during the transitional
  conflict. Commit `cc98c8e0` atomically integrated that state by reverting the
  later equal-indent statement gate and its five synchronized records. The
  worktree then contained only the unrelated untracked `logs/` directory.
- An independent read-only audit found the existing ParenthesizedExpression,
  CallTail and IndexTail Item/Separator/terminal-Close Missing witnesses
  evidence-complete for one bounded Draft row. No parser or test edit and no
  verification rerun were needed for this M0 record synchronization.

## Selected next candidate: Projection-tail ordinary Missing

- The next bounded M1 candidate is ordinary Item, Separator and terminal Close
  `Missing` for ProjectionTupleTail and ProjectionRecordTail. Existing evidence
  does not prove these two owner structures directly.
- Add ten real-shell ordered-CST witnesses: leading-comma Item, omitted
  Separator, EOF Close, accepted empty and accepted single-item control for
  each owner. Spread RHS, Error, nested recovery, foreign/caller/fence paths,
  repeated/semicolon/trivia variants and global interpreter work remain
  excluded.

## Projection-tail ordinary Missing audit closure

- One additive ten-witness test now proves Item, Separator and terminal Close
  `Missing`, plus accepted empty and single-item controls, in real
  ProjectionTupleTail and ProjectionRecordTail shells. It classifies each role
  from ordered CST before record comparison and proves exact ranges, parentage,
  lossless source, excluded-node absence and fresh/frozen equality.
- The independent post-write specification audit was clean. Scoped rustfmt and
  diff checks passed; the wrapper-disabled focused test passed 1 with 1,422
  filtered out. No benchmark process or broad suite was used.
- Spread RHS, Error, nested recovery, foreign/caller/fence paths,
  repeated/semicolon/trivia variants, interpreter construction and ledger/API
  migration remain separate. Select the next bounded unmapped candidate before
  further implementation.

## RuleLiteral indirect Missing audit closure

- A read-only M1 audit mapped the five indirect `emit_rule_missing` calls to
  four structural slots: one interpolation Close reached through two exits,
  braced lazy Close, unbraced lazy Name and the outer RuleLiteral terminator.
  Existing direct Rowan evidence was sufficient, so no producer, repair round
  or test rerun was needed; this synchronization is M0.
- The catalog row is bounded to its ASCII direct witnesses. Shifted/UTF-8 and
  fresh/frozen tests remain compatibility support; direct-CST UTF-8 Missing
  ranges, RuleSequence Error, nested Rule grammar, broader boundary variants,
  interpreter work and ledger/API migration remain open.
- Cursor-wide deletion is not the next gate. `SyntaxIn`, `LexIn`, source and
  lexical transactions, immutable operator observation, current-Item scanning
  and lossless CST recovery remain. Only the parser-owned diagnostic ledger,
  reservations/IDs/frozen reconciliation and diagnostic transport/storage are
  scheduled for atomic retirement after Construction gates 1–3 close.

## RuleCapture required-RHS audit closure

- The selected M1 slice covered only existing `{a=;}` Error-to-Missing and
  `{a=; b?}` Error-to-RuleItem witnesses after a direct Capture Equals. The
  pre-write audit found a direct-proof gap, and one Astra implementer added
  bounded assertions for source flattening, native closing brace, childless
  Missing and the exact retry RHS token/node shell.
- Independent delta review was clean. Scoped rustfmt and diff checks passed;
  the wrapper-disabled exact focused test passed 1 with 1,422 filtered out.
  No production code, existing expectation or test name changed, and no broad
  suite or benchmark process was used.
- This promotes only those two forms to catalog-audited evidence-complete
  Draft. Bare Missing/accepted-only forms, longer Error runs, deeper RHS,
  interpolation/fence/caller variants, other Rule slots and gates 2–4 remain
  open. Select the next bounded gate-1 candidate before further implementation.

## RuleField/RulePath required-name audit closure

- The selected M1 slice covered `{a.12 b}` and `{a::💥 b}` one-item name Error
  followed by a separate outer RuleItem, plus the existing `{a.12?}` proof that
  a quantifier remains outside the failed RuleField. The pre-write audit found
  an assertion gap rather than a parser defect.
- One Astra implementer replaced permissive ancestor/text checks with exact
  immediate ancestry, direct token/node ownership and ranges, full-source and
  native-close assertions. Independent delta review was clean. Scoped rustfmt
  and diff checks passed; the wrapper-disabled exact test passed 1 with 1,422
  filtered out. No production code, broad suite or benchmark process changed.
- The two rows are catalog-audited evidence-complete Draft only for those
  witnessed Error/continuation forms. Missing/accepted-name, newline/fence and
  broader boundaries, other Rule slots, nested grammar and gates 2–4 remain
  open. Select the next bounded gate-1 candidate before further implementation.

## Nested Rule close-slot audit closure

- The selected M1 slice was the single `{(a` EOF composition where the inner
  RuleItem parenthesis close and outer RuleBody close Missing share `3..3`.
  Pre-write audit found that sorting by parent masked natural Rowan preorder
  and that exact ancestry/native-token/childless-node evidence was absent.
- One Astra implementer replaced the sort-based check with exact nested CST,
  source/token ranges, direct empty Missing and structurally derived close-role
  assertions before record comparison. Independent delta review was clean.
  Scoped rustfmt/diff checks and the wrapper-disabled exact test passed; 1 test,
  1,422 filtered out. No production code, broad suite or benchmark changed.
- Both rows are catalog-audited evidence-complete Draft only for this nested EOF
  composition. Accepted closes/postfix, nonempty pending leading,
  fence/caller/recursive variants, other Rule slots and gates 2–4 remain open.
  Select the next bounded gate-1 candidate before further implementation.

## RuleSequence terminal Error-group audit closure

- The selected M1 slice was terminal RuleBody `{;💥}`: two adjacent direct
  Error tokens representing one repeated-Item occurrence. Pre-write audit found
  missing terminal-frame and CST-only projection assertions, not a parser
  defect.
- One Astra implementer added exact Root/Body/Alternation/Sequence structure,
  native braces/source, absence of Missing/Invalid, exact UTF-8 leaf ranges and
  maximal group, then derived singleton `Literal(RuleItem)`, primary zero from
  CST ancestry. Independent delta review was clean. Scoped rustfmt/diff checks
  and the wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No
  production code, broad suite or benchmark changed.
- The row is catalog-audited evidence-complete Draft only for this terminal
  RuleBody witness. Retry, parenthesized/interpolation callers,
  separator/newline/fence, nested grammar, ExpressionList and gates 2–4 remain
  open. Select the next bounded gate-1 candidate before further implementation.

## Rule ExpressionList pending-fence handoff closure

- The selected M1 slice covered the pending fence Item returned through the
  existing empty-list RuleItem/RuleCall/RuleIndex callers. CST prefix, Close
  Missing and native-close controls were already audited; the remaining harness
  gap discarded `RuleWitnessExit` and `LineEntry`.
- One Astra implementer added a richer test-only wrapper and proved `Returned`,
  `PhysicalStart`, complete Yumark fence facts and coordinates, exact Item
  extent/equality with unconsumed CRLF leading, terminal-leading emission and
  source reconstruction for all three callers. No production API changed.
  Independent delta review was clean. Scoped rustfmt/diff checks and the
  wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No broad suite
  or benchmark ran.
- The stale catalog/coverage statements that called fence CST/range or pending
  Item identity open are reconciled. Outer Yumark construction, nonempty/nested
  fence lists, other fences, other Rule/ExpressionList slots and gates 2–4
  remain open. Select the next bounded gate-1 candidate before implementation.

## Known open boundaries and deferred work

- The global schema remains partial across expressions, Pattern, Type,
  declarations/headers, literals/Rule and statement/root/virtual contexts.
  Catalog-audited bounded Draft rows are not whole-family approval.
- TypeDeclaration header `STOP_WITH` is a recorded authority conflict between
  C15's no-DefinitionIntroducer handoff and TND's With-excluding form boundary;
  neither observed result is certified by the attachment row. Resolve the
  governing sources before changing that affected behavior.
- The source census is not a semantic-slot count or retirement proof. Its
  indirect `emit_rule_missing` publishers remain explicit census exceptions,
  although the four RuleLiteral child slots are now mapped. The
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

Most recent focused check (180-second cap, one build job, one test thread):

```sh
timeout 180s env RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-syntax --lib tests::pattern::recovery::default_expression:: -- --test-threads=1
```

Result: 7 passed, 0 failed, 0 ignored; 1,409 filtered out. Scoped
`rustfmt --edition 2024 --check crates/yu-syntax/src/tests/pattern/recovery/default_expression.rs`
also passed. The default-wrapper form failed before compilation because the
environment's sccache lacked operation permission; the wrapper-disabled rerun
is the meaningful focused result. The prior Mod/Binding/With checkpoints passed
13, 12 and 11; the inner Alias checkpoint passed 59 Use-module tests. No
workspace build, broad suite or performance experiment was needed for the M1
closure/M0 record update. Future checks follow
`rules/testing.md`; inspect resource behavior before broadening. `cargo xtask
check-graph` checks dependencies, not syntax behavior.

- Current daily record: [`2026-09-15`](../notes/progress/daily/2026-09-15.md).
- Complete pre-handoff task text: [`archived navigation`](../notes/progress/task-navigation-before-solo-handoff-2026-09-12.md).
  It preserves all 1,737 original lines, including older confirmed facts,
  rejected approaches, verification history and source locators. It is not an
  active queue or authority to resume superseded work.
- Earlier history: [`typed-recovery ledger`](../notes/progress/successor-typed-recovery-ledger.md)
  and [`pre-recovery-authority task archive`](../notes/progress/rewrite-state-before-recovery-authority-2026-09-08.md).
