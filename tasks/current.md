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

## StringLiteral outer-terminator audit closure

- The selected M1 slice covered five existing outer-terminator witnesses:
  accepted empty/UTF-8 normal and heredoc forms, a mismatched two-quote heredoc
  text run, and two final childless heredoc Missing forms including UTF-8.
  Pre-write audit found incomplete direct-CST assertions, not a parser defect.
- One Astra implementer strengthened the existing named test with exact
  Root/StringLiteral ancestry, ordered node/token spellings and UTF-8 ranges,
  full source, opener-selected native StringEnd versus final Missing, and
  structural slot derivation before records. Independent delta review was
  clean. Scoped rustfmt/diff checks and the wrapper-disabled exact test passed;
  1 test, 1,422 filtered out. No production code, broad suite or benchmark ran.
- The row is catalog-audited evidence-complete Draft only for those five forms.
  StringPiece interiors, arbitrary heredoc variants, expanded caller/fence
  coverage and gates 2–4 remain open. Select the next bounded gate-1 candidate.

## RuleLiteral UTF-8 equal-offset composition closure

- The selected M1 slice added one `~"é{α` EOF witness to the mapped RuleLiteral
  indirect Missing row. It exercises UTF-8 in both outer raw text and the
  admitted interpolation RuleItem without adding redundant ASCII coverage.
- One Astra implementer proved the exact native topology and byte ranges,
  source/remainder, two childless Missing nodes at `7..7`, natural inner
  interpolation-Close before outer-terminator preorder, and CST-context-derived
  singleton expectations with primary zero. The owning fence-aware EOF path is
  correctly observed as `EofAfterTrivia`. Independent delta review was clean.
  Scoped rustfmt/diff checks and the wrapper-disabled exact test passed; 1 test,
  1,422 filtered out. No production code, broad suite or benchmark ran.
- Only this UTF-8 EOF composition extends the audited row. UTF-8 lazy capture,
  other boundary/leading variants, nested Rule recovery and gates 2–4 remain
  open. Select the next bounded gate-1 candidate.

## RuleLiteral UTF-8 braced-lazy composition closure

- The selected M1 slice added the existing `~":{α` compatibility source as one
  direct-CST witness. It proves the braced lazy Close and enclosing RuleLiteral
  terminator as distinct childless Missing nodes at `6..6`.
- One Astra implementer added exact UTF-8 topology/ranges/source and
  `EofAfterTrivia` assertions, natural Close-before-Terminator preorder, and
  structural role selection requiring direct Colon+OpenBrace before singleton
  expectation/primary-zero comparison. Independent pre-write and post-write
  audits were clean. Scoped rustfmt/diff checks and the wrapper-disabled exact
  test passed; 1 test, 1,422 filtered out. No production code, broad suite or
  benchmark ran.
- UTF-8 unbraced Name, other boundary/leading/CRLF/fence forms, nested Rule and
  gates 2–4 remain open. Select the next bounded gate-1 candidate.

## RuleLiteral UTF-8 unbraced-Name composition closure

- The selected M1 slice added one `~"é:` direct-CST witness. UTF-8 outer text
  shifts the unbraced required Name and enclosing terminator Missing to the
  shared byte frontier `5..5` without pretending that an admitted UTF-8 name is
  absent.
- One Astra implementer proved exact source/topology/ranges and
  `EofAfterTrivia`, childless Name-before-Terminator preorder, and structural
  selection from exact direct `[Colon token, Missing node]` children with no
  OpenBrace. Singleton Identifier/terminator expectations and primary zero are
  derived before records. Independent pre-write and delta audits were clean.
  Scoped rustfmt/diff checks and the wrapper-disabled exact test passed; 1 test,
  1,422 filtered out. No production code, broad suite or benchmark ran.
- The four RuleLiteral indirect Missing slots now each have bounded ASCII and
  UTF-8 direct evidence through the recorded compositions. Other
  boundary/leading/CRLF/fence forms, nested Rule and gates 2–4 remain open.
  Select the next bounded gate-1 candidate.

## RuleField/RulePath native-close Missing closure

- The selected M1 slice added paired `{a.}` and `{a::}` direct-CST witnesses
  for required Name Missing immediately before the native RuleBody close.
- One Astra implementer proved exact complete ancestry/inventories, native
  introducers and braces, unique childless Missing at `3..3` / `4..4`, absence
  of Error/Invalid/later continuation, and CST-derived field/path Name roles
  with singleton Identifier and primary zero before records. Independent
  pre-write and delta audits were clean. Scoped rustfmt/diff checks and the
  wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No production
  code, broad suite or benchmark ran.
- The two named-postfix rows now cover the witnessed native-close Missing and
  prior Error continuations. Accepted names, newline/EOF/fence/interpolation
  callers, recursive Rule grammar and gates 2–4 remain open. Select the next
  bounded gate-1 candidate.

## RuleCapture bare required-RHS Missing closure

- The selected M1 slice added one `{a=}` direct-CST witness for the zero-Error
  required RHS Missing before the native RuleBody close. Existing Capture proof
  covered only Error-to-Missing and Error-to-RuleItem.
- One Astra implementer proved the complete exact tree/source, terminal
  RuleCapture with direct Equals and childless Missing at `3..3`, unique
  Missing/no Error/Invalid, native RBrace and CST-derived singleton
  `Literal(RuleItem)` with primary zero before records. Independent pre-write
  and delta audits were clean. Scoped rustfmt/diff checks and the
  wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No production
  code, broad suite or benchmark ran.
- The row now covers three witnessed zero/one-Error terminal/retry forms.
  Accepted-only RHS, longer Error runs, deeper/recursive Rule, other
  boundary/caller variants and gates 2–4 remain open. Select the next bounded
  gate-1 candidate.

## RuleField LF required-Name Missing closure

- The selected M1 slice strengthened the existing `{a.\nnext}` witness. A
  physical LF stops RuleField Name admission, stays native under
  RuleAlternation, and `next` begins its second RuleSequence.
- One Astra implementer proved the complete exact tree and token sequence,
  unique childless Missing at `3..3`, absence of Error/Invalid, full source and
  native close, plus CST-derived RuleFieldName singleton Identifier/primary
  zero before records. Existing shared LF/Capture assertions stayed unchanged.
  Independent pre-write and delta audits were clean. Scoped rustfmt/diff checks
  and the wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No
  production code, broad suite or benchmark ran.
- RulePath/Capture LF promotion, CRLF/EOF/fence/interpolation, accepted names,
  recursive Rule and gates 2–4 remain open. Select the next bounded gate-1
  candidate.

## RuleCapture CRLF required-RHS Missing closure

- The selected M1 slice strengthened the existing `{a=\r\nnext}` witness. The
  terminal Capture publishes its bare RHS Missing before physical CRLF, while
  `next` begins the second RuleSequence.
- One Astra implementer proved the full exact tree/token inventory, terminal
  Capture with direct Equals and unique childless Missing at `3..3`, native
  CRLF `3..5` under RuleAlternation, second Item `5..9`, native close and
  CST-derived singleton `Literal(RuleItem)`/primary zero before records.
  Independent pre-write and delta audits were clean. Scoped rustfmt/diff checks
  and the wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No
  production code, broad suite or benchmark ran.
- Accepted RHS, longer Error runs, LF/EOF/fence/interpolation callers,
  recursive Rule and gates 2–4 remain open. Select the next bounded gate-1
  candidate.

## Public Root Rule EOF-leading composition closure

- The selected M1 slice strengthened the existing public-Root `~"{a=  `
  witness. The RuleLiteral subtree ends at CST frontier `5`, while trailing
  horizontal whitespace remains a direct Root child at `5..7`.
- One Astra implementer proved the complete exact node/token topology, three
  childless Missing occurrences at `5..5` in Capture-RHS, interpolation-Close
  and outer-terminator preorder, absence of Error/Invalid, and CST-derived
  singleton expectations/primary zero before compatibility records. Existing
  scanned-EOF record coordinates and sibling cases stayed unchanged.
  Independent pre-write and delta audits were clean. Scoped rustfmt/diff
  checks and the wrapper-disabled exact test passed; 1 test, 1,422 filtered
  out. No production code, broad suite or benchmark ran.
- Other leading/comment/CRLF/fence and caller variants, recursive Rule and
  gates 2–4 remain open. Select the next bounded gate-1 candidate.

## RulePath LF required-Name Missing closure

- The selected M1 slice strengthened the existing `{a::\nnext}` witness. A
  physical LF stops RulePath Name admission, stays native under
  RuleAlternation, and `next` begins its second RuleSequence.
- One Astra implementer proved the complete exact nine-node/six-token tree,
  direct RulePath with ColonColon and unique childless Missing at `4..4`, LF
  `4..5`, second Item `5..9`, native braces, absence of Error/Invalid and the
  CST-derived RulePathName singleton Identifier/primary-zero projection before
  records. Existing assertions and siblings stayed unchanged. Independent
  pre-write and delta audits were clean. Scoped rustfmt/diff checks and the
  wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No production
  code, broad suite or benchmark ran.
- Accepted names, CRLF/parenthesis/EOF/fence/interpolation, recursive Rule and
  gates 2–4 remain open. Select the next bounded gate-1 candidate.

## Gate-1 publication-mechanism completeness audit

- A read-only M1 Astra audit re-ran the direct publisher census at `589a1e57`.
  It remains 123 call sites in 39 files: 59 Missing, 9 Error-item, 53
  Error-run and 2 structured Invalid. The historical four-emitter census is
  only a search baseline; the newline callback is a fifth publication entry
  mechanism, and wrapper callers must not be double-counted as executions.
- The audit reconciled ten `emit_rule_missing` callers, the single newline
  callback and the two structured Invalid callers/three roles against current
  mapped evidence. It corrected stale navigation for the completed bounded
  fence proof and three RuleLiteral UTF-8 EOF compositions. No production
  defect or new semantic decision was found. No build, test or measurement
  ran for this record-only audit.
- Gate 1 is not complete. The distinct `RuleFrame::LiteralInterpolation`
  RuleSequence Error residual is now closed below; delegated BracketRow
  Item/Close internals remain the next major residual. The audit did not
  independently certify every caller discriminator behind all 123 sites.

## RuleLiteralInterpolation RuleSequence Error closure

- The selected M1 slice adds one bounded `~"{| if ] a}"` direct-CST witness
  for the interpolation-specific repeated-Item row. This frame deliberately
  does not inherit Body/Parenthesis stops for `|`, `if`, or `]`.
- One Astra implementer proved the exact five-node/eleven-token topology, five
  adjacent direct Error leaves as one maximal `3..9` group, admitted retry
  RuleItem `9..11`, native interpolation/literal closes, full source and no
  Missing/Invalid/Error node. Direct RuleSequence-to-interpolation ancestry
  derives singleton `Literal(RuleItem)`, primary zero and the combined group
  range before three unchanged per-Item compatibility records. Independent
  pre-write and delta audits were clean. Scoped rustfmt/diff checks and the
  wrapper-disabled exact test passed; 1 test, 1,422 filtered out. No production
  code, broad suite or benchmark ran.
- A separate evidence-complete Draft row now records this bounded ancestor
  identity. EOF/fence/outer-quote, newline/CRLF/UTF-8, nested Rule/public caller
  variants and gates 2–4 remain open. Audit BracketRow Item/Close internals
  next.

## BracketRow Item/Close CST-role collision proof

- A pre-write Astra audit traced all reachable BracketRow owner phases and
  confirmed that `BracketRowSeparator` is live through explicit branches;
  disabling inherited separators only disables Type-ML splitting.
- One Astra implementer added the bounded collision witness
  `T [A@] -> U` versus `T [A)] -> U`. Both have the same exact six-element
  BracketRow subtree, normalized Error range `4..5`, one direct Error group and
  the same trailing-arrow ancestry, while the retained contract requires
  Item/TypeExpression versus Close/`]` singleton roles with primary zero.
  Fresh/frozen replay, full source and sentinel shifts are pinned. Independent
  delta audit was clean. Scoped rustfmt/diff checks plus the collision and two
  neighboring exact tests passed; each ran 1 test with 1,423 filtered out. No
  production code, broad suite or benchmark ran.
- This is a BLOCKING owner-level structural ambiguity for the affected mapping,
  not an implementation repair or mapped schema. Do not merge roles or inspect
  Error spelling. An explicit structural decision is required before changing
  production topology. Separator mapping and unrelated Gate-1 work can proceed
  independently.

## BracketRow no-gap Separator Missing closure

- The selected M1 slice strengthened the authoritative `T [A{}] -> U` no-gap
  alternative. One Astra implementer proved exact ordered BracketRow and nested
  `NamedRecordTypeClose` topology, a unique childless direct Missing `4..4`
  between two TypeExpression children, no Error/Invalid, full sentinel/source
  and the accepted Arrow/RHS suffix.
- Direct item order derives `Type(BracketRowSeparator)`, singleton
  `DelimitedSequenceSeparator` and primary zero before fresh/frozen records.
  The first inferred test topology omitted the already-authoritative record
  close wrapper; the single allowed repair corrected that assertion without
  changing production or expected output. Independent final audit was clean.
  Scoped rustfmt/diff checks plus the new exact test and two neighboring
  controls passed; each ran 1 test with 1,424 filtered out. No broad suite or
  benchmark ran.
- This closes only the bounded no-gap alternative. Deeper-newline Separator
  evidence is closed below; the Item/Close collision still requires an owning
  structural decision. Gate 1 remains incomplete.

## BracketRow deeper-newline Separator Missing closure

- Explorer reachability analysis found the real child-return witness
  `T [:{A\n  B] -> U`; a normal `T [A\n  B] -> U` is TypeApply and cannot prove
  this branch. Pre-write audit corrected the proposed PV Missing range before
  implementation: it is `6..6`, before the un-emitted newline leading, not
  `9..9`.
- One Astra implementer proved complete BracketRow/PV/tail topology, terminal
  PV Close Missing `6..6`, BracketRow-owned Newline `6..7` and Whitespace
  `7..9`, Separator Missing `9..9`, next TypeExpression and fresh/frozen green
  equality. Both roles and singleton/primary-zero projections derive from CST
  before records. Independent delta audit was clean. Scoped rustfmt/diff and
  the deeper, no-gap and accepted-control exact tests passed; each ran 1 test
  with 1,425 filtered out. No broad suite or benchmark ran.
- Both explicit Separator publication branches now have bounded evidence.
  Exhaustive callers/boundaries remain open, and the independent Item/Close
  topology collision remains BLOCKING pending its owning decision.

## Required-Type fresh Missing caller reconciliation

- A read-only M1 Astra audit found 12 production call expressions and 20
  owner/shape transports into the shared required-Type entry. Five transports
  cannot reach fresh Missing after caller priority checks; 15 production role
  contexts remain reachable.
- Eight contexts already have bounded mappings: Type RHS, Act Head/Source,
  Derives RoleReference, Pattern/Expression annotations and Enum/Error
  FromType. Seven initially lacked their own row: Role Head, Impl
  Head/Description, Cast TargetType and Struct/Enum/Error named-field Type.
  Role Head is closed below; the other six remain open. No build, test or
  benchmark ran for the reconciliation itself.
- The audit also refreshed the stale named-field required-Type source locator.
  This finite transport audit does not certify all boundary variants or nested
  Type recovery.

## RoleDeclaration fresh required-Head Missing closure

- The selected M1 slice strengthened existing `role ;` evidence with a
  structure-selected projection before records. Ordered
  `RoleKw Whitespace TypeExpression(Missing) Semicolon` selects exactly one
  `Declaration(Role(Head))`, singleton TypeExpression, primary zero at CST
  `5..5`; the shifted compatibility record remains `105..105`.
- One Astra implementer added 34 test-only lines. Exact ancestry, unique
  childless Missing, no Error/Invalid, semicolon handoff, EOF and fresh/frozen
  seeded replay were already pinned. Independent pre-write and delta audits
  were clean. Scoped rustfmt/diff and the exact test passed; 1 test, 1,425
  filtered out. No production code, broad suite or benchmark ran.
- The bounded `role ;` Head row is now catalog-audited evidence-complete Draft.
  Other boundaries/layout/fences, malformed/retried/nested Type, other Role
  phases and gates 2–4 remain open. Select another unmapped required-Type
  caller while the BracketRow structural decision remains pending.

## ImplDeclaration fresh required-Type Missing closure

- The selected M1 slice strengthened the existing `impl ;` Head and `impl T:`
  Description witnesses. Exact ordered declaration placement versus actual-
  Colon `ImplDescription` ancestry now selects the two roles before records;
  each projects singleton TypeExpression, primary zero from its sole childless
  Missing at `5..5` or `7..7`.
- One Astra implementer added 57 test-only lines. Existing exact topology,
  no-cascade behavior, Error/Invalid exclusions and fresh/frozen replay stayed
  unchanged. Independent pre-write and delta audits were clean. Scoped
  rustfmt/diff and the exact test passed 1. No production code, broad suite or
  benchmark ran.
- The bounded two-role row is now catalog-audited evidence-complete Draft.
  Required-Type fresh Missing has four unmapped reachable contexts left: Cast
  TargetType plus Struct/Enum/Error named-field Type. Other Impl boundaries,
  malformed/retried/nested Type and gates 2–4 remain open.

## CastTarget fresh required-Type Missing closure

- The selected M1 slice added one complete `cast(x): ;` direct-CST proof.
  Completed CastPattern plus actual-Colon CastTarget ancestry selects the empty
  TypeExpression/Missing as `Declaration(Cast(TargetType))`, singleton
  TypeExpression, primary zero at `9..9` before records.
- One Astra implementer proved the full canonical node/token inventory, unique
  childless Missing, no Error/Invalid, semicolon/EOF handoff, isolated typed
  harness shape and fresh/frozen replay. The single repair replaced invalid
  cross-harness Root equality with CastDeclaration-subtree equality while
  retaining same-harness whole-tree equality. Independent final audit was
  clean. Scoped rustfmt/diff and exact test passed 1 with 1,426 filtered out.
  No production code, broad suite or benchmark ran.
- Status: evidence-complete Draft for `cast(x): ;` only. Struct/Enum/Error
  named-field Type are now the three remaining unmapped reachable contexts in
  this required-Type inventory. Broader Cast/Type and gates 2–4 remain open.

## Named-field required-Type fresh Missing closure

- The selected M1 slice added one coherent three-owner matrix for
  `struct S {a:}`, `enum E { A {a:} }` and `error E { A {a:} }`. Complete
  declaration/variant/named-brace ancestry distinguishes Struct FieldType from
  Enum/Error Variant NamedFieldType despite their common StructField shape.
- One Astra implementer proved exact canonical node/token ownership, unique
  childless TypeExpression Missing at `12..12` / `14..14` / `15..15`, native
  closes, EOF and sentinel fresh/frozen replay. The one repair added explicit
  singleton TypeExpression/primary-zero projection before record construction.
  Independent final audit was clean. Scoped rustfmt/diff and exact test passed
  1 with 1,427 filtered out. No production code, broad suite or benchmark ran.
- All 15 reachable role contexts in the bounded shared required-Type fresh-
  Missing transport inventory now have mapped witnesses. This does not certify
  every layout/boundary alternative or nested Type, and Gate 1 remains
  incomplete. Struct indented fields, tuple/positional exclusions, broader
  recovery and gates 2–4 remain open.

## Required-expression caller reconciliation and WhereKw Guard closure

- A read-only M1 audit bounded the shared required-expression surface to 12
  caller/phase classes and 24 fresh-Missing/initial-Error cells. This is a
  caller-discriminator inventory, not exhaustive parser coverage.
- One Astra implementer added an additive six-case Case/Catch WhereKw Guard
  matrix. Direct Rowan ancestry and child order prove empty Missing, terminal
  maximal Error and IdentifierExpression retry as
  `CaseLike(Guard)`/Expression/primary zero, with exact ranges, trivia
  ownership, Arrow/body handoff and no record- or spelling-based selection.
- Independent pre-write and post-write audits were clean. Scoped rustfmt/diff
  and four focused `case_schema_` tests passed; no production code, broad suite
  or benchmark ran. These six alternatives are evidence-complete Draft only.
- Elsif Condition and the ordinary-EOF production infix-operand Missing
  discriminator are closed below. All identified direct-proof gaps in this
  bounded reconciliation are closed. Prefix/infix contextual recursion,
  broader boundaries/layout, nested owners and Gate 1 completion remain open.

## Elsif Condition required-expression closure

- One Astra implementer added a three-case direct-Rowan matrix for Missing,
  terminal maximal Error and IdentifierExpression retry before actual Colon.
  Complete ancestry, second-arm ordinal and direct ElsifKw distinguish this
  Condition from the initial If and nested Nud slots.
- Exact node/token ranges and ownership prove the maximal Error group, retry
  leading, Colon/body handoff, accepted body and whole-tree recovery census.
  The CST-only projection is Condition/Expression/primary zero.
- Independent pre-write and post-write audits were clean. Scoped rustfmt/diff
  and the exact test passed 1 with 1,429 filtered out; no repair, production
  change, broad suite or benchmark ran.
- These three alternatives are evidence-complete Draft only. EOF/fence
  absence, missing introducer, later companions, layout, nested Nud and the
  broader required-expression surface stay open.

## Production infix-operand Missing discriminator closure

- One Astra implementer added the ordinary-EOF `a +` direct-CST witness.
  Accepted lhs, InfixOperatorUse and final childless Missing occur as the exact
  three direct OperatorChain children; full ancestry and order select
  Expression(Nud)/Expression/primary zero at `3..3` without records or operator
  spelling.
- Exact node/token ownership and ranges, sole recovery, lossless source and EOF
  Item extent are pinned. The existing dangling-operator tests remain retained
  controls.
- Independent pre-write and post-write audits were clean. After one
  formatting-only repair, scoped rustfmt/diff and the exact test passed 1 with
  1,430 filtered out. No production change, broad suite or benchmark ran.
- This closes the last identified direct-proof gap in the bounded 12-class,
  24-cell caller reconciliation only. Recursive/boundary combinations, nested
  owners and global Gate 1 remain open.

## Shared initial Pattern Cast caller closure

- A read-only M1 specification audit enumerated ordinary, alternation, five
  delimiter, Binding, For, Case/Catch and guarded caller classes. It found one
  omitted reachable class: the parenthesized Cast mandatory-policy entry into
  shared initial Pattern recovery.
- One Astra implementer added three direct-Rowan Cast witnesses. Current-tail
  Primary Missing, singleton initial Error-to-Identifier retry and nested
  AlternationRhs reset are selected from complete
  Root/Statement/Cast/Pattern ancestry and direct order before records.
- Direct Cast-owned absence remains distinct. Bare accepted/retry Cast and
  structured Record wrong-kind entries admit a NUD before delegation and do
  not reach shared initial Missing/Error.
- Independent post-write audit was clean. Scoped rustfmt/diff and the exact
  test passed 1 with 1,431 filtered out; no production change, broad suite or
  benchmark ran. This closes only the bounded reachable initial caller table;
  boundaries, nested grammar and global Gate 1 remain open.

## Required-Type initial Error inventory and Impl closure

- A read-only M1 audit found 12 production calls and 20 reachable owner/shape
  transports for initial nonempty Type Error. Unlike fresh Missing, tuple and
  positional guards admit malformed non-NUDs, so all 20 can reach
  `Type(Primary)` terminal/retry recovery.
- Existing mapped rows covered six contexts completely and Act Head/Source
  retry in two more. One Astra implementer added structure-selected projection
  assertions for Impl Head and Description terminal, singleton-retry and
  three-leaf-retry witnesses.
- Ordered ImplDeclaration versus actual-Colon ImplDescription ancestry selects
  both groups as `Type(Primary)`/TypeExpression/primary zero. Retry leading,
  semicolon/EOF ownership and no caller Missing cascade are pinned before
  compatibility records.
- Independent pre-write and post-write audits were clean. After one
  formatting-only repair, scoped rustfmt/diff and the exact test passed 1 with
  1,431 filtered out; no production change, broad suite or benchmark ran.
- Impl closes two contexts, leaving ten without dedicated mapped Error
  coverage. Act terminal coverage remains a separate bounded residual;
  broader boundaries/layout, nested Type and global Gate 1 remain open.

## Role Head initial required-Type Error closure

- One Astra implementer added structure-only projections to the existing Role
  Head schema test for a protected-semicolon terminal Error, singleton retry
  and three-leaf UTF-8 retry.
- Complete Root/Statement/Role ancestry and the direct RoleKw/native-leading
  prefix select `Type(Primary)`/TypeExpression/primary zero over `5..6` or
  `5..9`. Retry TypeExpression owns its leading; no caller Missing is emitted.
- `role @ ;` retains its semicolon and leading as a pending boundary and is not
  presented as an EOF Error witness. Existing fresh/frozen and seeded-record
  compatibility checks remain unchanged.
- Independent pre-write and post-write audits were clean. After one
  formatting-only repair, scoped rustfmt/diff and the exact test passed 1 with
  1,431 filtered out; no production change, broad suite or benchmark ran.
- Role closes one context, leaving nine of the 20 required-Type Error
  transports without dedicated mapping. Act terminal and broader
  boundaries/layout/nested Type remain open; global Gate 1 is incomplete.

## Cast TargetType initial required-Type Error closure

- One Astra implementer added a three-case direct-CST matrix after completed
  CastPattern and actual target Colon: form-boundary terminal, singleton retry
  and three-leaf retry.
- Complete canonical topology selects the direct CastTarget Error group as
  `Type(Primary)`/TypeExpression/primary zero over `9..10` or `9..13` before
  records. Retry leading stays inside TypeExpression; terminal form-leading and
  semicolon remain CastDeclaration-owned.
- No Missing/Invalid/other Error occurs. Canonical and typed CastDeclaration
  subtrees agree, typed fresh/frozen trees agree, and all three complete at
  EOF. TargetIntroducer and later BodyIntroducer recovery remain excluded.
- Independent pre-write and post-write audits were clean. Scoped rustfmt/diff
  and the exact test passed 1 with 1,432 filtered out; no repair, production
  change, broad suite or benchmark ran.
- Cast closes one context, leaving eight of 20 required-Type Error transports
  without dedicated mapping. Act terminal and broader Cast/Type boundaries,
  layout, nesting and global Gate 1 remain open.

## Named-field initial required-Type Error closure

- One Astra implementer added a nine-case matrix for Struct, Enum and Error
  named-brace fields crossed with terminal, singleton retry and three-leaf
  retry Type errors.
- Complete declaration/variant/StructField ancestry plus actual Identifier and
  Colon select `Type(Primary)`/TypeExpression/primary zero before records.
  Retry leading belongs to TypeExpression; inner and outer closes retain their
  native owners and every path completes at EOF without Missing cascade.
- One repair corrected only a new compatibility fact: three CST Error leaves
  arise from two lexical Items, so the second legacy fact includes its internal
  leading. CST topology, grouping and projected ranges were unchanged.
- Independent pre-write and post-write audits were clean. The final scoped
  rustfmt/diff and exact test passed 1 with 1,433 filtered out; two test
  invocations, no production change, broad suite or benchmark.
- Three contexts close, leaving five of 20 required-Type Error transports
  unmapped: three tuple-field and two positional-payload contexts. Act terminal
  and broader boundary/layout/nested Type work remain open; Gate 1 is incomplete.

## Tuple-field and positional-payload initial required-Type Error closure

- Mode: M1 with one Astra pre-write audit, one Astra implementer and one
  independent post-write specification audit; no repair round.
- Fifteen witnesses cross Struct/Enum/Error tuple fields and Enum/Error
  positional payloads with terminal, singleton-retry and three-leaf-retry
  malformed Type. Separate ordered CST discriminators select direct
  `StructField` versus direct `EnumVariant` ownership before records.
- Both owner families derive `Type(Primary)`/TypeExpression/primary zero,
  maximal Error ranges, retry-leading ownership, native closes, no recovery
  cascade, EOF handoff and fresh/frozen agreement.
- Scoped rustfmt/diff and the wrapper-disabled exact test passed: 1 passed, 0
  failed, 1,434 filtered out. One test invocation ran; no repair, production
  change, broad suite or benchmark, and measurement budget usage was zero.
- These five contexts close the bounded mapping for all 20 reachable
  required-Type initial Error owner/shape transports. Act terminal remains a
  separate residual; broader boundaries/layout, recursive Type, occurrence
  combinations and global Gate 1 remain open.

## Act Head/Source semicolon-terminal required-Type Error closure

- Mode: M1 with one Astra pre-write audit, one Astra implementer and one
  independent post-write specification audit; no repair round.
- The audit separated occurrence shape from transport identity: Act Head and
  Source were already two of the closed 20 transports through retry evidence,
  while their no-retry semicolon-terminal alternatives lacked one common
  structural proof.
- Additive `act @;` and `act A = @;` witnesses now select Head versus completed
  Head plus actual Equals Source from ordered CST, then derive one
  `Type(Primary)` group, singleton TypeExpression expectation and primary zero
  before records. Act consumes the returned semicolon and fresh/frozen runs
  finish at EOF without Missing, Invalid, retry or BodyIntroducer cascade.
- Scoped rustfmt/diff and the wrapper-disabled exact test passed: 1 passed, 0
  failed, 1,435 filtered out. Two test invocations ran; no repair, production
  change, broad suite or benchmark, and measurement budget usage was zero.
- This closes only the bounded Act semicolon-terminal residual; the
  20-transport count is unchanged. Multileaf, EOF-terminal, other
  boundaries/layout/attachments, recursive Type and global Gate 1 remain open.

## BracedStatementBlock direct Statement Error proof closure

- Mode: M1 with one Astra architect/pre-write audit, one Astra implementer and
  one independent post-write specification audit; one assertion repair.
- The existing short catalog row claimed direct raw Error evidence, but its
  seven-witness test did not explicitly derive maximal groups or
  `BracedStatementBlock(Statement)` projection. The coverage text also
  overclaimed terminal/protected prefixes contrary to the catalog exclusion.
- Additive assertions now use complete
  Statement/OperatorChain/BracedStatementBlock ancestry and direct sequence
  order before records. They prove singleton, three-leaf ASCII, UTF-8/LF and
  CRLF-separated maximal groups, Statement expectation/primary zero,
  separator/retry/native-close ownership, no Missing/Invalid cascade, full
  source/empty remainder and fresh/frozen parity.
- The one repair removed an incorrect direct-child assumption: retry leading
  belongs inside the admitted Statement subtree, while the semicolon separator
  owns its following space in the corresponding witness. Existing fixtures and
  semantic expectations were unchanged.
- Scoped rustfmt/diff and the wrapper-disabled exact test passed: 1 passed, 0
  failed, 1,435 filtered out. Three test invocations ran; no production change,
  broad suite or benchmark, and measurement budget usage was zero.
- This closes only the seven ordinary matching-close witnesses. Terminal/
  protected-close/fence variants, exact `LineEntry` and pending EOF payload,
  nested recovery, other Statement sequences and global Gate 1 remain open.

## Shared indented first-Statement transport reconciliation

- Mode: read-only M1 census plus independent specification audit and M0
  record synchronization; no implementer or repair round.
- An explorer enumerated exactly 12 production calls into the shared indented
  Statement block kernel: Assignment, Colon, With, If, CaseLike, For, Binding,
  Mod, Role, Impl, Act and Cast. Eleven already had bounded linked rows;
  Assignment was the sole partial transport because its existing evidence had
  no dedicated catalog link.
- Independent audit found the existing five-case Assignment test sufficient:
  complete AssignmentTail/block ancestry with direct preceding Equals,
  accepted Statement, EOF Missing `6..6`, terminal maximal Error `6..9`,
  Error-to-Statement retry,
  protected `]` handoff, exact exits/remainders and fresh/frozen equality. It
  structurally selects `Assignment(IndentedStatement)`, singleton Statement
  expectation and primary zero before compatibility checks.
- Catalog and coverage now link this final transport, closing the bounded
  first-slot census at 12/12 without code or test changes. No test, broad suite
  or benchmark ran for the record-only synchronization; measurement usage was
  zero and the prior braced exact check remains the latest verification.
- This is not twelve unique roles or exhaustive indented-block coverage. Later
  sequence slots, nested Statements, caller-local introducers, other
  boundaries/layout/fences and global Gate 1 remain open.

## BracedStatementBlock terminal Error-to-Close composition closure

- Mode: M1 with one Astra architect/pre-write audit, one Astra implementer and
  one independent post-write specification audit; one mechanical repair and
  one comment correction.
- Four existing non-fence prefix witnesses now prove the full direct
  composition: required-Statement Error `1..2` followed in preorder by local
  closing-Brace Missing at `2..2` or horizontal-EOF `4..4`. Complete shell
  ancestry/order selects `BracedStatementBlock(Statement)` and the distinct
  `ClosingDelimiter` role before records, with singleton expectations and
  primary zero.
- EOF witnesses retain full source, block-owned trailing space, `InLine`, empty
  remainder and EOF payload. Protected `)`/`]` witnesses retain only `{@` in
  CST and preserve exact pending leading, token, extent, `InLine` and `tail`.
  Fresh/frozen trees, records and handoffs agree without extra Statement
  Missing, retry, separator or Invalid.
- The mechanical repair consumed a non-cloneable pending Item while inspecting
  its leading; a comment-only correction removed a misleading nonexistent
  Close role name. Existing fixtures and semantic expectations were unchanged.
- Scoped rustfmt/diff and the wrapper-disabled exact test passed: 1 passed, 0
  failed, 1,435 filtered out. Four test invocations ran; no production change,
  broad suite or benchmark, and measurement usage was zero.
- This closes only the four non-fence compositions. The fifth quoted Yumark
  fence is mapped separately below; other boundaries/trivia, nested recovery
  and global Gate 1 remain open.

## BracedStatementBlock quoted-Yumark-fence composition closure

- Mode: M1 with one Astra architect/pre-write audit, one Astra implementer and
  one independent post-write specification audit; one mechanical helper repair.
- The fifth existing terminal-prefix witness now proves owned CST `{@`,
  Statement Error `1..2`, then closing-delimiter Missing `2..2` before records.
  It separately proves pending CRLF `2..4`, borrowed boundary/temporary record
  coordinate `4`, and inspected quote/fence/newline extent `4..10`; none of
  these coordinates is harmonized or relocated.
- Exact borrowed fence facts, pending Item equality/extents, `PhysicalStart`,
  unconsumed remainder and source conservation are fixed. Fence-aware
  fresh/frozen trees, records and handoffs agree with no duplicate recovery,
  retry, separator, native close or Invalid.
- The mechanical repair replaced the ordinary leading emitter, which rejects
  boundary Items, with the existing terminal-boundary helper. Structural and
  range assertions were unchanged.
- Scoped rustfmt/diff and the wrapper-disabled exact test passed: 1 passed, 0
  failed, 1,435 filtered out. Three test invocations ran; no production change,
  broad suite or benchmark, and measurement usage was zero.
- This closes only the one quoted-fence composition. Other fences/prefixes,
  outer Yumark construction, other braced callers, nested recovery and global
  Gate 1 remain open.

## BracedStatementBlock direct Statement Error caller reconciliation

- Mode: M1 with one Astra architect/pre-write audit, one Astra implementer and
  one independent post-write specification audit; no repair round.
- Production has six direct braced-block calls: one expression NUD plus Mod,
  Role, Impl, Act and For. The NUD rows were already closed; the five non-NUD
  callers previously had record-only compatibility evidence without structural
  Error ownership or projection proof.
- Existing five witnesses now prove complete caller/header/block ancestry,
  exact native direct children, one maximal Error group and the invariant
  `BracedStatementBlock(Statement)` projection with singleton Statement and
  primary zero. There is no Missing, Invalid, retry, duplicate Error or
  caller-body recovery.
- Mod/Role/Impl/Act retain EOF completion while For retains `Ok(())`; all prove
  `InLine`, full source, empty remainder and fresh/frozen tree/record/exit
  equality after structural proof.
- Scoped rustfmt/diff and the wrapper-disabled exact test passed: 1 passed, 0
  failed, 1,435 filtered out. Three test invocations ran; no production change,
  broad suite or benchmark, and measurement usage was zero.
- This closes one matching-close Error alternative for five caller transports.
  Additional NUD variants beyond separately mapped rows, protected/fence,
  header/attachment, Missing/Separator/Close, nested recovery and global Gate
  1 remain open.

## Nested For-body BracedStatementBlock Error composition closure

- Mode: M1 with one Astra architect/pre-write audit, one Astra implementer and
  one independent post-write specification audit; no repair round.
- Existing `{for x in xs {@}; use a}` topology now proves its full nested path:
  Root/Statement/OperatorChain/outer block/first Statement/For/inner block,
  plus the distinct accepted outer Use sibling after native `; `.
- The outer block has zero direct recovery occurrences. Its admitted For carries
  the inner block's sole maximal Error `14..15`, which projects
  `BracedStatementBlock(Statement)`, singleton Statement and primary zero. No
  Missing, Invalid, duplicate outer recovery or caller recovery occurs.
- Inner close, outer separator, accepted Use and outer close retain native
  owners; the outer handoff is EOF `24..24` with `InLine` and empty remainder.
  Fresh/frozen trees, records and exits agree after structural projection.
- Scoped rustfmt/diff and the wrapper-disabled exact test passed: 1 passed, 0
  failed, 1,435 filtered out. Three test invocations ran; no production change,
  broad suite or benchmark, and measurement usage was zero.
- This closes one nested For/Use composition only. Deeper recursion, malformed
  For headers, other siblings, protected/fence exits, other block slots and
  global Gate 1 remain open.

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
timeout 180s env RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-syntax tests::braced_statement_recovery::braced_statement_raw_error_stays_in_nested_for_body -- --exact --test-threads=1
```

Result: 1 passed, 0 failed, 0 ignored; 1,435 filtered out. Scoped
`rustfmt --edition 2024 --check crates/yu-syntax/src/tests/braced_statement_recovery.rs`
and `git diff --check` also passed. Earlier fence/matching-close braced/Act/
tuple/positional/named-field/Cast/Role/Impl evidence remains historical rather
than the latest check. No workspace build,
broad suite or performance experiment was needed for this M1 closure/M0 record
update. Future checks follow
`rules/testing.md`; inspect resource behavior before broadening. `cargo xtask
check-graph` checks dependencies, not syntax behavior.

- Current daily record: [`2026-09-15`](../notes/progress/daily/2026-09-15.md).
- Complete pre-handoff task text: [`archived navigation`](../notes/progress/task-navigation-before-solo-handoff-2026-09-12.md).
  It preserves all 1,737 original lines, including older confirmed facts,
  rejected approaches, verification history and source locators. It is not an
  active queue or authority to resume superseded work.
- Earlier history: [`typed-recovery ledger`](../notes/progress/successor-typed-recovery-ledger.md)
  and [`pre-recovery-authority task archive`](../notes/progress/rewrite-state-before-recovery-authority-2026-09-08.md).
