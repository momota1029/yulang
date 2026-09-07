# BracketRow current-Item recovery

Status: Authoritative; private BracketRow-owned construction complete

Date: 2026-09-08

Scope: private BracketRow Item, Separator and Close sites in
`rewrite/type_expr/delimited.rs`. LeadingEffectTypeHead, BracketRowArrow,
record/forall and aggregate embedded/header/public certification remain later.

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary under the user's no-subagent instruction

## Retained grammar and selected recovery

Retain the architecture's BR-G/N/L attachment, full Type items, explicit and
qualifying-newline separators, opening baseline and actual matching-close
priority. BracketRow keeps dormant Type-ML provenance; a standalone or outer
TypeApply does not turn `F A` into two row items. Leading rows still require a
head and trailing rows still require an arrow; this slice does not migrate
those separate recovery producers.

Select only the following current-Item changes to BR-RP recovery:

1. Reuse the non-Call malformed-Item run used by P/E, retaining BracketRow's
   qualifying implicit-newline stop. An admitted retry Item's leading is
   emitted directly under BracketRow, never detached and appended to the
   preceding Error. Initial leading is also row-owned; intermediate malformed
   Items keep their leading inside one Error. This supersedes BR-RP1 and the
   T4 register amendment's eighth-terminal requirement only for that old
   retry-leading ownership, including same-line and deeper-newline trivia.
2. Caller stops and known outer closes always outrank a fresh or retried Item,
   including caller words that are otherwise valid Type NUDs. Preserve the
   complete leading-plus-token Item at that handoff. The ordinary-horizontal
   P/E/Call exception does not apply to BracketRow. An actual matching `]`
   still wins over a stop bit for `]`.
3. Retain the distinct BracketRow close-slot procedure: an unclaimed mismatch
   is one typed close Error, then retry only close tokens. A valid Item after
   that error is not admitted into the row; it remains pending with a Missing
   close. Fresh slots still publish Item Missing before a local mismatch, but
   a malformed Item Error or completed item does not add an Item Missing.
4. Publish the already-approved missing separator when a completed item returns
   a no-gap NUD or a deeper-newline NUD. Emit admitted continuation leading
   before that separator record, anchoring it at the next NUD. Keep actual
   close, literal separator, protected boundary and qualifying newline ahead
   of this recovery. Deeper-newline non-NUDs after a completed item remain
   pending with only the row's Missing close.

Every B-owned recovery uses native CST token kinds, `COMMITTED_RECOVERY_RULE`,
one same-role/range expectation and primary index zero. Item expects
TypeExpression; Separator expects DelimitedSequenceSeparator; Close expects
`]`. Item Error has one OtherCharacter fact for the complete emitted run;
close Error records the actual punctuation. Missing has no unexpected facts.
This native B close representation supersedes the T4 register amendment's
coalesced-Unknown close-Error rule only for BracketRow.
Missing anchors use an abstract boundary's inspected coordinate, otherwise
the Item's remaining-start after any permitted emission. Raw arrow/head
Missing nodes from the still-unmigrated parent are not B-owned records.

## Pre-write controls and site ledger

| source | ordered B-owned records |
| --- | --- |
| `T [,] -> U` | Item Missing `3..3` |
| `T [:] -> U` | Item Error `3..4`, native Colon child |
| `T [@ A] -> U`, `T [@\n  A] -> U`, comment/CRLF variants | Item Error `3..4`; retry leading directly under row |
| `T [A{}] -> U` | Separator Missing `4..4` |
| `T [)] -> U` | Item Missing `3..3`, close Error `3..4` |
| `T [A)] -> U` | close Error `4..5` |
| `T [@ )] -> U` | Item Error `3..4`, close Error `5..6`; no Item Missing |
| `T [` | Item Missing `3..3`, close Missing `3..3`; parent arrow remains raw |
| `T [A` | close Missing `4..4`; parent arrow remains raw |
| `T [@` | Item Error `3..4`, close Missing `4..4`; parent arrow remains raw |
| `F(T [A)` | row close Missing `6..6`; outer Call consumes native `)` |
| `T [A) B] -> U` | close Error `4..5`, close Missing `5..5`; space/`B` remains pending, no return to item parsing |
| `T [@ else rest`, explicit ELSE stop | Item Error `3..4`, close Missing `4..4`; complete space/word Item pending |

Accepted controls cover both attachments, full TypeApply, nested rows, empty
rows, explicit/implicit separators and deeper actual closes. Boundaries cover
initial, after-separator, after-item and after-error phases; caller words,
outer delimiters, ordinary/comment/LF/CRLF leading, abstract fences, shifted
origins, seeded state and distinct frozen IDs. PV structured Error controls
retain outer-first reservation order and emitted ranges.

Sites: shared Item/Separator/Close emitters, BracketRow initial and deeper-
newline branches, malformed-Item run, post-separator handling and the distinct
close retry. The raw `missing_bracket_row_close` helper can disappear once all
of its callers use the typed owner-local path; record-owned raw helpers remain.

## Verification and cost

M2, primary-only implementation and deterministic verification. Budget one
scoped implementation/repair pass, focused B tests and the complete Type filter,
TypeDeclaration/output/recovery-output siblings, one package check and scoped
format/diff checks. No independent-review claim or broad workspace run.

Use the existing total Error-run terminal and constant owner policy branch.
No source rescan, buffer, partial-Item capability or new generic library API.
All scanning is forward and linear; records allocate only on recovery. Zero
benchmark samples/processes are budgeted.

## Construction result

Completed 2026-09-08 by the primary without independent review, per the user's
direct-work instruction. The shared delimiter module has no raw Error/Missing
construction left. P/E/B reuse the total Item-error scan with an owner-selected
newline stop; B still has its separate close-only retry and preserves caller
words and known outer closes before emitting their leading. The no-gap B
separator is published at the next Item. The unused raw B-close helper was
removed; record-owned raw helpers were retained.

Six focused tests pass, including accepted grammar, native typed records,
same-line/comment/LF/CRLF retry ownership, explicit caller and outer-close
boundaries across five phases, close-only continuation, quoted fences,
shifted origins and PV reservation nesting. Three existing tests changed only
their superseded raw-B or retry-leading expectations. Complete Type filter:
147 passed; TypeDeclaration: 39; output: 4; recovery output: 25. Package check,
scoped rustfmt and diff checks passed. No timing samples/processes or broad
workspace suite were used. The arrow/head and aggregate certification gates
remain open.
