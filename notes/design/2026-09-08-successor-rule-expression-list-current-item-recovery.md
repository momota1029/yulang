# Rule ExpressionList current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: `rewrite/rule/expression_list.rs`: required item, after-item separator
and close recovery for Rule bracket atoms, RuleCall and RuleIndex; plus the
small `item.rs` one-prefix coordinate callback needed to retain a single
leading-fragment traversal while publishing repeated newline slots. It adds the
private role vocabulary required by this already-authoritative ordinary list
owner. RuleLiteral, String/Virtual, Statement/declaration, Colon/sequence
context and public dispatch remain separate.

Authority: direct-literal cone §§2 and 4.2; typed-output amendment §4;
recovery-authority amendment §§1--3. Concrete role publication is delegated;
accepted list grammar is unchanged.

## Slots and recovery

Add `GrammarRole::ExpressionList(ExpressionListRole::{Item, Separator})` and
`ConstructRole::ExpressionList`. Item expects `Expression`; Separator expects
`DelimitedSequenceSeparator`; close uses existing `ClosingDelimiter` with the
current Parenthesis or Bracket delimiter and its exact close punctuation.

Item and close Missing are zero-width singleton committed-rule records.
Malformed Item and after-item Separator each retain the current one-Item Error
policy: native token kind, one `OtherCharacter` fact over its exact emitted
range, then scan the next Item outside Error. Do not merge consecutive Error
nodes. Existing child Expression recovery retains its own role.

Required-item Error does not satisfy the item slot; a following separator or
terminal boundary still publishes Item Missing. Repeated newline separators
retain their individual Missing coordinates at the physical newline end. Valid
trailing separators require no Item Missing. Ordinary EOF anchors at successor
while retaining its complete pending Item and leading; fence/outer close keep
their inspected boundary and pending Item/leading unchanged. Matching local
close is emitted by its existing caller.

## Evidence and execution

Covered fresh/frozen Item, Separator and both close roles; repeated fenced
CRLF newline coordinates; one-Item Error/retry and Error-then-Missing order;
EOF/fence/outer-close leading; nested child records; all three callers;
UTF-8/shifted coordinates; accepted empty/trailing separator controls. The
coordinate callback initializes extent and fragment cursor once and emits one
prefix through the last ordinary newline, so its cost is linear in physical
leading, foreign splits and emitted recovery work. M2 used one implementation
pass, no repair bundle, plus independent specification/recovery and regression
audits. Focused Rule tests passed 40, the new recovery filter 5 and
`recovery_output` 25; package check, scoped format and diff checks passed.
Benchmark budget remained zero samples/processes under the static cost audit.
