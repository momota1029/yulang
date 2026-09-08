# Cast Pattern close current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the active recovery-selection delegation. Reviewed-by:
scoped M2 read-only preflight.

Scope: `cast_pattern_close_normalized` only: its two Missing sites and one
malformed close Error run. Pattern value, target, form/body and no-local-frame
paths remain unchanged.

Authority: `CAST-R` close rows in the architecture, typed-output extent
requirements, and delegated successor recovery selection.

All publications use `ClosingDelimiter { owner: ConstructRole::CastPattern,
delimiter: Parenthesis }` with `Punctuation(Close(Parenthesis))`. Missing is
zero-width; Error is one maximal nonempty native lexical run with one
OtherCharacter fact over its emitted range. Local `)` consumes first; colon
then form punctuation remain unread for their subsequent phases; outer close,
stop, EOF and fence remain unread. Error never adds a second Missing.

The selected EOF-leading rule is: only a nonempty same-line EOF leading suffix
belongs in the still-open close Error and extends its node, record and fact
together. Newline EOF leading remains pending. This supersedes the prior raw
close loop's accidental deeper-newline Error ownership; it aligns Error extent
with the sealed typed output and does not alter accepted syntax.

Construction completed 2026-09-09. The existing `CastPattern` close role now
has no dead-code exemption. M2 preflight and delta review found no concrete
defect; the delta review confirmed lexical transition parity, unchanged
no-local-frame behavior, no Error-to-Missing cascade, and coherent same-line
EOF extent publication. Focused Cast tests (14), direct Pattern/normalized/
recovery-output tests (162), package check, format check, and diff check
passed. Benchmark use: zero samples/processes.
