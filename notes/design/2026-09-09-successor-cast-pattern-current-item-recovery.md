# Cast Pattern current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the active recovery-selection delegation and
successor-parser continuation. Reviewed-by: scoped M2 read-only preflight.

Scope: the initially absent Cast Pattern slot in
`cast_pattern_value_normalized`. CastPattern closing-delimiter recovery,
Target, form/body, and malformed nonempty Pattern recovery remain separate
owners. No accepted syntax, Pattern child policy, wrapper or generic API
change.

Authority: `CAST-R` rows for exact opener plus absent Pattern, local close and
colon/form handoff in `2026-08-20-yu-syntax-chasa-architecture.md`; the
current recovery-authority amendment; and the user's recovery-selection
delegation.

## Contract

An initially absent Pattern publishes exactly one zero-width
`Declaration(Cast(Pattern))` Missing with `ExpectedSyntax::Pattern`, committed
source, primary index zero and no unexpected facts. It owns only the immediate
absent slot: malformed nonempty Pattern input stays in the existing required
Pattern child as its native `Pattern(Primary)` Error, and nested Pattern, Type
and delimiter records retain their own roles.

Classify, in order, actual Cast-local `)`, allowed-gap `:`/`;`/`=`, then
protected outer/EOF/layout/fence boundary. Leave the Item unread and route it
through the existing incomplete-Pattern transition when positive close/phase
evidence exists. Thus `cast()` consumes its local close after one Cast Pattern
Missing; `cast(: T;`, `cast(;` and `cast(= value` preserve punctuation for
their next phase without a close/target cascade. Protected boundaries return
with their Item/leading unchanged and no later slot record. The no-local-frame
case never converts an outer/unowned `)` into local ownership.

Missing anchors at remaining start, except abstract boundary coordinate; EOF
follows the existing owner leading rule. Retain the existing Pattern child
stops, caller closes, origin/line/fence/ambient/sequence transport.

Verify fresh/shifted/frozen/seeded exact records for EOF/CRLF/fence/newline,
local versus outer `)`, colon/form handoff, malformed/valid Pattern retry and
nested close controls. Run Cast, direct Pattern/normalized/recovery-output,
package check, format and diff. Measurement budget: zero samples/processes.

## Completion evidence

The initial absence is now published before the generic Pattern child, then
uses the existing incomplete-Pattern transition for local close and phase
handoff. Nonempty malformed Pattern input remains native to Pattern recovery.
Exact fresh/shifted/frozen/seeded records cover EOF, CRLF, local close, colon,
semicolon and equals; a quoted-fence control proves its boundary coordinate.
M2 preflight and delta review found no scoped defect. Cast 13; direct
Pattern/normalized/recovery-output 162; package check, format and diff passed.
Benchmark use: zero samples/processes.
