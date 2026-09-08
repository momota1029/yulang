# Cast PatternIntroducer current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the current recovery-selection delegation and the
instruction to continue the successor parser. Reviewed-by: scoped M2
read-only owner preflight.

Scope: the raw Missing/Error sites of `cast_pattern_introducer_normalized` and
its one lexical current-Item scan in `declaration/cast_decl.rs`. Pattern value,
CastPattern close, target introducer/type, form/body and statement recovery
remain their current separate owners. No accepted Cast syntax, wrapper,
operator selection, delimiter ownership, public dispatch or generic recovery
API changes.

Authority: `CAST-R` in
`2026-08-20-yu-syntax-chasa-architecture.md`, especially its PatternIntroducer
rows and one-error/no-cascade rule; the current recovery-authority amendment's
truthful typed-record requirements; and the user's explicit recovery-selection
delegation. Yulang2 remains accepted-input evidence only.

## Publication

Every recovery selected by this slot has the one identity
`GrammarRole::Declaration(DeclarationRole::Cast(CastRole::PatternIntroducer))`
and one expectation
`Punctuation(Open(Parenthesis))`, with committed-rule source and primary index
zero. A Missing is zero-width with no unexpected facts. An Error is one
nonempty maximal run, with one `OtherCharacter` token fact spanning its emitted
range. Existing native token kinds remain native inside Error.

The finite outcomes are:

| inspected current Item | publication | continuation |
| --- | --- | --- |
| `;` or `=` admitted across an allowed gap | Missing | keep Item unread; enter form |
| `:` admitted across an allowed gap | Missing | keep Item unread; enter target |
| `)` | Missing | keep Item unread; no Cast-local frame exists |
| abstract boundary, active stop, line stop, separator, unread close, disallowed gap, or EOF | Missing | preserve pending Item/leading and return |
| reusable Pattern NUD without `(` | Missing | start existing `CastPattern`; retry same Item as Pattern without local-close authority |
| other non-boundary Item | Error | scan forward lexically to a row above, exact `(`, or reusable Pattern NUD |

The Error scanner uses the same total current-Item acquisition and Pattern
vocabulary as normal entry. It does not parse a grammar child or build a nested
node. The existing entry leading remains Cast-owned; internal run leading and
the existing same-line EOF leading belong to Error, while retry/boundary and
newline EOF leading stay pending.

`:`/`;`/`=` retain their phase priority before generic boundary classification.
An actual `(` consumes and creates the existing local Pattern frame. A reusable
Pattern NUD retries without that frame. In particular, malformed-run to bare
Pattern NUD publishes exactly one PatternIntroducer Error: do not append the
old duplicate Missing. Later Pattern/close/target/form failures are distinct
only after their own positive evidence; no same-cause cascade is introduced.

## Boundary and verification

An absent opener anchors at the remaining Item start, except an abstract
boundary anchors at its coordinate. Ordinary EOF follows the existing Cast
leading policy. `)` is always unread in this slot, whether outer-owned or
unowned. Preserve baseline, stops, line/fence handoff, ambient context and
sequence context unchanged.

Before closure verify exact fresh, shifted, frozen and seeded records for every
row, multi-Item malformed runs, retry to `(` and bare Pattern NUD, EOF/
newline/CRLF/UTF-8/fence leading, active contextual stop, allowed and
disallowed newline gaps, outer `)`, and effect-free optional Cast rejection.
Keep accepted Cast and the nested Pattern/close/target/form controls unchanged.
Run the Cast owner suite, its direct Pattern/Type/statement/recovery-output
cone, one package check, scoped format and diff. Measurement budget: zero
samples/processes unless material uncertainty appears.

## Completion evidence

Construction used the existing sealed Error-run capability, extended narrowly
to admit a nonempty same-line EOF-leading suffix only while its Error remains
open. That suffix extends the Error node, committed range, and one unexpected
fact together; empty or newline EOF leading remains outside Error. No generic
parser/recovery API was added.

The first M2 delta review found the initial Error/CST extent mismatch; its
repair then exposed the empty-EOF call. A final scoped review closed both:
`cast @` records `5..6`, while `cast @   ` records and emits `5..9`. The full
PatternIntroducer table is exact in fresh, shifted, frozen, and seeded modes,
including multi-Item Error, retry, phase handoff, active stop, CRLF, UTF-8,
and fence controls. Cast: 12 passed; direct Pattern/required-Type/
recovery-output cone: 84 passed; `cargo check -p yu-syntax`, format and diff
passed. Benchmark use: zero samples/processes.
