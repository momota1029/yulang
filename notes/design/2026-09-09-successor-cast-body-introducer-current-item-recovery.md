# Cast BodyIntroducer current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the active recovery-selection delegation.
Reviewed-by: scoped M2 read-only preflight.

Scope: the raw Missing site and malformed Error run in `cast_form_normalized`.
TargetType remains delegated to its existing required-Type owner; post-`=` Body
and IndentedStatement stay separate owners. No accepted Cast syntax, form
selection, target Type grammar, body grammar, wrapper, public dispatch, or
generic recovery API changes.

Authority: `CAST-R` BodyIntroducer rows in
`2026-08-20-yu-syntax-chasa-architecture.md`, D8e of the authoritative Yumark
adoption matrix, the current recovery-authority amendment's truthful typed
record requirements, and the user's explicit recovery-selection delegation.

All publications use `Declaration(Cast(BodyIntroducer))` with
`Punctuation(Semicolon)`. Missing is zero-width with no unexpected facts.
Error is one maximal nonempty native lexical run with one `OtherCharacter` fact
over its exact emitted extent. Each record has one expectation with
`COMMITTED_RECOVERY_RULE` and primary index zero.

Allowed exact `;` and `=` take priority and remain actual form evidence: the
former is bodyless and the latter enters the later Body owner. A boundary, EOF,
active stop, line stop, separator, unread close, or disallowed gap publishes
one Missing while retaining the whole Item and leading; it never cascades a
Body Missing. The Error scan uses the form-punctuation lexical vocabulary: it
reuses the existing Type token acquisition only because it keeps exact `=`
separate from a malformed Statement operator, without invoking a Type grammar
owner or changing target acceptance. It stops before an allowed form starter or
protected boundary. On either Error exit the next Item stays unread for
ordinary form/boundary logic and no Missing follows.

Initial leading remains Cast-owned outside Error, internal run leading belongs
to Error, and retry/boundary leading stays outside. The selected EOF-leading
rule matches the preceding Cast gates: only nonempty same-line EOF leading
extends the still-open Error node, record, and unexpected fact together; empty
or newline/CRLF EOF leading remains pending. This is a malformed-only
successor-recovery selection.

Before closure verify exact fresh, shifted, frozen and seeded records for
Missing at EOF, outer/active closes, separators, active `else`, fence, and
allowed/disallowed LF/CRLF gaps; Error retry to `;` and `=`, multi-Item and
UTF-8 runs, boundary/EOF exits, CST EOF-leading ownership, actual starter
ownership, and no Body cascade. Retain accepted forms and nested TargetType
controls. Run Cast plus direct Pattern/Type/normalized/recovery-output tests,
one package check, scoped format and diff. Measurement budget: zero
samples/processes unless material uncertainty appears.

## Completion evidence

`cast_form_normalized` now publishes the selected BodyIntroducer Missing/Error
records through one lexical-only Error run. `CastVocabulary::Form` is limited
to token acquisition for exact form punctuation: it uses the existing Type
token vocabulary to leave `=` for the form owner, without entering Type
grammar or broadening accepted forms. `==` remains malformed.

Fresh, shifted, frozen and seeded tests cover EOF, closes, separator, active
`else`, CRLF, UTF-8, malformed retry, fence coordinates, and no Body cascade.
Direct CST controls prove that `@ ;` retains a bodyless semicolon form and
`@ = value` retains the equals-led `CastBody`; same-line versus CRLF EOF
leading ownership is covered separately. The quoted-fence Missing anchors at
its inspected abstract coordinate, after the CRLF carrier.

M2 preflight and delta review found no production defect. Cast: 19;
Pattern/Type/normalized/recovery-output: 358; package check, format, and diff
passed. Benchmark use: zero samples/processes.
