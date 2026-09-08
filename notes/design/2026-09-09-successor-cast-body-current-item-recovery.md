# Cast Body current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the active recovery-selection delegation.
Reviewed-by: scoped M2 read-only preflight.

Scope: the post-`=` equal-or-shallower newline Missing in
`cast_definition_body_normalized`, plus the inline initial Missing and
malformed Error run in `cast_inline_body_normalized`. The strictly-deeper
indented path remains the existing `Cast(IndentedStatement)` child owner.
TargetType, BodyIntroducer, accepted body grammar, nested Expression recovery,
wrappers, public dispatch, and generic recovery APIs remain unchanged.

Authority: `CAST-R` Body rows in
`2026-08-20-yu-syntax-chasa-architecture.md`, D8f of the authoritative Yumark
adoption matrix, the current recovery-authority amendment's truthful typed
record requirements, the completed Binding inline-Body protected-boundary
policy, and the user's explicit recovery-selection delegation.

All owned publications use `Declaration(Cast(Body))` with
`Expression`. Missing is zero-width with no unexpected facts. Error is one
maximal nonempty lexical run with one `OtherCharacter` fact over its exact
emitted extent; it has one mapped expectation with `COMMITTED_RECOVERY_RULE`
and primary index zero.

After exact `=`, a strictly-deeper indentation enters the existing
`Cast(IndentedStatement)` Statement child; its recovery is not relabelled or
duplicated as Body. Equal-or-shallower newline, EOF, separator, active stop,
line stop, abstract/fence boundary, and unread close publish one Body Missing
and retain the whole current Item. In particular, the post-equals newline
probe rolls back to the outer statement owner. A normal inline NUD enters the
ordinary Expression body unchanged.

The Boundary-leading rule retains Binding's protected-boundary policy while
matching the preceding Cast gates' EOF split: ordinary EOF with nonempty
same-line leading emits that leading in `CastBody` before anchoring Missing at
the successor; abstract/fence, separator, close, stop, and every LF/CRLF
boundary keep their Item and leading pending. This replaces the old Cast raw
branch's eager non-EOF boundary-leading emission.

For a non-boundary non-NUD Item, emit initial leading directly in `CastBody`,
then use the same lexical-only Expression current-Item acquisition as normal
entry to consume one maximal Error run. Internal run leading belongs to Error;
retry/boundary leading remains outside. Stop before a NUD or any protected
boundary, return the next Item unchanged, and either retry the ordinary
Expression entry or hand the boundary up with no second Body Missing. Only a
nonempty same-line EOF-leading suffix extends the still-open Error node,
record, and unexpected fact together; empty or LF/CRLF EOF leading remains
pending. No grammar child or builder may run inside Error.

Before closure verify exact fresh, shifted, frozen, and seeded Body records for
EOF, separators, closes, active `else`, fence, LF/CRLF and shallower-newline
boundaries; Error retry, multi-Item/UTF-8 runs, boundary exits and EOF-leading
ownership. Prove actual separator/close handoff, no Body record after Error,
accepted inline bodies, and deeply indented missing/malformed Statements with
only their child role. Run Cast plus direct Expression/statement/normalized/
recovery-output tests, one package check, scoped format and diff. Measurement
budget: zero samples/processes unless material uncertainty appears.

## Completion evidence

The three raw publishers are replaced by the selected `Cast(Body)` helpers:
the equal-or-shallower post-equals branch, initial inline boundary, and sealed
inline Error run. `CastRole::Body` is live and no longer has a dead-code
exemption. The old generic `cst_output::emit_missing` helper had no remaining
callers after this replacement and was removed.

Exact fresh, shifted, frozen, and seeded tests cover EOF, whitespace EOF,
separators, closes, active `else`, CRLF, fence coordinates, Error retry,
UTF-8 extent, and no duplicate Body record. CST controls distinguish same-line
from LF/CRLF EOF ownership. The deeper indented recovery proves it publishes
only its existing `Cast(IndentedStatement)` child role; accepted and nested
Expression behavior stays in its existing owner.

M2 preflight and delta review found no production defect. Cast: 22;
expression recovery: 6; normalized: 83; recovery-output: 25; package check,
format, and diff passed. The direct statement filter had one unchanged
non-Cast assertion failure (`my role = value`); review found no dependency
from this gate, so it was not altered. Benchmark use: zero samples/processes.
