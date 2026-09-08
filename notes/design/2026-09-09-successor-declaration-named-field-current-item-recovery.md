# Declaration named-field current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: the shared declaration named-field internal driver presently hosted by
`declaration/struct_decl.rs`, and its explicit role transport from Struct and
Enum/Error variant callers. This gate publishes `Field`, `FieldName`, and
`FieldColon`; the already-selected caller-specific `FieldType` Missing stays
at the existing required-Type entry. Field sequence, separator, matching-close,
outer-close, tuple-only, body-introducer, header, variant sequence, and trailing
attachment recovery are excluded.

Authority: recovery authority §3; typed-output commitments; SD-R's Struct
field table; ENUM-R/ERROR-R's neutral field-driver requirement; the Struct
actual-close trailing amendment. The pre-write specification audit found that
the driver is shared by Struct and Enum/Error variants and that the old
`missing_type_role` argument cannot truthfully label the remaining slots.

## Owner transport

The owner-neutral field driver receives one finite `DeclarationFieldRoles`
value from every caller. It contains the caller's `Field`, `FieldName`,
`FieldColon`, and `FieldType` grammar roles. Struct supplies its four Struct
roles; Enum and Error variant adapters supply their corresponding nested
Variant roles. The driver does not inspect a declaration keyword, fabricate a
Struct role for variants, or remap nested Type recovery. `FieldType` remains
the existing required-Type outer Missing override; descendant malformed Type
records retain their native Type roles.

This establishes the explicit shared-driver interface needed to replace the
misleading placement beneath the Struct owner. The physical move to
`declaration/fields.rs` follows as a separate behavior-preserving topology
gate after the remaining sequence/separator/close publication: moving only the
named-field interior now would leave the shared sequence mechanics under a
false Struct boundary. `struct_decl.rs` retains Struct header/body ownership
and `declaration_variant.rs` remains the variant sequence adapter. This is not
a generic parser utility or a new recovery capability.

## Selected internal current-Item rule

All Missing records are zero-width, have no unexpected facts, have exactly one
mapped expectation from `COMMITTED_RECOVERY_RULE`, and primary index zero.
All Error records are one maximal nonempty forward lexical run with native
tokens and one `OtherCharacter` fact for each emitted Item. Initial leading is
emitted by the field owner before Error; internal leading belongs to Error;
retry and protected-boundary leading remains outside Error. Ordinary EOF
leading remains pending after an Error. This intentionally changes the two
old Struct field assertions that placed initial or terminal leading inside the
Error node, while preserving every source literal and source byte exactly
once.

The finite rows are:

| slot / current Item | record and continuation |
| --- | --- |
| literal `:` at a named field start | `Missing(FieldName, Identifier)`; consume `:` and enter the existing RHS path |
| malformed field-start run reaches a same-line literal `:` | one `Error(FieldName, Identifier)` over that run; do not add Missing Name; consume `:` and enter the existing RHS path |
| malformed field-start run reaches raw name or a field boundary first | one `Error(Field, Identifier)`; leave the retry Item/boundary unchanged for the sequence owner; do not add Missing Field |
| accepted raw name, then same-line Type starter | `Missing(FieldColon, Colon)` and retry that Item through the existing RHS Type path |
| accepted raw name, then boundary, EOF, or non-qualifying newline | one `Missing(FieldColon, Colon)` only; do not cascade FieldType |
| accepted raw name, malformed colon run reaches literal `:` | one `Error(FieldColon, Colon)`; consume `:` and enter the existing RHS path |
| accepted raw name, malformed colon run reaches same-line Type starter | one `Error(FieldColon, Colon)`; retry the Type Item; no Missing FieldColon or FieldType cascade |
| accepted raw name, malformed colon run reaches protected boundary | one `Error(FieldColon, Colon)`; retain the boundary; no Missing cascade |

The scanner stops before an abstract/EOF boundary, active stop, matching or
outer close, comma, qualifying implicit separator, literal colon, raw retry
name, or same-line Type starter as applicable. It reads forward once, has no
run vector, CST-derived extent, diagnostic sorting, source replay, or parser
call inside Error. A field-start run is classified as `FieldName` only when
the actual forward scan reaches the literal-colon continuation; it is otherwise
the sequence-level `Field` failure. That classification is committed while
streaming and is never rewritten after emission.

## Retained boundaries and evidence

Preserve matching-close priority, variant `Borrow` versus Struct `Recover`,
variant pipe lexical mode, tuple TypeApply grouping, the mandatory-Type Equals
ownership correction, field-head candidate behavior, exact Item origin/line/
fence handoff, and actual-close-only Struct trailing attachment. No accepted
source, wrapper, operator table, delimiter policy, or field grammar changes.

Before integration, cover fresh/seeded/frozen and shifted coordinates for each
role family; UTF-8 and CRLF; initial/internal/retry/EOF leading; malformed
name to colon versus whole-field/boundary; colon error to colon/type/boundary;
literal missing name/colon; existing FieldType and nested Type controls;
Struct and Enum/Error variants; protected close/fence/stops; and accepted
named/tuple/layout controls. Run the focused Struct/variant/required-Type/
normalized/recovery-output cone, one package check, format and scoped diff.
Benchmark budget: zero samples/processes unless material uncertainty appears.

## Completion

The finite role transport and Field/FieldName/FieldColon publication are
implemented. One review repair changed multi-Item unexpected facts to their
actual emitted Item extents, gives active stops priority over colon/Type retry,
and limits Type retry to same-line Items. Struct and Enum/Error variant fresh/
frozen controls, active-colon handoff, multi-Item internal trivia, normalized
and recovery-output controls pass. The physical `fields.rs` move remains
deliberately open with the raw shared sequence/separator/close gate.
