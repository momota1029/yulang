# TypeDeclaration header current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-09

Approved-by: user through the recovery-selection delegation in
`2026-09-08-successor-recovery-authority-amendment.md`

Scope: TypeDeclaration mandatory Name and equality DefinitionIntroducer only.
Existing RHS, parameter, derives/companion, attached-impl and nominal/equality
form ownership remain unchanged.

Authority: TD-R/TND-R/TND-J, typed-output §§3--4 and recovery-authority §§1--3.

## Records and form preservation

Name publishes `Declaration(Type(Name))`, expected Identifier. Definition
introducer publishes `Declaration(Type(DefinitionIntroducer))`, expected lone
Equals. Missing is zero-width with no unexpected facts; Error has the actual
nonempty native lexical run and `OtherCharacter` facts. Both use one committed
expectation and primary zero.

Run the existing form classifier before introducer recovery. Valid nominal
forms remain zero recovery. Exact `=` enters the existing typed RHS; `==` and
`=>` are not split. A terminal Name failure never cascades introducer/RHS; a
terminal introducer failure never becomes Nominal or RHS Missing. Raw header
identifier scanning retains its existing priority over Type payload scanning.

## Current Item and leading

Classify existing header boundaries before emitting initial leading. Protected
active stops, layout/fence boundaries and their whole remaining Items retain
their leading/payload, suffix, origin and line. This gate does **not** broaden
the existing inactive-right-close boundary policy.

For malformed Name/introducer, initial leading belongs directly to
TypeDeclaration; internal lexical run leading belongs to Error; retry leading
belongs directly to TypeDeclaration outside Error. Ordinary EOF after Error
emits its remaining leading directly in TypeDeclaration, then returns EOF with
no second Missing. This deliberately supersedes the old malformed-only Error
text assertions (`"@ "` becomes `"@"`), including EOF-parent ownership, while
preserving each source literal, lossless product, continuation and cardinality.

Name retry stops before raw name, exact `=`, or the existing boundary; exact
`=` takes equality without a duplicate Name. Introducer retry stops before
exact `=` or admitted TypePrimary and retries it outside Error; a boundary
after Error returns unchanged without RHS Missing. All Error scanning is
lexical-only and forward-only.

## Evidence

Audit changed retry/EOF Error text assertions explicitly. Add exact
fresh/shifted/frozen/seeded Name/introducer records, UTF-8/CRLF/foreign-prefix
and quoted fence handoff, initial/post-run boundaries, raw/contextual-name
controls, lone-equals controls, nominal zero-recovery forms, no-cascade and
nested RHS ownership. M2 implementation, compiler/recovery and regression
review, one repair bundle; focused TypeDeclaration/Type/normalized/output
checks, package check, format and diff; benchmark zero.
