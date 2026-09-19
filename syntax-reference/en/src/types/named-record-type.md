# Named-record types

## 1. Authority and scope

This page defines `NamedRecordType` in `syntax-v0`. The Authoritative named
record sections of the 2026-08-20 syntax architecture, the record-field and
record-sequence current-Item recovery records, and the named-record slot
authority govern this page.

It covers `{a: A, b: B}` as a type primary, its fields, separators, close, and
recovery. It does not define record patterns or expressions, field semantics,
type checking, lowering, or diagnostic wording.

## 2. Accepted syntax

```text
TypePrimary := ... | NamedRecordType
NamedRecordType := "{" G* [ TypeRecordField { RecordTypeSeparator TypeRecordField } [ RecordTypeSeparator ] ] "}"
TypeRecordField := Identifier TypeRecordFieldTrivia ":" TypeRecordFieldTrivia TypeExpression
RecordTypeSeparator := comma | qualifying newline
TypeRecordFieldTrivia := empty | same-line trivia | deeper continuation trivia
```

The opening trivia establishes the layout base. An equal-or-shallower newline
returns to separator judgment; a deeper newline continues the field RHS.
Semicolons, shorthand fields, defaults, spreads, sigil names, numeric names,
and path-qualified names are not accepted field syntax.

## 3. Admission and boundaries

At a required type-primary position, `{` admits a named record and commits to
that owner. `F {a: A}` is an apply argument; adjacent `F{a: A}` supplies no
apply authority.

Only a plain identifier starts a field. The record owns field colons, commas,
layout, and its matching close. Before an RHS consumes a whitespace apply,
the field-sequence judge recognizes a complete following `Identifier ... :`
head. It recovers the missing record separator and retries that field; it does
not turn the next field into the previous RHS apply. Caller boundaries and
outer closes remain unconsumed.

## 4. Direct Rowan CST

`NamedRecordType` contains its braces, trivia, direct `TypeRecordField`
children, and accepted commas in source order. A `TypeRecordField` contains
its name, colon, trivia, and direct `TypeExpression` RHS in source order.
Qualifying newline separators remain trivia.

`NamedRecordTypeSeparator` contains only an existing separator `Missing` or
raw `Error` occurrence. `NamedRecordTypeClose` consists of native trivia and
raw errors followed by either an accepted `}` or `Missing`:

```text
NamedRecordTypeClose := NativeTrivia* ( Error NativeTrivia* )* ( "}" | Missing )
```

There is one `NamedRecordTypeClose` wrapper for each committed record. These
wrappers add no separate diagnostic and do not wrap accepted commas or whole
fields.

## 5. Recovery CST

An absent field, field name, colon, RHS, separator, or close produces one
slot-local `Missing`; malformed source for that slot is a raw `Error` group.
A same-line complete next field head produces a separator `Missing` and retries
the field at the same position. A semicolon is separator recovery, not a field
separator.

Field recovery stays distinct from sequence recovery. A pending whole-field
`Missing` precedes a close node, including at the same byte coordinate. A
matching close is local. Once close recovery commits, its native trivia, raw
errors, and final `}` or `Missing` remain in that one close wrapper. A
protected caller boundary or outer close remains outside the record, and no
spread, shorthand, default, or `Invalid` node is invented.

## 6. Source/CST examples

`{a: A, b: List(Int)}` has two direct `TypeRecordField` children; the second
RHS contains `TypeCallTail`.

In the following form, the newlines and indentation are source-bearing record
children, not synthetic separators.

```text
{
  a: A
  b: B
}
```

`F {a: A}` contains a `TypeApplyArgument` whose primary is
`NamedRecordType`.

## 7. Composition

[Standalone `TypeExpression` core](type-expression-core.md) defines the RHS
and surrounding apply behavior. The [syntax content
model](../conventions/syntax-content-model.md), [Rowan CST
notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md) define the shared
`syntax-v0` conventions.
