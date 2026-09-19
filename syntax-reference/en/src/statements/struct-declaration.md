# `struct` declaration

## 1. Authority and scope

This page specifies `StructDeclaration` in `syntax-v0`. `SD-G`, `SD-J`,
`SD-T`, and `SD-R` in the Authoritative Struct declaration grammar, plus the
later named-field, field-sequence, foreign-close, derives, companion, and
actual-close amendments, govern it. Field meaning, constructors, methods, and
lowering are outside this page.

## 2. Accepted syntax

```text
StructDeclaration := [ VisibilityKw Gstruct+ ] StructKw Gstruct+ StructName Gstruct* StructBody
VisibilityKw := MyKw | OurKw | PubKw
StructKw := exact maximal word "struct"
StructName := Identifier
StructBody := Semicolon | NamedBracedStructBody | NamedIndentedStructBody | TupleStructBody
NamedBracedStructBody := LBrace StructOpeningTrivia [ StructNamedField { StructBracedFieldBoundary StructNamedField } [ StructBracedFieldBoundary ] ] RBrace
TupleStructBody := LParen StructOpeningTrivia [ StructTupleField { StructBracedFieldBoundary StructTupleField } [ StructBracedFieldBoundary ] ] RParen
NamedIndentedStructBody := Colon StructIndentedOpeningTrivia StructNamedField { StructIndentedFieldBoundary StructNamedField } [ TrailingIndentedComma ]
StructNamedField := Identifier Gfield-name Colon Gfield-type RequiredTypeExpression(Struct::FieldType)
StructTupleField := RequiredTypeExpression(Struct::FieldType)
StructBracedFieldBoundary := CommaBoundary | ImplicitStructNewlineBoundary(struct_list_base)
StructIndentedFieldBoundary := CommaBoundary | ImplicitIndentedFieldNewlineBoundary(block_indent)
TrailingIndentedComma := CommaBoundary before EOF, dedent, or an active outer boundary
Gfield-name := empty or same-line trivia
```

`RequiredTypeExpression` is the full required type production in the
[TypeExpression reference](../types/type-expression-core.md). `Gstruct+` is
non-empty declaration-continuing trivia; `Gstruct*` is empty or one such run.
`Gfield-type` permits empty, same-line, or strictly-deeper continuation trivia.

## 3. Admission and boundaries

An exact bare or visibility-led `struct` selects this declaration. Its body
begins only with `;`, `{`, `(`, or a lone `:`. Braced and tuple lists may be
empty; an indented list is non-empty. In braced and tuple lists, a qualifying
newline has indent at most `struct_list_base`; in an indented list it has indent
equal to `block_indent`. A deeper line continues a field type. `::` is not a
field colon.

## 4. Source-order Rowan schema

The closed schema is:

```text
StructDeclaration := [ VisibilityKw Trivia ] StructKw Trivia StructName
  { Trivia DerivesClause }
  ( Semicolon
  | DeclarationCompanion
  | NamedIndentedStructBody
  | NamedBracedStructBodyActualClose { Trivia DerivesClause } [ DeclarationCompanion ]
  | TupleStructBodyActualClose { Trivia DerivesClause } [ DeclarationCompanion ] )
NamedBracedStructBodyActualClose := NamedBracedStructBody whose RBrace is an actual matching close
TupleStructBodyActualClose := TupleStructBody whose RParen is an actual matching close
NamedBracedStructBody := LBrace Trivia { StructField | Comma | Trivia | StructFieldForeignClose } RBrace
TupleStructBody := LParen Trivia { StructField | Comma | Trivia | StructFieldForeignClose } RParen
NamedIndentedStructBody := Colon Trivia { StructField | Comma | Trivia }
StructField := NamedStructFieldContent | TupleStructFieldContent
NamedStructFieldContent := Identifier Trivia Colon Trivia TypeExpression
TupleStructFieldContent := TypeExpression
StructFieldForeignClose := Error+
```

The header position admits header derives before either a body or a header
companion. Only an actual matching braced or tuple close opens the trailing
position, where derives precede an optional companion. A semicolon, an
indented body, and a missing or mismatched close do not open it. Braced and
tuple bodies have one actual or recovered close; indented bodies have none.
`StructFieldForeignClose`, where present, is a direct delimited-list child,
never a `StructField` child.
In named braced and indented bodies, `StructField` contains
`NamedStructFieldContent`; in tuple bodies, it contains
`TupleStructFieldContent`.

## 5. Recovery CST

Header name and body-introducer recovery use their own slots without
same-cause cascades. A malformed header run is `Error+` in its header slot and
may retry at its named body starter. A complete name followed by EOF, an owner
boundary, or an equal-or-shallower newline has exactly one
`Missing(Struct::BodyIntroducer)`.

For named fields, a leading or repeated separator yields one missing field per
required field slot. A missing field name before a literal colon is
`Missing(Struct::FieldName)`; malformed field-name text is `Error+` in that
slot. A same-line complete next field head after a field yields exactly one
`Missing(Struct::FieldSeparator)` before that next field. An accepted name
followed by a same-line type starter yields `Missing(Struct::FieldColon)`, and
an accepted colon followed by a boundary yields
`Missing(Struct::FieldType)`. A separator error is `Error+` in the field-
separator slot, not a valid separator.

Tuple fields use one required `TypeExpression` each. A leading or repeated
comma creates one missing tuple field type; malformed type content remains
TypeExpression-owned. Same-line type primaries remain one TypeExpression and
do not imply a separator.

At a local close, the list retries its own close slot. A missing matching close
is one close-slot `Missing`; a protected outer close remains unread. No slot
adds another missing node after its own malformed run reaches a boundary. The
distinct field, field-name, field-colon, field-type, separator, and close
slots retain those cardinalities.

Matching close has priority. An absent close is one `Missing` at its close
slot. A protected outer close remains unread. A locally consumed foreign close
is one `StructFieldForeignClose` containing `Error+`; it is distinct from a
field-separator `Error`.

```xml
<StructDeclaration>
  <StructKw text="struct" />
  <Whitespace text=" " />
  <Identifier text="S" />
  <Whitespace text=" " />
  <LBrace text="{" />
  <Whitespace text=" " />
  <StructField>
    <Identifier text="x" />
    <Missing />
    <Whitespace text=" " />
    <TypeExpression><Identifier text="Int" /></TypeExpression>
  </StructField>
  <Whitespace text=" " />
  <RBrace text="}" />
</StructDeclaration>
```

The `Missing` is the field-colon slot; the type remains one structural child.

For `struct S { @ }`, the list owns the raw field failure. A locally consumed
foreign close instead uses the distinct wrapper shown by the schema.

```xml
<StructDeclaration><StructKw text="struct" /><Whitespace text=" " /><Identifier text="S" /><Whitespace text=" " /><LBrace text="{" /><Whitespace text=" " /><Error text="@" /><Whitespace text=" " /><RBrace text="}" /></StructDeclaration>
```

For `struct S { x: T ] }`, the locally consumed foreign close is wrapped once.

```xml
<StructDeclaration><StructKw text="struct" /><Whitespace text=" " /><Identifier text="S" /><Whitespace text=" " /><LBrace text="{" /><Whitespace text=" " /><StructField><Identifier text="x" /><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="T" /></TypeExpression></StructField><Whitespace text=" " /><StructFieldForeignClose><Error text="]" /></StructFieldForeignClose><Whitespace text=" " /><RBrace text="}" /></StructDeclaration>
```

## 6. Source and CST examples

The accepted source `struct S { x: Int }` has one named field.

```xml
<StructDeclaration>
  <StructKw text="struct" />
  <Whitespace text=" " />
  <Identifier text="S" />
  <Whitespace text=" " />
  <LBrace text="{" />
  <Whitespace text=" " />
  <StructField><Identifier text="x" /><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="Int" /></TypeExpression></StructField>
  <Whitespace text=" " />
  <RBrace text="}" />
</StructDeclaration>
```

## 7. Attachments, composition, and non-goals

Header derives attach after a complete name. Trailing derives attach only after
an actual matching braced or tuple close. See [derives attachment](derives-attachment.md),
[Rowan CST notation](../conventions/rowan-cst.md), and [recovery topology](../conventions/recovery-error-invalid-topology.md).
