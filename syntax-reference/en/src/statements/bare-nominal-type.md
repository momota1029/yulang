# Bare nominal `type` declaration

## 1. Authority and scope

This page specifies the bare nominal `TypeDeclaration` form in `syntax-v0`.
`TND-G`, `TND-J`, `TND-T`, and `TND-R`, with the shared `TD` header authority,
govern it. Nominal identity, constructors, visibility meaning, lowering,
resolution, and formatting are outside this page.

## 2. Accepted syntax

```text
NominalTypeDeclaration := TypeDeclarationHeader [ HeaderDerivesAttachment(Type) ] NominalTypeDeclarationEnd
TypeDeclarationHeader := [ VisibilityKw Gtype+ ] TypeKw Gtype+ TypeName [ DeclarationTypeParameterList ]
VisibilityKw := MyKw | OurKw | PubKw
TypeKw := exact maximal word "type"
TypeName := Identifier
DeclarationTypeParameterList := Gtype-param DeclarationTypeParameter { Gtype-param DeclarationTypeParameter }
DeclarationTypeParameter := Identifier | SigilIdentifier
NominalTypeDeclarationEnd := Gtype-terminal NominalStatementBoundary | MaximalStrictlyDeeperTrailingTriviaBeforeEOF EOF
```

`Gtype+` is non-empty type-continuation trivia; `Gtype-terminal` is empty or
same-line trivia; `Gtype-param` is non-empty same-line trivia. Parameters are
greedy and same-line only.

## 3. Form selection, layout, and boundaries

After a complete header, exact `impl` selects the attached-implementation form
and exact lone `=` selects equality before nominal termination. A qualifying
`with` has its own authorized position before equality selection. Nominal form
ends at EOF, an outer semicolon, an equal-or-shallower newline, an admitted
statement-sequence newline, an active outer comma or right delimiter, or an
ambient boundary. Those boundaries remain unconsumed.

## 4. Source-order Rowan schema

```text
TypeDeclaration := [ VisibilityKw Trivia ] TypeKw Trivia Identifier
                   [ DeclarationTypeParameterList ] { Trivia DerivesClause } [ Trivia ]
DeclarationTypeParameterList := Trivia ( Identifier | SigilIdentifier )
                                { Trivia ( Identifier | SigilIdentifier ) }
```

The nominal form has exactly one `TypeDeclaration` node and no nominal,
header, empty-RHS, or empty-body wrapper. A parameter-list node exists only
when it has one or more parameters. A terminal semicolon belongs to the outer
statement owner.

## 5. Recovery CST

An absent name is `Missing(TypeDeclaration::Name)`; a malformed name is
`Error+` in the name slot and may retry at a raw name. Neither adds a nominal,
definition-introducer, or RHS recovery for the same cause. A complete header
followed by a reusable non-parameter type primary without `=` gets
`Missing(TypeDeclaration::DefinitionIntroducer)` and retries equality. A
terminal boundary instead selects nominal form.

```xml
<TypeDeclaration>
  <TypeKw text="type" /><Whitespace text=" " /><Missing />
</TypeDeclaration>
```

A malformed name is a raw `Error+` in the same name slot.

```xml
<TypeDeclaration><TypeKw text="type" /><Whitespace text=" " /><Error text="@" /></TypeDeclaration>
```

## 6. Source and CST examples

The accepted source `type Point` is represented once, in source order.

```xml
<TypeDeclaration><TypeKw text="type" /><Whitespace text=" " /><Identifier text="Point" /></TypeDeclaration>
```

## 7. Composition and non-goals

Header derives attach after the complete header. A type-attached `impl` is a
third TypeDeclaration form, not a nominal continuation. See [derives attachment](derives-attachment.md)
and [equality `type` declaration form](equality-type.md).
