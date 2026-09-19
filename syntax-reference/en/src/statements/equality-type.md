# Equality `type` declaration

## 1. Authority and scope

This page specifies the equality `TypeDeclaration` form in `syntax-v0`.
`TD-G`, `TD-J`, `TD-T`, and `TD-R`, together with `TND` form selection, govern
it. Alias meaning, lowering, resolution, and formatting are outside this page.

## 2. Accepted syntax

```text
EqualityTypeDeclaration := TypeDeclarationHeader [ HeaderDerivesAttachment(Type) ] Gtype* Equals Gtype-rhs RequiredTypeExpression(TypeDeclaration::Rhs) [ TrailingDerivesAttachment(Type) ] [ DeclarationCompanion ]
TypeDeclarationHeader := [ VisibilityKw Gtype+ ] TypeKw Gtype+ TypeName [ DeclarationTypeParameterList ]
VisibilityKw := MyKw | OurKw | PubKw
TypeKw := exact maximal word "type"
TypeName := Identifier
DeclarationTypeParameterList := Gtype-param DeclarationTypeParameter { Gtype-param DeclarationTypeParameter }
DeclarationTypeParameter := Identifier | SigilIdentifier
Gtype+ := non-empty TypeContinuationTrivia(type_base)
Gtype* := empty or one TypeContinuationTrivia(type_base)
Gtype-rhs := empty or one TypeContinuationTrivia(type_base)
Gtype-param := non-empty same-line trivia
```

`RequiredTypeExpression` names the full required type production in the
[TypeExpression reference](../types/type-expression-core.md). Continuation
trivia is same-line or strictly deeper than `type_base`.

## 3. Admission, layout, and boundaries

An exact type header followed by exact lone `=` selects equality. `==`, `=>`,
and operator runs are not split. The RHS is one full TypeExpression. Its outer
episode recognizes declaration `Semicolon` and `With` stops; nested type
episodes suspend them. Outer separators, closes, equal-or-shallower newlines,
and ambient boundaries remain outside the RHS.

## 4. Source-order Rowan schema

```text
TypeDeclaration := [ VisibilityKw Trivia ] TypeKw Trivia Identifier
                   [ DeclarationTypeParameterList ] { Trivia DerivesClause }
                   Trivia Equals Trivia TypeExpression { Trivia DerivesClause }
                   [ DeclarationCompanion ]
DeclarationTypeParameterList := Trivia ( Identifier | SigilIdentifier )
                                { Trivia ( Identifier | SigilIdentifier ) }
```

Equality has one `TypeDeclaration`, one `Equals`, and one RHS TypeExpression.
It has no equality-only wrapper, empty parameter list, or synthetic separator.

## 5. Recovery CST

Missing or malformed name recovery occupies only the name slot. Before a
reusable RHS type primary, a missing `=` is
`Missing(TypeDeclaration::DefinitionIntroducer)` and retries the RHS at the
same position. After an accepted or recovered introducer, an absent RHS is
`Missing(TypeDeclaration::Rhs)`. After accepted or retried RHS content begins,
malformed nested content remains Type-owned.

```xml
<TypeDeclaration>
  <TypeKw text="type" /><Whitespace text=" " /><Identifier text="Result" />
  <Whitespace text=" " /><Equals text="=" /><Whitespace text=" " /><TypeExpression><Missing /></TypeExpression>
</TypeDeclaration>
```

An initial malformed RHS run is `Error+` directly in the `TypeDeclaration`
RHS slot. A `TypeExpression` occurs only for accepted or retried RHS content.

```xml
<TypeDeclaration><TypeKw text="type" /><Whitespace text=" " /><Identifier text="Id" /><Whitespace text=" " /><Equals text="=" /><Whitespace text=" " /><Error text="@" /></TypeDeclaration>
```

## 6. Source and CST examples

The accepted source `type Id = Int` has one RHS child.

```xml
<TypeDeclaration><TypeKw text="type" /><Whitespace text=" " /><Identifier text="Id" /><Whitespace text=" " /><Equals text="=" /><Whitespace text=" " /><TypeExpression><Identifier text="Int" /></TypeExpression></TypeDeclaration>
```

## 7. Attachments, composition, and non-goals

Header derives attach after the complete header; trailing derives and a
companion may attach after the equality RHS. See [derives attachment](derives-attachment.md)
and [bare nominal `type` declaration form](bare-nominal-type.md).
