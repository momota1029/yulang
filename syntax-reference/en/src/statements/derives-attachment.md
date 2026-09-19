# Shared `derives` clause attachment

## 1. Authority and scope

This page specifies `DerivesClause` and its `syntax-v0` attachment positions.
The Authoritative `DRV-G`, `DRV-J`, `DRV-T`, and `DRV-R` govern the clause,
its Struct and Type hosts, layout, CST, and recovery. It does not specify role
resolution, supported targets, generated implementations, or `via` validation.

## 2. Accepted syntax

```text
HeaderDerivesAttachment(Owner) := DerivesAttachmentTrivia(owner_base) DerivesClause { DerivesAttachmentTrivia(owner_base) DerivesClause }
TrailingDerivesAttachment(Owner) := DerivesAttachmentTrivia(owner_base) DerivesClause { DerivesAttachmentTrivia(owner_base) DerivesClause }
DerivesClause := DerivesKw DerivesRoleTrivia(owner_base) RequiredTypeExpression(Derives::RoleReference)
                 { DerivesRoleGap(owner_base) Comma DerivesRoleTrivia(owner_base) RequiredTypeExpression(Derives::RoleReference) }
                 [ DerivesRoleGap(owner_base) ViaKw DerivesViaTrivia(owner_base) RequiredRawIdentifier(Derives::ViaTarget) ]
DerivesKw := exact contextual word "derives"
ViaKw := exact contextual word "via" inside an accepted DerivesClause
DerivesAttachmentTrivia(base) := empty | non-empty same-line trivia | non-empty strictly-deeper continuation trivia(base)
DerivesRoleTrivia(base) := TypeChainTrivia(base)
DerivesRoleGap(base) := TypeChainTrivia(base)
DerivesViaTrivia(base) := TypeChainTrivia(base)
```

`RequiredTypeExpression` is the full required type production in the
[TypeExpression reference](../types/type-expression-core.md). The comma is the
only role separator: `derives Eq Debug` is one TypeExpression.

## 3. Hosts, admission, and boundaries

Struct admits a header run after a complete name and a trailing run after an
actual matching braced or tuple close. Type admits a header run after its
complete header and a trailing run after its equality RHS. Repeated clauses
are accepted at each opened position. Caller-owned gaps, separators, closes,
ambient boundaries, non-qualifying newlines, incomplete Struct closes, and
indented Struct dedents do not start an attachment.

## 4. Source-order Rowan schema

```text
DerivesClause := DerivesKw Trivia TypeExpression
                 { Trivia Comma Trivia TypeExpression }
                 [ Trivia ViaKw Trivia Identifier ]
StructDeclarationWithDerives := StructSharedHeader [ HeaderDerivesAttachment(Struct) ]
  ( Semicolon
  | DeclarationCompanion
  | NamedIndentedStructBody
  | NamedBracedStructBodyActualClose [ TrailingDerivesAttachment(Struct) ] [ DeclarationCompanion ]
  | TupleStructBodyActualClose [ TrailingDerivesAttachment(Struct) ] [ DeclarationCompanion ] )
NamedBracedStructBodyActualClose := NamedBracedStructBody whose RBrace is an actual matching close
TupleStructBodyActualClose := TupleStructBody whose RParen is an actual matching close
TypeDeclarationWithDerives := TypeDeclarationHeader [ HeaderDerivesAttachment(Type) ]
  ( TypeAttachedImplForm
  | NominalTypeDeclarationEnd
  | EqualityTypeDeclaration [ TrailingDerivesAttachment(Type) ] [ DeclarationCompanion ]
  | DeclarationCompanion )
```

Each accepted clause is exactly one `DerivesClause` child. Its role count is
one or more; its optional `via` tail contains exactly one target identifier.
Attachment position adds no wrapper or synthetic separator.

## 5. Recovery CST

The first role and every comma-following role are mandatory. A missing role is
`Missing(Derives::RoleReference)` in its TypeExpression slot. Malformed role
content remains TypeExpression-owned. After `ViaKw`, a missing target is
`Missing(Derives::ViaTarget)`; a malformed target is `Error+` in that target
slot and may retry at an identifier without a second missing node.

```xml
<DerivesClause>
  <DerivesKw text="derives" />
  <Whitespace text=" " />
  <TypeExpression><Identifier text="Eq" /></TypeExpression>
  <Comma text="," />
  <Whitespace text=" " />
  <TypeExpression><Missing /></TypeExpression>
</DerivesClause>
```

A malformed target is raw source in the target slot, not a second `Missing`.

```xml
<DerivesClause><DerivesKw text="derives" /><Whitespace text=" " /><TypeExpression><Identifier text="Eq" /></TypeExpression><Whitespace text=" " /><ViaKw text="via" /><Whitespace text=" " /><Error text="@" /></DerivesClause>
```

## 6. Source and CST examples

The accepted source `derives Eq, Debug via key` has two roles and one target.

```xml
<DerivesClause>
  <DerivesKw text="derives" /><Whitespace text=" " />
  <TypeExpression><Identifier text="Eq" /></TypeExpression><Comma text="," /><Whitespace text=" " />
  <TypeExpression><Identifier text="Debug" /></TypeExpression><Whitespace text=" " />
  <ViaKw text="via" /><Whitespace text=" " /><Identifier text="key" />
</DerivesClause>
```

## 7. Composition and non-goals

Role references retain the ordinary full TypeExpression surface. See [struct declaration](struct-declaration.md),
[bare nominal `type` declaration form](bare-nominal-type.md), and [equality `type` declaration form](equality-type.md).
