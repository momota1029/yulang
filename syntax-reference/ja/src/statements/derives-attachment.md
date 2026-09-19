# Shared `derives` clause attachment

## 1. 権限と対象範囲

このページは、`syntax-v0`の`DerivesClause`とattachment positionを定める。
Authoritativeな`DRV-G`、`DRV-J`、`DRV-T`、`DRV-R`がclause、StructとTypeのhost、layout、CST、recoveryを統治する。
role resolution、supported target、generated implementation、`via` validationは対象外である。

## 2. 受理する構文

```text
HeaderDerivesAttachment(Owner) := DerivesAttachmentTrivia(owner_base) DerivesClause { DerivesAttachmentTrivia(owner_base) DerivesClause }
TrailingDerivesAttachment(Owner) := DerivesAttachmentTrivia(owner_base) DerivesClause { DerivesAttachmentTrivia(owner_base) DerivesClause }
DerivesClause := DerivesKw DerivesRoleTrivia(owner_base) RequiredTypeExpression(Derives::RoleReference) { DerivesRoleGap(owner_base) Comma DerivesRoleTrivia(owner_base) RequiredTypeExpression(Derives::RoleReference) } [ DerivesRoleGap(owner_base) ViaKw DerivesViaTrivia(owner_base) RequiredRawIdentifier(Derives::ViaTarget) ]
DerivesKw := exact contextual word "derives"
ViaKw := exact contextual word "via" inside an accepted DerivesClause
DerivesAttachmentTrivia(base) := empty | non-empty same-line trivia | non-empty strictly-deeper continuation trivia(base)
DerivesRoleTrivia(base) := TypeChainTrivia(base)
DerivesRoleGap(base) := TypeChainTrivia(base)
DerivesViaTrivia(base) := TypeChainTrivia(base)
```

`RequiredTypeExpression`は[TypeExpressionの参照](../types/type-expression-core.md)にあるfull required type productionである。
roleを区切るのはcommaだけであり、`derives Eq Debug`はTypeExpression一つである。

## 3. Host、受理、境界

Structはcomplete nameの後のheaderとactual matching bracedまたはtuple closeの後のtrailingでrunを受け入れる。
Typeはcomplete headerの後とequality RHSの後で受け入れる。
各opened positionではrepeated clauseを受け入れる。
caller-owned gap、separator、close、ambient boundary、non-qualifying newline、incomplete Struct close、indented Struct dedentはattachmentを始めない。

## 4. Source-order Rowan schema

```text
DerivesClause := DerivesKw Trivia TypeExpression { Trivia Comma Trivia TypeExpression } [ Trivia ViaKw Trivia Identifier ]
StructDeclarationWithDerives := StructSharedHeader [ HeaderDerivesAttachment(Struct) ]
  ( Semicolon
  | DeclarationCompanion
  | NamedIndentedStructBody
  | NamedBracedStructBodyActualClose [ TrailingDerivesAttachment(Struct) ] [ DeclarationCompanion ]
  | TupleStructBodyActualClose [ TrailingDerivesAttachment(Struct) ] [ DeclarationCompanion ] )
NamedBracedStructBodyActualClose := RBraceがactual matching closeであるNamedBracedStructBody
TupleStructBodyActualClose := RParenがactual matching closeであるTupleStructBody
TypeDeclarationWithDerives := TypeDeclarationHeader [ HeaderDerivesAttachment(Type) ]
  ( TypeAttachedImplForm
  | NominalTypeDeclarationEnd
  | EqualityTypeDeclaration [ TrailingDerivesAttachment(Type) ] [ DeclarationCompanion ]
  | DeclarationCompanion )
```

accepted clauseは`DerivesClause` child一つである。
roleは一つ以上であり、optionalな`via` tailはtarget identifier一つを持つ。
attachment positionはwrapperやsynthetic separatorを加えない。

## 5. Recovery CST

first roleとcomma後のroleはmandatoryである。
missing roleはTypeExpression slotの`Missing(Derives::RoleReference)`である。
malformed role contentはTypeExpression ownerに残る。
`ViaKw`の後のmissing targetは`Missing(Derives::ViaTarget)`であり、malformed targetはtarget slotの`Error+`である。

```xml
<DerivesClause><DerivesKw text="derives" /><Whitespace text=" " /><TypeExpression><Identifier text="Eq" /></TypeExpression><Comma text="," /><Whitespace text=" " /><TypeExpression><Missing /></TypeExpression></DerivesClause>
```

malformed targetはsecond `Missing`ではなくtarget slotのraw sourceである。

```xml
<DerivesClause><DerivesKw text="derives" /><Whitespace text=" " /><TypeExpression><Identifier text="Eq" /></TypeExpression><Whitespace text=" " /><ViaKw text="via" /><Whitespace text=" " /><Error text="@" /></DerivesClause>
```

## 6. SourceとCSTの例

受理する`derives Eq, Debug via key`はrole二つとtarget一つを持つ。

```xml
<DerivesClause><DerivesKw text="derives" /><Whitespace text=" " /><TypeExpression><Identifier text="Eq" /></TypeExpression><Comma text="," /><Whitespace text=" " /><TypeExpression><Identifier text="Debug" /></TypeExpression><Whitespace text=" " /><ViaKw text="via" /><Whitespace text=" " /><Identifier text="key" /></DerivesClause>
```

## 7. 構成と非対象

role referenceはordinary full TypeExpression surfaceを保つ。
[struct declaration](struct-declaration.md)、[bare nominal `type` declaration form](bare-nominal-type.md)、[equality `type` declaration form](equality-type.md)を参照する。
