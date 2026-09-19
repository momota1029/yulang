# Bare nominal `type` declaration

## 1. 権限と対象範囲

このページは、`syntax-v0`のbare nominal `TypeDeclaration` formを定める。
shared `TD` header authorityとAuthoritativeな`TND-G`、`TND-J`、`TND-T`、`TND-R`が統治する。
nominal identity、constructor、visibility meaning、lowering、resolution、formattingは対象外である。

## 2. 受理する構文

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

`Gtype+`はnon-empty type-continuation trivia、`Gtype-terminal`はemptyまたはsame-line trivia、`Gtype-param`はnon-empty same-line triviaである。
parameterはgreedyかつsame-line onlyである。

## 3. Form selection、layout、境界

complete headerの後ではexact `impl`がattached-implementation formを、exact lone `=`がequalityをnominal terminationより先に選ぶ。
qualifying `with`にはequality selectionより前の固有のpositionがある。
nominal formはEOF、outer semicolon、equal-or-shallower newline、admitted statement-sequence newline、active outer commaまたはright delimiter、ambient boundaryで終わる。
これらのboundaryはconsumeしない。

## 4. Source-order Rowan schema

```text
TypeDeclaration := [ VisibilityKw Trivia ] TypeKw Trivia Identifier [ DeclarationTypeParameterList ] { Trivia DerivesClause } [ Trivia ]
DeclarationTypeParameterList := Trivia ( Identifier | SigilIdentifier ) { Trivia ( Identifier | SigilIdentifier ) }
```

nominal formには`TypeDeclaration` node一つだけがある。
nominal、header、empty RHS、empty bodyのwrapperは作らない。
parameter listはparameter一つ以上のときだけ作る。
terminal semicolonはouter statement ownerが持つ。

## 5. Recovery CST

absent nameは`Missing(TypeDeclaration::Name)`であり、malformed nameはname slotの`Error+`である。
同じcauseからnominal、definition-introducer、RHS recoveryを作らない。
complete headerの後で`=`なしにreusable non-parameter type primaryが続くと、`Missing(TypeDeclaration::DefinitionIntroducer)`を置いてequalityをretryする。
terminal boundaryではnominal formを選ぶ。

```xml
<TypeDeclaration><TypeKw text="type" /><Whitespace text=" " /><Missing /></TypeDeclaration>
```

malformed nameは同じname slotのraw `Error+`である。

```xml
<TypeDeclaration><TypeKw text="type" /><Whitespace text=" " /><Error text="@" /></TypeDeclaration>
```

## 6. SourceとCSTの例

受理する`type Point`はsource orderで一度だけ表す。

```xml
<TypeDeclaration><TypeKw text="type" /><Whitespace text=" " /><Identifier text="Point" /></TypeDeclaration>
```

## 7. 構成と非対象

header derivesはcomplete headerの後にattachする。
type-attached `impl`はthird `TypeDeclaration` formであり、nominal continuationではない。
[derives attachment](derives-attachment.md)と[equality `type` declaration form](equality-type.md)を参照する。
