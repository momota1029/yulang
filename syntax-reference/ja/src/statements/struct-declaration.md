# `struct` 宣言

## 1. 権限と対象範囲

このページは、`syntax-v0`の`StructDeclaration`を定める。
AuthoritativeなStruct declaration grammarの`SD-G`、`SD-J`、`SD-T`、`SD-R`と、named-field、field-sequence、foreign-close、derives、companion、actual-closeの後続amendmentが統治する。
field meaning、constructor、method、loweringは対象外である。

## 2. 受理する構文

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

`RequiredTypeExpression`は[TypeExpressionの参照](../types/type-expression-core.md)にあるfull required type productionである。
`Gstruct+`はnon-empty declaration-continuing trivia、`Gstruct*`はemptyまたはそのrunである。
`Gfield-type`はempty、same-line、またはstrictly deeper continuation triviaを許す。

## 3. 受理と境界

exact bareまたはvisibility-ledの`struct`がこの宣言を選ぶ。
bodyは`;`、`{`、`(`、lone `:`だけで始まる。
bracedとtuple listはemptyにできるが、indented listはnon-emptyである。
bracedとtupleのqualifying newlineは`struct_list_base`以下、indented listでは`block_indent`と等しいindentを持つ。
deeper lineはfield typeのcontinuationであり、`::`はfield colonではない。

## 4. Source-order Rowan schema

```text
StructDeclaration := [ VisibilityKw Trivia ] StructKw Trivia StructName
  { Trivia DerivesClause }
  ( Semicolon
  | DeclarationCompanion
  | NamedIndentedStructBody
  | NamedBracedStructBodyActualClose { Trivia DerivesClause } [ DeclarationCompanion ]
  | TupleStructBodyActualClose { Trivia DerivesClause } [ DeclarationCompanion ] )
NamedBracedStructBodyActualClose := RBraceがactual matching closeであるNamedBracedStructBody
TupleStructBodyActualClose := RParenがactual matching closeであるTupleStructBody
NamedBracedStructBody := LBrace Trivia { StructField | Comma | Trivia | StructFieldForeignClose } RBrace
TupleStructBody := LParen Trivia { StructField | Comma | Trivia | StructFieldForeignClose } RParen
NamedIndentedStructBody := Colon Trivia { StructField | Comma | Trivia }
StructField := NamedStructFieldContent | TupleStructFieldContent
NamedStructFieldContent := Identifier Trivia Colon Trivia TypeExpression
TupleStructFieldContent := TypeExpression
StructFieldForeignClose := Error+
```

header positionは、header derivesの後にbodyまたはheader companionを受け入れる。
trailing positionが開くのはactual matching bracedまたはtuple closeの後だけであり、そこでderivesがoptionalなcompanionに先行する。
semicolon、indented body、missingまたはmismatched closeの後には開かない。
bracedとtupleはactualまたはrecovered closeを一つ持ち、indented bodyはcloseを持たない。
`StructFieldForeignClose`はdelimited listのdirect childであり、`StructField`のchildではない。
named bracedとindented bodyでは、`StructField`が`NamedStructFieldContent`を含む。
tuple bodyでは、`StructField`が`TupleStructFieldContent`を含む。

## 5. Recovery CST

header nameとbody introducerのrecoveryは、same-cause cascadeを作らず固有のslotを使う。
malformed header runはheader slotの`Error+`であり、named body starterでretryできる。
complete nameの後がEOF、owner boundary、またはequal-or-shallower newlineなら、`Missing(Struct::BodyIntroducer)`は一つだけである。

named fieldでは、leadingまたはrepeated separatorがrequired field slotごとにmissing field一つを作る。
literal colonの前のmissing field nameは`Missing(Struct::FieldName)`であり、malformed field-name textはそのslotの`Error+`である。
fieldの後にsame-lineのcomplete next field headが続けば、そのnext fieldの前に`Missing(Struct::FieldSeparator)`を一つだけ置く。
accepted nameの後にsame-line type starterが来れば`Missing(Struct::FieldColon)`を置く。
accepted colonの後のboundaryは`Missing(Struct::FieldType)`を置く。
separator errorはfield-separator slotの`Error+`であり、valid separatorではない。

tuple fieldはそれぞれrequired `TypeExpression`一つを使う。
leadingまたはrepeated commaはmissing tuple field type一つを作り、malformed type contentはTypeExpression ownerに残る。
same-line type primaryは一つのTypeExpressionであり、separatorを推測しない。

local closeではlistが自身のclose slotをretryする。
missing matching closeはclose-slot `Missing`一つであり、protected outer closeはunreadのまま残る。
malformed runがboundaryへ達したslotに別のMissingを加えない。
field、field-name、field-colon、field-type、separator、closeのslotは、このcardinalityを保つ。

matching closeが優先する。
absent closeはclose slotの`Missing`一つである。
protected outer closeはunreadのまま残る。
locally consumed foreign closeは`Error+`を持つ`StructFieldForeignClose`一つであり、field-separator `Error`とは異なる。

```xml
<StructDeclaration><StructKw text="struct" /><Whitespace text=" " /><Identifier text="S" /><Whitespace text=" " /><LBrace text="{" /><Whitespace text=" " /><StructField><Identifier text="x" /><Missing /><Whitespace text=" " /><TypeExpression><Identifier text="Int" /></TypeExpression></StructField><Whitespace text=" " /><RBrace text="}" /></StructDeclaration>
```

この`Missing`はfield-colon slotであり、typeはstructural child一つのままである。

`struct S { @ }`ではlistがraw field failureを持つ。
locally consumed foreign closeはschemaで示した別のwrapperを使う。

```xml
<StructDeclaration><StructKw text="struct" /><Whitespace text=" " /><Identifier text="S" /><Whitespace text=" " /><LBrace text="{" /><Whitespace text=" " /><Error text="@" /><Whitespace text=" " /><RBrace text="}" /></StructDeclaration>
```

`struct S { x: T ] }`では、locally consumed foreign closeを一度だけwrapperで包む。

```xml
<StructDeclaration><StructKw text="struct" /><Whitespace text=" " /><Identifier text="S" /><Whitespace text=" " /><LBrace text="{" /><Whitespace text=" " /><StructField><Identifier text="x" /><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="T" /></TypeExpression></StructField><Whitespace text=" " /><StructFieldForeignClose><Error text="]" /></StructFieldForeignClose><Whitespace text=" " /><RBrace text="}" /></StructDeclaration>
```

## 6. SourceとCSTの例

受理する`struct S { x: Int }`はnamed field一つを持つ。

```xml
<StructDeclaration><StructKw text="struct" /><Whitespace text=" " /><Identifier text="S" /><Whitespace text=" " /><LBrace text="{" /><Whitespace text=" " /><StructField><Identifier text="x" /><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="Int" /></TypeExpression></StructField><Whitespace text=" " /><RBrace text="}" /></StructDeclaration>
```

## 7. 構成と非対象

header derivesはcomplete nameの後にattachする。
trailing derivesはactual matching bracedまたはtuple closeの後だけにattachする。
[derives attachment](derives-attachment.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。
