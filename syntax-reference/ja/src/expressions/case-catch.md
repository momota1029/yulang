# `case` と `catch` 式

## 1. 権威と対象範囲

このページは、`syntax-v0`の`CaseExpression`と`CatchExpression`を定める。
2026年8月20日の`yu-syntax` architectureが、受理構文と直接 Rowan CSTを定める。
Authoritativeな2026年9月8日のCaseLike structuralとArrow/Body recoveryの記録、および2026年9月9日のseparatorとCatch-closeの記録が、recovery CSTを定める。

対象は、expression primary、label、scrutinee、arm family、pattern、任意のguardとCatch handler、exact arrow、body、separator、Catch braceである。
lambda form、exhaustiveness、guard、handler、label、exception、valueの意味、HIR、型、diagnostic wording、formattingは定めない。

## 2. 受理構文

```text
CaseExpression  := CaseKw  CaseHead CaseBlock
CatchExpression := CatchKw CatchHead CatchBlock
CaseHead := G* [ CaseLabel G* ] CaseScrutinee
CatchHead := G* [ CatchLabel G* ] CatchScrutinee
CaseLabel := SigilIdentifier
CatchLabel := SigilIdentifier
SigilIdentifier := Apostrophe!Identifier
CaseScrutinee := OperatorChain
CatchScrutinee := OperatorChain
CaseBlock := ":" (CaseInlineArms | CaseIndentedArms)
CatchBlock := ":" (CatchInlineArm | CatchIndentedArms) | "{" CatchBracedArms "}"
CaseInlineArms := CaseArm { CaseArmSeparator CaseArm } [ CaseArmSeparator ]
CatchBracedArms := CatchArm { CatchArmSeparator CatchArm } [ CatchArmSeparator ]
CaseArmSeparator := ","
CatchArmSeparator := ","
CaseArm  := Pattern [ CaseGuard ] "->" ArmBody [ ";" ]
CatchArm := Pattern [ "," Pattern ] [ CatchGuard ] "->" ArmBody [ ";" ]
CaseGuard := (IfKw | WhereKw) OperatorChain
CatchGuard := (IfKw | WhereKw) OperatorChain
ArmBody := OperatorChain | IndentedStatementBlock
```

`case`と`catch`は、別々のoperand-starting primaryである。
Case inline armはcommaで区切る。
colon-inline Catchはarmを正確に一つ持つ。
indented CaseとCatchのarm、およびbraceで囲むCatch armは複数のarmを持てる。
Caseはbrace arm blockを受理しない。

## 3. 受理と境界

対応するprimaryを受理するのは、最大の語として正確に一致するcontextual word `case`と`catch`だけであり、`casefold`と`catcher`はidentifierのままである。
caseのscrutineeは`:`で停止する。
catchのscrutineeは`:`または`{`で停止するため、direct braced blockを所有できるのはCatchだけである。

label内のapostropheとidentifierはadjacentであり、whitespaceで`SigilIdentifier`を分けられない。
`->`は動的にassociationするoperatorではなく、exactなfixed punctuationである。
Catch handlerのcommaは直接の`CatchArm` childであり、arm-list commaは選んだarm familyに属する。
current-depthのCatch-brace newlineとindented arm-indent newlineはそのfamilyに属し、indented body blockがstatement newlineを所有する。
active arm ownerは、nested colon、comma、arrow、brace、guard word、closeの表記を、それぞれのimmediate ownerへ戻す。

## 4. 直接 Rowan CST

`CaseExpression`と`CatchExpression`は、`OperatorChain`の直接のprimary childである。
`CaseExpression`は、keyword、任意の`CaseLabel`、direct `CaseScrutinee`、direct case blockをsource orderで持つ。
`CatchExpression`は、keyword、任意の`CatchLabel`、direct `CatchScrutinee`、direct catch blockをsource orderで持つ。
各labelは、adjacentなapostropheとidentifierを持つ`SigilIdentifier` token一つを含む。
各scrutineeは、その`OperatorChain`を直接含む。
`CaseArm`は、direct `Pattern`、任意の`CaseGuard`、exactな`Arrow`、body、任意のsemicolonを持つ。
`CatchArm`は、direct `Pattern`、任意のhandler `Pattern`、任意の`CatchGuard`、exactな`Arrow`、body、任意のsemicolonを持つ。
generic case-like wrapperはない。

`CatchBlock`は、braceがある場合にそのbraceを直接持ち、そのbraceは`BracedStatementBlockExpression`を作らない。
Case inline armのcommaは、direct `CaseArmSeparator` wrapperに入る。
Catch-braced armのcommaは、direct `CatchArmSeparator` wrapperに入る。
arm bodyは、直接の`OperatorChain`一つまたは直接の`IndentedStatementBlock`一つを持つ。

```text
CaseExpression := CaseKw [ CaseLabel ] CaseScrutinee CaseBlock
CatchExpression := CatchKw [ CatchLabel ] CatchScrutinee CatchBlock
CaseInlineArms := CaseArm { CaseArmSeparator CaseArm } [ CaseArmSeparator ]
CatchBracedArms := CatchArm { CatchArmSeparator CatchArm } [ CatchArmSeparator ]
CaseArm := Pattern [ CaseGuard ] Arrow ArmBody [ Semicolon ]
CatchArm := Pattern [ Comma Pattern ] [ CatchGuard ] Arrow ArmBody [ Semicolon ]
```

## 5. Recovery CST

block introducerがなければ、colon expectationを持つzero-widthの`Missing`を`CaseLike(Block)`に一つ置く。
Catchが`{`を受理した後にlocal closeがなければ、代わりにbrace-close expectationを持つ`CaseLike(Block)`を使う。
colon後で同じ深さ以下のarm不在は`CaseLike(Arm)`を使い、完全な次のitemをouter ownerに残す。
最初のarmとCatch handlerのpattern recoveryは、Pattern ownerを通じて`CaseLike(Pattern)`と`CaseLike(Handler)`をそれぞれ一度だけ使う。

arrowがない位置でbody NUDを受理すると、bodyをparseする前に`CaseLike(Arrow)`のmissing nodeを一つ置く。
arrowとbodyが同じboundaryでどちらもなければ、その一つのArrow nodeが、順序付けたArrow-punctuationとBody-expression expectationを持つ。
この場合、二つ目の`Missing` nodeは作らない。
arrowを受理した後にbodyがなければ、`CaseLike(Body)`を使う。
malformed bodyは、`CaseLike(Body)`にあるmaximalかつnon-emptyなraw `Error` group一つとなり、同じslotを再試行できる。

arm commaなしで次のpatternを受理する前に、zero-widthの`CaseLike(Separator)` missing nodeを一つ置き、同じitemを正確に一度再試行する。
separator wrapperもseparator error scanも作らない。
Catchのarm sequenceが終了するたびに、`CatchBlock`は対応する`}`またはlocal close missing nodeを一つ置き、それ以外のprotected itemを未消費のまま残す。
nested pattern、guard、bodyのrecoveryをarm familyが重複して記録することはない。

## 6. Source/CSTの例

`case 'go x: 1 if ok -> yes, _ -> no`は、label、scrutinee、直接のarm二つ、arm separatorをsource orderで置く。

```xml
<CaseExpression>
  <CaseKw text="case" /><Whitespace text=" " />
  <CaseLabel><SigilIdentifier text="'go" /></CaseLabel><Whitespace text=" " />
  <CaseScrutinee><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></CaseScrutinee>
  <CaseBlock>
    <Colon text=":" /><Whitespace text=" " />
    <CaseArm><Pattern><IntegerPattern><IntegerLiteral text="1" /></IntegerPattern></Pattern><Whitespace text=" " /><CaseGuard><IfKw text="if" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="ok" /></IdentifierExpression></OperatorChain></CaseGuard><Whitespace text=" " /><Arrow text="->" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="yes" /></IdentifierExpression></OperatorChain></CaseArm>
    <CaseArmSeparator><Comma text="," /></CaseArmSeparator><Whitespace text=" " />
    <CaseArm><Pattern><WildcardPattern><Underscore text="_" /></WildcardPattern></Pattern><Whitespace text=" " /><Arrow text="->" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="no" /></IdentifierExpression></OperatorChain></CaseArm>
  </CaseBlock>
</CaseExpression>
```

`catch action { err, handler -> recover; }`では、handler comma、second pattern、arrow、body、semicolonが、直接のbraced `CatchBlock`内にある一つの`CatchArm`に属する。

braceで囲むCatch blockが複数のarmを持つ場合、各arm-list commaは`CatchArmSeparator`である。
これは`CatchArm`内のhandler commaとは異なる。

`catch action: err, handler -> recover`は、任意のsecond handler patternを持つ、正確に一つのcolon-inline Catch armである。

## 7. 構成

[動的演算子列](operator-chain.md)が、primary placement、scrutinee、guard、inline bodyを定める。
[pattern reference](../patterns/pattern-core.md)がarmのPattern grammarを定め、nested pattern recoveryを所有する。
[layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md)と共有indented blockが、current-depthのarmとbody boundaryを定める。
