# `if` 式

## 1. 権威と対象範囲

このページは、`syntax-v0`の`IfExpression`を定める。
2026年8月20日の`yu-syntax` architectureが、受理構文と直接 Rowan CSTを定める。
Authoritativeな2026年9月8日のrequired-operandとIf current-Item recoveryの記録が、condition、introducer、bodyのrecoveryを定める。
indented `Statement` transportとColon layout-sequenceの記録が、共有するbody boundaryを定める。

対象は、`if`、同列の`elsif` arm、任意の`else` arm、直接のarm CST、および必須slotのrecoveryである。
branch value、branchの型とeffect、operator association、brace arm body、HIR、diagnostic wording、formattingは定めない。

## 2. 受理構文

```text
IfExpression := IfArm { IfContinuation ElsifArm } [ IfContinuation ElseArm ]
IfArm := IfKw G* Condition Gcont ColonIntroducedArmBody
ElsifArm := ElsifKw G* Condition Gcont ColonIntroducedArmBody
ElseArm := ElseKw Gcont (ColonIntroducedArmBody | OperatorChain)
Condition := OperatorChain under current-depth StopSet { Colon, LeftBrace, Elsif, Else }
ColonIntroducedArmBody := ":" (InlineArmExpression | IndentedStatementBlock)
InlineArmExpression := OperatorChain
IfContinuation := horizontal trivia | newline with next indent >= if base indent
Gcont := chain-continuing trivia under the active If companion boundary
```

`elsif`は、正確に一つのcontextual wordである。
`else if`は`elsif` armではなく、nested `IfExpression`をbodyに持つ`ElseArm`である。
armのcolonは、colon後のnewlineが厳密に深く`IndentedStatementBlock`を選ぶ場合を除き、inline body chainを正確に一つ所有する。

## 3. 受理と境界

operand-starting primaryを受理するのは、最大の語として正確に一致する`if`だけであり、`ifx`はidentifierのままである。
通常のNUD word admissionではなく、active expressionのcompanion frameが`elsif`と`else`をarm boundaryとして認識する。
conditionは`:`、`{`、`elsif`、`else`の前で停止するため、armのcolonが`ColonApplicationTail`になることはない。

式はbase indentationを一度だけ取得する。
同じarmの候補になれるのは、horizontal continuation、またはそのbase以上のnewlineだけである。
より浅いcontinuationまたはkeywordでないcontinuationは、outer ownerに残る。
companion frameはすべての`elsif` armをまたいで存続し、式自身のelse bodyをparseする前に終了する。

## 4. 直接 Rowan CST

`IfExpression`は、`OperatorChain`の直接のprimary childである。
source orderで、`IfArm`を一つ、`ElsifKw`で始まる同列の`IfArm`を0個以上、`ElseArm`を最大一つ持つ。
各`IfArm`は、`OperatorChain`を持つdirect `Condition`を含む。
colonで導入する各arm bodyは、`Colon`とinlineの`OperatorChain`または`IndentedStatementBlock`を直接持つ。
arm bodyには、generic colon-applicationまたはinline-list wrapperはない。

```text
IfExpression := IfArm { ElsifArm } [ ElseArm ]
IfArm := (IfKw | ElsifKw) Condition Colon (OperatorChain | IndentedStatementBlock)
Condition := OperatorChain
ElseArm := ElseKw (Colon (OperatorChain | IndentedStatementBlock) | OperatorChain)
```

## 5. Recovery CST

conditionがなければ、`IfExpression(Condition)`にzero-widthの`Missing`を一つ置く。
EOFの`if`では、introducerまたはbodyのmissing nodeを連鎖させない。
conditionを保持した後に必須のcolonまたはbodyがなければ、arm bodyの不在を一つ記録する。
colonを受理した後にbodyがなければ、body missing nodeを一つ置く。
同じ深さ以下のcolon後newlineはouter ownerに残る。

malformed inline bodyは、maximalかつnon-emptyなraw `Error` group一つとなり、その後に同じbody slotを再試行する。
受理した`elsif`または`else`はkeywordを保持し、identifierへrollbackせず、対応するmissing bodyを置く。
最初の`ElseArm`の後に式は終了し、それ以降の`else`はouter recoveryに残る。
共有するrequired-operand kernelがcondition recoveryを提供し、indented bodyは`IfExpression(IndentedStatement)`をblockのentryとchild slotへtransportする。
`Missing` nodeはzero-width、raw `Error` groupはnon-emptyであり、nested recoveryはnested ownerに属する。

## 6. Source/CSTの例

`if x: 1 else: 0`では、colonはarmが所有し、colon-application nodeはない。

```xml
<IfExpression>
  <IfArm>
    <IfKw text="if" /><Whitespace text=" " />
    <Condition><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></Condition>
    <Colon text=":" /><Whitespace text=" " />
    <OperatorChain><IntegerLiteral text="1" /></OperatorChain>
  </IfArm>
  <Whitespace text=" " />
  <ElseArm>
    <ElseKw text="else" /><Colon text=":" /><Whitespace text=" " />
    <OperatorChain><IntegerLiteral text="0" /></OperatorChain>
  </ElseArm>
</IfExpression>
```

`if x: 1 elsif y: 2 else: 0`は、`ElseArm`の前に同列の`IfArm`を二つ持つ。

```text
if x:
  1
  2
else: 0
```

最初のarmは、直接の`Statement` childを二つ持つ`IndentedStatementBlock`を一つ持つ。
dedentした`else`は、enclosing `IfExpression`へ戻る。

## 7. 構成

[動的演算子列](operator-chain.md)は、primaryのvalue positionとbody chainを定める。
[colon application](colon-application.md)はbody chain内で使えるが、armのcolonを所有しない。
[layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md)と共有indented blockが、current-depthのbody boundaryを定める。
