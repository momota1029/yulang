# 動的演算子列

## 1. 権威と対象範囲

このページは、`syntax-v0`の`OperatorChain`を定める。
受理構文とflatな直接Rowan CSTは、2026年8月20日の`yu-syntax` architectureにあるprecedence-neutral dynamic operator chain追補に従う。
required operandのrecoveryは2026年9月8日のoperand current-Item recoveryが定める。
共通の構文モデルとrecovery表記は、[構文の内容モデル](../conventions/syntax-content-model.md)と[Rowan CST表記](../conventions/rowan-cst.md)を参照する。

対象は、operator role、primary、fixed postfix、ML argument、annotation、terminal outer tail、operand slotのrecoveryである。
numeric binding powerによる結合、HIR、型、演算子の値や実行意味は定めない。

## 2. 受理構文

```text
OperatorChain := OperandSlot { Continuation } [ TerminalOuterContinuation ]
OperandSlot := { PrefixOperatorUse G* } (PrimaryHead | NullfixOperatorUse)
Continuation := FixedPostfixContinuation
              | G* SuffixOperatorUse
              | G* InfixOperatorUse G* OperandSlot
              | MlApplicationContinuation
              | G* TypeAnnotationContinuation
FixedPostfixContinuation := CallTail | IndexTail | FieldTail | ProjectionTail | PathTail
MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgument := OperatorChain under the ml_arg stop scope
TerminalOuterContinuation := ColonApplicationTail | AssignmentTail | WithBodyTail
```

operator spellingは、その位置でexact syntax environmentが許すroleとしてだけ受理する。
prefix、infix、suffix、nullfixは同じsource spellingでも異なるroleになり得る。
`=`はdynamic LED operatorが不成立になった後にだけ`AssignmentTail`になり得る。

## 3. Admissionとboundary

value positionはprimary、nullfix、またはaccepted prefix列を受理する。
operand-complete positionはfixed punctuation tail、ML boundary、annotation、terminal outer tail、suffix、infixを構文上の優先順で判定する。
numeric binding powerはこの判定にもCSTの親子関係にも使わない。

active stop、delimiter、structural terminator、ambient owner boundaryは未消費のままcallerへ返す。
terminal outer continuationはchainを終了する。
fixed postfixとML applicationは、その後も同じchainのoperand-complete positionを保つ。

## 4. 直接 Rowan CST

`OperatorChain`はsource orderでprimary、operator-use node、fixed tail node、nested `MlArgument` chain、annotation、terminal tailを並べる。
`PrefixOperatorUse`、`InfixOperatorUse`、`SuffixOperatorUse`、`NullfixOperatorUse`は、accepted spellingを一つずつ保持する。
left/right operand edgeやapplication subtreeはCSTに追加しない。

fixed tailはtargetをchildにせず、そのtail自身のdelimiterまたはrequired slotだけをnested CSTとして所有する。
`MlArgument`のargumentはnested `OperatorChain`である。
`AssignmentTail`、colon application、`with:` bodyはterminal childである。

## 5. Recovery CST

uniqueなdangling prefixまたはinfix roleは、そのoperator-use nodeを残し、required operand slotにzero-widthの`Missing`を置く。
non-boundaryでnon-NUDなrunはmaximal raw `Error` groupとしてchainに直接置く。
その後にadmitted operandがあれば同じslotを再試行する。
safe boundaryへ達したraw groupはrecovered operandとなり、同じ原因の`Missing`を追加しない。

unresolvable operator-shaped spellingはrole nodeを得ない。
nested constructの`Missing`またはraw `Error`は、そのconstruct自身のslotに属し、outer operand slotへ移らない。
`Invalid`は通常のoperator operand recoveryをwrapしない。

## 6. Source/CST例

`+`がinfix role、`-`がprefix role、`!`がsuffix roleとしてavailableなenvironmentでは、`-a + b!`は次のsource orderを持つ。

```xml
<OperatorChain>
  <PrefixOperatorUse><Operator text="-" /></PrefixOperatorUse>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
  <SuffixOperatorUse><Operator text="!" /></SuffixOperatorUse>
</OperatorChain>
```

同じenvironmentで`a +`はinfix useを保持し、operand slotをrecoverする。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <Missing />
</OperatorChain>
```

## 7. Composition

丸括弧element、fixed tails、terminal tailsはそれぞれのconstruct pageが所有する。
後段のassociationは同じflat item列とexact association environmentから結合結果を得るが、CSTを書き換えない。
numeric binding powerだけの変更はsurface `OperatorChain`の形を変えない。
