# Colon application

## 1. 正本と対象範囲

このページは、`syntax-v0`のterminal `ColonApplicationTail`を定める。
受理するgrammarとdirect Rowan CSTは、2026-08-20の`yu-syntax` architectureに従う。
current recoveryとcurrent-depth sequence ownershipは、Authoritativeな2026-09-08のColon/With inline、indented Statement role transport、Colon layout sequenceの各記録に従う。
共通の表記は、[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[recoveryの`Error`と`Invalid`のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。

このページは、complete `OperatorChain`に続くlone colon、そのinline argumentまたはindented statement block、およびrecovery CSTを扱う。
`if`、declaration、pattern、typeが所有するcolon form、target association、callまたはrecordの解釈、HIR、type、diagnostic wording、formattingは扱わない。

## 2. 受理する構文

```text
ColonApplicationTail := ":" ColonBody
ColonBody := InlineColonArguments | IndentedStatementBlock
InlineColonArguments := OperatorChain { ColonArgumentBoundary OperatorChain }
ColonArgumentBoundary := "," | qualifying current-depth newline
```

`:`直後のphysical newlineは、following indentationがcaptured baseよりstrictly deeperのときだけ`IndentedStatementBlock`を選ぶ。
それ以外では、first bodyはinline `OperatorChain`一つである。
outer current-depth sequence ownerがなければ、tailが後続のliteral commaとqualifying newlineを所有する。
outer ownerがあれば、inline argument一つをparseしてそのboundaryを返す。

## 3. Admissionとboundary

operand-complete `OperatorChain`の後にあるunreserved lone `:`だけが、このterminal tailをadmitする。
`::`はsplitしない。
active colon stop、ML mode、close、outer separator、owner boundaryはadmissionより先にreturnする。
admit後、このtailはenclosing chainを終える。

layoutの選択はsequence-owner queryより先に行う。
equal-or-shallower post-colon newlineは、newlineとfollowing itemをouter ownerへ残す。
colon-owned inline sequenceでは、following indentationがcaptured base以下のnewlineがqualifyingとなる。
deeper newlineはcontinuation triviaに残る。
commaとその周囲のqualifying newlineは一つのboundary episodeであり、empty argumentもsynthetic separatorも作らない。
end直前のfinal qualifying newlineはvalid terminal boundaryである。

## 4. Direct Rowan CST

`ColonApplicationTail`は`OperatorChain`のdirect terminal childであり、targetをchildに持たない。
`Colon`、所有するtrivia、literal commaを伴うdirect RHS `OperatorChain` child、またはdirect `IndentedStatementBlock`をsource orderで持つ。
qualifying newline separatorはtriviaのままであり、separator nodeもsynthetic tokenも作らない。

```text
OperatorChain := <completed-chain children> ColonApplicationTail
ColonApplicationTail := Colon (OperatorChain { Comma OperatorChain } | IndentedStatementBlock)
```

outer sequenceは、commaまたはqualifying newlineを`ColonApplicationTail`の外に残す。
nested colon applicationはnested argument chainのchildであり、outer chainのsecond terminal childではない。

## 5. Recovery CST

accepted colonにinline RHSがなければ、`ColonApplication(Rhs)`にzero-width `Missing`一つを置く。
colon-owned leading commaはfirst argumentのzero-width missing一つを置く。
literal comma後にrequired argumentがなければ、EOFまたはprotected boundaryでmissingとなる。
outer sequenceが所有するtailは、そのcommaまたはqualifying newlineをconsumeせず、colon argument recoveryを追加しない。

non-boundaryかつnon-NUDのinline runは、`ColonApplication(Rhs)`または`ColonApplication(InlineArgument)`にmaximal raw `Error` group一つを置く。
admitted valueは同じslotをretryする。
malformed slotのinitial leadingはnative tail contentであり、interior leadingは`Error`に属する。
retryとboundaryのleadingは、そのownerに残る。
Errorがprotected boundaryへ達したとき、same-causeの`Missing`を追加しない。

indented alternativeは、`ColonApplication(IndentedStatement)`をshared block entryとrequired child Statement slotへtransportする。
block recoveryは`IndentedStatementBlock`に残り、colon tailはduplicate nodeを追加しない。
すべての`Missing`はzero-widthであり、raw `Error` groupはnon-emptyである。

## 6. Source/CSTの例

`a + b: x`では、complete chainの後にtarget-free tailを置く。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <Whitespace text=" " />
  <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
  <ColonApplicationTail>
    <Colon text=":" /><Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
  </ColonApplicationTail>
</OperatorChain>
```

rootの`f: x, y`では、tailがinline argument二つを持つ。

```xml
<ColonApplicationTail>
  <Colon text=":" /><Whitespace text=" " />
  <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
  <Comma text="," /><Whitespace text=" " />
  <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
</ColonApplicationTail>
```

次のsourceはshared indented blockを選ぶ。

```text
f:
  x
  y
```

tailは`Colon`とdirect `IndentedStatementBlock`一つを持ち、blockがopening triviaとstatement sequenceを所有する。

## 7. Composition

[Dynamic operator chain](operator-chain.md)がterminal-continuation positionを定める。
[layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md)がqualifying current-depth newline boundaryを定める。
shared `IndentedStatementBlock`がindented bodyのstatement sequenceとtransportされたrecovery slotを所有する。
