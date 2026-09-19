# `with:` body tail

## 1. 正本と対象範囲

このページは、`syntax-v0`のterminal `WithBodyTail`を定める。
受理するgrammarとdirect Rowan CSTは、2026-08-20の`yu-syntax` architectureに従う。
recoveryとindented body transportは、Authoritativeな2026-09-08のColon/With inlineとindented Statement role transportの記録に従う。
共通の表記は、[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[recoveryの`Error`と`Invalid`のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。

このページは、generic expressionの`with:` continuation、canonical `Statement`一つからなるinline bodyまたはindented statement block、およびrecovery CSTを扱う。
declaration companion、`with { ... }`、target association、companion semantics、HIR、type、diagnostic wording、formattingは扱わない。

## 2. 受理する構文

```text
WithBodyTail := WithKw G* ":" WithBody
WithBody := InlineWithBody | IndentedStatementBlock
InlineWithBody := Statement [ ";" ]
```

`with`はexact maximal wordであるため、`withx`と`with?`はこのtailをadmitしない。
required colonはlone colonであり、`::`はsplitしない。
`with`と`:`の間のtriviaにはnewlineを含められる。
colon後のphysical newlineは、strictly deeper indentationのときだけindented blockを選ぶ。
それ以外では、bodyはinline canonical `Statement`一つである。

## 3. Admissionとboundary

operand-complete positionでは、active owner stop、matching close、equal-or-shallower newlineがこのtailより先にreturnする。
`with`がstoppedでなければ、そのexact probeはdynamic LED、fixed postfix、ML application、colon applicationより優先する。
acceptするとtailをcommitし、identifier、operator、ML argumentへfallbackしない。

`WithBodyTail`はterminalであり、target childを持たない。
bodyはfresh statementとchain contextを開始する。
したがって、`a with: b: c`または`a with: b with: c`のnested tailはbodyに属し、outer `a` chainには属さない。
optional inline semicolonはtailが一回だけ所有する。
後続のtriviaとouter boundaryはtailの外に残る。

## 4. Direct Rowan CST

`WithBodyTail`は`OperatorChain`のdirect terminal childであり、targetをwrapしない。
`WithKw`、introducer trivia、`Colon`、body trivia、direct `Statement`一つまたはdirect `IndentedStatementBlock`一つをsource orderで持つ。
`InlineWithBody` CST wrapperはない。

```text
OperatorChain := <completed-chain children> WithBodyTail
WithBodyTail := WithKw G* Colon (Statement [ Semicolon ] | IndentedStatementBlock)
```

inline bodyの`Statement`は、nested `OperatorChain`とnested terminal tailを所有する。
indented bodyのstatement separatorは`IndentedStatementBlock`が所有し、このalternative後のsemicolonを`WithBodyTail`は所有しない。

## 5. Recovery CST

accepted `with`にcolonがなければ、`WithBody(Introducer)`にzero-width `Missing`一つを置く。
同じboundaryでbody missing nodeをcascadeしない。
colonがない位置でinline statementが開始するときは、introducer missing nodeの後にそのsame positionをbodyとしてretryする。
`::`は、そのmissing node後もbodyまたはouter recoveryに残る。

accepted colonにbodyがなければ、`WithBody(Body)`にzero-width `Missing`一つを置く。
equal-or-shallower newlineでは、newlineとfollowing itemをouter statement ownerに残す。
malformed non-statement inline runは、`WithBody(Body)`のmaximal non-empty raw `Error` group一つであり、admitted canonical statementからsame-slot retryする。
nested recoveryはnested statementまたはtailに属し、`WithBodyTail`はduplicateしない。

indented alternativeは、`WithBody(IndentedStatement)`をshared block entryとchild Statement recovery slotへtransportする。
protected comma、close、dedent、stop、retry pointはunconsumed boundaryのまま残る。

## 6. Source/CSTの例

`a + b with: cleanup`では、complete outer chainの後にbodyを置く。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <Whitespace text=" " />
  <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
  <Whitespace text=" " />
  <WithBodyTail>
    <WithKw text="with" /><Colon text=":" /><Whitespace text=" " />
    <Statement><OperatorChain><IdentifierExpression><Identifier text="cleanup" /></IdentifierExpression></OperatorChain></Statement>
  </WithBodyTail>
</OperatorChain>
```

`a with: b: c`では、nested colonはbodyのchainにある。

```xml
<WithBodyTail>
  <WithKw text="with" /><Colon text=":" /><Whitespace text=" " />
  <Statement>
    <OperatorChain>
      <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
      <ColonApplicationTail><Colon text=":" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="c" /></IdentifierExpression></OperatorChain></ColonApplicationTail>
    </OperatorChain>
  </Statement>
</WithBodyTail>
```

次のsourceはdirect `IndentedStatementBlock` body一つを持つ。

```text
value with:
  body
```

## 7. Composition

[Dynamic operator chain](operator-chain.md)がterminal continuation positionとsibling tailを定める。
[Colon application](colon-application.md)はbody statement内に現れうる。
shared indented blockがindented body sequenceを所有し、`WithBody(IndentedStatement)` recoveryをtransportする。
