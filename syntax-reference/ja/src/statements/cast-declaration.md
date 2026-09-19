# Standalone `cast` declaration

## 1. 権限と対象範囲

このページは、`syntax-v0`の`CastDeclaration`を定める。
TargetTypeとretained caller-boundary residualを含むAuthoritativeな`CAST-G`、`CAST-J`、`CAST-T`、`CAST-R`が統治する。
conversion registrationとapplication、expected-type behavior、coherence、lowering、resolution、inference、formattingは対象外である。

## 2. 受理する構文

```text
CastDeclaration := [ VisibilityKw Gcast+ ] CastKw Gcast-pattern CastPatternGroup Gcast-target CastTarget Gcast-form CastForm
VisibilityKw := MyKw | OurKw | PubKw
CastKw := exact maximal word "cast"
CastPatternGroup := LParen Gcast-delimited* RequiredPattern(Cast::Pattern) Gcast-delimited* RParen
CastTarget := Colon Gcast-type RequiredTypeExpression(Cast::TargetType)
CastForm := Semicolon | Equals CastDefinitionBody
CastDefinitionBody := Gcast-inline RequiredOperatorChain(Cast::Body) | IndentedStatementBlock(item-role := Cast::IndentedStatement)
```

`RequiredPattern`、`RequiredTypeExpression`、`RequiredOperatorChain`は、それぞれ[Patternの参照](../patterns/pattern-core.md)、[TypeExpressionの参照](../types/type-expression-core.md)、[OperatorChainの参照](../expressions/operator-chain.md)のrequired productionを指す。
`Gcast+`と`Gcast-*`は`CAST-G`で定めるCast declaration-continuing triviaである。

## 3. 受理、layout、境界

exact bareまたはvisibility-ledの`cast`がこの宣言を選ぶ。
`casting`と`castaway`はordinary wordに残る。
accepted Cast-local `(`のmatching closeだけがpatternを閉じる。
exact `:`がtargetを始め、その後のexact `;`または`=`がformを選ぶ。
`=`の後のsame-line triviaはinline OperatorChainを、strictly deeper newlineはindented statement blockを選ぶ。
equal-or-shallower newlineとprotected boundaryはouter ownerに残る。

## 4. Source-order Rowan schema

```text
CastDeclaration := [ VisibilityKw Trivia ] CastKw Trivia CastPattern Trivia CastTarget Trivia ( Semicolon | Equals CastBody )
CastPattern := LParen Trivia Pattern Trivia RParen
CastTarget := Colon Trivia TypeExpression
CastBody := Trivia OperatorChain | IndentedStatementBlock
```

`CastPattern`一つ、`CastTarget`一つ、selected form一つを持つ。
bodyless formはdirect semicolonを持つ。
definitionはdirect `Equals`一つと`CastBody`一つを持つ。
signature、conversion-rule、source-type、synthetic body nodeは作らない。

## 5. Recovery CST

Cast-owned slotは`Cast::PatternIntroducer`、`Cast::Pattern`、`CastPattern`のclose、`Cast::TargetIntroducer`、`Cast::TargetType`、`Cast::BodyIntroducer`、`Cast::Body`である。
missing slotは`Missing`であり、raw malformed runはそのslotの`Error+`である。
prefix failureはscanのために`)`、`:`、`;`、`=`をconsumeせず、same-causeのdownstream Missingも作らない。
nested Pattern、TypeExpression、expressionのrecoveryはchild ownerに残る。

acceptedまたはrecovered target colonの後でEOF、`;`、`=`に達したときは、formをそのpunctuationからretryする前に`Missing(Cast::TargetType)`を置く。
これは`Cast::TargetIntroducer`のMissingとは異なる。

```xml
<CastDeclaration><CastKw text="cast" /><CastPattern><LParen text="(" /><Pattern><IdentifierPattern><Identifier text="x" /></IdentifierPattern></Pattern><RParen text=")" /></CastPattern><CastTarget><Colon text=":" /><Whitespace text=" " /><TypeExpression><Missing /></TypeExpression></CastTarget><Semicolon text=";" /></CastDeclaration>
```

missing delimiterがCast patternまたはtargetの内側でouter caller boundaryを隠し、nested ownerがそのboundaryをconsumeまたはreinterpretできる場合は、known caller-boundary residualである。
これはaccepted syntaxでもCast recoveryでもなく、別のauthorityを必要とするretained limitationである。

initial malformed target runは、`CastTarget`に直接置く`Error+`である。
`TypeExpression`はacceptedまたはretried target contentにだけ置く。

```xml
<CastDeclaration><CastKw text="cast" /><CastPattern><LParen text="(" /><Pattern><IdentifierPattern><Identifier text="x" /></IdentifierPattern></Pattern><RParen text=")" /></CastPattern><CastTarget><Colon text=":" /><Whitespace text=" " /><Error text="@" /></CastTarget><Semicolon text=";" /></CastDeclaration>
```

## 6. SourceとCSTの例

受理する`cast(x: A): B = x`はpattern一つ、target一つ、inline body一つを持つ。

```xml
<CastDeclaration><CastKw text="cast" /><CastPattern><LParen text="(" /><Pattern><IdentifierPattern><Identifier text="x" /></IdentifierPattern><PatternTypeAnnotation><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="A" /></TypeExpression></PatternTypeAnnotation></Pattern><RParen text=")" /></CastPattern><CastTarget><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="B" /></TypeExpression></CastTarget><Whitespace text=" " /><Equals text="=" /><CastBody><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></CastBody></CastDeclaration>
```

## 7. 構成と非対象

Patternとtargetはordinaryの参照grammarを使う。
Castはbraceまたはcolon declaration body、punctuation-free target/body split、Cast固有の`via` keywordを追加しない。
[Rowan CST表記](../conventions/rowan-cst.md)と[回復のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。
