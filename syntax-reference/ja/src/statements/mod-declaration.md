# `mod` 宣言

## 1. 権限と対象範囲

このページは、`syntax-v0`の`ModDeclaration`を定める。
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`のAuthoritativeなcanonical `Statement`とroot `Declaration`の`mod`拡張、特にModがこのページを統治する。
module loading、namespace、export、test execution、derives、companion、loweringは対象外である。

## 2. 受理する構文

```text
ModDeclaration := [ VisibilityKw Gmod ] ModKw Gmod ModIdentity Gmod ModBody
VisibilityKw := MyKw | OurKw | PubKw
ModKw := exact maximal word "mod"
ModIdentity := Name | TestModuleMarker [ Gmod Name ]
Name := Identifier
TestModuleMarker := Identifier("test")
BodyStarter := Semicolon | LBrace | Colon
ModBody := Semicolon | BracedStatementBlockExpression | Colon ModColonBody
ModColonBody := G0* Statement [ Semicolon ] | IndentedStatementBlock
G0* := physical newlineを含まないmaximal trivia
```

`Gmod`はempty、same-lineのmaximal trivia、またはdeclaration baseよりstrictly deeperなindentへ続くtriviaである。
`Statement`、`BracedStatementBlockExpression`、`IndentedStatementBlock`は、名前付きの参照productionを使う。

## 3. 受理と境界

exact bare `mod`またはadmitted visibility prefixの後の`mod`が、この宣言を選ぶ。
`module`、`modular`、`my_mod`は分割しない。
`mod`直後の`test`はmarkerであり、body starterが続く場合だけanonymousである。
したがってEOFで終わる`mod test`にはsecond nameのMissingがある。

bodyを始めるのはexactな`;`、`{`、lone `:`だけである。
`:`の後ではsame-line triviaがinline `Statement`を、strictly deeperなnewlineがindented blockを選ぶ。
equal-or-shallower newline、outer separator、close、dedent、stopはouter ownerに残る。

## 4. Source-order Rowan schema

`ModDeclaration`のclosed source-order schemaは次のとおりである。

```text
ModDeclaration := [ VisibilityKw Trivia ] ModKw Trivia
                  ( Name | TestModuleMarker [ Trivia Name ] ) Trivia
                  ( Semicolon | BracedStatementBlockExpression |
                    Colon ( Statement [ Semicolon ] | IndentedStatementBlock ) )
TestModuleMarker := Identifier("test")
```

header、body、anonymous name、inline bodyのwrapperは作らない。
identity alternativeとbody alternativeはそれぞれ一つだけである。

## 5. Recovery CST

`Name`、`TestName`、`BodyIntroducer`、colon bodyのfailureは、それぞれのslotに置く。
missing slotは`Missing`であり、malformed runはそのslotの隣接する`Error` leafである。
name failureからsame-causeのbody-introducer failureを作らない。
blockのrecoveryとclose handoffは、選んだblock nodeが持つ。

```xml
<ModDeclaration><ModKw text="mod" /><Whitespace text=" " /><Missing /><Semicolon text=";" /></ModDeclaration>
```

この`Missing`はname slotであり、semicolonは選ばれたbodyである。

`mod @;`では、同じname slotがraw malformed sourceを`Error+`として保つ。

```xml
<ModDeclaration><ModKw text="mod" /><Whitespace text=" " /><Error text="@" /><Semicolon text=";" /></ModDeclaration>
```

## 6. SourceとCSTの例

受理する`mod test {}`は、marker一つとbraced body一つを持つ。

```xml
<ModDeclaration><ModKw text="mod" /><Whitespace text=" " /><TestModuleMarker><Identifier text="test" /></TestModuleMarker><Whitespace text=" " /><BracedStatementBlockExpression><LBrace text="{" /><RBrace text="}" /></BracedStatementBlockExpression></ModDeclaration>
```

## 7. 構成と非対象

`Root`では`ModDeclaration`を直接置く。
nested canonical ownerでは、`Statement`の宣言child一つである。
[Rowan CST表記](../conventions/rowan-cst.md)と[回復のtopology](../conventions/recovery-error-invalid-topology.md)も参照する。
