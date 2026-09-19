# Standalone `impl` declaration shell

## 1. 権限と対象範囲

このページは、`syntax-v0`のstandalone `ImplDeclaration` shellを定める。
Impl current-Item recovery recordとAuthoritativeな`IMD-G`、`IMD-J`、`IMD-T`、`IMD-R`が統治する。
type-attached tail、companion、member semantics、conformance、lowering、resolution、inference、formattingは対象外である。

## 2. 受理する構文

```text
ImplDeclaration := [ VisibilityKw Gimpl+ ] ImplKw Gimpl-head RequiredTypeExpression(Impl::Head) ImplAfterHead
VisibilityKw := MyKw | OurKw | PubKw
ImplKw := exact maximal word "impl"
ImplAfterHead := ImplDescription ImplBody | ImplBody
ImplDescription := DescriptionColon G0* RequiredTypeExpression(Impl::Description)
ImplBody := BodylessSemicolon | BracedStatementBlockExpression | ImplColonBody
ImplColonBody := BodyColon G0* RequiredCanonicalStatement(Impl::Body) [ InlineTerminalSemicolon ] | BodyColon Gimpl-indent IndentedStatementBlock(Impl::IndentedStatement)
G0* := physical newlineを含まないmaximal trivia
Gimpl-indent := declaration baseよりstrictly deeperなindentへ続くnon-empty continuation trivia
```

`RequiredTypeExpression`は[TypeExpressionの参照](../types/type-expression-core.md)のfull required type productionを使う。
`RequiredCanonicalStatement`は名前付きcanonical `Statement` productionを使う。

## 3. 受理、phase selection、境界

exact bareまたはvisibility-ledの`impl`がこの宣言を選ぶ。
`implFoo`、`implement`、`my_impl`は分割しない。
headの後のfirst bare colonは、その後のtriviaにphysical newlineがない場合だけdescription colonである。
descriptionの後のcolonはbody colonである。
`;`、`{`、body colonが三つのbody formを選ぶ。
outer separator、dedent、matching close、unclaimed boundaryはouter ownerに残る。

## 4. Source-order Rowan schema

```text
ImplDeclaration := [ VisibilityKw Trivia ] ImplKw Trivia TypeExpression [ ImplDescription ] ( Semicolon | BracedStatementBlockExpression | Colon ( Statement [ Semicolon ] | IndentedStatementBlock ) )
ImplDescription := Colon Trivia TypeExpression
```

declarationはhead一つ、descriptionを0または1個、selected body form一つを持つ。
header、body、member-list、separatorのwrapperは作らない。

## 5. Recovery CST

absent headは`Missing(Impl::Head)`であり、body introducerへcascadeしない。
accepted description colonの後のmissing descriptionは`Missing(Impl::Description)`であり、same-causeのbody recoveryを作らない。
complete headの後のabsent body starterは`Missing(Impl::BodyIntroducer)`である。
accepted body colonの後のabsent inline bodyは`Missing(Impl::Body)`である。
acceptedまたはretried headまたはdescription contentが始まった後のmalformed nested contentはTypeExpression ownerに残り、bracedとindented recoveryはselected child nodeに残る。

```xml
<ImplDeclaration><ImplKw text="impl" /><Whitespace text=" " /><TypeExpression><Identifier text="T" /></TypeExpression><Missing /></ImplDeclaration>
```

initial malformed head runは、`ImplDeclaration`に直接置く`Error+`である。
initial malformed description runは、`ImplDescription`に直接置く。
`TypeExpression`はacceptedまたはretried contentにだけ置く。

```xml
<ImplDeclaration><ImplKw text="impl" /><Whitespace text=" " /><Error text="@" /><Semicolon text=";" /></ImplDeclaration>
```

## 6. SourceとCSTの例

受理する`impl int: Eq;`はdescription一つとbodyless body一つを持つ。

```xml
<ImplDeclaration><ImplKw text="impl" /><Whitespace text=" " /><TypeExpression><Identifier text="int" /></TypeExpression><ImplDescription><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="Eq" /></TypeExpression></ImplDescription><Semicolon text=";" /></ImplDeclaration>
```

## 7. 構成と非対象

headとdescriptionはordinary full TypeExpression grammarを保つ。
bodyはcanonical statementとexisting statement blockを使う。
`via`はImpl keywordではない。
[bare nominal `type` declaration form](bare-nominal-type.md)と[回復のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。
