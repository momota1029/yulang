# Indexとprojection tail

## 1. 権威と対象範囲

このページは、`syntax-v0`における`IndexTail`、`ProjectionTupleTail`、`ProjectionRecordTail`、`ProjectionRecordSpreadItem`を定める。
受理構文と直接Rowan CSTは、2026年8月20日の`yu-syntax` architectureにあるIndexとprojection fixed-tail各節に従う。
式区切りcurrent-Item recoveryとraw-slot CSTの各追補が、これらのtailで用いる共有の区切りrecovery topologyを定める。
[layout-aware comma-or-newline 区切り列の authority](../cross-cutting/layout-aware-separator-authority.md)は、item listのcaptureするbaseとqualifying newline boundaryを定める。
共通の`syntax-v0`表記とrecovery要素は、[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復の`Error`と`Invalid`のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。

対象は、source-orderのIndexとprojection continuation、区切られたitem、record projectionのspread itemである。
semantic indexまたはprojection、record validation、spread positionまたはmultiplicity validation、演算子の結合、名前解決、型、実行意味、diagnostics wording、formattingは定めない。

## 2. 受理構文

```text
FixedPostfixContinuation += IndexTail | ChainContinuingTrivia ProjectionTail

ChainContinuingTrivia := maximal G* with no physical newline
                        | maximal G* whose following-line indent is deeper than the active base

IndexTail := "[" G*
             [ OperatorChain { IndexSeparator OperatorChain } [ IndexSeparator ] ]
             "]"
ProjectionTail := ProjectionTupleTail | ProjectionRecordTail
ProjectionTupleTail := ".(" G*
                       [ OperatorChain { ProjectionTupleSeparator OperatorChain } [ ProjectionTupleSeparator ] ]
                       ")"
ProjectionRecordTail := ".{" G*
                        [ ProjectionRecordItem { ProjectionRecordSeparator ProjectionRecordItem } [ ProjectionRecordSeparator ] ]
                        "}"
ProjectionRecordItem := OperatorChain | ProjectionRecordSpreadItem
ProjectionRecordSpreadItem := ".." G* OperatorChain

IndexSeparator := "," | ";" | qualifying current-depth newline
ProjectionTupleSeparator := "," | ";" | qualifying current-depth newline
ProjectionRecordSeparator := "," | ";" | qualifying current-depth newline
```

index tailの`[`はcompleted operandにadjacentである。
`ChainContinuingTrivia`はouter-chain levelのempty、same-line、またはdeeper-line triviaである。
projectionは`ChainContinuingTrivia`の後でdotとopenerがadjacentである。
したがって、`a.(x)`と`a.{x}`はprojectionであり、`a. (x)`と`a. {x}`はprojectionではない。
exactな`..`のspread authorityはrecord projection item positionだけが持つ。
Indexとtuple projectionのitemはspread itemを受理しない。

## 3. Admissionとboundary

operand-complete positionでは、active stop、matching close、equal-or-shallower newlineがfixed tailを受理する前に各ownerへ返る。
accepted dynamic spellingはdynamic roleを保つ。
leading triviaがない`[`は`IndexTail`を受理する。
exactな`.(`と`.{`は`ChainContinuingTrivia`の後でfield recoveryより先にprojectionを受理する。
introducerを受理したtailはそのtailを確定し、enclosing chainはそのtailがcloseまたはそのrecoveryを終えた後にだけ再開する。

index itemはliteral separator、`]`、またはqualifying current-depth newlineで停止する。
tuple projection itemは対応する`)`のboundaryを使い、record projection itemは対応する`}`のboundaryを使う。
各tailはcomma、semicolon、qualifying current-depth newlineをitem boundaryとして受理する。
より深いnewlineはcurrent itemのcontinuation triviaに残る。

item内のcolon applicationはright-hand-side chainを一つだけ取り、container boundaryをそのtailへ返す。
item内でqualifyするML continuationはそのitemに残る。
equal-or-shallower newlineはML separatorにならず、区切りownerへ返る。

## 4. 直接 Rowan CST

`IndexTail`、`ProjectionTupleTail`、`ProjectionRecordTail`は`OperatorChain`のdirect source-order childである。
これらはtarget expressionをchildに持たない。
genericな`ProjectionTail` CST wrapperはない。

`IndexTail`は`LBracket`、item `OperatorChain`、literal separator、trivia、`RBracket`を直接持つ。
`ProjectionTupleTail`は`Dot`、`LParen`、item `OperatorChain`、literal separator、trivia、`RParen`を直接持つ。
`ProjectionRecordTail`は`Dot`、`LBrace`、ordinary item `OperatorChain`または`ProjectionRecordSpreadItem`、literal separator、trivia、`RBrace`を直接持つ。
qualifying newline separatorはtriviaのままであり、separator nodeもsynthetic tokenも作らない。
projection前の`ChainContinuingTrivia`は、enclosing `OperatorChain`のdirect native contentである。
これはprojection tailのsource range外にある。

`ProjectionRecordSpreadItem`は`DotDot`、後続trivia、nested right-hand-side `OperatorChain`を直接持つ。
exactなmarkerは、より長いoperator-shaped spellingから分割しない。

## 5. Recovery CST

`a[]`、`a.()`、`a.{}`はempty tailであり、item `Missing`を持たない。
leadingまたはrepeated literal separatorは、そのseparatorの前にあるabsent item slotへzero-widthの`Missing`を一つ置く。
separatorなしで同じ行にadmitted next itemが現れた場合は、separator slotへzero-widthの`Missing`を一つ置き、そのitemを同じ位置から再試行する。
validなML continuationはcurrent itemに残り、separator recoveryを起こさない。

malformed itemは、その区切りowner内のmaximal non-empty raw `Error` group一つとなる。
後続のordinary itemまたはexact spread itemは同じslotを再試行できる。
matching closeがない場合は、close slotへzero-widthの`Missing`を一つ置き、protected outer boundaryを未消費で残す。
このownerが消費するforeign closeは`ExpressionDelimitedForeignClose`内のraw `Error` groupとなる。
rejected separator runは`ExpressionDelimitedSeparator`内のraw `Error` groupとなる。
各wrapperはnon-emptyで連続したgroup一つだけを含み、`Missing`、accepted punctuation、retry leading、`Invalid`を含まない。

exactな`..`の後にrecord spreadのright-hand sideがなければ、そのright-hand-side slotへzero-widthの`Missing`を一つ置く。
separatorとcloseは消費しない。
malformed spread right-hand sideはmaximal non-empty raw `Error` group一つとなり、同じslotを再試行できる。
`...`や`..+`のようなより長いspellingは`DotDot`とrecoveryへ変換しない。
ordinary item内のmalformed colon applicationはnested tailでrecoverする。
projection tailはduplicate recoveryを追加しない。

## 6. Source/CST例

`a[i; j]`はIndexTail内に二つのindex itemとliteral semicolonを置く。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <IndexTail>
    <LBracket text="[" />
    <OperatorChain><IdentifierExpression><Identifier text="i" /></IdentifierExpression></OperatorChain>
    <Semicolon text=";" />
    <Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="j" /></IdentifierExpression></OperatorChain>
    <RBracket text="]" />
  </IndexTail>
</OperatorChain>
```

`a .(x, y)`はcontinuing spaceをouter chainに置き、field tailでなくtuple-projection tailを使う。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <ProjectionTupleTail>
    <Dot text="." /><LParen text="(" />
    <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
    <Comma text="," /><Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
    <RParen text=")" />
  </ProjectionTupleTail>
</OperatorChain>
```

`a.{..rest}`はspread markerとright-hand-side chainを専用item nodeに置く。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <ProjectionRecordTail>
    <Dot text="." /><LBrace text="{" />
    <ProjectionRecordSpreadItem>
      <DotDot text=".." />
      <OperatorChain><IdentifierExpression><Identifier text="rest" /></IdentifierExpression></OperatorChain>
    </ProjectionRecordSpreadItem>
    <RBrace text="}" />
  </ProjectionRecordTail>
</OperatorChain>
```

## 7. Composition

[動的演算子列](operator-chain.md)はenclosing source-order chainとそのほかのcontinuationを定める。
[Call、field、path、ML-application tail](call-field-path-tails.md)はsibling fixed tailとML continuationを定める。
共通recovery topologyは、direct raw `Error` groupと二つのexpression-delimited raw-slot wrapperの読み方を定める。
