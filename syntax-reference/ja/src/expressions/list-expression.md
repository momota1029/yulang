# リスト式

## 1. 権威と対象範囲

このページは、`syntax-v0`における`ListExpression`を定める。
受理構文と直接Rowan CSTは、2026年11月4日のAuthoritativeなparser gap closure追補のWP-7に従う。
[layout-aware comma-or-newline区切り列のauthority](../cross-cutting/layout-aware-separator-authority.md)は、この構文のseparator規則を定める。
共通の表記とrecovery要素は、[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復の`Error`と`Invalid`のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。

対象は、角括弧、通常item、spread item、commaとlayoutによるseparator、close、および各slotのrecoveryである。
リスト値の型、spreadの評価、要素の型付け、およびリストpatternは定めない。

## 2. 受理構文

```text
ListExpression :=
    "[" G*
    [
        ListExpressionItem
        { ListExpressionSeparator ListExpressionItem }
        [ ListExpressionSeparator ]
    ]
    "]"

ListExpressionItem := OperatorChain | ListExpressionSpreadItem
ListExpressionSpreadItem := ".." G* OperatorChain
ListExpressionSeparator := "," G* | qualifying newline
```

`[]`、`[1]`、`[1, 2,]`、`[1, ..xs, 3]`を受理する。
spread itemは0個以上を任意のitem位置に置ける。
各通常itemとspreadのRHSは`MlMode::All`の`OperatorChain`として読む。
したがって、`[1 2]`はmissing separatorを持たず、ML application `1 2`を一つのitemとして持つ。

## 3. Admissionとboundary

`[`はvalue positionで`ListExpression`を開始する。
既存operandにtriviaなしで続く`[`は`IndexTail`を開始するため、`xs[0]`はindexである。
triviaを伴う`[`はML argumentを開始できるため、`xs [0]`はlist式`[0]`を引数に持つapplicationである。

各itemの`OperatorChain`が所有するML applicationとfixed tailを読んだ後、list ownerはcomma、対応する`]`、またはqualifying current-depth newlineを境界として扱う。
より深いnewlineは、現在のitemのcontinuation triviaとして残る。
item parserが同一行の次item candidateを返した場合、list ownerはseparator slotに`Missing`を置き、同じ位置からitemを再試行する。

## 4. 直接Rowan CST

`ListExpression`は`OperatorChain`のdirect childである。
そのchildはsource orderで`LBracket`、通常itemの`OperatorChain`、`ListExpressionSpreadItem`、literal comma、trivia、`RBracket`となる。
qualifying newlineはtriviaのままであり、synthetic separator nodeにはならない。

各`ListExpressionSpreadItem`は`DotDot`とRHSの`OperatorChain`を持つ。
通常itemは追加のitem wrapperを持たない。

## 5. Recovery CST

initial item slotまたはcomma後のitem slotが必要な要素を得られない場合、`ListExpression`はzero-widthの`Missing`を置く。
missing local closeはclose slotに`Missing`を置き、protected outer boundaryを消費しない。
このため、unclosedな`[1, 2`はsource末尾にmissing closeを持ち、`[,]`はcommaの前にmissing itemを持つ。

spread markerはRHSがなくても`ListExpressionSpreadItem`に属する。
`[..]`のspread nodeは`DotDot`の後にzero-widthの`Missing`を持ち、実在する`RBracket`はlist ownerに残る。

通常のmalformed item runは`ListExpression`直下のraw `Error` groupである。
このownerが消費するforeign closeは`ExpressionDelimitedForeignClose`内のraw `Error` groupである。
たとえば、`[1)]`では`)`がforeign close recoveryとなり、後続の`]`がlistのcloseとなる。

## 6. SourceとCSTの例

`[1 2]`はML applicationを一つのitemとして持つ。

```xml
<OperatorChain>
  <ListExpression>
    <LBracket text="[" />
    <OperatorChain>
      <IntegerLiteral><Integer text="1" /></IntegerLiteral>
      <Whitespace text=" " />
      <MlArgument><OperatorChain><IntegerLiteral><Integer text="2" /></IntegerLiteral></OperatorChain></MlArgument>
    </OperatorChain>
    <RBracket text="]" />
  </ListExpression>
</OperatorChain>
```

`[..]`はspread ownerを保ったままRHSを回復する。

```xml
<OperatorChain>
  <ListExpression>
    <LBracket text="[" />
    <ListExpressionSpreadItem>
      <DotDot text=".." />
      <Missing />
    </ListExpressionSpreadItem>
    <RBracket text="]" />
  </ListExpression>
</OperatorChain>
```

## 7. Composition

inner chainのoperator role、ML application、fixed tailは[dynamic operator chain](operator-chain.md)が定める。
list式の後のouter continuationも、そのouter chainが所有する。
対応するlist patternは[list pattern](../patterns/list-pattern.md)が定める。

未対応の開き区切りから宣言行で回復する規則は、[対応する閉じ区切りがない場合](../conventions/recovery-error-invalid-topology.md#対応する閉じ区切りがない場合)を参照する。
