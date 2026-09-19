# 丸括弧式

## 1. 権威と対象範囲

このページは、`syntax-v0`における`ParenthesizedExpression`を定める。
受理構文と直接Rowan CSTは、2026年8月20日の`yu-syntax` architectureの丸括弧式とprecedence-neutral chainの各節、および2026年9月8日の式区切りcurrent-Item recoveryと2026年9月10日のraw-slot CST追補に従う。
[layout-aware comma-or-newline 区切り列の authority](../cross-cutting/layout-aware-separator-authority.md)は、この構文のseparator ruleを定める。
この範囲だけで、以前の丸括弧式のseparator部分をsupersedeする。
`syntax-v0`のfreeze、共通の表記、recovery要素は、[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復の`Error`と`Invalid`のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。

対象は、丸括弧、elementの`OperatorChain`、commaとlayoutによるseparator、close、およびこれらのslotのrecoveryである。
unit、grouping、tupleの解釈、演算子の結合、型推論、実行時表現、ほかの丸括弧構文は定めない。

## 2. 受理構文

```text
ParenthesizedExpression :=
    "(" G*
    [
        OperatorChain
        { ParenthesizedSeparator OperatorChain }
        [ ParenthesizedSeparator ]
    ]
    ")"

ParenthesizedSeparator := "," G* | qualifying newline
```

`()`、`(a)`、`(a,)`、複数elementの形式を受理する。
commaはliteralなseparatorである。
qualifying current-depth newlineは、opening triviaから得たbase indentationと同じか浅い次行indentでelement boundaryになる。
より深いindentのnewlineは、continuation triviaとして現在の`OperatorChain`に残る。
semicolonはこの構文のseparatorではない。

## 3. Admissionとboundary

`(`はvalue positionで受理する。
各elementは、現在の丸括弧のcomma、`)`、またはqualifying current-depth layout newlineで停止する`OperatorChain`である。
より深いnewlineは、current elementのcontinuation triviaとして残る。
completedな丸括弧式はouter `OperatorChain`へ戻り、そこでfixed postfix、suffix、infixを続けられる。

同じ行の次element candidateがseparatorなしで現れると、separator slotのrecoveryを行って同じ位置からelementを再試行する。
caller-owned boundaryとnested delimiter scopeはこの構文が消費しない。
local ownerはcommaとmatching `)`のownershipを保ち、matching `)`をlocal closeとして先に受理する。

## 4. 直接 Rowan CST

`ParenthesizedExpression`は`OperatorChain`のdirect childである。
そのchildはsource orderで`LParen`、0個以上の`OperatorChain` element、literal comma、trivia、`RParen`となる。
newline separatorはtriviaであり、synthetic separator nodeにはならない。
`(a,)`のcommaはsource-bearing leafとして残る。

各inner `OperatorChain`は独立したelementである。
丸括弧nodeはelementを別のgroupingまたはtuple nodeでwrapしない。

## 5. Recovery CST

initial item slotまたはcomma後のitem slotが必要なelementを得られない場合、`ParenthesizedExpression`はそのslotにzero-widthの`Missing`を置く。
immediate real `)`はempty formであり、element `Missing`を置かない。
separatorなしのelement retryでは、separator slotに`Missing`を置く。
missing local closeはclose slotに`Missing`を置き、protected outer boundaryは未消費のまま残す。

通常のmalformed item runは`ParenthesizedExpression`直下の隣接したraw `Error` leafである。
rejected semicolonは`ExpressionDelimitedSeparator`内のraw `Error` groupである。
このownerが消費するforeign closeは`ExpressionDelimitedForeignClose`内のraw `Error` groupである。
これらのwrapperは一つのnonempty groupだけを含み、`Missing`、accepted punctuation、retry leading、`Invalid`を含まない。

raw groupの後にadmitted elementがあれば、同じitem slotを満たす。
protected boundaryに達したgroupはboundaryを残し、同じ原因の`Missing`を追加しない。

## 6. Source/CST例

`()`はelementを持たない。

```xml
<OperatorChain>
  <ParenthesizedExpression>
    <LParen text="(" />
    <RParen text=")" />
  </ParenthesizedExpression>
</OperatorChain>
```

`(a,)`は一つのelementとliteral commaを持つ。

```xml
<OperatorChain>
  <ParenthesizedExpression>
    <LParen text="(" />
    <OperatorChain><IdentifierExpression><Identifier text="a" /></IdentifierExpression></OperatorChain>
    <Comma text="," />
    <RParen text=")" />
  </ParenthesizedExpression>
</OperatorChain>
```

`(;)`ではsemicolonがseparator recoveryのslotを示す。

```xml
<OperatorChain>
  <ParenthesizedExpression>
    <LParen text="(" />
    <ExpressionDelimitedSeparator><Error text=";" /></ExpressionDelimitedSeparator>
    <RParen text=")" />
  </ParenthesizedExpression>
</OperatorChain>
```

## 7. Composition

inner chainのoperator roleとfixed tailは[dynamic operator chain](operator-chain.md)が定める。
丸括弧の後のouter continuationも、そのouter chainが所有する。
direct `Error`、`ExpressionDelimitedSeparator`、`ExpressionDelimitedForeignClose`の診断上の読み方は、共通recovery topologyに従う。
