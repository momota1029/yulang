# 波括弧で囲む文ブロック

## 1. 権威と対象範囲

このページは、`syntax-v0`の`BracedStatementBlockExpression`を定める。
2026年8月20日の`yu-syntax` architectureが、受理構文と直接 Rowan CSTを定める。
Authoritativeな2026年9月8日のbraced canonical Statement-sequence recoveryの記録が、必須statement、separator、local closeのrecoveryを定める。
Authoritativeな2026年11月7日のparser gap closure addendum 2、WP-13が、式のbrace内のspread itemを追加する。

対象は、operand-starting brace block、その直接のcanonical statementとspread item、separator、close、およびrecovery CSTである。
recordの意味やfieldの検証、control-flowのbrace body、`CatchBlock`、HIR interpretation、型、diagnostic wording、formattingは定めない。

## 2. 受理構文

```text
BracedStatementBlockExpression :=
    "{" G*
    [ BraceExpressionItem { BraceStatementSeparator BraceExpressionItem } [ BraceStatementSeparator ] ]
    G0 "}"
BraceExpressionItem := Statement | RecordExpressionSpreadItem
RecordExpressionSpreadItem := ".." G* OperatorChain
BraceStatementSeparator := G0 ("," | ";") G* | qualifying current-depth newline
```

blockはemptyでよい。
comma、semicolon、qualifying current-depth newlineは、完了したitemを区切る。
より深いnewlineは、現在のitemに残る。
各separator formはtrailingにでき、empty statementを作らない。
`{x: 1, ..rest,}`のように、spreadの後にも末尾のcommaを置ける。

## 3. 受理と境界

operand-required positionでは、単独の`{`がこのprimaryを受理し、対応するbrace scopeをcommitする。
blockはcurrent-depthのstatement separatorとlocal closeを所有する。
このscopeが戻るまで、outer stop、separator、closeはsuspendされる。

必須statementの前とseparatorの後では、対応する`}`がlocal block boundaryになる。
nested delimiterとlexical regionは、outer blockにseparatorまたはcloseを渡せない。
`{x: 1, y: 2}`では、blockが所有するcommaが最初のstatementを終えるため、各statementは通常の一引数colon applicationを持てる。

item先頭のexactな`..`はspreadであり、宣言されたprefix演算子より優先する。
spreadのRHSは、`ListExpressionSpreadItem`と同じく`MlMode::All`の`OperatorChain`として読む。
`{..(1..3)}`の括弧内を含め、item先頭以外の`..`は通常のrange演算子やsuffix演算子としての読み方を保つ。

## 4. 直接 Rowan CST

`BracedStatementBlockExpression`は、`OperatorChain`の直接のprimary childである。
source orderで、`LBrace`、opening trivia、直接の`Statement`または`RecordExpressionSpreadItem` child、`BlockStatementSeparator` child、closing trivia、`RBrace`を持つ。
comma、semicolon、qualifying newlineの各separatorには、`BlockStatementSeparator` wrapper一つがある。
commaまたはsemicolonのwrapperは、`G0`、literal punctuation、following triviaを所有する。
newline wrapperはnative trivia leafを持ち、synthetic tokenを作らない。
このnodeにはrecord wrapperもempty `Statement` nodeもない。
`RecordExpressionSpreadItem`は、`DotDot`とRHSの`OperatorChain`を直接持ち、`Statement`には包まれない。
`{..rest}`をrecordとして読む判断は後段に属し、CSTにはrecordとblockを区別するnodeを追加しない。

```text
BracedStatementBlockExpression := LBrace { Statement | RecordExpressionSpreadItem | BlockStatementSeparator | trivia } RBrace
RecordExpressionSpreadItem := DotDot G* OperatorChain
BlockStatementSeparator := G0 (Comma | Semicolon) G* | qualifying current-depth newline trivia
Statement := OperatorChain | canonical statement form
```

## 5. Recovery CST

必須statement phaseでcommaまたはsemicolonに達すると、`BracedStatementBlock(Statement)`にzero-widthの`Missing`を一つ置き、punctuationをseparator phaseに残す。
boundaryではないnon-statement runは、同じstatement slotにmaximalかつnon-emptyなraw `Error` group一つとなり、後続の受理したstatementがそのslotを再試行する。
separator、qualifying newline、close、nonlocal close、fence、EOFに達したerrorは、同じ原因のmissing nodeを追加しない。

完了したstatementの後、separatorなしで新しいstatementを受理すると、`BracedStatementBlock(Separator)`にzero-widthの`Missing`を一つ置く。
validなempty block、multiline application、trailing separatorは、作り出したstatement missing nodeを追加しない。
local `}`がなければ、`ClosingDelimiter { BracedStatementBlockExpression, Brace }`にzero-widthの`Missing`を一つ置く。
すべてのnonlocal closeは、実際のownerのために未消費のまま残る。

error前のinitial leadingはblock固有のcontentに残り、interior leadingは`Error`に属し、retryまたはprotected-boundaryのleadingはpendingのまま残る。
nested statementは、それぞれのrecovery roleを保持する。

spreadのRHSのrecoveryは、[list expression](list-expression.md)と同じ共有parserが所有する。
RHSがなければspread node内にzero-widthの`Missing`を一つ置き、separatorとcloseはbrace ownerに残す。
malformed RHSはmaximalかつnon-emptyなraw `Error` group一つとなり、後続の式が同じRHS slotを再試行できる。
brace itemのerror runの後でも、受理されたspread itemはitem slotを再試行できる。

## 6. Source/CSTの例

`{}`はvalidなempty blockである。

```xml
<BracedStatementBlockExpression>
  <LBrace text="{" /><RBrace text="}" />
</BracedStatementBlockExpression>
```

`{x, y}`は、statement二つとcomma separator wrapper一つをblockに直接置く。

```xml
<BracedStatementBlockExpression>
  <LBrace text="{" />
  <Statement><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></Statement>
  <BlockStatementSeparator><Comma text="," /><Whitespace text=" " /></BlockStatementSeparator>
  <Statement><OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain></Statement>
  <RBrace text="}" />
</BracedStatementBlockExpression>
```

`{x,}`はvalidであり、`Statement`一つ、trailing `BlockStatementSeparator`一つ、`Missing` nodeなしを持つ。

`{x: 1, y: 2}`は直接のstatementを二つ持つ。
commaはblock separatorであり、各statementは通常の`ColonApplicationTail`を持つ。

`{..rest}`はspread item一つをbraceの直接のchildに置く。

```xml
<BracedStatementBlockExpression>
  <LBrace text="{" />
  <RecordExpressionSpreadItem>
    <DotDot text=".." />
    <OperatorChain><IdentifierExpression><Identifier text="rest" /></IdentifierExpression></OperatorChain>
  </RecordExpressionSpreadItem>
  <RBrace text="}" />
</BracedStatementBlockExpression>
```

`{x: 1, ..rest}`、`{..rest, x: 1}`、`{x, ..rest}`も、同じspread nodeを持つ。
spreadを含まない`{x: 1}`、`{x}`、`{;}`のCSTは変わらない。

## 7. 構成

[動的演算子列](operator-chain.md)がblockのprimary positionを定める。
[layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md)が、qualifying current-depth newline boundaryを定める。
[colon application](colon-application.md)は個々のstatement内で動作し、block separatorをこのblockへ戻す。
