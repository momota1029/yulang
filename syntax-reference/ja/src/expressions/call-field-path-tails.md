# Call、field、path、ML-application tail

## 1. 権威と対象範囲

このページは、`syntax-v0`における`CallTail`、`FieldTail`、`PathTail`、`MlArgument`を定める。
受理構文と直接Rowan CSTは、2026年8月20日の`yu-syntax` architectureにあるfixed-tail各節に従う。
式区切りcurrent-Item recovery、raw-slot CST、fixed-tail recovery、ML separator-leading ownershipの各追補が、ここで用いるrecoveryとsource ownershipを定める。
2026年9月8日のfixed-tail recovery追補と2026年9月10日のCST slot schema catalogは、FieldTailとPathTailのrecovered slot handoffを定める。
[layout-aware comma-or-newline 区切り列の authority](../cross-cutting/layout-aware-separator-authority.md)は、call itemのcaptureするbaseとqualifying newline boundaryを定める。
共通の`syntax-v0`表記とrecovery要素は、[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復の`Error`と`Invalid`のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。

対象は、completed operandの後に置くsource-order continuationである。
Indexとprojection tail、terminal tail、演算子の結合、名前解決、型、実行意味、diagnostics wording、formattingは定めない。

## 2. 受理構文

```text
FixedPostfixContinuation := CallTail
                           | ChainContinuingTrivia FieldTail
                           | ChainContinuingTrivia PathTail

ChainContinuingTrivia := maximal G* with no physical newline
                        | maximal G* whose following-line indent is deeper than the active base

CallTail := "(" G*
            [ OperatorChain { CallSeparator OperatorChain } [ CallSeparator ] ]
            ")"
CallSeparator := "," | ";" | qualifying current-depth newline

FieldTail := "." Identifier
PathTail := "::" G* PathSegment
PathSegment := Identifier | SigilIdentifier

MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgumentSeparator := non-empty trivia with no physical newline
                     | trivia with a physical newline whose following indent is deeper than the active base
MlArgument := OperatorChain under the ML-argument stop scope
```

call openerはcompleted operandにadjacentである。
`ChainContinuingTrivia`はouter-chain levelのempty、same-line、またはdeeper-line triviaである。
field tailのdotとidentifierもadjacentである。
fieldとpath tailは`ChainContinuingTrivia`の後に置き、`PathTail`は`::`後のmaximal `G*`を受理する。
callはitem listでcomma、semicolon、qualifying current-depth newlineを受理する。

## 3. Admissionとboundary

operand-complete positionでは、active stop、matching close、equal-or-shallower newlineがtailを受理する前に各ownerへ返る。
accepted dynamic spellingもdynamic roleを保つ。
これらの判定の後、adjacentな`(`は`CallTail`を受理する。
exactな`.identifier`は`ChainContinuingTrivia`の後に`FieldTail`を受理し、exactな`::`は`ChainContinuingTrivia`の後に`PathTail`を受理する。
projection形式の`.(`と`.{`はfield recoveryより先に判定する。
より長いaccepted dot spellingはfield tailへ分割しない。

ML applicationは、qualifyingなnon-empty trivia runとshared `OperatorChain` NUD candidateの両方を要する。
したがって、`f(x)`はcall tailであり、`f (x)`はparenthesized expressionから始まるnested chainを持つML argumentである。
equal-or-shallower newlineはML separatorではない。
一つのML argumentを受理した後のqualifying separator triviaはenclosing chainが所有し、sibling ML argumentを導入できる。

call itemはliteral separator、matching `)`、またはqualifying current-depth newlineで停止する。
call item内のcolon applicationはright-hand-side chainを一つだけ取り、list boundaryをcallへ返す。
item内でqualifyするML continuationはそのitemに残る。
fixed tailがcloseまたはそのrecoveryを終えると、surrounding `OperatorChain`はoperand-complete positionを再開する。

## 4. 直接 Rowan CST

4形式はすべて`OperatorChain`のsource-order childである。
tailはtarget expressionをchildに持たない。

`CallTail`は`LParen`、openingとinter-itemのtrivia、nested argument `OperatorChain`、literalな`Comma`または`Semicolon` leaf、`RParen`を直接持つ。
qualifying newlineはtriviaのままであり、separator nodeもsynthetic tokenも作らない。
`FieldTail`は`Dot`と`Identifier`を直接持つ。
`PathTail`は`ColonColon`、separator後のtrivia、`Identifier`または`SigilIdentifier`を直接持つ。
fieldまたはpath tail前の`ChainContinuingTrivia`は、enclosing `OperatorChain`のdirect native contentである。
これはtailのsource range外にある。

admitted ML argumentの前にあるseparator leadingは、enclosing `OperatorChain`のdirect native contentである。
`MlArgument`はargument payloadから始まり、nested `OperatorChain`を直接持つ。
separator leadingは`MlArgument`にもnested chainにも属さない。

## 5. Recovery CST

`f()`はempty callであり、argument `Missing`を持たない。
leadingまたはrepeated call separatorは、literal separatorの前にあるabsent item slotへzero-widthの`Missing`を一つ置く。
separatorなしで同じ行にadmitted next itemが現れた場合は、separator slotへzero-widthの`Missing`を一つ置き、同じ位置からitemを再試行する。
current itemにとってvalidなML continuationは一つのitemに残り、separator recoveryを起こさない。

malformed call itemはcall owner内のmaximal non-empty raw `Error` group一つとなり、後続itemは同じslotを再試行できる。
matching closeがない場合は、close slotへzero-widthの`Missing`を一つ置き、protected outer boundaryを未消費で残す。
このownerが消費するforeign closeは`ExpressionDelimitedForeignClose`内のraw `Error` groupとなる。
rejected call-separator runは`ExpressionDelimitedSeparator`内のraw `Error` groupとなる。
各wrapperはnon-emptyで連続したgroup一つだけを含み、`Missing`、accepted punctuation、retry leading、`Invalid`を含まない。

dotを受理した後にfield nameがなければ、field-name slotへzero-widthの`Missing`を置く。
`::`を受理した後にpath segmentがなければ、path-segment slotへzero-widthの`Missing`を置く。
malformed nameまたはsegmentは、そのtail内のmaximal non-empty raw `Error` group一つとなる。
recovered field-nameまたはpath-segment slotは、各tailにとってterminalである。
tailはleadingを含むretained Itemをouter tailへ渡す。
後続continuationはrecovered tailのnameまたはsegmentを置き換えず、そのsiblingとなる。
`..`、`...`、`.(`、`.{`はfield tailとrecoveryへ変換しない。

ML separatorにshared NUD candidateがなければ、ML nodeを作らない。
admitted ML argumentにoperandがなければ、nested `OperatorChain`がoperand recoveryを所有する。
`MlArgument`はrecoveryを追加しない。

## 6. Source/CST例

`f(x, y)`はcall punctuationとargument chainをtail内に保持する。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="f" /></IdentifierExpression>
  <CallTail>
    <LParen text="(" />
    <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
    <Comma text="," />
    <Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
    <RParen text=")" />
  </CallTail>
</OperatorChain>
```

`f x y`はsiblingのML argument二つを持つ。
各spaceはouter chainが所有する。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="f" /></IdentifierExpression>
  <Whitespace text=" " />
  <MlArgument><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></MlArgument>
  <Whitespace text=" " />
  <MlArgument><OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain></MlArgument>
</OperatorChain>
```

`a .b :: c`はcontinuing triviaを各fixed tailの外に置く。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <FieldTail><Dot text="." /><Identifier text="b" /></FieldTail>
  <Whitespace text=" " />
  <PathTail><ColonColon text="::" /><Whitespace text=" " /><Identifier text="c" /></PathTail>
</OperatorChain>
```

## 7. Composition

[動的演算子列](operator-chain.md)はouter source-order chainとdynamic roleを定める。
[Indexとprojection tail](index-projection-tails.md)は残りのfixed postfixを定める。
共通recovery topologyは、direct raw `Error` groupと二つのexpression-delimited raw-slot wrapperの読み方を定める。
