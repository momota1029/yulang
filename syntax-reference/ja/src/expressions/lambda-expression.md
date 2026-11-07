# Lambda式

## 1. 権威と対象範囲

このページは、`syntax-v0`における`LambdaExpression`を定める。
受理構文、admission、直接Rowan CSTは、Authoritativeなparser gap closure追補のWP-10（2026年11月4日）と第2追補のWP-12（2026年11月7日）に従う。
bodyのoperatorおよびapplication規則は、[dynamic operator chain](operator-chain.md)を参照する。
共通の表記とrecovery要素は、[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復の`Error`と`Invalid`のtopology](../conventions/recovery-error-invalid-topology.md)を参照する。

対象は、backslash、parameter列、exact arrow、body、全header admission、およびparameter patternのrecoveryである。
カリー化の意味、束縛、capture、wildcardの意味、および型付けは定めない。

## 2. 受理構文

```text
LambdaExpression := "\\" LambdaHeaderGap LambdaParameter
                    { LambdaHeaderGap LambdaParameter }
                    LambdaHeaderGap ExactArrow OperatorChain

LambdaParameter := Identifier | ParenthesizedPattern | RecordPattern
ExactArrow := "->"
```

`LambdaHeaderGap`は空、またはlogical layout newlineを含まない既存のinline triviaである。
parameterは1個以上必要であり、bare parameterはidentifierに限る。
record patternは波括弧のまま書ける。
それ以外のpatternは丸括弧で囲む。

```yulang
\x -> x + 1
\x y -> x + y
\(a, b) -> a
\{x, y} -> x + y
\{x, ..rest} -> x
\x {a, b} (c, d) -> x
\x (just y) -> y
\(x: int) -> x
```

複数parameterのカリー化は意味論の規則であり、構文木を入れ子のlambdaへ書き換えない。
ソースで入れ子にした`\x -> \y -> x`だけが、body内に別の`LambdaExpression`を持つ。

## 3. Admissionとboundary

value positionでは、parserはdynamic operatorを選ぶ前にheader全体をsource-onlyで調べる。
headerは、backslash、1個以上のadmitted parameter、およびexact `->`がそろったときだけlambdaとしてcommitする。
parenthesized parameterの先読みは丸括弧を、record parameterの先読みは波括弧を釣り合わせる。
入れ子の同じ括弧も数えるが、literal、line comment、nested block comment内の括弧は数えない。
この先読みはparserを再帰的に実行せず、CSTまたはdiagnosticを作らない。

headerにarrowがない場合、parameterの括弧が閉じない場合、またはparameterがadmitted formでない場合、backslashはlambda tokenにならない。
たとえば、`\x y`、`\{x, y}`、`\(a, b -> a`、`\{x, y -> x`、`\1 -> x`、`\x.y -> x`、`\x ->> x`はlambdaではない。
このときは通常のoperator selectionとrecoveryが同じ位置から動き、宣言済みの`\`演算子を選べる。
反対に、complete headerは同じ綴りの演算子より先にlambdaを選ぶ。

parameter間の隣接は既存のPattern規則に従う。
`\(a, b)(c) -> a`はcomplete headerであり、隣接する`(c)`は先行patternの`PatternCallTail`となる。
したがって、このheaderは2個ではなく1個のparenthesized-pattern parameterを持つ。

lambdaはexpression NUD位置と、triviaの後にML argumentを開始できる位置でadmitされる。
そのため、`f (\x y -> x)`と`f \x y -> x`の両方を受理する。
bodyは`MlMode::All`の`OperatorChain`であり、callerのcomma、close、qualifying newline、およびfenceを越えない。

## 4. 直接Rowan CST

`LambdaExpression`は`OperatorChain`のdirect childである。
そのchildはsource orderで`Backslash`、parameter、`Arrow`、bodyの`OperatorChain`となる。
triviaも同じsource orderに残る。

bare identifier parameterはdirect `Identifier` tokenであり、`Pattern` wrapperを持たない。
parenthesized parameterはdirect `Pattern` nodeであり、その内側に`ParenthesizedPattern`を持つ。
record parameterもdirect `Pattern` nodeであり、その内側に既存の`RecordPattern`を持つ。
spreadは、その`RecordPattern`内の既存の`RecordPatternSpreadItem`となる。
parameter列を表す追加wrapperと、カリー化を表すsynthetic lambdaは置かない。

```xml
<LambdaExpression>
  <Backslash text="\\" />
  <Identifier text="x" />
  <Whitespace text=" " />
  <Pattern>
    <ParenthesizedPattern>
      <LParen text="(" />
      <Pattern>...</Pattern>
      <RParen text=")" />
    </ParenthesizedPattern>
  </Pattern>
  <Whitespace text=" " />
  <Arrow text="->" />
  <OperatorChain>...</OperatorChain>
</LambdaExpression>
```

## 5. Recovery CST

complete headerへcommitした後は、各parenthesized parameterとrecord parameterを通常のPattern parserが読む。
そのため、local comma、missing item、foreign close、およびtype annotationのrecoveryは[patternの形式](../patterns/pattern-core.md)に従う。
たとえば、`\(a,) -> a`のtrailing commaは受理され、`\(,) x -> x`はparameterの`Pattern`内に`Missing`を持つ。

bodyがない`\x ->`はcomplete headerである。
この場合、`Backslash`、parameter、`Arrow`を保ち、bodyのmandatory operand slotにzero-widthの`Missing`を置く。
一方、header admissionに失敗した入力は`LambdaExpression`を作らず、lambda固有のrecoveryも始めない。

## 6. Composition

parameter内の構文とrecoveryは[Pattern](../patterns/index.md)が定める。
bodyとlambdaの外側に続くoperator、ML application、およびfixed tailは[dynamic operator chain](operator-chain.md)が定める。

