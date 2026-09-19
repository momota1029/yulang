# Pattern型注釈

## 1. syntax-v0の対象範囲

Pattern型注釈は、完成したPatternに付ける、optionalかつterminalな`: TypeExpression`の接尾形式である。
binding target、caseとcatchのpattern、nested patternを含め、canonical Patternが許される位置で使える。
このページはsyntax-v0の解析とdirect Rowan CSTのrecoveryだけを定める。

## 2. grammar

```text
Pattern := Pattern@Lowest
Pattern@P := PatternPrimary { ExistingAliasOrAlternationTail } [ PatternTypeAnnotation if P <= TypeAnnotation ]
PatternTypeAnnotation := Gpta Colon Gpta RequiredTypeExpression(Pattern::TypeAnnotation)
```

`Gpta`は、[Pattern core](pattern-core.md)で定義する `G*` の最大の trivia run である。
physical newlineを含まないrun、または外側のPatternの開始時にcaptureしたcontinuation baseより最後のnewline後のindentationが深いphysical newlineを含むrunを受理する。
equal-or-shallower newlineでは、run全体をrollbackする。

accepted colonの後では、type expressionが必要である。
注釈自体はoptionalかつterminalである。

## 3. 順序と所有権

型注釈の優先順位は、alternationとaliasより低い。
したがって、`A | B as c: Int`はalternation全体に注釈を付ける。
注釈を一つ受理した後、同じPatternではalias、alternation、注釈をもう一度判定しない。

activeなcaller colonは注釈の認識より先に勝ち、`::`は注釈のcolonではない。
record fieldでは、nested Patternを始める前に最初のsame-line colonを`RecordPatternField`が所有する。
したがって、`{a: A}`のcolonはfieldに属し、`{a: A} : SomeType`は外側のPatternに注釈を付ける。

## 4. Direct Rowan CST

lossless Rowan CSTは、外側の`Pattern`の末尾に`PatternTypeAnnotation`を置く。
このnodeはaccepted colon、post-colon trivia、requiredな`TypeExpression` entryをsource順に含む。
accepted pre-colon triviaは、`Pattern`の直接の子に残る。
syntheticなcolon、separator、stop tokenは作らない。

次のsourceでは、最初のcolonはrecord fieldに属し、2個目は外側の注釈に属する。

```text
{a: A} : SomeType
```

注釈nodeは、2個目のcolon、その後のspace、`TypeExpression(SomeType)`を含む。

## 5. recovery topology

colonを受理した後、required type entryには次の結果がある。

| colon後の入力 | direct CSTの結果 | 所有権と継続 |
| --- | --- | --- |
| valid type primary | `PatternTypeAnnotation > TypeExpression` | type expressionがcompleteになる。 |
| EOF、active stop、close、comma、semicolon、equal-or-shallower newline | emptyな`TypeExpression`内のzero-width `Missing(Pattern::TypeAnnotation, TypeExpression)` | boundaryは所有者のために未消費のまま残る。 |
| malformed runの後のvalid type primary | nonemptyな`Error(Type::Primary, TypeExpression)`を1個、続けて`TypeExpression` | required slotはそのprimaryでretryする。 |
| malformed runの後のboundary | nonemptyな`Error(Type::Primary, TypeExpression)`を1個 | recoveryはboundaryを返し、同じ原因のMissingを追加しない。 |

たとえば、`my y: = 1`では、required typeのzero-width Missingが`=`の前に置かれる。
`=`はbinding headerが所有したままである。

## 6. caller boundaryとmultiline recovery

注釈は、caller stop、delimiter state、indentation stateを変更せずに、既存のrequired `TypeExpression` parserへ入る。
binding targetでは、`=`をbinding ownerへ残す。
caseとcatchのpatternでは、guardと`->`をarm ownerへ残す。
最初のcatch patternでは、handler commaもcatch ownerへ残す。
delimited patternでは、local commaと対応するcloseをdelimiter ownerへ残す。

malformed typeのrecoveryでは、`TMN` classifierがError後の最大のtrivia runを判定する。
activeなcaller newlineはindentationとretry candidateより先に勝つ。
この`TMN-CallerBoundary`の結果は、未消費のtrivia開始位置にrollback-scoped positional fenceを置く。
type parserと外側のtype ownerは、fence内のtriviaとその後のcaller boundaryを消費しない。
ほかの`TMN`結果はfenceを作らない。
ほかのmultiline結果では、Pattern base snapshot を使う。
required type slotに残れるのは、deeper newlineだけである。

## 7. 範囲外と関連ページ

この形式は、注釈の意味、type checking、Pattern lowering、constructorまたはMLのPattern tail、diagnosticsの文言、formattingを定めない。
RHSは既存の`TypeExpression` entryであり、専用のtype grammarを追加しない。

aliasとalternationは[Pattern core](pattern-core.md)、field colonの所有権は[record pattern](record-pattern.md)を参照する。
