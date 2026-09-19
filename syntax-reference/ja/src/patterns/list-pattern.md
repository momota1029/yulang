# List pattern

## 1. syntax-v0の対象範囲

ListPattern は、bracket で囲む Pattern primary である。
empty form と trailing separator を含め、通常の Pattern item と spread item を受け入れる。
このページは構文と recovery topology を定め、spread の matching や capture の意味は定めない。

## 2. grammar

```text
ListPattern := LBracket OpeningTrivia [ ListPatternItem { ListPatternSeparator ListPatternItem } [ ListPatternSeparator ] ] RBracket
ListPatternItem := Pattern@Lowest | ListPatternSpreadItem
ListPatternSpreadItem := DotDot G* Pattern@Lowest
ListPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(list_pattern_base)
```

`..tail` と `.. tail` は spread item である。
`...` と `..+` は `DotDot` と別の token に分割しない。
semicolon は ListPattern separator ではない。
`OpeningTrivia` と base snapshot は、[Pattern core](pattern-core.md)の定義を使う。

## 3. itemとdelimiterの所有権

`[` の後は、ListPattern が comma と対応する `]` を所有する。
item judge は、対応する close、exact `DotDot`、通常の Pattern primary の順に判定する。
外側の close は消費せずに返す。

spread marker は、RHS が incomplete でも `ListPatternSpreadItem` に属する。
nested Pattern の recovery はその owner node を保ち、list の recovery へ付け替えない。

## 4. Direct Rowan CST

direct Rowan CST は、外側の `Pattern` の下に `ListPattern` を置く。
`ListPattern` は `LBracket`、`RBracket`、source の comma と trivia、通常の子 `Pattern`、`ListPatternSpreadItem` を含む。
各 spread node は `DotDot` と RHS の Pattern を含む。

separator となる newline は list の子の間の source trivia のままである。
CST は、その newline や source にない separator の node を作らない。

## 5. recovery topology

通常の item がなければ、list-item slot に zero-width の `Missing` を 1 個置く。
spread RHS がなければ、既存の `ListPatternSpreadItem` 内に `Missing` を 1 個置く。
comma と close は list owner のまま残る。

同一行に次の item が隣接すれば、zero-width の missing separator を 1 個置き、その item で retry する。
malformed な通常 item は、最大の lexical run に対する nonempty の raw `Error` を 1 個置き、valid item で retry する。
malformed separator または unclaimed wrong close は、それを所有する sequence phase の raw `Error` 1 個となる。
recovery は comma、close、caller boundary、fence、valid retry item の前で止まり、同じ原因の 2 個目の Missing を置かない。

## 6. layoutとcaller boundary

list base は `[` の直後に capture する。
次行の indentation がその base 以下なら newline は item boundary になる。
より深い indentation は current item に残る。
同じ boundary cluster では explicit comma が qualifying newline より先に勝つ。

対応する `]` は caller-close 処理より先に勝つ。
caller boundary または fence では、pending trivia と boundary を caller のために消費しない。

## 7. 範囲外と関連ページ

ListPattern は spread の個数、位置、matching、binding、型付け、lowering の規則を定めない。
式の list 構文も定めない。

syntax-v0 の recovery は、Pattern の delimited-slot と sequence の確定済み決定に従う。
共通の Pattern の挙動は [Pattern core](pattern-core.md)、brace で囲む形式は [record pattern](record-pattern.md)を参照する。
