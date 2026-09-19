# Record pattern

## 1. syntax-v0の対象範囲

RecordPattern は、name-headed field と spread を brace で区切る Pattern primary である。
shorthand field、nested Pattern field、default、empty form、trailing separator を含む。
このページは構文と direct CST の recovery topology だけを定める。

## 2. grammar

```text
RecordPattern := LBrace OpeningTrivia [ RecordPatternItem { RecordPatternSeparator RecordPatternItem } [ RecordPatternSeparator ] ] RBrace
RecordPatternItem := RecordPatternField | RecordPatternSpreadItem
RecordPatternField := PatternFieldName [ G0 Colon G* Pattern@Lowest [ G0 Equals G* OperatorChain ] | G0 Equals G* OperatorChain ]
PatternFieldName := Identifier | SigilIdentifier
RecordPatternSpreadItem := DotDot G* Pattern@Lowest
RecordPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(record_pattern_base)
```

`G0` は physical newline を含まない。
`==`、`=>`、`=+` は default marker のために分割しない。
semicolon は RecordPattern separator ではない。
`OpeningTrivia` と base snapshot は、[Pattern core](pattern-core.md)の定義を使う。

## 3. fieldとdelimiterの所有権

field name の後では、nested Pattern の解析を始める前に最初の same-line `:` を `RecordPatternField` が所有する。
最初の same-line exact `=` は、その field の default を始める。
それ以外は shorthand field となる。

RecordPattern は comma と対応する `}` を所有する。
nested Pattern と default の式は local comma または close で止まる。
外側の close は消費せずに返す。

## 4. Direct Rowan CST

direct Rowan CST は、外側の `Pattern` の下に `RecordPattern` を置く。
`RecordPattern` は `LBrace`、`RBrace`、source の comma と trivia、`RecordPatternField`、`RecordPatternSpreadItem` を含む。
spread node は `DotDot` と RHS の Pattern を含む。
default field は `Equals` を保持し、その `OperatorChain` を含む。

record の wrong-kind Pattern recovery は `Invalid(Pattern(...))` として構造化する。
item phase の Invalid は `RecordPattern` の直接の子となる。
separator phase の Invalid は `RecordPatternSeparator` で 1 回だけ包む。
これらの node は、diagnostic-bearing wrapper を増やさずに phase を保存する。

## 5. recovery topology

item、nested Pattern、spread RHS、separator、close がなければ、それぞれの直近 slot に zero-width の `Missing` を 1 個置く。
accepted `=` の後に式がなければ、default-expression の Missing を含む empty `OperatorChain` を置く。
marker は field owner のまま残る。

通常の malformed item と separator run は、順序付けられた sequence context 内の最大の nonempty raw `Error` child となる。
消費した foreign close は別である。
各 occurrence を `RecordPatternForeignClose` で 1 回だけ包み、その source-bearing child は close の raw `Error` だけとする。
この node は通常の item や separator の Error、accepted local close、Invalid node、retry content を包まない。

recovery は comma、close、caller boundary、fence、valid retry candidate の前で止まる。
同じ原因の 2 個目の Missing は置かない。

## 6. layoutとcaller boundary

record base は `{` の直後に capture する。
次行の indentation がその base 以下なら field を区切る。
より深い indentation は current field に残る。
implicit newline は source trivia であり、separator node を作らない。

対応する `}` は caller-close 処理より先に勝つ。
caller boundary または fence では、pending trivia と boundary を caller のために消費しない。
local `}` は同種の caller close より先に勝つ。

## 7. 範囲外と関連ページ

RecordPattern は duplicate name、spread の位置、matching、capture、型、lowering を検証しない。
record expression と record type の構文も定めない。

syntax-v0 の recovery は、Pattern の delimited-slot、sequence、default-expression、RecordPattern foreign-close の確定済み決定に従う。
共通の挙動は [Pattern core](pattern-core.md)、bracket の形式は [list pattern](list-pattern.md)、外側の注釈は [型注釈](type-annotation.md)を参照する。
