# Pattern coreとparenthesized pattern

## 1. syntax-v0の対象範囲

このページは、identifier、integer、symbol、alias、alternation、parenthesized patternから成る syntax-v0 の Pattern core を定める。
list と record の primary は、それぞれのページで定める。
末尾の型注釈は、[型注釈](type-annotation.md)で定める。

## 2. grammar

```text
Pattern := Pattern@Lowest
Pattern@P := PatternPrimary { PatternTail(P) }
PatternTail(P) := G* PatternAliasTail if P <= Alias
                | G* PatternAlternationTail if P <= Alternation
PatternAliasTail := AsKw G+ Identifier
PatternAlternationTail := Pipe G* Pattern@Alternation
PatternPrimary := IdentifierPattern | IntegerPattern | SymbolPattern
                | ParenthesizedPattern | ListPattern | RecordPattern
                | RuleLiteral | StringLiteral | RuleExpression
IdentifierPattern := Identifier | SigilIdentifier
IntegerPattern := Integer
SymbolPattern := Colon!Identifier
ParenthesizedPattern := LParen OpeningTrivia [ Pattern { PatternSeparator Pattern } [ PatternSeparator ] ] RParen
PatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(pattern_base)
```

`G*` は、連続する source trivia の最大の run である。
`G+` は、empty でない最大の run である。
`OpeningTrivia` は delimiter opener の直後にある `G*` である。
各 delimited Pattern は、その opening trivia の後で次の base を snapshot する。

```text
pattern_base := if OpeningTrivia ends after a physical newline
                   and following_line_indentation > incoming_base
                then following_line_indentation
                else incoming_base
```

後続の token や recovery position は、その base を再計算しない。

1 個の quote は Pattern primary を `RuleLiteral` へ route する。
3 個以上の quote run は `StringLiteral` へ route する。
Pattern に `NormalString` route はない。
`RuleExpression` は自身の CST を保ち、Pattern primary としても許される。

## 3. 順序と所有権

core は固定の Pattern 優先順位を使う。
`as` は alternation の RHS 内で結合するため、`A | B as c` は alias を RHS に持つ alternation となる。
外側の型注釈は terminal であり、core tail が戻った後にだけ判定する。

連続した `:identifier` は、active な caller colon より先に SymbolPattern として判定する。
この複合形がなければ、active な caller colon は消費しない。
`as` は alias tail の位置でだけ文脈的な keyword になる。

`(` の後は、parenthesized owner が comma と対応する `)` を所有する。
外側の close は、消費せず caller へ返す。

## 4. Direct Rowan CST

lossless Rowan CST は、1 個の `Pattern` node を外側に置く。
primary は `IdentifierPattern`、`IntegerPattern`、`SymbolPattern`、`ParenthesizedPattern`、`ListPattern`、`RecordPattern`、`RuleLiteral`、`StringLiteral`、`RuleExpression` のいずれかになる。
`SymbolPattern` は colon と隣接する identifier を含む。

`PatternAliasTail` は `AsKw` と binding identifier を含む。
`PatternAlternationTail` は `Pipe` と再帰する RHS の `Pattern` を含む。
`ParenthesizedPattern` は `LParen`、子 Pattern、source の comma と trivia、`RParen` を含む。
separator となる newline は子の間の source trivia のままであり、CST は synthetic な separator node を作らない。

## 5. recovery topology

primary がなければ、直近の primary slot に zero-width の `Missing` を 1 個置く。
malformed primary は、最大の malformed run に対する nonempty の raw `Error` を 1 個置き、同じ slot で valid primary を retry する。
retry される primary の leading trivia は Error の外にあり、直接の Pattern content となる。

確定した symbol colon の後で隣接する名前がなければ、`SymbolPattern` に `Missing` を 1 個置く。
この場合は scan も Error も作らない。
`as` の後に binding がなければ `PatternAliasTail` に `Missing` を 1 個置く。
`|` の後に RHS がなければ `PatternAlternationTail` に `Missing` を 1 個置く。
raw Error が boundary に達した場合は、同じ原因の 2 個目の Missing を置かずに boundary を返す。

## 6. layoutとcaller boundary

parenthesized base は `(` の直後に capture する。
次行の indentation がその base 以下なら newline は item を区切る。
より深い newline は current Pattern に残る。
implicit newline は valid な source trivia であり、missing comma ではない。

comma のない同一行の隣接 item は、zero-width の missing separator を 1 個作り、その item で retry する。
対応する local close は caller-close 処理より先に勝つ。
caller boundary、fence、保護された outer close は消費しない。

## 7. 範囲外と関連ページ

このページは Pattern の binding 意味、constructor 意味、網羅性、名前解決、型付け、lowering を定めない。
また、Pattern entry point 以外の list、record、リテラル、型の構文も定めない。

syntax-v0 の recovery は、Pattern primary、delimited slot、sequence の確定済み決定に従う。
内部の形式は、[list pattern](list-pattern.md)、[record pattern](record-pattern.md)、[型注釈](type-annotation.md)を参照する。
