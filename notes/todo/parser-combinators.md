# Parser Combinators TODO

目的: parser combinators を compiler internals だけでなく、Yulang 側から使える機能として実装する。

## 目標の形

```text
source text / stream
  -> parser value
  -> success(value, rest) | 構造化された parse error
```

## 最初の設計上の問い

- 最初の parser API は pure、effectful、または両方のどれか。
- parser state は input position だけを持つか、user state も持つか。
- parse error は expected tokens、committed failures、source spans をどう保持するか。
- parser failure は `result`、error effects、内部 parser result 型のどれを使うか。
- parser API は将来の string slicing や byte/text 区別とどう関係するか。
- 安定した `result` 型が存在する前に parser combinators を有用にできるか。

## 最小 kernel

- `item`
- `satisfy`
- `map`
- `and_then`
- sequencing
- choice
- repetition
- optional
- token/string matching
- position/span capture

## Error semantics の方針

- backtracking behavior を決める。
- cut / commit の syntax または combinator を決める。
- alternatives の error merging を決める。
- diagnostics に必要な context は保ちつつ、hot path の parser result を毎回大きくしない。

## Examples

- integers と identifiers を parse する。
- 小さな expression language を parse する。
- config 風 format を parse する。
- 役に立つ error message 付きで小さな command language を parse する。

## 最初の slice でやらないこと

- compiler parser をすぐ library 中心に書き直さない。
- compiler parser internals を public API として露出しない。
- error handling の方向が安定する前に、広い parser API を固定しない。
