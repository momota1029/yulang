# `\.method(...)`
- `\x -> x.method(...)`の略記
- `_.method`より安心安全

# `\catch: ...`
- `\(x: [_] _) -> catch x: ...`の略記

# `\case: ...`

# `\'label x ->`
- 再帰関数の略記。普通に`'label x`で起動できると嬉しいね

# 型の中の`impl`表現
- ちょっとどうするか考え中

# `...`
- PerlのYadaYada operator
  - 忘れたことにはさせない

# `rule`と`~""`
- 構文としてはあるんだけどdesugerがないのでちゃんと決める
- ただのパーサコンビネータなので`parse::choice()`と`parse::read()`/`parse::cut()`、あと変数代入とレコードや配列に脱糖されるだけ。

