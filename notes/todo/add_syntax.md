# `\.method(...)`
- `\x -> x.method(...)`の略記
- `_.method`より安心安全

# `\'label x ->`
- 再帰関数の略記。普通に`'label x`で起動できると嬉しいね

# `\catch: ...`, `\case: ...`
- `my anon(x: [_] _) = catch x: ...; anon`の略記
- `my anon(x) = case x: ...; anon`

# `catch 'label x:`, `case 'label x:`
- このときの`'label`は自分自身を指す。上の再帰関数と同じ。

# `\catch 'label: ...`, `\case 'label: ...`
- 複合技

# 型の中の`impl`表現
- ちょっとどうするか考え中

# `...`
- PerlのYadaYada operator
  - 忘れたことにはさせない

# `rule`と`~""`
- 構文としてはあるんだけどdesugerがないのでちゃんと決める
- ただのパーサコンビネータなので`parse::choice()`と`parse::read()`/`parse::cut()`、あと変数代入とレコードや配列に脱糖されるだけ。

