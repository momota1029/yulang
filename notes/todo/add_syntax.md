# `\.method(...)` (2026-05-17 実装済み)
- `\x -> x.method(...)`の略記
- `_.method`より安心安全
- parser / lowering / VM regression 追加済み。`\.x` は `\recv -> recv.x`
  相当として既存の suffix lowering に乗せる。
- 2026-05-21: `\.method1(a, b).method2(c, d)` のように suffix chain を
  そのまま続けられることを parser / VM regression で固定。

# `\'label x ->` (2026-05-17 実装済み)
- 再帰関数の略記。普通に`'label x`で起動できると嬉しいね
- parser / lowering / VM regression 追加済み。空白なしの `\'label` だけを
  recursive lambda label とし、`\ 'label` は従来通り引数 pattern として扱う。

# `\catch: ...`, `\case: ...` (2026-05-19 実装済み)
- `my anon(x: [_] _) = catch x: ...; anon`の略記
- `my anon(x) = case x: ...; anon`
- parser / lowering / VM regression 追加済み。空白なしの `\case` / `\catch`
  だけを shorthand とし、受け取った 1 引数を `case` の scrutinee / `catch`
  の computation として既存 lowering に乗せる。

# `catch 'label x:`, `case 'label x:` (2026-05-19 実装済み)
- このときの`'label`は自分自身を指す。上の再帰関数と同じ。
- parser / lowering / VM regression 追加済み。`case 'go x:` は recursive
  case function を作って `x` に即適用し、`catch 'loop action:` は shallow
  handler の resume 後に明示的に `'loop` を呼び直せる。

# `\catch 'label: ...`, `\case 'label: ...` (2026-05-19 実装済み)
- 複合技
- parser / lowering / VM regression 追加済み。関数そのものを返す形で、
  `\catch 'loop:` は wildcard effectful computation を受け取る。

# 型の中の`impl`表現
- ちょっとどうするか考え中

# `...` (2026-05-19 実装済み)
- PerlのYadaYada operator
  - 忘れたことにはさせない
- parser / lowering / VM regression 追加済み。式としては `never` 型の
  nullfix primitive に lower し、評価された時点で VM error にする。未到達枝では
  `never` として使える。

# `rule`と`~""`
- 構文としてはあるんだけどdesugerがないのでちゃんと決める
- ただのパーサコンビネータなので`parse::choice`と`parse::token()`/`parse::commit()`、あと変数代入とレコードや配列に脱糖されるだけ。
- `choice` は effect operation ではなく ordinary combinator。`commit` を局所
  handler で引き回し、「今起動した分岐が commit 済みか」と「消費したか」だけを
  見て backtrack 可否を決める。
- `run_with_pos` は `(value, pos)` を返し、`run` は最後まで読むことを保証して
  value だけを返す。`run_full` は互換 alias として `run` に寄せる。
- 2026-05-19: 最小 token desugar 追加。`~"abc"` と `rule { "abc" }` は
  `() -> [parse] ()` の parser value として `std::parse::token "abc"` に落ちる。
  `~":name"` は `() -> [parse] { name: str }` の parser value として
  `std::parse::word()` を束縛してから record に詰める。
  `~":category/:article/index.html"` のような literal と capture の列も、
  左から順に `token` / `word` を実行して最後に record を返す。
- `rule { ... }` の中では `token "/"` ではなく `"/"` を書く。`name = parser`
  は右辺 parser の戻り値をそのまま record field に入れる。
- `|` と `+` / `*` / `+?` / `*?` / `?` の lowering 追加済み。
  `|` は `std::parse::choice`、量化子は `some` / `many` / lazy variants /
  `optional` に落とす。interpolation は未実装。
