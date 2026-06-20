# Parser DSL の desugar 方針

決定日: 2026-05-15

## どこで解決するか

`rule { ... }` ブロックは **AST 化（lower3）段階** でコンビネータ呼び出しに desugar する。
専用の AST ノードは残さない。infer3 から先は普通の関数適用として扱う。

## `~"..."` の型

| 形                | 型                                  |
| ----------------- | ----------------------------------- |
| `~"abc"`          | `() -> [parse] ()`                  |
| `~":name"`        | `() -> [parse] { name: str }`       |

キャプチャがあるときはレコード型になり、複数のキャプチャは合成（マージ）される想定。
`char` は Unicode scalar value ではなく extended grapheme cluster として扱う。
`~":name"` の token は、identifier 専用ではなく、空白でも punctuation でもない
grapheme cluster の連続文字列として扱う。Raku の word/identifier 系の使い勝手を
参考にしつつ、parser DSL では `punct` を区切りにする広い token として定義する。

## パーサ値の扱い（2026-05-11 決定の継承）

- `~"..."` および `rule { ... }` は **パーサ値（object）として第一級** に扱う
- 変数に格納された状態では「値」、起動したい場所で `()` を付けて発火させる
- 例: `my parser args = ~":name..."()`
- 「変数に格納されたら自動で `()` 起動」のような ad-hoc な切替えは採らない。
  `()` の有無で一律に決める方が規則がきれいで一本通る、というのが採用理由
- `[parse]` エフェクトを通じて入力位置・バックトラック・キャプチャを扱う

## ルールボディ内の局所ルール

- ルールボディの内側では、ident は **呼び出し扱い**（C 式適用が外で発生していないとき）
- これは `rule { ... }` の中だけの局所ルール。外側の式では普通の変数参照

## キャプチャ記法

| 記法       | 意味                                  |
| ---------- | ------------------------------------- |
| `~":name"` | lazy capture（`{ name: str }` に積む）|
| `{name}`   | パーサへの参照（キャプチャしない）    |

## stdlib 側

- `less` / `more` コンビネータは `undet` エフェクトの上に組む
- 最小の `parse` effect kernel は `item` / `peek` / `position` / `fail` /
  `commit` にする。`choice`、`read`、`satisfy`、`many`、`some` は stdlib の
  普通の parser combinator として組む。
- `rule` は PEG-like な ordered parser DSL として扱う。`many` / `some` は
  greedy かつ possessive に近く、後続 parser のためには戻らない。
  regex 的な lazy repetition は `rule` の active surface には入れず、
  将来必要なら別の regex / nondet parser 機構として設計する。
- `item` は 1 grapheme cluster の `char` を返し、`peek` は入力を消費せずに
  `opt char` を返す。
  `token` は `peek` で不一致を確認してから `item` で文字列を 1 文字ずつ消費する
  parser sugar の基礎とし、既存互換の `read` は `token` への alias とする。
  先頭不一致では入力を消費しないので、`"a" | "b"` のような PEG choice が右枝へ
  進める。
- `word` は `peek` で消費前に判定し、空白または punctuation に当たる直前で
  入力位置を進めずに停止する。これにより `many(satisfy ...)` 型の「読んでから
  失敗して区切り文字を消費する」問題を避ける。
- `run_with_pos` は `item` / `peek` / `position` / `fail` / `commit` を
  stdlib の handler として置き、`result (value, pos) parse_error` を返す。
  `run` は最後まで読むことを保証し、`result value parse_error` を返す。
  `run_full` は互換 alias として `run` に寄せる。
- `choice` は普通の combinator とし、局所 handler で `commit` と消費有無を
  引き回す。左分岐が未 commit かつ未消費で失敗した場合だけ右分岐を試す。
  消費後または commit 後の失敗はそのまま失敗として返し、commit 済みだった
  ことは外側の choice にも伝播する。
- capture record は parser runtime の隠れ state に積まない。`rule` / `~"..."`
  の desugar が、構文上の capture を見て最後に record を組む。
- `+` / `*` / `?` が capture を含む場合、desugar 側が list / optional に
  まとめてから record field に押し込む。

## CST 受け皿の現状（2026-05-19 時点）

- 古いパーサに参照実装あり: `crates/yulang-parser/src/expr/rule.rs`, `crates/yulang-parser/src/expr/scan/rule.rs`
- 現行 parser の CST から lower3 で最小 token desugar を開始済み。
  `~"abc"` と単一 token の `rule { "abc" }` は `() -> [parse] ()` の parser
  value として `std::parse::token "abc"` に落ちる。`rule { ... }` の中では
  `token "/"` ではなく `"/"` そのものを parser item として書く。
- `~":name"` や `~":category/:article/index.html"` は `RuleLitText` と
  `RuleLazyCapture` の列を左から順に parser action へ落とす。literal 部分は
  `std::parse::token`、capture 部分は `std::parse::word()` を一度束縛してから
  record に詰める。
  field の内側に effectful parse を直接置くと thunk 境界で parse operation が
  漏れるため、desugar は `my capture = word(); { name: capture }` 相当の
  順序を明示する。
- `rule { category = std::parse::word "/" article = std::parse::word }` のような
  `name = parser` は、parser の戻り値をそのまま record field に入れる。
  PEG の item は文字列固定ではなく値を返せる parser なので、capture は
  「読んだ文字列」ではなく「右辺 parser の値」を採用する。
- `|` は `std::parse::choice` に、`+` / `*` / `?` は
  `some` / `many` / `optional` に落とす。`+?` / `*?` は scanner token として
  残る場合があるが、active lowering では unsupported rule lazy quantifier として
  診断する。値を返さない parser の
  繰り返し結果は rule body 内で捨てて `()` にする。record を返す group を
  繰り返した場合は、その record の list を値として扱い、`name = (...) *` の
  形で field に押し込める。
- interpolation はまだ未実装。未実装形は成功 parser にはせず、到達時に `...`
  と同じ runtime error になる式へ落とす。
