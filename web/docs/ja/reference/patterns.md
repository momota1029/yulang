# パターンマッチ

パターンは Yulang が値に名前を bind するあらゆる場所に現れる：`case` arm、
`catch` arm、関数の引数、`my` binding、ラムダ。

## `case`

```yulang
case value:
    0 -> "zero"
    n -> "other"
```

各 arm は `pattern -> body`。arm は上から順に試され、最初にマッチしたものが
選ばれる。body は単一の式でも、colon block でも、brace block でもよい。

```yulang
case n:
    0 -> "zero"
    x ->
        my doubled = x * 2
        doubled.show
```

## パターンの種類

| パターン | 何にマッチするか |
|---------|------|
| `_` | 何でも（ワイルドカード）|
| `x` | 名前 `x` に bind |
| `42`、`"hi"`、`true`、`false`、`()` | リテラル |
| `(a, b)` | タプル |
| `{ x, y }` | フィールド `x` と `y` を持つレコード |
| `{ x = 0, y }` | `x` にデフォルト値を持つレコード |
| `{ x: name }` | フィールド `x` を `name` という名前に bind |
| `[]`、`[1, 2]`、`[x, ..rest]` | リストパターン |
| `[..init, last]` | 先頭側に spread を置いたリスト |
| `just x`、`nil` | prelude が re-export している enum variant |
| `opt::just x`、`opt::nil` | 修飾パスで書く enum variant |
| `tag x` | 短い名前で書く enum variant（`use enum::*` の後でのみ）|

## ガード

arm にはガードを `if` で付けられる。

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

ガードはパターンがマッチしたときだけ評価される。ガードが偽なら次の arm が
試される。

## リテラルパターン

```yulang
case msg:
    "" -> "empty"
    "hello" -> "greeting"
    _ -> "other"
```

リテラルパターンは構造的に等しい値にマッチする。

## タプルパターン

```yulang
case point:
    (0, 0) -> "origin"
    (x, 0) -> "on x axis at " + x.show
    (0, y) -> "on y axis at " + y.show
    (x, y) -> "(" + x.show + ", " + y.show + ")"
```

タプルパターンは入れ子にできる。`((a, b), c)` は、最初の要素自体がペアである
ペアにマッチする。

## レコードパターン

```yulang
case shape:
    { kind: "circle", radius } -> 3.14 * radius * radius
    { kind: "square", side }   -> side * side
    _                           -> 0
```

明示したフィールドはデフォルトを持たない限り必須。`{ field: bound_name }` で
フィールドを別名に bind できる。

### 別名とデフォルト

```yulang
case config:
    { host: h = "localhost", port = 80 } -> h + ":" + port.show
```

`host: h` で bind 名を `h` に変える。`port = 80` でデフォルトを与える。

### スプレッド

```yulang
case rec:
    { x, .._ }    -> x
    { ..tail, y } -> y    -- `tail` には残りではなく **入力 record 全体** が入る
```

`..name` は **入力 record 全体** を bind する（レコードの引き算は型システム上
十全には行えないので、`{ x, ..rest }` の `rest` から `x` を除く形は提供して
いない）。スプレッドは先頭にも末尾にも置けるが、どちらでも `name` には field
を列挙したものを含む全 field が入る。残りを「あること」として受け取りたい
だけなら `.._`、bind したくないときに使う。

## リストパターン

```yulang
case xs:
    []              -> "empty"
    [only]          -> "single: " + only.show
    [first, second] -> "pair"
    [head, ..tail]  -> "head: " + head.show
    [..init, last]  -> "ends with: " + last.show
```

`..rest` で残りの部分を捕まえる。リストパターンには spread を 1 つだけ
置ける。

## enum パターン

```yulang
enum color = red | green | blue

case c:
    color::red   -> 0
    color::green -> 1
    color::blue  -> 2
```

variant は enum の companion module に住んでいるので、通常は `color::red` の
ように書く。**修飾なしの `red` を使うには `use color::*` が必要** — `use`
なしだと、式位置の `red` は name error になり、pattern 位置の `red` は
silently に fresh binding（任意の値にマッチする `red` という変数）になる。
後者は無警告で意味が変わるので注意:

```yulang
enum color = red | green | blue
case c:
    red -> "r"      -- ここの `red` は fresh 変数。すべての値にマッチして
                    -- `green` / `blue` arm が unreachable になる。
    green -> "g"
    blue -> "b"
```

variant にマッチさせたいときは、`color::red` のように修飾するか、先に
`use color::*` を書く。

payload を持つ variant は、その payload を bind する。

```yulang
enum tree 'a:
    leaf
    node 'a (tree 'a) (tree 'a)

case t:
    tree::leaf -> 0
    tree::node value left right -> value + sum left + sum right
```

## 関数引数のパターン

```yulang
my add (x, y) = x + y
my translate { dx = 0, dy = 0 } point = point.move dx dy
```

トップレベルの binding パターン、ラムダ引数、`my` の分割代入は同じパターン
文法を共有する。

## `catch` のパターン

```yulang
catch action:
    log::put msg, k ->
        my logged = msg + "\n"
        k ()
    path_err::not_found _, _ -> "(missing)"
    value -> value
```

effect arm では operation 名をパターンとして書き、末尾の `k`（または `_`）が
継続に bind される。値 arm `v -> ...` は正常終了時に走る。

## `my` のパターン

```yulang
my (a, b) = (1, 2)
my { x, y } = some_point
my [first, ..rest] = some_list
```

これらは反駁不能なパターン — コンパイラはマッチが必ず成立する前提で扱う。
`my` で網羅性を欠くパターンを書くと型エラーになる。

## 関連ページ

- [関数 → オプショナル引数としてのレコードパターン](./functions)
- [制御構文 → catch](./control-flow)
- [エラー → 名指しで捕まえる](./errors)
