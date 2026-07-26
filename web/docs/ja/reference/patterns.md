# パターンマッチ

pattern は Yulang が値に名前を bind するあらゆる場所に現れる：`case` arm、`catch` arm、関数の引数、`my` binding、ラムダ。

## `case`

```yulang
case value:
    0 -> "zero"
    n -> "other"
```

各 arm は `pattern -> body`。
arm は上から順に試され、最初にマッチしたものが選ばれる。
body は単一の式でも、colon block でも、brace block でもよい。

```yulang
case n:
    0 -> "zero"
    x ->
        my doubled = x * 2
        doubled.show
```

## pattern の種類

| pattern | 何にマッチするか |
|---------|------|
| `_` | 何でも（wildcard）|
| `x` | 名前 `x` に bind |
| `42`、`"hi"`、`true`、`false`、`()` | リテラル |
| `"yes" \| "y"` | いずれか一方の選択肢（OR pattern）|
| `pat as value` | `pat` にマッチし、値全体も bind |
| `(a, b)` | tuple |
| `{ x, y }` | field `x` と `y` を持つ record |
| `{ x = 0, y }` | `x` に default 値を持つ record |
| `{ x: name }` | field `x` を `name` という名前に bind |
| `[]`、`[1, 2]`、`[x, ..rest]` | list pattern |
| `[..init, last]` | 先頭側に spread を置いた list |
| `:ready` | symbol |
| `:some value` | payload を持つ polyvariant |
| `just x`、`nil` | prelude が re-export している enum variant |
| `opt::just x`、`opt::nil` | 修飾 path で書く enum variant |
| `tag x` | 短い名前で書く enum variant（`use enum::*` の後でのみ）|

## guard

arm には guard を `if` で付けられる。

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

guard は pattern がマッチしたときだけ評価される。
guard が偽なら次の arm が試される。

## リテラル pattern

```yulang
case msg:
    "" -> "empty"
    "hello" -> "greeting"
    _ -> "other"
```

リテラル pattern は構造的に等しい値にマッチする。

## OR pattern

OR pattern `left | right` は左から順に選択肢を試し、いずれかがマッチすれば成功する。

```yulang
my affirmative answer = case answer:
    "yes" | "y" -> true
    _ -> false

say (affirmative "y")
```

OR pattern の選択肢は binding を統合しない。
現在の checker は異なる bind 名を受け入れ、同じ名前を両側に書いても別々の binding を作る。
選ばれた側が作らなかった binding を body から参照すると、実行時に unbound-local error になる。
選択肢には binding を置かないか、OR pattern 全体に alias を付ける。

## `as` alias

`as` pattern `pattern as name` は内側の pattern にマッチし、入力値全体も `name` に bind する。

```yulang
my normalize answer = case answer:
    ("yes" | "y") as matched -> matched
    _ -> "no"

say (normalize "y")
```

括弧によって alias が OR pattern 全体の外側に置かれるため、どちらの選択肢でも `matched` が作られる。

## 型 pattern は利用できない

parser は `pattern: type` を受理するが、現在の checker は `case` pattern の注釈を検査しない。
これは実行時の型検査ではなく、次の `text: str` も通常の名前 binding として `int` 値にマッチする。

```yulang
my result = case 41:
    text: str -> "annotation ignored"
    _ -> "fallback"

say result
```

この例は `annotation ignored` と出力する。
値の型を検査または制約するために pattern 注釈を使ってはならない。

## tuple pattern

```yulang
case point:
    (0, 0) -> "origin"
    (x, 0) -> "on x axis at " + x.show
    (0, y) -> "on y axis at " + y.show
    (x, y) -> "(" + x.show + ", " + y.show + ")"
```

tuple pattern は入れ子にできる。
`((a, b), c)` は、最初の要素自体がペアであるペアにマッチする。

## record pattern

```yulang
case shape:
    { kind: "circle", radius } -> 3.14 * radius * radius
    { kind: "square", side }   -> side * side
    _                           -> 0
```

明示した field は default を持たない限り必須。
`{ field: bound_name }` で field を別名に bind できる。

### 別名と default

```yulang
case config:
    { host: h = "localhost", port = 80 } -> h + ":" + port.show
```

`host: h` で bind 名を `h` に変える。
`port = 80` で default を与える。

### spread

```yulang
case rec:
    { x, .._ }    -> x
    { ..tail, y } -> y    // `tail` には残りではなく入力 record 全体が入る
```

`..name` は **入力 record 全体** を bind する（record の引き算は型システム上十全には行えないので、`{ x, ..rest }` の `rest` から `x` を除く形は提供していない）。
spread は先頭にも末尾にも置けるが、どちらでも `name` には field を列挙したものを含む全 field が入る。
入力にほかの field があってもよいことだけを示し、それらを bind しない場合は `.._` を使う。

## list pattern

```yulang
case xs:
    []              -> "empty"
    [only]          -> "single: " + only.show
    [first, second] -> "pair"
    [head, ..tail]  -> "head: " + head.show
    [..init, last]  -> "ends with: " + last.show
```

`..rest` で残りの部分を捕まえる。
list pattern には spread を 1 つだけ置ける。

## symbol pattern

symbol pattern `:name` は、同じ名前の symbol 値だけにマッチする。
symbol は payload を持たない。

```yulang
my state_name state = case state:
    :ready -> "ready"
    :waiting -> "waiting"

say (state_name :ready)
```

## polyvariant pattern

polyvariant pattern `:name payload ...` は同じ tag にマッチし、payload の pattern を順に適用する。

```yulang
my unwrap option = case option:
    :some value -> value
    :none -> 0

say (unwrap (:some 42))
```

enum variant と異なり、symbol と polyvariant には宣言も修飾した companion module path も要らない。

## enum pattern

```yulang
enum color = red | green | blue

case c:
    color::red   -> 0
    color::green -> 1
    color::blue  -> 2
```

variant は enum の companion module に住んでいるので、通常は `color::red` のように書く。
**修飾なしの `red` を使うには `use color::*` が必要である。**
`use` がなければ、式位置の `red` は name error になる。
pattern 位置では、任意の値にマッチする `red` という fresh binding になる。
後者は暗黙に意味が変わるため危険である。

```yulang
enum color = red | green | blue
case c:
    red -> "r"      // `red` はすべての値にマッチする fresh 変数
                    // `green` と `blue` の arm は unreachable になる
    green -> "g"
    blue -> "b"
```

variant にマッチさせたいときは、`color::red` のように修飾するか、先に `use color::*` を書く。

payload を持つ variant は、その payload を bind する。

```yulang
enum tree 'a:
    leaf
    node 'a (tree 'a) (tree 'a)

case t:
    tree::leaf -> 0
    tree::node value left right -> value + sum left + sum right
```

## 関数引数の pattern

```yulang
my add (x, y) = x + y
my translate { dx = 0, dy = 0 } point = point.move dx dy
```

トップレベルの binding pattern、ラムダ引数、`my` の分割代入は同じ pattern 文法を共有する。

## `catch` の pattern

```yulang
catch action:
    log::put msg, k ->
        my logged = msg + "\n"
        k ()
    path_err::not_found _, _ -> "(missing)"
    value -> value
```

effect arm では operation 名を pattern として書き、末尾の `k`（または `_`）が continuation に bind される。
値 arm `v -> ...` は正常終了時に走る。

## `my` の pattern

```yulang
my (a, b) = (1, 2)
my { x, y } = some_point
my [first, ..rest] = some_list
```

`my` の分割代入は、pattern が必ずマッチする前提で処理される。
binding の網羅性は検査されない。

## 関連ページ

- [関数 → オプショナル引数としての record pattern](./functions)
- [制御構文 → catch](./control-flow)
- [エラー → 名指しで捕まえる](./errors)
