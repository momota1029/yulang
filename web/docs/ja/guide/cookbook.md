# クックブック

日常的な Yulang のタスクを、短いレシピで並べた集。各レシピは「こう書く」を
最短で示し、背景は言語リファレンスへリンクする。

例は Yulang らしい **括弧を減らした書き方** をデフォルトにしている — `f x y`
の bare application、`f: ...` の colon application、字下げブロック。C 風の
`f(x, y)` は明示が要る場面に限る。

## 値と関数を定義する

```yulang
my answer = 42
my greet name = "hello, " + name
greet "Yulang"
```

`my` は private な binding。名前のあとに置いたパターンが curry された引数になる。

[関数](../reference/functions)

## 関数を公開する

```yulang
pub double x = x + x
```

`pub` は外部へ export。`our` は囲んでいる companion module 内で見えるようにする
（method 定義での既定）。

[モジュール](../reference/modules)

## `case` で場合分けする

```yulang
my describe n =
    case n:
        0 -> "zero"
        x if x < 0 -> "negative"
        _ -> "positive"
```

arm は上から順に試される。ガードは pattern の後ろに `if` を続けて書く。

[パターンマッチ](../reference/patterns)

## struct に method をつける

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

`with:` は struct の companion module を開く。レシーバ名 `p` は `.norm2` を
呼んだときの値を指す。

[構造体とロール](../reference/structs)

## role を型に対して実装する

```yulang
impl Add point:
    our a.add b = point { x: a.x + b.x, y: a.y + b.y }
```

role は interface を宣言する。`impl` は具体型に対して method を提供する。
レシーバ `a`（とここでは第二引数 `b`）は role の method signature と対応する。

[構造体とロール](../reference/structs)

## ループから早期脱出する

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

`sub:` は early-return のスコープを開く。`return value` は最も近い `sub:` を
抜ける。`for` の中では `last` / `next` / `redo` でループそのものを制御する。

[制御構文](../reference/control-flow)

## `$x` / `&x` で局所的な可変参照を使う

```yulang
{
    my $count = 0
    &count = $count + 1
    &count = $count + 1
    $count
}
```

`my $x = …` は局所の mutable binding を作る。`$x` で読み、`&x = value` で
書く。内部的には小さな handled `var` effect として展開されるので、effect 系の
外に逃げず、ちゃんと型に乗る。

[制御構文 → 参照](../reference/control-flow)

## オプショナル引数を作る

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area { width: 3, height: 4 }
area {}
```

デフォルト付きの record pattern は、呼び出し側で各 field を省略できるように
する。デフォルトは左から右へ評価され、後ろの field のデフォルトは前の field
を参照できる。

[関数](../reference/functions)

## 型付きエラーを投げて捕まえる

```yulang
my read_text_or_throw path =
    case fs::read_text path:
        opt::just text -> text
        opt::nil -> fail fs_err::not_found path

catch read_text_or_throw "/tmp/data":
    fs_err::not_found p, _ -> "(missing) " + p
    value -> value
```

`fail e` は `e.throw` の薄皮。`catch` arm は operation 名を直接書いて
エラーを捕まえる。エラーは常に具体名で扱うのが Yulang のスタイル。

[エラー](../reference/errors)

## エラーを `result` 値に閉じる

```yulang
case fs_err::wrap: read_text_or_throw "/tmp/data":
    result::ok text -> text
    result::err err -> err.show
```

`E::wrap` は thunk を走らせ、対応する error effect を捕まえて `result` 値を
返す。`err` 側は自動生成された `Display` impl で文字列化できる。

[エラー → wrap](../reference/errors)

## 複数のエラーを一つにまとめる

```yulang
pub error io_err:
    fs from fs_err
    parse from parse_err

my read_and_parse path =
    io_err::up:
        my text = read_text_or_throw path
        parse_json text
```

`from` は広いエラー型に narrower error を取り込む。`io_err::up` はブロック
内部の narrower error を `io_err` に持ち上げる handler。

[エラー → from 集約](../reference/errors)

## 自前 effect を handler で受ける

```yulang
pub act log:
    pub put: str -> ()

my run_into_strings(action: [log; _] _): (_, list str) =
    my $entries = []
    my result = catch action:
        log::put msg, k ->
            &entries = $entries + [msg]
            k ()
        v -> v
    (result, $entries)
```

`catch` は捕まえた operation を row から除く。各 arm は payload と継続 `k` を
受け取る。`k value` を呼ぶと、捕まえた地点以降の計算が再開する。

[エフェクト](../reference/effects)

## 非決定的に探索する

```yulang
use std::undet::*

(each [1, 2, 3] + each [10, 20]).list
```

`each xs` は `xs` から 1 つ要素を非決定的に選ぶ。`.list` は計算を走らせ、
すべての結果を集める。`.once` / `.logic` などで結果の形を切り替えられる。

[std::undet](../reference/std/undet)

## effectful な真偽値条件を扱う

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    "found at least one"
else:
    "no overlap"
```

Yulang の `if` は `std::junction` 経由で effectful な boolean 条件を受け取れる。
`all xs` / `any xs` で「全部」「いずれか」を表現する。

## 二つの型の間で cast を定義する

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }

my id: user_id = 7
my raw: int = id
```

`cast(x: A): B = body` は `Cast A` の impl と `type to = B` を生成する。
compiler は注釈や引数のような expected-type 境界で自動的に cast を挿入する。

[キャスト](../reference/casts)

## 関連ページ

- [ツアー](./tour) — 同じ機能群を物語仕立てで一通り紹介。
- [リファレンス](../reference/) — 言語の正式リファレンス。
- [構文スタイル](../reference/syntax-style) — 括弧を省く場面と書き方。
