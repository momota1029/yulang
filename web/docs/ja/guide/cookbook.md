# クックブック

日常的な Yulang のタスクを、短いレシピで並べた集です。各レシピは「こう書く」を最短で示し、背景は言語リファレンスへリンクします。

例は Yulang らしい **括弧を減らした書き方** をデフォルトにしています。`f x y` の bare application、`f: ...` の colon application、字下げブロックです。C 風の `f(x, y)` は明示が要る場面に限ります。

## 値と関数を定義する

```yulang
my answer = 42
my greet name = "hello, " + name
greet "Yulang"
```

`my` は private な binding です。名前のあとに置いたパターンが curry された引数になります。

[関数](../reference/functions)

## 関数を公開する

```yulang
pub double x = x + x
```

`pub` は外部へ export します。`our` は囲んでいる companion module 内で見えるようにします（method 定義での既定）。

[モジュール](../reference/modules)

## `case` で場合分けする

```yulang
my describe n =
    case n:
        0 -> "zero"
        x if x < 0 -> "negative"
        _ -> "positive"
```

arm は上から順に試されます。ガードは pattern の後ろに `if` を続けて書きます。

[パターンマッチ](../reference/patterns)

## struct に method をつける

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

`with:` は struct の companion module を開きます。レシーバ名 `p` は `.norm2` を呼んだときの値を指します。

[構造体とロール](../reference/structs)

## role を型に対して実装する

```yulang
impl Add point:
    our a.add b = point { x: a.x + b.x, y: a.y + b.y }
```

role は interface を宣言します。`impl` は具体型に対して method を提供します。レシーバ `a`（とここでは第二引数 `b`）は role の method signature と対応します。

[構造体とロール](../reference/structs)

## ループから早期脱出する

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

`sub:` は early-return のスコープを開きます。`return value` は最も近い `sub:` を抜けます。`for` の中では `last` / `next` / `redo` でループそのものを制御します。

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

`my $x = …` は局所の mutable binding を作ります。`$x` で読み、`&x = value` で書きます。内部的には小さな handled `var` effect として展開されるので、effect 系の外に逃げず、ちゃんと型に乗ります。

[制御構文 → 参照](../reference/control-flow)

## オプショナル引数を作る

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area { width: 3, height: 4 }
area {}
```

デフォルト付きの record pattern は、呼び出し側で各 field を省略できるようにします。デフォルトは左から右へ評価され、後ろの field のデフォルトは前の field を参照できます。

[関数](../reference/functions)

## 型付きエラーを投げて捕まえる

```yulang
my path = std::path::of_bytes (std::str::to_bytes "/tmp/data")

catch fs::read_text path:
    fs_err::not_found p, _ -> "(missing) %{p}"
    value -> value
```

`fail e` は `e.throw` の薄皮です。`catch` arm は operation 名を直接書いてエラーを捕まえます。エラーは常に具体名で扱うのが Yulang のスタイルです。

[エラー](../reference/errors)

## エラーを `result` 値に閉じる

```yulang
my path = std::path::of_bytes (std::str::to_bytes "/tmp/data")
my res = fs_err::wrap: fs::read_text path
case res:
    result::ok text -> text
    result::err _ -> "(fallback)"
```

`E::wrap` は thunk を走らせ、対応する error effect を捕まえて `result` 値を返します。エラー側を取り出して名前で分岐したい場合は `result::err (fs_err::not_found p) -> ...` のように pattern を深掘りします。

[エラー → wrap](../reference/errors)

## 複数のエラーを一つにまとめる

```yulang
pub error io_err:
    fs from fs_err
    parse from parse_err

my read_and_parse path =
    io_err::up:
        my text = fs::read_text path
        parse_json text
```

`from` は広いエラー型に narrower error を取り込みます。`io_err::up` はブロック内部の narrower error を `io_err` に持ち上げる handler です。

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

`catch` は捕まえた operation を row から除きます。各 arm は payload と継続 `k` を受け取ります。`k value` を呼ぶと、捕まえた地点以降の計算が再開します。

[エフェクト](../reference/effects)

## 非決定的に探索する

```yulang
use std::undet::*

(each [1, 2, 3] + each [10, 20]).list
```

`each xs` は `xs` から 1 つ要素を非決定的に選びます。`.list` は計算を走らせ、すべての結果を集めます。`.once` / `.logic` などで結果の形を切り替えられます。

[std::undet](../reference/std/undet)

## effectful な真偽値条件を扱う

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    "found at least one"
else:
    "no overlap"
```

Yulang の `if` は `std::junction` 経由で effectful な boolean 条件を受け取れます。`all xs` / `any xs` で「全部」「いずれか」を表現します。

## 二つの型の間で cast を定義する

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }

my id: user_id = 7
my raw: int = id
```

`cast(x: A): B = body` は `Cast A` の impl と `type to = B` を生成します。compiler は注釈や引数のような expected-type 境界で自動的に cast を挿入します。

[キャスト](../reference/casts)

## もう少し大きいサンプル

ここまでのレシピを組み合わせると、こういう小さなプログラムが書けます。すべて Playground で動きます。

### 小さな式評価器

`enum` と再帰関数だけで電卓を書けます。

```yulang
enum expr =
    num int
    | add (expr, expr)
    | mul (expr, expr)

my eval e =
    case e:
        expr::num n -> n
        expr::add (a, b) -> eval a + eval b
        expr::mul (a, b) -> eval a * eval b

eval (expr::add (expr::num 2, expr::mul (expr::num 3, expr::num 4)))
// → 14
```

`(expr, expr)` のように tuple を payload にすると、複数引数バリアントを安全に書けます。

### 再帰でリストを絞る

list spread pattern と再帰で、`filter` 的な処理を素直に書けます。

```yulang
my is_even n =
    std::int::eq (std::int::sub n (std::int::mul (std::int::div n 2) 2)) 0

my keep_evens xs =
    case xs:
        [] -> []
        [x, ..rest] ->
            my r = keep_evens rest
            if is_even x:
                [x] + r
            else:
                r

keep_evens [1, 2, 3, 4, 5, 6, 7, 8]
// → [2, 4, 6, 8]
```

### ループで集計する

`my $x = ...` の局所参照は、ループでの集計と相性がいいです。

```yulang
{
    my $best = 0
    for y in [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]:
        if y > $best: &best = y
        else: ()
    $best
}
// → 9
```

`$best` は block の外には漏れません。「ループの間だけ値を持ち回す」ような使い方が型に乗ります。

### 非決定的に探す

`each` と `guard` で、「条件を満たす組」を探索できます。

```yulang
use std::undet::*

{
    my a = each 1..20
    my b = each a..20
    my c = each b..20
    guard: a * a + b * b == c * c
    (a, b, c)
}.list
// → [(3, 4, 5), (5, 12, 13), (6, 8, 10), (8, 15, 17), ...]
```

`.list` を `.once` に変えると、最初に見つかった 1 組だけが返ります。前の選択を後の `each` の範囲に渡すことで、探索を早く絞れます。

## 関連ページ

- [ツアー](./tour) — 同じ機能群を物語仕立てで一通り紹介します。
- [リファレンス](../reference/) — 言語の正式リファレンス。
- [構文スタイル](../reference/syntax-style) — 括弧を省く場面と書き方。
