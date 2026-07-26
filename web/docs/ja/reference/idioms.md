# イディオム

通常の Yulang code では、このページの形式を既定として使う。
句読点を省ける構文を使いながら、call と control flow を読みやすく保つためである。

## 裸の application

日常的な呼び出しには `f x y` を使う。`f(x, y)` は引数を視覚的にまとめる場合や、
`f(-1)` のように次の token へ続くと読みづらい literal を渡す場合に限る。

```yulang
// イディオム
add 1 2
greet name
read_text path

// Yulang では非主流（書ける）
add(1, 2)
greet(name)
read_text(path)
```

## 大きな末尾には colon application

最後の引数がブロックや長い式のときは、`:` で右に流す。

```yulang
catch action:
    log::put msg, k -> handle msg
    v -> v

run_console:
    my answer = ask()
    say answer

io_err::wrap:
    read_text path
```

`f x: body` は「`f` を `x` に適用し、続いて colon の body に適用する」と
読める。handler 風 API やブロック形 API を呼ぶ標準形。

## メソッドのドットチェイン

最初の selection では dot を詰め、外側の bare-application 式へ付ける後続の dot の前には空白を置く。
selection 自体は application ではなく、`xs.map` で選んだ関数に後続の引数を適用する。
次の `.filter` の前にある空白は現在の引数を閉じるため、この chain は
`xs.map (double.filter ...)` ではなく `(xs.map double) .filter ...` を表す。

```yulang
xs.map double .filter (\x -> x > 0) .len
```

トップレベルでは `xs.map` も `xs .map` も同じ field 選択になる。空白の
有無で意味が変わるのは、ドットつき式が ML 風 application の引数の中に
あるときだけ。詳しくは
[Application](./application#whitespace-is-significant) を参照。

## companion method のための `with:`

companion method は declaration の `with:` block に置く。
`our recv.name args = body` と書くと、`self` 引数を別に宣言せずに `value.name args` で解決できる。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

## `with:` 内の attached `impl`

囲んでいる struct 名を二度書かないため、attached `impl` を使う。
囲んでいる型は role の第 1 引数として前置され、残りの role 引数は role 名の後ろに書く。

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index _ = b.value
```

## role はレシーバ形で

role method は receiver 形式で書く。`our a.method: T` は実装者に `T` 型の
`value.method` を与える。receiver 名は説明用なので、role を明確に読める名前を選ぶ。

```yulang
role Eq 'a:
    our a.eq: 'a -> bool

role Add 'a:
    our a.add: 'a -> 'a
```

## hand-rolled enum よりも `error E:`

enum、effect、`Throw` と `Display` の impl、`wrap` helper を手書きせず、`error E:` を使う。
declaration に `from` entry がある場合は `up` helper も生成される。
生成される surface が合わない場合だけ long form を使う。

```yulang
pub error path_err:
    not_found path
    denied path
```

## `e.throw` よりも `fail e`

error value を effect row に乗せるときは `fail` を使う。
prefix 形式にすると、関数を流し読みしても throw site を見つけやすい。

```yulang
fail path_err::not_found path
```

## 深いネストよりも `sub:` / `return`

conditional を入れ子にせず成功経路を平らに保つため、`sub:` と `return` を使う。
`sub:` が early-return scope を開く。

```yulang
sub:
    if not config.valid: return default
    my parsed = parse config
    if parsed.empty: return default
    process parsed
```

## 局所 mutability は `$x` / `&x`

局所的な mutable cell が必要な場合は、明示的な参照構文を使う。
compiler は handled `var` effect へ変換するため、mutation は型システムから見える。

```yulang
my incremented =
    my $count = 0
    &count = $count + 1
    $count
```

## effectful な `if`

条件自体が非決定的な場合は、effectful condition を使う。
`std::control::junction` が `if` の受け取る effectful boolean operation を提供し、
通常の `bool` condition は通常の経路を通る。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    "overlap"
else:
    "no overlap"
```

## 推論に任せ、境界で注釈する

local type は推論に任せ、public API boundary、generic constraint、固定する必要がある
residual variable に注釈を付ける。pipeline の `x | f` は左辺の値を右辺の式へ渡す。
F# や Elixir の `|>` に相当する形を bar 1 本で書く。

```yulang
my parse text = text
my render text = text
pub our_pipeline = "data" | parse | render

pub our_pipeline_typed(value: str): str =
    value | parse | render
```

## 関連ページ

- [構文スタイル](./syntax-style) — 空白と colon の正確なルール
- [クックブック](../guide/cookbook) — タスク指向のレシピ
- [落とし穴](../guide/pitfalls) — よくあるはまりどころ
