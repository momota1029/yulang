# イディオム

Yulang のコードが C 系よりも短く書けるのは、句読点を落とせる経路が複数
用意されているから。このページは「Yulang らしく読める」書き方を集める。

## 裸の application

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

`f x y` が日常的な呼び出し形。`f(x, y)` は引数を視覚的にまとめたいとき、
または `f(-1)` のように「次のトークンへ流れると読みづらいリテラル」を
渡すときに使う。

## 大きな末尾には colon application

最後の引数がブロックや長い式のときは、`:` で右に流す。

```yulang
catch action:
    log::put msg, k -> handle msg
    v -> v

run_console:
    my answer = ask()
    say answer

fs_err::wrap:
    read_text_or_throw path
```

`f x: body` は「`f` を `x` に適用し、続いて colon の body に適用する」と
読める。handler 風 API やブロック形 API を呼ぶ標準形。

## メソッドのドットチェイン

```yulang
xs.map double .filter (\x -> x > 0) .len
```

`.method` は selection と application を兼ねる。method は第一級なので、
`xs.map` は closure を待つ関数になる。`.filter` や `.len` の前に空白を
置いているのは、裸の application 列の中では空白が引数を一区切りにして、
次のドットを外側の式に付けるから — ここでは `(xs.map double) .filter ...`
と読ませる狙い。

トップレベルでは `xs.map` も `xs .map` も同じ field 選択になる。空白の
有無で意味が変わるのは、ドットつき式が ML 風 application の引数の中に
あるときだけ。詳しくは
[Application](./application#whitespace-is-significant) を参照。

## companion method のための `with:`

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

struct や `type` 宣言の `with:` は、その companion module を開く。
`our recv.name args = body` の形で書けば `value.name args` で解決されるので、
`self` 引数を別途宣言する必要がない。

## `with:` 内の attached `impl`

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index _ = b.value
```

attached `impl` は struct 名を二度書く手間を省く。囲んでいる型が role の
第一引数として自動で前置され、role の残りの引数は role 名の後ろに書く。

## role はレシーバ形で

```yulang
role Eq 'a:
    our a.eq: 'a -> bool

role Add 'a:
    our a.add: 'a -> 'a
```

`our a.method: T` は「実装者は `value.method` を `T` 型で得る」と読める。
レシーバ名はドキュメント用 — role が自然に読める名前を選ぶ。

## hand-rolled enum よりも `error E:`

```yulang
pub error fs_err:
    not_found path
    denied path
```

`error E:` 一行で、`enum` と `act` と `Throw` impl と `Display` impl と
`wrap` / `up` ヘルパーをまとめて手書きするのと同じものが揃う。糖衣を素直に
使う。ロングフォームは仕様外の挙動が必要になったときだけ。

## `e.throw` よりも `fail e`

```yulang
fail fs_err::not_found path
```

`fail` はエラー値を effect 行に乗せる prefix 演算子。`fail` を使うと、
関数を流し読みしたときに「ここで投げる」が一目で分かる。

## 深いネストよりも `sub:` / `return`

```yulang
sub:
    if not config.valid: return default
    my parsed = parse config
    if parsed.empty: return default
    process parsed
```

`sub:` は early-return のスコープ。ハッピーパスをフラットに保ち、
分岐の入れ子を避けるために使う。

## 局所 mutability は `$x` / `&x`

```yulang
my $count = 0
&count = $count + 1
```

本当に可変セルが欲しい場面では明示的な参照構文を使う。compiler は
これを handled `var` effect として展開するので、mutation も型システムに
見える。

## effectful な `if`

```yulang
if all xs < any ys:
    "overlap"
else:
    "no overlap"
```

effectful な boolean 条件は `std::junction` 経由で扱える。条件自体が
非決定的なときに使う。通常の `bool` 条件はそのままで動く。

## 推論に任せ、境界で注釈する

```yulang
pub our_pipeline = read_text "data.txt" | parse | render

pub our_pipeline_typed(path: str): [fs] str =
    read_text path | parse | render
```

`x | f` は左辺の値を右辺の式に流す — F# や Elixir の `|>` と同じ形を、
バー 1 本で書く。

推論はほとんどの型を埋める。注釈を入れるのは、API 境界のドキュメント、
generic を狭めたいとき、推論結果に残った変数を固定したいときに限る。

## 関連ページ

- [構文スタイル](./syntax-style) — 空白と colon の正確なルール
- [クックブック](../guide/cookbook) — タスク指向のレシピ
- [落とし穴](../guide/pitfalls) — よくあるはまりどころ
