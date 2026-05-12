# はじめに

Yulang は、role ベースの多相と代数的エフェクトを持つ、実験段階の静的型付き言語です。「やりたいことが短く書ける」を、特殊な構文ではなく、library で表現することを大事にしています。

::: tip Playground
このページの例はすべて <a href="/" target="_self">Playground</a> でそのまま動きます。読みながら触ると感じが掴めます。
:::

## まず動かす

トップレベルに式を書くと、その値が結果として表示されます。

```yulang
my greet name = "hello, %{name}"
greet "Yulang"
```

`my f x = ...` は「名前 + 引数のパターン」を一気に書く binding 構文です。文字列の中の `%{...}` は補間で、その場で値が `Display` 経由で文字列化されます。

## 構造体と method

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

`struct` は nominal な record 型で、`with:` ブロックには companion module へ入る method を書けます。`our p.norm2` の `p` は receiver 名で、`point` の値に対する `.norm2` として呼べます。`with:` で機能を後付けする発想なので、「型と振る舞いの両方を 1 箇所にまとめたい」ときに自然です。

## 普通には書けないことが書ける（1）— 非決定的探索

```yulang
use std::undet::*

{
    my a = each 1..
    my b = each a<..
    my c = each b<..
    guard: a * a + b * b == c * c
    (a, b, c)
}.once
```

`each xs` は「`xs` から 1 つ選ぶ」を 1 行で書ける式です。複数の `each` を組み合わせると、その組み合わせ全体が「ありえる世界の集合」になります。`.once` はその中から最初に成功する 1 件を返します。これは、ピタゴラス三角形を「条件を述べたら勝手に探してくれる」プログラムです。

## 普通には書けないことが書ける（2）— 局所的な参照

```yulang
{
    my $count = 0
    &count = $count + 1
    &count = $count + 1
    $count
}
```

`my $x = ...` は局所の可変 binding を作り、`$x` で読み、`&x = v` で書きます。見た目はただの代入ですが、内部的には小さい `var` effect として展開されるので、可変性が型にちゃんと載ります。「あちこちに書き込める変数」じゃなく、「読み書きする場所をその場で開いている」というニュアンスです。

## 普通には書けないことが書ける（3）— 副作用を取り扱う

```yulang
act console:
    pub read: () -> int

our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> k 42

run_console:
    ask()
```

`act` は副作用の interface を宣言します。`ask` は `console` effect を要求しますが、`run_console` がそれを `catch` で捕まえ、`k 42` で「読んだ結果は 42 だったことにして続行」と書き換えます。`run_console: ask()` の結果から `[console]` は消えます。これによって、テストで副作用を差し替えたり、handler を入れ替えるだけで挙動を切り替えたりできます。

## 覚えておくと早い概念

- program は statement の列です。トップレベル式は CLI / playground で評価・表示されます。
- binding の左辺は pattern です。`my f x = ...` も `my (a, b) = pair` も同じ binding の形です。
- `role` は interface で、`impl` で型ごとに実装します。`+` や `.show` も role 経由で解決されます。
- `[console] int` のような型は、「`int` を返し、`console` effect を起こすかもしれない計算」を表します。`catch` は effect operation を処理して、その effect を行から取り除きます。
- `struct` / `enum` / `act` / `error` / `role` は、method・variant・operation などを置く companion module を作ります。
- `//` `/* */` が通常コメント、`--` と `---` ... `---` は doc comment です。

## 次に読むもの

- [ツアー](./tour) — Yulang の主要機能を一通り見る
- [クックブック](./cookbook) — タスク指向の短いレシピ集
- [落とし穴](./pitfalls) — 引っかかりやすい挙動と回避策
- [リファレンス](/ja/reference/) — 構文と意味の詳細
- <a href="/" target="_self">Playground</a> — 実際に動かす
