# ツアー

Yulang の主要機能を短く巡るページです。すべての例は <a href="/" target="_self">Playground</a> で実行できます。

「最初に動かす」「型 + 効果」「データと振る舞い」「制御フロー」「エラー」の順で見ていきます。

## 基本

```yulang
1 + 2
```

トップレベルに式を書くと、その値が実行結果に表示されます。スクリプト言語みたいに「いきなり書いていきなり走る」感覚です。

```yulang
my double x = x + x
double 21
```

`my f x = ...` は「名前と引数を 1 行で並べる」関数 binding です。OCaml の `let f x = ...` や Haskell の `f x = ...` に近い書き方になります。複数引数なら `my add x y = x + y` のように並べます。

可視性は次の通り。

- `my` — private（同じ scope 内だけ）
- `our` — companion module に公開
- `pub` — 外部 module へ export

## 構造体

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

`struct` は nominal な record type です。Rust や OCaml の record と似ています。違うのは `with:` で **method を一緒に書ける** こと。`our p.norm2` の `p` は receiver 名で、`point` の値から `.norm2` として呼べます。class を作るほどではないけれど「型に紐付いた振る舞いを束ねたい」場面に向いています。

## 省略可能引数

record pattern の default は、named optional argument として使えます。

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
```

default は左から右へ評価され、前の field を参照できます。

```yulang
my f {a = 1, b = a + 1, c = b + 1} = (a, b, c)
f {}             // (1, 2, 3)
f { a: 10 }      // (10, 11, 12)
```

Python のキーワード引数 + default、Ruby のハッシュ展開、TypeScript の `function f({a = 1} = {})` に近い使い心地です。型はちゃんと推論されるので、注釈は要りません。

## Parser pattern

parser pattern は、`case` の arm で文字列を直接 match して、その場で部分文字列を
capture できます。`~"..."` は短い形、`rule { ... }` は guard や名前付き parser
piece を置きたいときの形です。

```yulang
use std::text::parse::*

my route = \line -> case line:
    ~"get :key" -> "GET " + key
    ~"set :key {v = ..}" -> "SET " + key + " = " + v
    rule { id = word } if id.starts_with "a" -> "user " + id
    _ -> "unknown"

(route "get color").say
(route "set color deep-blue").say
(route "alice").say
(route "???").say
```

## 可変 binding と参照

`my $x = ...` は可変 binding を作ります。`$x` は読み取り、`&x = v` は書き込みです。

```yulang
my $x = 10
&x = $x + 1
$x
```

`$` と `&` が見た目に出るのは、Perl / Raku 風です。「ふつうの binding は immutable、可変にしたいときだけ印を付ける」スタイルで、コードを読むときに「ここから状態がある」と一目で分かります。

field や index にもそのまま使えます。

```yulang
my $xs = [2, 3, 4]
&xs[1] = 6
$xs
```

内部的にはこれらは小さな `var` effect として展開されるので、関数を抜けない可変状態として型に乗ります。「グローバルに見える変数」ではなく「読み書きの場所をその場で開いている」というニュアンスです。

## 非決定性

`std::control::nondet` の `each` は「選ぶ」を 1 行で書けます。`.list` はすべての結果を集めます。

```yulang
(each [1, 2, 3] + each [4, 5, 6]).list
```

これは「`[1,2,3]` から 1 つ、`[4,5,6]` から 1 つ選んで足す。可能な組み合わせ全部」を表します。Prolog や Haskell の list monad、SQL の cross join のような考え方を、ふつうの式に埋め込めるイメージです。

無限範囲も扱えます。前の選択を使って後の範囲を絞れば、`.once` で最初に成功する組を返します。

```yulang
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
```

これは「ピタゴラス三角形を 1 個欲しい」と宣言したらそれを探してくる、というプログラムです。

## Junction

`all` と `any` は collection 全体に比較を持ち上げます。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

ふつうの言語なら `[1,2,3].all? { |x| [2,3,4].any? { |y| x < y } }` のように畳まないと書けないものを、`if` の中にそのまま書けます。`if` が effectful な条件を受け取れるように設計されているおかげです。

## エフェクト

`act` は effect interface を宣言します。operation は普通の関数のように呼び、`catch` で処理します。

```yulang
act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
```

`ask()` の型は `[console] int` で、これは「`int` を返すが `console` effect を起こすかもしれない計算」を意味します。`run_console` は `catch` でその operation を処理し、戻り値の型から `[console]` を取り除きます。

handler arm の `k` は continuation で、`k value` を呼ぶと operation の呼び出し位置へ値を返して計算を再開します。テスト用に handler を差し替えたり、loop / 早期 return / 例外を全部この仕組みで扱えるのが嬉しいところです。

## ループと早期 return

`for x in xs:` は `Fold` を実装する値を走査します。list や range は標準で対応しています。`sub:` は早期 return scope を作り、`return value` が直近の `sub:` から抜けます。

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```

`return` は parser 専用 keyword ではなく、prelude が `sub` effect の `return` operation を演算子として export しています。`last` / `next` / `redo` も同じ仕組みで、loop の effect を呼んでいるだけです。「早期脱出」「`break`」「`continue`」が、特殊構文ではなく **同じ effect 機構の応用** で書かれています。

## エラー

`error` は enum と effect operation 群を同時に作る糖衣です。

```yulang
error path_err:
    not_found path
    denied path
    invalid_path path
```

`path_err::not_found "path"` は、文脈によって data constructor としても、throwing operation としても読めます。

```yulang
my err: path_err = path_err::not_found "/x"   // 値
path_err::not_found "/x"                      // [path_err] effect を起こす
```

別の error へまとめる場合は `from` を使います。

```yulang
error app_err:
    path from path_err
```

エラーは effect row の中に名前で残るので、「何が起きうるか」が型を見ればわかります。`anyhow` のように消える `Display` ラッパーは意図的に持たず、必要なら `wrap` で `result` 値に閉じてから扱います。

## コメント

```yulang
// 通常の line comment

-- doc comment

---
複数行の doc comment
---
```

`--` は普通のコメントではなく doc comment なので、ただのメモには `//` を使います。

## 次に読むもの

- [クックブック](./cookbook) — タスク指向の短いレシピ集
- [落とし穴](./pitfalls) — 引っかかりやすい挙動と回避策
- [チートシート](./cheat-sheet) — 1 ページで構文を見渡す
- [リファレンス](/ja/reference/) — 各機能の詳細
