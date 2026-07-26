# 構文スタイル

通常のコードでは、Yulang の free-paren style を使う。
関数 application、colon application、インデント、ユーザー定義演算子が、C 系言語で括弧が担う構造の多くを表す。

このページでは、優先する書き方と、空白によって parse が変わる場所を定める。

## 大きな最後の引数には colon を使う

最後の引数が式全体や block になる場合は、`:` を使う。
こう書くと、括弧を深く重ねずに入れ子の呼び出しを書ける。

```yulang
say: "hello"

format:
    my name = "Yulang"
    "hello, {name}"

run_console:
    my answer = ask()
    say answer
```

```yulang
-- この形を優先する。
say: format: greeting name

-- 内側のコロン式を明示的にまとめたいときだけ括弧を使う。
say (format: greeting name)
```

`f x: body` は、`x` を通常の引数として渡し、`body` を colon 引数として渡す。
感覚としては `f x (body)` に近く、`(f x:) body` ではない。

```yulang
f x: g y z
```

## 単一式の colon block は inline に連ねる

`:` block の body 全体が単一の式だけなら、呼び出しごとにインデント block へ落とさず、呼び出し spine の中で連ねて書く。
これは body が一つの式だけである場合の規則である。
body に複数の statement、local binding、大きめの `if` / `else`、`case`、`catch`、handler branch があるなら、通常のインデント block のままにする。

```yulang
-- 入れ子の単一式 body では、この形を優先する。
say: run_console: ask()

-- 単一式を一つずつ block に広げない。
say:
    run_console:
        ask()
```

`:` の直後に空白を置くかどうかも style signal になる。
各段を別々の呼び出しとして読ませたいときは、空白を置く。

```yulang
say: run_console: ask()
```

chain 全体を一つに融合した操作として読ませたいときは、関数合成に近い見え方として空白を詰める。

```yulang
say:run_console:ask()
```

どちらも colon application である。
違いは、chain をどれくらい密につながったものとして読ませるかである。

## 空白は構文である

Yulang には、似て見えるが parse が違う呼び出し形式がある。

```yulang
f(x)    -- C-style call
f (x)   -- 括弧式 x を ML-style application で渡す
f: x    -- colon application
```

index でも同じである。

```yulang
xs[0]   -- index
xs [0]  -- list literal [0] を xs に渡す
```

symbol では、この差が特に重要になる。

```yulang
f:foo   -- colon application。f に foo を渡す
f :foo  -- ML application。f に symbol :foo を渡す
```

symbol を渡したいときに `f:foo` と詰めて書かないこと。
意味が変わる。

## 改行は ML application を切る

空白による application は行志向である。
改行は現在の ML application chain を切る。
ただし、インデントされた colon block など、明示的に続く構文は別である。

```yulang
f x y

f:
    x
    y
```

引数式を行をまたいで続けたい場合は、`:` か grouped expression を使う。
ただし、括弧内の同じ grouping level でただ改行すると tuple / group item の区切りとして読まれることがある。
式を続けたい行はインデントする。

```yulang
f:
    g x
    h y

f (g
    x)
```

## receiver-first の dot 呼び出しを使う

左側の値に属する操作には receiver-first の dot 呼び出しを使う。
field / method selection は dot syntax で書くが、selection 自体は呼び出しではない。
選択された値に対して、通常の application が続く。

```yulang
xs.len
xs.map f
text.splice(range 1 3, "bc")
```

constructor、effect operation、module export としての名前を強く見せたいものは `module::name` を使う。

```yulang
path_err::not_found "/x"
std::control::nondet::each xs
```

末尾に dot 呼び出しを置くためだけに括弧を足すのは避ける。
receiver が左側に自然に立たない場合は、呼び出しの形を組み替える。

```yulang
-- この形を優先する。
say: 1 + 2

-- 括弧が `.say` のためだけなら見直す。
(1 + 2).say
```

本当に grouping や曖昧性の解消が目的なら、括弧はそのまま使ってよい。
この規則が対象にするのは、dot 呼び出しを構文上可能にするためだけの括弧である。

## 左から右へのデータフローには pipe を使う

pipeline 演算子は `|` である。
左辺の値を、右辺の呼び出し spine の最初の引数として渡す。

```yulang
1 | add 2    -- add 1 2

xs
    | map f
    | filter pred
```

`|` は左結合で、通常の infix 演算子より弱く結合する。

```yulang
a + b | f    -- (a + b) | f
```

## block はインデントを基本にする

複数行の body には、インデント block を使うのが基本である。

```yulang
my total xs =
    my start = 0
    fold add start xs
```

小さい block を式の中に置きたい場合は、brace block が便利である。

```yulang
my inc = \x -> { x + 1 }
```

block の最後の式が、その block の値になる。

## 関数は header pattern で書く

binding の左辺は pattern である。
head が名前のとき、その後ろの pattern は curried 関数引数になる。
小さい関数は、この direct header style を優先する。

```yulang
my add x y = x + y
my area { width = 1, height = 2 } = width * height
```

関数値そのものを式として扱いたい場合は、明示的なラムダを使う。

```yulang
my mapper = \f xs -> xs.map f
```

default 付き record pattern は、小さい optional named argument を書くための基本形である。

```yulang
my box { width = 1, height = width } = width * height

box {}
box { width: 3 }
```

default は左から右へ評価されるため、後ろの default は前の field を参照できる。

## `case` と `catch` の arm は縦に並べる

小さい式では inline branch も便利だが、pattern が多いコードは arm ごとに改行した方が読みやすい。

```yulang
act console:
    our write: str -> ()

case value:
    nil -> fallback
    just x -> x

catch action:
    console::write text, k -> k ()
    value -> value
```

条件は、その条件を持つ arm に guard として置く。

```yulang
case n:
    x if x < 0 -> "negative"
    _ -> "non-negative"
```

## 拡張は `with:` block に置く

`struct`、`enum`、`act`、`error`、`role`、`type ... with:` 宣言は companion namespace を作る、または拡張する。
method や近い実装詳細は、その対象に属すると見える `with:` block に置く。

```yulang
type str with:
    our s.splice r insert = std::text::str::splice s r insert

struct point { x: int, y: int } with:
    our p.len2 = p.x * p.x + p.y * p.y
```

こうすると、receiver-style API が、それを所有する型 / effect の近くにまとまる。

`with:` は expression-local な拡張にも使える。
public companion API ではなく、その式の近くにだけ置きたい helper binding は、式の `with:` に寄せると読みやすい。

```yulang
loop initial with:
    our loop state =
        if done state:
            state
        else:
            loop: step state
```

## constraint は必要な binding の近くに置く

type variable に role constraint が必要な場所では、その場で `where` を使う。
呼び出しを通すためだけに、関係の薄い helper binding へ constraint を押し込んではならない。
constraint は、その role に依存する境界へ置く。

```yulang
my double(x: 'a): 'a =
    where 'a: Add
    x + x
```

## 演算子は import される syntax として扱う

演算子のすべてが parser builtin ではない。
module は prefix / infix / suffix / nullfix / lazy infix 演算子を定義して export できる。
公開演算子宣言は module の先頭か prelude 的な module に置き、下流のファイルが parse される前に syntax を import できるようにする。

```yulang
-- export する module の先頭付近に置く。
pub infix(+) 6.0.0 6.0.0 = add
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b -> ...
pub prefix(return) 1.0.0 = \value -> value
```

`return`、`last`、`next`、`redo` のような word 演算子も、記号演算子と同じ演算子 model に乗る。
ユーザーコード側では、特別な parser 例外のように扱わないこと。

## 短絡評価には lazy 演算子を使う

短絡評価は evaluator の特殊処理ではなく、lazy 演算子 syntax として書く。

```yulang
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b ->
    if a():
        b()
    else:
        false
```

両側の operand が thunk として渡されるので、body 側でどちらを force するか決められる。
これにより、`and` / `or` は library-defined syntax のまま lazy evaluation behavior を持てる。

## 型注釈は境界に置く

local code では、多くの場合 inference に任せる。

```yulang
my id(x) = x
```

public contract を示したい場所、曖昧さを減らしたい場所、意図した cast boundary を明示したい場所には annotation を置く。

```yulang
pub my id(x: 'a): 'a = x

my result: result str io_err = io_err::wrap:
    read_text path
```

type variable は `'a` のような sigil identifier で書く。
通常の関数宣言では、type variable のための独立した binder は要らない。

## 状態は明示的な syntax で見せる

mutation や local-reference 的な挙動には、明示的な参照構文を使う。

```yulang
my incremented =
    my $count = 0
    &count = $count + 1
    $count
```

通常の `my` binding は immutable に見える形に保つ。

## コメントと doc コメントは別物

通常のコメントには `//` と `/* ... */` を使う。

```yulang
// local note

/* longer note */
```

`--` と `--- ... ---` は doc コメント専用である。
documentation syntax として parse され、tooling に残る可能性がある。

```yulang
-- 次の宣言を説明する。

---
長い documentation block。
---
```

## まとめ

- 入れ子の括弧より、whitespace application と `:` を優先する。
- 入れ子の単一式 `:` block は inline に連ねる。本物の複数 statement block はインデントのままにする。
- `say: run_console: ask()` は段階を見せる形、`say:run_console:ask()` は意図的に融合した chain として読ませる形として使い分ける。
- 括弧は default punctuation ではなく、grouping を示したいときに使う。
- 末尾の dot 呼び出しを可能にするためだけの括弧は避ける。
- 通常の関数 binding は `my f x y = ...` の形を優先する。
- 小さい optional named argument には record-pattern default を使う。
- pattern が多い `case` と `catch` は arm を縦に並べる。
- method、attached impl、expression-local helper は、自然な `with:` block の近くに置く。
- `f(x)` と `f (x)` は違う。
- `f:foo` と `f :foo` は違う。
- export する演算子 syntax は、importer が parse 前に見える位置に置く。
- 本物の block は indentation、小さい inline block は braces が向いている。
