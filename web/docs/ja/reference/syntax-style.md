# 構文スタイル

Yulang は、括弧を少なめに書けるように設計されている。関数適用、コロン適用、インデント、ユーザー定義演算子が、C 系言語で括弧が担う構造の多くを表す。

このページでは、Yulang らしく読むための書き方と、空白によって parse が変わる場所をまとめる。

## 大きな最後の引数にはコロンを使う

最後の引数が式全体や block になる場合は、`:` を使う。

```yulang
say: "hello"

format:
    my name = "Yulang"
    "hello, {name}"

run_console:
    my answer = ask()
    say answer
```

こう書くと、括弧を深く重ねずに入れ子の呼び出しを書ける。

```yulang
-- この形を優先する。
say: format: greeting name

-- 内側のコロン式を明示的にまとめたいときだけ括弧を使う。
say (format: greeting name)
```

`f x: body` は、`x` を通常の引数として渡し、`body` をコロン引数として渡す。感覚としては `f x (body)` に近く、`(f x:) body` ではない。

```yulang
f x: g y z
```

## 空白は構文である

Yulang には、似て見えるが parse が違う呼び出し形がある。

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

symbol を渡したいときに `f:foo` と詰めて書かないこと。意味が変わる。

## 改行は ML application を切る

空白による application は行志向である。改行は現在の ML application chain を切る。ただし、インデントされたコロン block など、明示的に続く構文は別である。

```yulang
f x y

f:
    x
    y
```

引数式を行をまたいで続けたい場合は、`:` か grouped expression を使う。ただし、括弧内の同じ grouping level でただ改行すると tuple / group item の区切りとして読まれることがある。式を続けたい行はインデントする。

```yulang
f:
    g x
    h y

f (g
    x)
```

## receiver-first の dot call を使う

field / method selection は dot syntax で書く。selection 自体は call ではない。選択された値に対して、通常の application が続く。

```yulang
xs.length
xs.map f
text.splice(range 1 3, "bc")
```

左側の値に属する操作は receiver-first の dot call で書くのが自然である。constructor、effect operation、module export としての名前を強く見せたいものは `module::name` を使う。

```yulang
fs_err::not_found "/x"
std::undet::each xs
```

## 左から右へのデータフローには pipe を使う

pipeline operator は `|` である。左辺の値を、右辺 call spine の最初の引数として渡す。

```yulang
1 | add 2    -- add 1 2

xs
    | map f
    | filter pred
```

`|` は左結合で、通常の infix operator より弱く結合する。

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

binding の左辺は pattern である。head が名前のとき、その後ろの pattern は curried function argument になる。

```yulang
my add x y = x + y
my (head, tail) = pair
my area { width = 1, height = 2 } = width * height
```

小さい関数は、この direct header style を優先する。関数値そのものを式として扱いたい場合は、明示的な lambda を使う。

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

小さい式では inline branch も便利だが、pattern が多い code は arm ごとに改行した方が読みやすい。

```yulang
case value:
    nil -> fallback
    just x -> x

catch action:
    console::println_native text, k -> k ()
    value -> value
```

条件は、その条件を持つ arm に guard として置く。

```yulang
case n:
    x if x < 0 -> "negative"
    _ -> "non-negative"
```

## 拡張は `with:` block に置く

`struct`、`enum`、`act`、`error`、`role`、`type ... with:` declaration は companion namespace を作る、または拡張する。method や近い実装詳細は、その対象に属すると見える `with:` block に置く。

```yulang
type str with:
    our s.splice r insert = std::str::splice s r insert

struct point { x: int, y: int } with:
    our p.len2 = p.x * p.x + p.y * p.y
```

こうすると、receiver-style API が、それを所有する type / effect の近くにまとまる。

`with:` は expression-local な拡張にも使える。public companion API ではなく、その式の近くにだけ置きたい helper binding は、式の `with:` に寄せると読みやすい。

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

```yulang
my double(x: 'a): 'a =
    where 'a: Add
    x + x
```

call を通すためだけに、関係の薄い helper binding へ constraint を押し込まないほうが読みやすい。constraint は、その role に依存する境界へ置く。

## operator は import される syntax として扱う

operator のすべてが parser builtin ではない。module は prefix / infix / suffix / nullfix / lazy infix operator を定義して export できる。

```yulang
pub infix(+) 6.0.0 6.0.0 = add
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b -> ...
pub prefix(return) 1.0.0 = return_value
```

下流の file がその operator を parse する必要があるなら、その file を parse する前に operator syntax が import されていなければならない。そのため、公開 operator declaration は module の先頭や prelude 的な module に置くのが自然である。

`return`、`last`、`next`、`redo` のような word operator も、記号 operator と同じ operator model に乗る。ユーザーコード側では、特別な parser 例外のように扱わないこと。

## 短絡評価には lazy operator を使う

短絡評価は evaluator の特殊処理ではなく、lazy operator syntax として書く。

```yulang
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b ->
    if a():
        b()
    else:
        false
```

両側の operand が thunk として渡されるので、body 側でどちらを force するか決められる。これにより、`and` / `or` は library-defined syntax のまま lazy evaluation behavior を持てる。

## type annotation は境界に置く

local code では、多くの場合 inference に任せる。

```yulang
my id(x) = x
```

public contract を示したい場所、曖昧さを減らしたい場所、意図した cast boundary を明示したい場所には annotation を置く。

```yulang
pub my id(x: 'a): 'a = x

my result: result str fs_err = fs_err::wrap:
    read_text path
```

type variable は `'a` のような sigil identifier で書く。通常の function declaration では、type variable のための独立した binder は要らない。

## 状態は明示的な syntax で見せる

mutable / local-reference 的な挙動は、見た目で分かるように書く。

```yulang
my $count = 0
&count = $count + 1
```

mutation を意図する場所ではこの形を使い、通常の `my` binding は immutable に見える形に保つ。

## comment と doc comment は別物

通常の comment には `//` と `/* ... */` を使う。

```yulang
// local note

/* longer note */
```

`--` と `--- ... ---` は doc comment 専用である。documentation syntax として parse され、tooling に残る可能性がある。

```yulang
-- 次の宣言を説明する。

---
長い documentation block。
---
```

## まとめ

- 入れ子の括弧より、whitespace application と `:` を優先する。
- 括弧は default punctuation ではなく、grouping を示したいときに使う。
- 通常の関数 binding は `my f x y = ...` の形を優先する。
- 小さい optional named argument には record-pattern default を使う。
- pattern が多い `case` と `catch` は arm を縦に並べる。
- method、attached impl、expression-local helper は、自然な `with:` block の近くに置く。
- `f(x)` と `f (x)` は違う。
- `f:foo` と `f :foo` は違う。
- export する operator syntax は、importer が parse 前に見える位置に置く。
- 本物の block は indentation、小さい inline block は braces が向いている。
