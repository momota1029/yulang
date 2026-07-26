# 適用と演算子

Yulang には関数呼び出しの表記がいくつかある。
すべて同じ curried application へ lower され、表記と結合の強さだけが異なる。

## 4つの呼び出し形式

| 形式 | 構文 | 説明 |
|------|------|------|
| ML-style juxtaposition | `f x y` | 空白で並べる |
| C-style call | `f(x, y)` | callee と `(` の間に空白を置かない |
| Field/method selection | `x.method`、`x.method y`、`x.method(y)` | 値を selection し、必要ならその結果を適用する |
| Colon block call | `f: body` | body 全体を単一引数にする |

call form は curried application へ lower される。
dot selection 単体は selection であり、引数が続くと選択された値を適用する。

```yulang
f x y           // ((f x) y)
f(x, y)         // ((f x) y)
x.method y      // ((x.method) y)
x.method(y, z)  // (((x.method) y) z)
```

C-style form の `f()` は、空の引数リストではなく unit value `()` を `f` に適用する。

## 空白は意味を持つ

Yulang は次の token より前に、空白かコメントがあるかを見る。
その trivia によって tight postfix と ML-style juxtaposition を区別する。

```yulang
f(x)     // C-style call: callee は f、arg は x
f (x)    // ML application: callee は f、arg は括弧で囲んだ x

xs[0]    // index suffix: xs.index 0
xs [0]   // ML application: callee は xs、arg は list literal [0]

x.field  // method/field selection
x .field // field selection。`.` の前には空白を置ける
```

空白の規則は次のとおりである。

- `(` と `[` は、直前の token から空白やコメントを挟まずに続くときだけ call suffix または index suffix になる。
- `.field` は top level では常に field/method selection であり、直前の空白を許す。ただし、ML argument の中では次に示す tight mode の規則によって、どの head に付くかが変わる。

## 結合の例

ML juxtaposition の引数に tight postfix が続くと、空白の位置によって grouping が変わる。

```yulang
f g(x)    // f (g(x)): g と (x) の間に空白がない
f g (x)   // (f g) x: ( の前の空白で次の ML arg になる
f(g)(x)   // (f g) x: C-style call が 2 回続く
f(g, x)   // (f g) x: comma-separated args も curried
(f g)(x)  // (f g) x: 明示的な grouping
```

同じ規則が `[...]` にも当てはまる。

```yulang
f xs[0]   // f (xs[0]): index は xs に付く
f xs [0]  // (f xs) [0]: [0] は index ではなく list literal の引数
```

method/field selection でも同様である。

```yulang
f x.g     // f (x.g): .g は x に付く
f x .g    // (f x).g: . の前の空白で外側の head に付く
g.h(x)    // (g.h)(x): method の後に C-style call
g.h (x)   // (g.h) x: method の後に ML application
```

長い chain も各段階で左から右に結合する。

```yulang
f.method(y).other[0] z
// groups as ((((f.method)(y)).other)[0]) z
```

ML juxtaposition の右辺を parse するとき、parser は先頭に空白がある token の直前で止まる tight mode を使う。
そのため、空白のない `g(x)` は一つの引数になり、`g (x)` の空白は control を外側の head に戻す。

## 結合の強さ

AST では dot selection、call suffix、index suffix、path step は同じ最も強い level にある。
いずれも左から右へ結合する。

```yulang
f.method(y).other[0] z
// groups as ((((f.method)(y)).other)[0]) z
```

各段階は次の順で解決する。

1. `.method`、`(...)`、`[...]`、`::name` のうち、text 上で次にある postfix を選ぶ。
2. 現在の head に付く postfix をすべて消費した後、残りを ML-style juxtaposition の引数として受け取る。
3. infix operator はそれらの外側へ、それぞれの precedence に従って適用する。

## 演算子との優先順位

postfix form には `.`、`::`、`(...)`、`[...]` がある。
これらと juxtaposition は、prelude のすべての infix operator より強く結合する。

```yulang
1 + f x         // 1 + (f x)
1 + x.method    // 1 + (x.method)
1 + xs[0]       // 1 + (xs[0])
not x.field     // not (x.field)
not f x         // not (f x)
```

prelude operator を強い順に並べると、次のようになる。

| Level | Operator | Form |
|-------|----------|------|
| 8 | `not`、prefix/suffix `..`、`..<`、`<..` | prefix / suffix |
| 6 | `*`、`/` | infix |
| 5 | `+`、`-` | infix |
| 4 | `..`、`..<`、`<..`、`<..<` | infix（range） |
| 3 | `==`、`!=`、`<`、`<=`、`>`、`>=` | infix |
| 2 | `and` | infix（lazy） |
| 1 | `or` | infix（lazy） |

```yulang
1 + 2 * 3                 // 1 + (2 * 3)
a == b and c == d         // (a == b) and (c == d)
1..n + 1                  // 1..(n + 1)、range は + の外側
```

user-defined operator は固有の binding power を指定する。

```yulang
pub prefix(not) 8.0.0 = bool_not
pub infix(++) 5.0.0 5.0.1 = append
pub suffix(..) 8.0.0 = range_from
```

binding power は小さい整数を dot で区切った vector である。
辞書順で比較し、足りない component は `0` とみなすため、`5`、`5.0`、`5.0.0` は等しい。
`5.0.1` は `5.0.0` より少し強い。

prefix operator と suffix operator は、それぞれ binding power を 1 つ取る。
infix operator は left binding power と right binding power の 2 つを取る。
左右に異なる値を指定できるため、結合性と細かな grouping を表せる。
right binding power は left binding power よりわずかに強くできる。
その場合、次の同 level operator は現在の右辺の外側に結合する。

## ML application が空白で終わる位置

ML-style argument の右辺は、次の token より前に空白があれば止まる tight mode で parse される。
この規則により、`f x y` は `f (x y)` ではなく `(f x) y` になる。

```yulang
f x y      // ((f x) y): 左結合
f (x y)    // 明示的な grouping
f x.field  // f (x.field): .field の前に空白がない
f x .field // (f x).field: . の前の空白で外側へ戻る
```

ML application の途中にある改行も引数を終わらせる。

```yulang
f x         // f x
my y = z    // 別の statement。f の引数ではない
```

## 推奨するコロン形式

`expr: rest_of_line_or_block` は、括弧を使わずに単一引数を渡す Yulang の慣用表記である。
引数が式の右側全体である場合に使う。
コロンはすべての operator と postfix form より弱く結合するため、右側全体が body になる。

```yulang
f: g x       // f (g x)
f: g: h x    // f (g (h x)): 右結合
f: x + 1     // f (x + 1): operator も body に入る
sub: return value  // sub (return value)
```

引数全体を括弧で囲める場合も、free-paren style では `:` を優先する。

```yulang
// 括弧を使う形
print(format(greeting(name)))

// コロンを使う形
print: format: greeting name

// handler body を含む完全な形
catch (run_console (ask ())):
    value -> value

catch run_console: ask():
    value -> value
```

indented block も body にでき、最後の式が値になる。

```yulang
run_console:
    my line = ask()
    line + "!"
```

いくつかの制御構文と宣言構文も、body を `:` の後ろに置く。
これらはすべてが通常の `ApplyColon` call というわけではないが、同じ surface form を共有する。

```yulang
if cond: 1 else: 2
case x:
    0 -> "zero"
    _ -> "other"
catch action:
    op a, k -> k a
for x in xs:
    say x
sub:
    if cond: return value
    fallback
```

### コロンの結合位置

コロンはすべての infix operator より弱く結合する。
左側全体を関数、右側全体を引数として受け取る。

```yulang
1 + f: x        // (1 + f) x
f x: y          // (f x) y
not f: x        // (not f) x
```

コロンを内側で適用する場合は括弧を使う。

```yulang
g (f: x)        // g (f x)
1 + (f: x)      // 1 + (f x)
```

コロンが ML application の後ろに現れると、その application の外側で結合する。

```yulang
my y = f sub: 1   // (f sub): 1
my z = f (sub: 1) // f (sub: 1)
```

## `if`、`case`、`catch` は式

`if`、`case`、`catch` は任意の式位置に置ける。
いずれも body に `:` block form を使う。

```yulang
my answer = if cond: 1 else: 2
my v = case x:
    0 -> "zero"
    _ -> "other"

run: catch action:
    op a, k -> k a
```

## ラムダ

ラムダは先頭に `\` を置く。

```yulang
\x -> x + 1
\x y -> x * y
my add = \x y -> x + y
```

ラムダの body は、右端まで続く 1 つの完全な式である。

## `do` によるコールバック

`do` は後続の block を lambda として包み、囲んでいる call の最後の引数として渡す。
`my` binding では、左辺の pattern が lambda の parameter になる。

```yulang
write_text "/tmp/yulang-do.txt" "draft"
my result =
    my content = text_with("/tmp/yulang-do.txt", do)
    (content, content)
result
// 内側の binding ≡ text_with("/tmp/yulang-do.txt", \content -> (content, content))
```

API が callback を受け取り、その body を call の直後に書く場合に使う。

## パス区切り `::`

`a::b::c` は左結合であり、ほかの postfix form と同じ強さで結合する。

```yulang
std::data::list::map xs f        // (std::data::list::map) に xs と f を ML application
path_err::not_found "p"          // (path_err::not_found) "p"
```

`::` は path を 1 段進めるだけで、固有の effect や value を持たない。
左側の companion module から sub-name を解決する。
