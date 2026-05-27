# 適用と演算子

Yulang には関数呼び出しの表記がいくつかある。すべて curried application へ lower される。

## 4つの call form

| Form | Syntax | メモ |
|------|--------|------|
| ML-style | `f x y` | 空白で並べる |
| C-style | `f(x, y)` | callee と `(` の間に空白を置かない |
| Field/method selection | `x.method`, `x.method y`, `x.method(y)` | selection し、必要ならその結果を適用する |
| Colon block call | `f: body` | body 全体を単一引数にする |

```yulang
f x y           // ((f x) y)
f(x, y)         // ((f x) y)
x.method y      // ((x.method) y)
x.method(y, z)  // (((x.method) y) z)
```

`x.method` 単体は call ではなく selection である。後ろに引数が続いた場合、選択された値が関数として適用される。

`f()` は unit `()` を渡す call として読む。

## 空白は意味を持つ

```yulang
f(x)     // C-style call
f (x)    // ML application。arg は grouped expression

xs[0]    // index suffix
xs [0]   // xs に list literal [0] を渡す ML application

x.field  // selection
x .field // 外側の head への selection として読める
```

`(` と `[` は、直前 token との間に空白がないときだけ tight suffix になる。`.` は top-level では空白があっても selection だが、ML argument の中では tight mode の影響を受ける。

## 例

```yulang
f g(x)    // f (g(x))
f g (x)   // (f g) x
f(g)(x)   // (f g) x
f(g, x)   // (f g) x
```

```yulang
f xs[0]   // f (xs[0])
f xs [0]  // (f xs) [0]
```

```yulang
f x.g      // f (x.g)
f x .g     // (f x).g
g.h(x)     // (g.h)(x)
g.h (x)    // (g.h) x
```

## 演算子の優先順位

postfix forms、selection、juxtaposition は infix operator より強く結合する。

```yulang
1 + f x      // 1 + (f x)
1 + xs[0]    // 1 + (xs[0])
not f x      // not (f x)
```

prelude の主な operator:

| Level | Operators | Form |
|-------|-----------|------|
| 8 | `not`, prefix/suffix `..`, `..<`, `<..` | prefix / suffix |
| 6 | `*`, `/` | infix |
| 5 | `+`, `-` | infix |
| 4 | `..`, `..<`, `<..`, `<..<` | range |
| 3 | `==`, `!=`, `<`, `<=`, `>`, `>=` | comparison |
| 2 | `and` | lazy infix |
| 1 | `or` | lazy infix |

user-defined operator は自分で binding power を指定する。

```yulang
pub prefix(not) 8.0.0 = bool_not
pub infix(++) 5.0.0 5.0.1 = append
pub suffix(..) 8.0.0 = range_from
```

binding power は `.` 区切りの small integer vector である。比較は辞書順で、足りない桁は `0` として扱われるため、`5`、`5.0`、`5.0.0` は同じ強さになる。`5.0.1` は `5.0.0` より少し強い。

prefix / suffix operator は binding power を 1 つ持つ。infix operator は left binding power と right binding power の 2 つを持つ。左右で別の値を持てるため、結合性や細かい grouping を operator 定義側で表せる。

## Colon style

`expr: body` は「右側全体を引数にする」ための慣用表記。

```yulang
f: g x
f: g: h x
f: x + 1
sub: return value
```

括弧を増やすより、block や長い式には `:` を使う方が読みやすい。

ただし `:` が ML application の右側に現れた場合、ML 引数の中へ入らない。

```yulang
my y = f sub: 1   // (f sub): 1
my z = f (sub: 1) // f (sub: 1)
```

## `do` でコールバックを後置する

`do` は、後続のブロックを lambda として包み、囲んでいる関数呼び出しの最後の
引数として渡すためのマーカー。`my` binding の左辺 pattern は、その lambda の
引数になる。

```yulang
my &fh = open_in "data.txt" do
$fh
// ≡ open_in "data.txt" (\&fh -> $fh)
```

API がコールバックを受け取るとき、その本体を呼び出しの直後にそのまま書きたい
場合に使う。
