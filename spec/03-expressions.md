# 章3 式

状態の凡例は [README](README.md)。この章は式の骨格を扱う。**pattern は [章3b](03b-patterns.md)**、effect と handler の意味は章5 に回す。
`do` / `sub` / `return` / `for` / `last` / `next` / `redo` / `$x` / `&x` は、制御構文として別にまとめる（章3c）。
Yulang は式指向で、ここに出る構文はほとんどが式として値を持つ。

## 3.1 literal　〔数値型は確定、他は要確認〕

```yulang
1            // integer
1.5          // float
"hello"      // string
true         // bool
()           // unit
(1, "x")     // tuple
[1, 2, 3]    // list
{x: 1, y: 2} // record
```

- list は spread を持つ: `[1, ..xs, 3]`。record も spread を持つ: `{x: 1, ..rest}`。

- `int` は**任意精度**、`1.5` のような小数 literal は `float`（確定, 2026-11-04）。

出典: `main:notes/design/yulang-language-report.md` §6.1
`float` の精度と string の書式は、型と標準ライブラリの章で扱う。

## 3.2 名前・path・field　〔要確認〕

```yulang
x
std::data::list::map
p.x
xs[0]
```

- 単純な名前は、字句的な local、module scope、`use` で入れた名前の順に探す。
- `a::b` は module path。
- `p.x` は field selection、または method。まず receiver の型に結びついた field と method を探し、次に role の method と effect 行の method を探す。
- `xs[0]` は index で、`xs.index 0` のように field selection と application に落ちる。
- `x.foo::bar` は「`foo::bar` を `x` に適用する」method の糖衣で、field を取ってから path を進む意味ではない。

出典: `main:notes/design/yulang-language-report.md` §6.2、`main:web/docs/ja/reference/modules.md` §Dot selection

## 3.3 application　〔要確認〕

呼び出しの形は 4 つあり、**どれも同じカリー化された application に落ちる**。違うのは表記と結合の仕方だけ。

```yulang
f x y            // ((f x) y)    ML 風: 空白で並べる
f(x, y)          // ((f x) y)    C 風: callee と ( の間に空白がない
x.method y       // ((x.method) y)
f: body          // body 全体を 1 つの引数にする
```

- `f()` は空の引数リストではなく、unit `()` を 1 つ適用する。
- 空白は意味を持つ（`f(x)` と `f (x)` と `f: x` は別。章1.4）。
- `.` / `::` / `(...)` / `[...]` の後置と ML の並置は、prelude のどの infix 演算子よりも強く結合する。

```yulang
1 + f x          // 1 + (f x)
not x.field      // not (x.field)
```

- 並置の右辺では、空白の直前で止まる。そのため `f g(x)` は `f (g(x))`、`f g (x)` は `(f g) x`。

出典: `main:web/docs/ja/reference/application.md`

## 3.4 lambda　〔要確認〕

```yulang
\x -> x + 1
\x y -> x + y     // \x -> \y -> x + y
```

- `\pat -> body`。引数は名前に限らず pattern を書ける。複数並べるとカリー化された lambda になる。

出典: `main:notes/design/yulang-language-report.md` §6.4

## 3.5 block と `with`　〔要確認〕

```yulang
{
    my x = 1
    x + 1
}

target with:
    our helper = ...
```

- block は文を順に評価し、最後の式が値になる。
- `with:` は、本体（tail）の前に局所的な binding 群を開く。その中の `our` / `pub` は tail から見える。

出典: `main:notes/design/yulang-language-report.md` §6.5

## 3.6 `if`　〔要確認〕

```yulang
if n < 0: "negative"
elsif n == 0: "zero"
else: "positive"

if cond { a } else { b }
```

- `if` は式で、条件は `bool`。`elsif` と `else` を持てる。条件は上から順に試す。
- `else` がないとき、式全体は `()` を返す。then 側は**何型でもよく**、値は捨てられる（確定, 2026-11-04）。
  Simple-sub の体系では、値を分解する方法がないので、捨てても型の整合は壊れない。
- 条件が effectful な場合の扱い（junction。`all` / `any`）は章5 で書く。

出典: `main:web/docs/ja/reference/control-flow.md`

## 3.7 `case`　〔要確認〕

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

- arm は上から順に試し、最初に pattern が合って guard が真になった arm が選ばれる。
- guard は pattern の後ろに `if`（または `where`）で書く。guard からは pattern が束縛した名前が見える。
- **網羅性を検査する**。どの arm にも合わない場合があるなら、エラーになる（確定, 2026-11-04）。
- 網羅性の細部（guard 付きの arm の扱いなど）は [章3b](03b-patterns.md) に書く。

出典: `main:web/docs/ja/reference/control-flow.md` §case、`main:notes/design/yulang-language-report.md` §6.7

## 3.8 `catch`（骨格のみ）　〔意味は章5〕

```yulang
catch expr:
    value -> value
    effect_pat, k -> body
```

- arm の pattern が 1 個なら value arm、2 個なら effect arm。effect arm の 2 個目の pattern は継続 `k` を受け取る。
- handler の意味、effect の「引ける」条件（章末 T2）は章5 で書く。

出典: `main:notes/design/yulang-language-report.md` §6.8

## 3.9 パイプライン `|`　〔存在は確定、細部は要確認〕

```yulang
"data" | parse | render
xs | map f
```

- `x | f` は左辺の値を右辺に渡す。**仮採用: `lhs | rhs` は `rhs lhs`**、つまり `xs | map f` は `map f xs`（ユーザー判断, 2026-11-04。
  素材の一方は「最初の引数」と書いていたが、ユーザーも確信がなく、`map f xs` で良いとした）。
- 結合力は旧い文書で `5`（比較より弱い）とされている。現行の値は未確認。

出典: `main:web/docs/ja/reference/idioms.md`、`main:notes/design/yulang-language-report.md` §6.3

## 3.10 parser DSL（`rule { ... }` と `~"..."`）　〔仕様に入れると確定〕

`~"GET :resource"` や `rule { ... }` は parser 値を作る。`case` の arm では**入力文字列全体**にマッチし、名前付き capture を binding にする。

```yulang
my request(source: str): str = case source:
    ~"GET :resource" -> resource
    _ -> "no match"
```

- 意味が大きいので、専用の章（parser DSL）を後で立てる。ここでは、`case` の arm に parser pattern が書けることだけを述べる。

出典: `main:web/docs/ja/reference/parser-dsl.md`

## 確認してほしい点

- **E6** `|` の仮採用（`rhs lhs`）を、実装と突き合わせて確かめる。結合力の現行値も確かめる。
