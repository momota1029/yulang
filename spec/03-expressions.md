# 章3 式

状態の凡例は [README](README.md)。この章は式の骨格を扱う。**pattern は次の章**、effect と handler の意味は章5 に回す。
`do` / `sub` / `return` / `for` / `last` / `next` / `redo` / `$x` / `&x` は、制御構文として別にまとめる（章3b）。
Yulang は式指向で、ここに出る構文はほとんどが式として値を持つ。

## 3.1 literal　〔要確認〕

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

出典: `main:notes/design/yulang-language-report.md` §6.1
数値型（`int` / `float` の精度）と string の書式は、型と標準ライブラリの章で扱う（確認 E1）。

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
- `else` がないとき、式全体は `()` を返す。then 側の値は捨てられる（確認 E2）。
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
- pattern の形は次の章。網羅性の検査（確認 E3）。

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

## 3.9 パーサにはあるが意味のない構文

`rule { ... }` と `~"pattern"`（mark）は、パーサにはあるが式としての意味を持たない。仕様には載せず、parser DSL を扱うときに書く（確認 E4）。

## 確認してほしい点

- **E1** 数値 literal の型（`int` は任意精度か、固定幅か。`1.5` の型は何か）は、この章に書くか、標準ライブラリの章に回すか。
- **E2** `else` のない `if` は、then 側が `()` 型でなければならないか。それとも then 側は何型でもよく、値は捨てられるのか。
- **E3** `case` は網羅性を検査するか。arm がどれも合わなかったときはどうなるか。
- **E4** `rule` / `~"pattern"`（parser DSL）は言語仕様に入れるか。入れるなら、いつの章で書くか。
- **E5** パイプライン `lhs | rhs`（左辺を右辺の最初の引数にする）は、素材の一方（報告書）にだけある。現行の言語に存在するか。
