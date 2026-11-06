# 空白で意味が変わる形

Yulang では、同じ文字の並びでも、**空白の有無**で別の構文として読まれることがある。
見た目の違いを、そのまま意味の違いにしている。読む人の目に素直に映る書き方を保つための設計。

## 呼び出しの三つの形

```yulang
f(x)    // 呼び出し: f に x を渡す
f (x)   // f に「括弧で囲んだ式 x」を渡す(ML 風の裸の application)
f: x    // colon application: `:` の後ろ全体を 1 つの引数にする
```

状態: 確定(仮採用の細部あり)・未検査。出典: `spec/01-lexical.md` 1.4。

どれも、最後は同じカリー化された application になる。違うのは、**どこまでを引数と読むか**。

```yulang
f x y        // ((f x) y)    ML 風: 空白で並べる
f(x, y)      // ((f x) y)    C 風: f と ( の間に空白が無い
x.method y   // ((x.method) y)
f: body      // body 全体を 1 つの引数にする
```

- `f()` は、空の引数リストではなく、unit `()` を 1 つ適用する。引数なしの関数という概念は無い。
- `f x: body` は `f x (body)` に近い。`(f x:) body` ではない。

## dot の前の空白

ML 風の引数の中では、dot の前の空白が効く。

```yulang
f xs.map      // f (xs.map)     dot の前に空白が無い → xs.map が 1 つの引数
f xs .map     // (f xs).map     dot の前に空白がある → (f xs) に .map を適用
```

状態: 仮採用・未検査。出典: `spec/01-lexical.md` 1.4。

## index と、リストの適用

```yulang
xs[0]     // index: xs.index 0 と同じ(Index role の糖衣)
xs [0]    // xs に list literal [0] を適用する(index にはならない)
```

`f(x)` と `f (x)` の区別と同じ原則。状態: 確定・未検査。出典: `spec/03-expressions.md` 3.2。

## 並置の右辺は、空白の直前で止まる

```yulang
f g(x)     // f (g(x))
f g (x)    // (f g) x
```

状態: 仮採用・未検査。出典: `spec/03-expressions.md` 3.3。

## path と method

```yulang
x.foo::bar     // foo::bar を x に適用する method の糖衣(foo::bar x)。field を取ってから path を進む意味ではない
(x.foo)::bar   // field を取ってから path を進みたいときは括弧で包む
```

状態: 確定・未検査。出典: `spec/03-expressions.md` 3.2。

## 波括弧: record か block か

波括弧は、先頭が名前で `,` が付くと record、それ以外は block として読まれる。

```yulang
{x: 1, y: 2}   // record
{x: 1,}        // field が 1 つの record(末尾に , を付ける)
{x, y}         // {x: x, y: y}(値を省略した field)
{x,}           // {x: x}
{x: 1}         // block(x: 1 は application)
{x}            // block(値は x)
{}             // 空の record
{;}            // 空の block(値は unit)
```

理由は、`;` が式の意味を変える(文の区切り)のに対して、`,` は変えないから。
状態: 確定・未検査。出典: `spec/03-expressions.md` 3.1。

## 前置演算子と application

前置演算子(`-` や `not`)は、application より弱い。

```yulang
-f x       // -(f x)
not f x    // not (f x)
-x.abs     // -(x.abs)
```

状態: 確定・未検査。出典: `spec/03-expressions.md` 3.3。
