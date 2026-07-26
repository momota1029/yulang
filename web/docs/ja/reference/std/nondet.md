# `std::control::nondet`

`std::control::nondet` は、`nondet` effect による非決定性計算を提供する標準ライブラリ module である。

```yulang
use std::control::nondet::*
```

## Effect

```yulang
pub act nondet:
    pub branch: () -> bool
    pub reject: () -> never
```

`branch` は二分岐の選択を作る。`reject` は現在の分岐を捨てる。
高水準の `each` や `guard` はこの上に作られている。

## `each`

```yulang
(each [1, 2, 3]).list   // [1, 2, 3]
(each 1..).once         // opt::just 1
```

`each xs` は `xs` から要素を一つ選び、その選択を `nondet` effect で通知する。`xs` には list や range など、`Fold` を実装する値を渡せる。

## `guard`

```yulang
{
    guard: true
    "kept"
}.once

{
    guard (1 == 1)
    "kept"
}.once
```

条件が `false` のとき、`guard` は `reject` を呼んでその分岐を捨てる。

## Collector

collector は非決定性を持つ式に method call として付ける。

| Method | Result type | 説明 |
|--------|-------------|------|
| `.list` | `list 'a` | 分岐順のすべての結果 |
| `.logic` | `list 'a` | 無限分岐に向く breadth-first scheduling で集めたすべての結果 |
| `.once` | `opt 'a` | 最初の結果。なければ `nil` |

各 collector は `branch` と `reject` を処理し、型から `nondet` effect を取り除く。

## 例: ピタゴラス数

```yulang
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
```

結果は `just (3, 4, 5)`。

独立した `each 1..` を 3 つ置き、`guard: a <= b` / `guard: b <= c` で絞っても同じ探索を書けるが、現在の VM と browser Wasm stack には上のように範囲を先に絞る形の方が軽い。

## Junction

companion module の `std::control::junction` は `all xs` と `any xs` を提供する。これらは `nondet` の一部ではないが、collection を包み、`junction` effect を通じて一つの比較をすべての要素に適用する。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

`all` / `any` は prelude から使える。
