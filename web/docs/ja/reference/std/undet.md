# std::control::nondet

`std::control::nondet` は非決定性計算を提供する標準ライブラリ module。

```yulang
use std::control::nondet::*
```

## Effect

```yulang
act undet:
    pub branch: () -> bool
    pub reject: () -> never
```

`branch` は二分岐の選択を作る。`reject` は現在の分岐を捨てる。
高水準の `each` や `guard` はこの上に作られている。

## `each`

```yulang
each [1, 2, 3]
each 1..
```

`each xs` は `xs` から要素を一つ選ぶ。`xs` は `Fold` を実装する値ならよい。

## `guard`

```yulang
guard: condition
guard (a == b)
```

condition が false のとき、`guard` は `reject` を呼んでその分岐を捨てる。

## Collector

collector は非決定性を持つ式に method call として付ける。

| Method | Result type | 説明 |
|--------|-------------|------|
| `.list` | `list 'a` | すべての結果 |
| `.logic` | `list 'a` | breadth-first scheduling で集める |
| `.once` | `opt 'a` | 最初の結果。なければ `nil` |

collector は `branch` と `reject` を処理し、型から `undet` effect を取り除く。

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

独立した `each 1..` を 3 つ置いて `guard: a <= b` / `guard: b <= c` で絞る書き方も同じ意味に近いが、現在の VM と browser Wasm stack には上のように範囲を先に絞る形の方が軽い。

## Junction

`std::control::junction` の `all` / `any` は `undet` とは別の effect だが、collection に対する比較を一つの式として書ける。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

`all` / `any` は prelude から使える。
