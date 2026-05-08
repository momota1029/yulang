# 演算子宣言

演算子は、値の定義であると同時に parser table へ syntax を追加する宣言です。
下流の file は、その演算子 syntax を import した後でなければ、その演算子を
parse できません。

## Fixity

```yulang
pub nullfix(return) = std::flow::sub::return ()
pub prefix(return) 1.0.0 = std::flow::sub::return

pub prefix(not) 8.0.0 = std::bool::not

pub infix (+) 5.0.0 5.0.0 = \x -> \y -> x.add y
pub suffix (..) 8.0.0 = std::range::from_included
```

使える fixity は次の通りです。

| Fixity | 使用例 |
|--------|--------|
| `nullfix` | `return` |
| `prefix` | `not x`, `return x` |
| `infix` | `x + y` |
| `suffix` | `0..` |

binding power は `5.0.0` のような dot 区切りの数値で書きます。infix operator は
左と右の binding power を持ちます。

## Lazy Operator

```yulang
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b ->
    if a: b() else: false
```

`lazy` operator は右辺を遅延 computation として受け取ります。標準の `and` と
`or` はこれを使って短絡評価します。

## Import

```yulang
use std::ops::*
use my_ops::(+)
use my_ops::* without (+), debug
```

operator syntax は直接 import、glob import、`without` による除外ができます。
parser は後続の式を読む前に operator syntax を知る必要があるため、これは通常の
値 import 以上に重要です。

## Prelude Operator

標準 prelude は arithmetic、comparison、boolean、range、loop、return の演算子を
export します。これらも通常の exported syntax であり、ユーザー code も module に
同様の演算子を定義して明示的に import できます。
