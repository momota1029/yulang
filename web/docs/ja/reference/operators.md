# 演算子宣言

Yulang の演算子は、通常の export された binding に parser table への構文
追加が組み合わさったもの。下流の file は、その演算子 syntax を import した
後でなければ、その演算子を parse できない。

## Fixity

```yulang
pub nullfix(return) = std::flow::sub::return ()
pub prefix(return) 1.0.0 = std::flow::sub::return

pub prefix(not) 8.0.0 = std::bool::not

pub infix (+) 5.0.0 5.0.0 = \x -> \y -> x.add y
pub suffix (..) 8.0.0 = std::range::from_included
```

| Fixity | 使用例 | メモ |
|---|---|---|
| `nullfix` | `return` | オペランドを取らないキーワード風演算子 |
| `prefix` | `not x`、`return x`、`fail e` | 右オペランド 1 つ |
| `infix` | `x + y`、`xs ++ ys` | 2 オペランド。左右の binding power を持つ |
| `suffix` | `0..`、`x?` | 左オペランド 1 つ |

`prefix(...)` / `infix (...)` の名前部分は、記号名のときは丸括弧で囲む。
`not` / `return` のような通常の識別子もそのまま丸括弧に入れる。

## binding power

binding power は `5.0.0` のような dot 区切りの 10 進数で書く。数が大きい
ほど強く結合する。infix 演算子は `<left>.<right>` のペアを持ち、真ん中で
非対称にすると結合方向を決められる：

- `5.0.0 5.0.0` — レベル 5 で左結合（`+` / `-` の標準）
- `4.0.0 4.0.1` — 右側にわずかな bias（右結合）

prelude の選択値：

| 演算子 | binding |
|---|---|
| `or` | `1.0.0`（lazy）|
| `and` | `2.0.0`（lazy）|
| `==`、`!=`、`<`、`<=`、`>`、`>=` | `3.0.0` |
| `..`、`..<`、`<..`、`<..<` | `4.0.0` |
| `+`、`-` | `5.0.0` |
| `*`、`/` | `6.0.0` |
| `not`（prefix） | `8.0.0` |

ユーザコードに新しい演算子を入れるときは、prelude のレベルと衝突せず、
間に収まるように選ぶ。

## Lazy 演算子

`lazy infix` の body は **両方** のオペランドを thunk（`() -> value`）として受け取る。必要な側だけ force すればよく、`a and b` のような呼び出し側で thunk 化を意識する必要はない。prelude の `and` / `or` はこの仕組みで短絡評価を実現している：

```yulang
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b ->
    if a():
        b()
    else:
        false

pub lazy infix(or) 1.0.0 1.0.0 = \a -> \b ->
    if a():
        true
    else:
        b()
```

## 演算子を関数として呼ぶ

演算子定義の右辺は普通の binding なので、パス経由で関数として呼べる：

```yulang
1 + 2
std::int::add 1 2     // 明示形（あまり使わない）
(1).add 2             // role method 経由
```

`+` 自体は `std::ops` の中で `\x -> \y -> x.add y` として定義されているので、
underlying な `Add` role method `x.add y` を直接呼ぶ形が、operator を
第一級参照する最も近い書き方になる。

演算子の実装を第一級参照したいときに役立つ。

## Import

```yulang
use std::ops::*
use my_ops::(+)
use my_ops::* without (+), debug
```

演算子 syntax は丸ごと import、名前指定で import（記号演算子は括弧で囲む）、
glob から `without` で除外、のいずれもできる。parser が後続の式を読む前に
演算子定義を知る必要があるので、これは通常の値 import 以上に重要。

## 新しい演算子を定義する

```yulang
pub infix (++) 4.0.0 4.0.0 = \xs -> \ys -> xs.append ys

[1, 2] ++ [3, 4]   // [1, 2, 3, 4]
```

右辺は普通の curry 関数。優先順位の階層の中で適切な binding power を選ぶ。

## 落とし穴

- 記号演算子は最初の使用前に import する必要がある。順序が逆だと、name
  解決ではなく parse error として弾かれる。
- `pub prefix(name) ...` の宣言と `use foo::(+)` のような import は、両方とも
  syntax をスコープに持ち込む。値だけのパス import は syntax を持ってこない。
- 2 つの glob import が同じ演算子名を出してくると衝突する。`without` で片方
  を除外して曖昧さを解消する。

## 関連ページ

- [適用と演算子](./application) — parse された演算子と裸 application の関係
- [構文スタイル](./syntax-style) — 記号まわりの空白ルール
- [`std::ops`](./std/core) — prelude の演算子定義
