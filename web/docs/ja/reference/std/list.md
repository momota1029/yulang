# `std::data::list`

不変な list。`Index`、`Fold`、`+`（連結）に対応する。

## 構築

```yulang
[]
[1, 2, 3]
[head, ..tail]

std::data::list::empty()              // []
std::data::list::singleton 1          // [1]
std::data::list::cons(0, [1, 2])      // [0, 1, 2]
```

`[ ... ]` リテラルが日常形。`cons` と `singleton` は型変数の情報を残したい
ときに役立つ。

## index とスライス

```yulang
my xs = [10, 20, 30, 40]

xs[0]            // 10
xs[xs.len - 1]   // 40
xs[1..<3]        // [20, 30]
xs[..2]          // [10, 20]
xs[1..]          // [20, 30, 40]
```

`list 'a` は `Index` を `int` と `range` の両方に実装する。範囲外の `int`
index は実行時失敗、`range` スライスは末尾を超えるとクランプされる。

## 長さと述語

```yulang
xs.len              // 4
std::data::list::is_empty xs    // false
```

`Len` を通じて `xs.len` が使える。

## 反復

```yulang
for x in xs:
    say x

xs.fold 0 (\acc x -> acc + x)
```

`list 'a` は `Fold` を実装するので、`for` も `fold` も使える。`for` の body
は各要素に対して関数として適用される。

## 変換

```yulang
xs.map double                          // [20, 40, 60, 80]
xs.filter (\x -> x > 15)               // [20, 30, 40]
xs.rev                                 // [40, 30, 20, 10]
xs.sort                                // [10, 20, 30, 40]
xs.append [50, 60]                     // [10, 20, 30, 40, 50, 60]
xs + [50, 60]                          // 同じ — list は Add を実装
```

`map` / `filter` / `rev` / `sort` / `append` は新しい list を返す。元の list
は変わらない。

## 先頭・末尾の取得

```yulang
xs.first    // opt::just 10
xs.last     // opt::just 40

case std::data::list::uncons xs:
    opt::just (head, tail) -> head
    opt::nil               -> default
```

`first` / `last` / `uncons` は `opt` を返すので、空リストを綺麗に扱える。

## 可変な list 参照

```yulang
my $xs = [1, 2, 3]
&xs[1] = 99
$xs                  // [1, 99, 3]

&xs.push 4           // [1, 99, 3, 4]  （Index ref impl 経由）
```

`xs` が参照に入っているとき（`my $xs = ...`）、`ref _ (list _)` 用の `Index`
impl で `&xs[i] = value` が書ける。`&xs.push v` も対応する ref method を
通る。

## 非決定性

```yulang
use std::control::nondet::*

(each xs).list
(each xs).once
```

`each` は要素を 1 つ非決定的に選ぶ。`.list` は全ての分岐を新しい list に
集める、`.once` は最初の 1 つを `opt` で返す。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `empty()` | `() -> list 'a` |
| `singleton(x)` | `'a -> list 'a` |
| `cons(x, xs)` | `'a -> list 'a -> list 'a` |
| `is_empty(xs)` | `list 'a -> bool` |
| `xs.len` | `list 'a -> int` |
| `xs.map f` | `list 'a -> ('a -> 'b) -> list 'b` |
| `xs.filter p` | `list 'a -> ('a -> bool) -> list 'a` |
| `xs.fold z f` | `list 'a -> 'b -> ('b -> 'a -> 'b) -> 'b` |
| `xs.rev` | `list 'a -> list 'a` |
| `xs.append ys` | `list 'a -> list 'a -> list 'a` |
| `xs.sort` | `list 'a -> list 'a`（`Ord 'a` を要求）|
| `xs.first` / `xs.last` | `list 'a -> opt 'a` |
| `uncons(xs)` | `list 'a -> opt ('a, list 'a)` |

## 関連ページ

- [パターン → リストパターン](../patterns)
- [`std::data::range`](./core) — スライスと反復に使う range
- [`std::control::nondet`](./undet) — 非決定的な反復
