# 数値と bool の標準ライブラリ

このページでは、`std::bool`、`std::int`、`std::float`、`std::num`、`std::num::frac` を扱う。
`primitive` 操作と、演算子が使う `role` `method` を区別する。

## `std::bool`

`std::bool` は、組み込みの `bool` 型に等値比較、否定、小文字の文字列化を提供する。

```yulang
(
    std::bool::eq true false,
    std::bool::not false,
    std::bool::to_string true,
    not true,
)
```

結果は `(false, true, "true", false)` になる。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `eq(x, y)` | `bool -> bool -> bool` |
| `not(x)` | `bool -> bool` |
| `to_string(x)` | `bool -> str` |

## `std::int`

`std::int` は、`int` の比較、整数算術、切り捨て除算、剰余、10 進と 16 進の文字列化を提供する。

```yulang
(
    std::int::add 2 3,
    std::int::sub 7 2,
    std::int::mul 3 4,
    std::int::div 7 2,
    17 mod 5,
    std::int::to_string (-42),
    std::int::to_hex 255,
    std::int::to_upper_hex 255,
)
```

結果は `(5, 5, 12, 3, 2, "-42", "ff", "FF")` になる。
`div` と `mod` の演算子は整数の `primitive` を呼ぶ。
0 による除算または剰余は実行時に失敗する。

整数の `/` 演算子は異なる振る舞いをする。
`std::num::Div` を通して解決され、正確な `frac` を返す。
たとえば、`2 / 4` は `1/2`、`2 div 4` は `0` になる。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `eq(x, y)` | `int -> int -> bool` |
| `lt(x, y)` / `le(x, y)` | `int -> int -> bool` |
| `gt(x, y)` / `ge(x, y)` | `int -> int -> bool` |
| `add(x, y)` | `int -> int -> int` |
| `sub(x, y)` | `int -> int -> int` |
| `mul(x, y)` | `int -> int -> int` |
| `div(x, y)` / `x div y` | `int -> int -> int` |
| `mod(x, y)` / `x mod y` | `int -> int -> int` |
| `to_string(x)` | `int -> str` |
| `to_hex(x)` / `to_upper_hex(x)` | `int -> str` |

## `std::float`

`std::float` は、`float` の比較、算術、文字列化の `primitive` を提供する。

```yulang
(
    std::float::lt 1.0 2.0,
    std::float::add 1.5 2.0,
    std::float::sub 5.0 1.5,
    std::float::mul 2.0 3.5,
    std::float::div 7.0 2.0,
    std::float::to_string 1.5,
)
```

結果は `(true, 3.5, 3.5, 7, 3.5, "1.5")` になる。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `eq(x, y)` | `float -> float -> bool` |
| `lt(x, y)` / `le(x, y)` | `float -> float -> bool` |
| `gt(x, y)` / `ge(x, y)` | `float -> float -> bool` |
| `add(x, y)` | `float -> float -> float` |
| `sub(x, y)` | `float -> float -> float` |
| `mul(x, y)` | `float -> float -> float` |
| `div(x, y)` | `float -> float -> float` |
| `to_string(x)` | `float -> str` |

## `std::num`

`std::num` は、`+`、`-`、`*`、`/` が使う算術 `role` と、文字列埋め込みが使う 16 進書式の `role` を定義する。

| Role | member |
| --- | --- |
| `Add 'a` | `a.add: 'a -> 'a` |
| `Sub 'a` | `a.sub: 'a -> 'a` |
| `Mul 'a` | `a.mul: 'a -> 'a` |
| `Div 'a` | `a.div: 'a -> Div::out` |
| `LowerHex 'a` | `a.lower_hex: str` |
| `UpperHex 'a` | `a.upper_hex: str` |

`int`、`float`、`frac` は 4 個の算術 `role` を実装する。
整数の `Div::out` は `frac` であり、ほかの 2 個の除算 `impl` は `receiver` と同じ型を返す。
`str` と `list 'a` は、連結として `Add` を実装する。
2 個の 16 進 `role` を実装するのは `int` だけである。

```yulang
my half = std::num::frac::new 1 2

(
    2.add 3,
    2.div 4,
    (7.0).div 2.0,
    half.mul half,
    "a".add "b",
    [1].add [2],
    255.lower_hex,
    255.upper_hex,
)
```

結果は `(5, 1/2, 3.5, 1/4, "ab", [1, 2], "ff", "FF")` になる。

## `std::num::frac`

`frac` は、正確な有理数演算に使う公開された `{ num: int, den: int }` の値である。
`new` は 2 個の `field` を最大公約数で約分し、負号を `num` へ移す。

```yulang
my x = std::num::frac::new 6 (-8)
my y = std::num::frac::new 1 2

(
    (x.num, x.den),
    std::num::frac::add x y,
    std::num::frac::sub x y,
    std::num::frac::mul x y,
    std::num::frac::div x y,
    x < y,
    std::num::frac::to_float x,
    x.show,
)
```

結果は `((-3, 4), -1/4, -5/4, -3/8, -3/2, true, -0.75, "-3/4")` になる。
比較演算子は `Eq` と `Ord` の `impl` から来る。
`Display` は `to_string` を使う。

`new` には 0 でない分母を渡す。
現在の実装は、この不変条件を検証しない。
0 でない分子と分母 `0` を渡すと `den` が `0` のままになり、`new 0 0` は実行時に失敗する。
`frac { num, den }` を直接構築した場合も正規化を迂回する。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `new(n, d)` | `int -> int -> frac` |
| `add(x, y)` / `x + y` | `frac -> frac -> frac` |
| `sub(x, y)` / `x - y` | `frac -> frac -> frac` |
| `mul(x, y)` / `x * y` | `frac -> frac -> frac` |
| `div(x, y)` / `x / y` | `frac -> frac -> frac` |
| `eq(x, y)` / `x == y` | `frac -> frac -> bool` |
| `lt(x, y)` / `le(x, y)` | `frac -> frac -> bool` |
| `gt(x, y)` / `ge(x, y)` | `frac -> frac -> bool` |
| `to_float(x)` | `frac -> float` |
| `to_string(x)` / `x.show` | `frac -> str` |

## 関連ページ

- [演算子](../operators)：演算子の宣言と優先順位
- [文字列](../strings)：数値の表示と 16 進の文字列埋め込み
- [cast](../casts)：`int`、`frac`、`float` の間の暗黙変換
- [標準ライブラリ一覧](./)：すべての `module` の一覧
