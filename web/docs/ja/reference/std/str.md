# `std::text::str`

このページでは、不変な文字列と、その `Index`、`Len`、`Add`（連結）、`Display`、`Debug` の操作を扱う。

## リテラルと連結

```yulang
my name = "Yulang"

"hello"
"hello, " + name
"" + 1.show + " items"
```

`+` で文字列を連結する。
`Add` impl は数値の `+` と同じ role 機構を共有するので、`s.add t` でも呼べる。

## 長さ

```yulang
"hello".len    // 5
```

`Len` を通じて `.len` が使える。

## index とスライス

```yulang
my s = "yulang"

s[0]            // y を表す char
s[s.len - 1]    // g を表す char
s[1..<3]        // "ul"
s[..2]          // "yul"
s[2..]          // "lang"
```

文字列は `Index` を `int`（`char`）と `range`（`str` の部分文字列）の両方に実装する。

## splice

```yulang
"abcd".splice (range 1 3) "XY"     // "aXYd"
```

`splice` は範囲の中身を差し替えた新しい文字列を返す。
元の文字列は変わらない。

## 文字列化

```yulang
1.show              // "1"
true.show           // "true"
(1.5).show          // "1.5"
[1, 2, 3].show      // "[1, 2, 3]"
["a", "b"].show     // "[a, b]"
```

`.show` は `Display` role 経由で解決される。
prelude は primitive、`unit`、`list`、`opt`、`result`、よく使う tuple arity にユーザ向けの `Display` impl を提供する。
ただし payload も `Display` を持つ必要がある。
ユーザ型は `error E:`（自動生成）か `impl Display T: our v.show = ...` で `Display` を得る。
`Display` を持つ値には、`.show` を改行付きで出力する `.say` も生える。

構造値の開発者向け表示には `.debug` を使う。

```yulang
[1, 2, 3].debug      // "[1, 2, 3]"
(just "x").debug     // "just \"x\""
```

`.debug` は `Debug` role 経由で解決される。
prelude は primitive、`list`、`opt`、`result`、よく使う tuple arity に `Debug` impl を提供する。
ただし payload も `Debug` を持つ必要がある。
basic runtime host は record や長い tuple の構造 fallback も表示するため、`yulang run` や playground での調査にも使える。
`str` 自体には、生の文字列を改行なしまたは改行付きで出力する `.print` と `.println` がある。
これらは `Debug` method ではなく `str` method である。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `s.len` | `str -> int` |
| `s + t` / `s.add t` | `str -> str -> str` |
| `s[i]` | `str -> int -> char` |
| `s[r]` | `str -> range -> str` |
| `s.splice r t` | `str -> range -> str -> str` |
| `value.show` | `Display 'a => 'a -> str` |
| `value.debug` | `Debug 'a => 'a -> str` |
| `value.say` | `Display 'a => 'a -> [out] ()` |
| `s.print` | `str -> [out] ()` |
| `s.println` | `str -> [out] ()` |

## 関連ページ

- [`std::data::list`](./list)：list 操作と組み合わせる場面が多い
- [文字列](../strings)：文字列まわりの構文
- [キャスト](../casts)：文字列と wrapper 型の変換
