# `std::str`

不変な文字列。`Index`、`Len`、`Add`（連結）、`Display`、`Debug` に対応する。

## リテラルと連結

```yulang
"hello"
"hello, " + name
"" + 1.show + " items"
```

`+` で文字列を連結する。`Add` impl は数値の `+` と同じ role 機構を共有する
ので、`xs.add ys` でも呼べる。

## 長さ

```yulang
"hello".len    // 5
```

`Len` を通じて `.len` が使える。

## index とスライス

```yulang
my s = "yulang"

s[0]            // "y"
s[s.len - 1]    // "g"
s[1..<3]        // "ul"
s[..2]          // "yu"
s[2..]          // "lang"
```

文字列は `Index` を `int`（1 文字の文字列）と `range`（部分文字列）の両方に
実装する。

## splice

```yulang
"abcd".splice (range 1 3) "XY"     // "aXYd"
```

`splice` は範囲の中身を差し替えた新しい文字列を返す。元の文字列は変わらない。

## 文字列化

```yulang
1.show              // "1"
true.show           // "true"
(1.5).show          // "1.5"
```

`.show` は `Display` role 経由で解決される。各プリミティブには既定の
`Display` impl が付いてくる。ユーザ型は `error E:`（自動生成）か
`impl Display T: our v.show = ...` で `Display` を得る。

構造値の開発者向け表示には `.debug` を使う。

```yulang
[1, 2, 3].debug      // "[1, 2, 3]"
(just "x").debug     // "just \"x\""
```

`.debug` は `Debug` role 経由で解決される。prelude は primitive、`list`、`opt`、`result`、よく使う tuple arity に `Debug` impl を提供する。ただし payload も `Debug` を持つ必要がある。basic runtime host は record や長い tuple の構造 fallback も表示するため、`yulang run` や playground での調査にも使える。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `s.len` | `str -> int` |
| `s + t` / `s.add t` | `str -> str -> str` |
| `s[i]` | `str -> int -> str`（1 文字の文字列）|
| `s[r]` | `str -> range -> str` |
| `s.splice r t` | `str -> range -> str -> str` |
| `value.show` | `Display 'a => 'a -> str` |
| `value.debug` | `Debug 'a => 'a -> str` |

## 関連ページ

- [`std::list`](./list) — list 操作と組み合わせる場面が多い
- [文字列](../strings) — 文字列まわりの構文
- [キャスト](../casts) — 文字列と wrapper 型の変換
