# 文字列

Yulang の文字列型は `str` である。文字列は UTF-8 text として扱う。標準ライブラリの index / slice は raw byte offset ではなく Unicode scalar value の位置で扱う。古い名前として `string` も一部で受け付けるが、新しいコードでは `str` を使う。

## リテラル

```yulang
"hello"
"a\nb\u{21}"
"""
line1
line2
"""
```

文字列リテラルでは `\n` のような escape と、`\u{1F600}` のような Unicode escape を使える。triple quote の文字列は複数行にできる。

## 埋め込み

```yulang
my name = "yu"
"hello %{name}"
"n = %{12}"
"ok = %{true}"
```

`%{...}` は値を `Display` role で文字列化する。標準 prelude は primitive、`list`、`opt`、`result`、よく使う tuple arity に `Display` 実装を提供する。ただし payload も `Display` を持つ必要がある。

整数の hex 表示には lower / upper hex role を使う。

```yulang
"hex = %x{255}"
"HEX = %X{255}"
```

## Index と Slice

```yulang
"aあ🙂"[1]          // "あ"
"aあ🙂z"[1..<3]     // "あ🙂"
"aあ🙂z"[range 1 3]
```

`str` は `Index str int` と `Index str range` を実装する。index は byte offset ではなく文字位置である。

## Splice

```yulang
"aあ🙂z".splice (range 1 3) "bc"  // "abcz"
```

`std::str::splice` と `.splice` method は、文字範囲を別の文字列で置き換える。

## Display と `.show`

```yulang
1.show              // "1"
true.show           // "true"
"text".show         // "text"
[1, 2, 3].show      // "[1, 2, 3]"
["a", "b"].show     // "[a, b]"
(just "x").show     // "just x"
```

`.show` は `str` への正準的な変換である。`Display` role 経由で解決される。標準 prelude は primitive、`unit`、`list`、`opt`、`result`、よく使う tuple arity に、ユーザ向けの `Display` impl を提供する。文字列は quote なしで表示するため、文字列を含む構造値の `.show` は lossless な調査ではなく、読みやすい出力向けである。`Display` は `.say` も提供し、`.show` の結果を改行付きで出力する。

ユーザ型に `Display` を定義するのは通常の role 構文を使う。

```yulang
impl Display point:
    our p.show = "(%{p.x}, %{p.y})"
```

戻り値は `point::show p` / `p.show` の結果であり、文字列テンプレートの `%{p}` でフォーマットされる値でもある。

## Debug と `.debug`

```yulang
[1, 2, 3].debug      // "[1, 2, 3]"
(just "x").debug     // "just \"x\""
(1, true).debug      // "(1, true)"
```

`.debug` は開発者向けの構造表示である。`Debug` role 経由で解決される。標準 prelude は primitive、`list`、`opt`、`result`、よく使う tuple arity に `Debug` impl を提供する。basic runtime host は record や長い tuple の構造 fallback も表示するため、`yulang run` や playground では形ごとの impl を増やさずに調査できる。`Debug` は `.print` / `.println` も提供し、`.debug` の結果を改行なし/改行付きで出力する。ユーザに見せる文字列には `.show` / `.say` を使い、構造値を調べるときには `.debug` / `.print` / `.println` を使う。

## コメント

```yulang
// line comment

/* nested
   block comment */

-- doc line comment

---
doc block
---
```

`//` と `/* ... */` は通常コメントである。`--` と `--- ... ---` は documentation comment で、tooling が参照する可能性がある。
