# 文字列

Yulang の文字列型は `str` です。文字列は UTF-8 text として扱います。
標準ライブラリの index / slice は raw byte offset ではなく Unicode scalar value
の位置で扱います。古い名前として `string` も一部で受け付けますが、新しいコード
では `str` を使います。

## リテラル

```yulang
"hello"
"a\nb\u{21}"
"""
line1
line2
"""
```

文字列リテラルでは `\n` のような escape と、`\u{1F600}` のような Unicode
escape を使えます。triple quote の文字列は複数行にできます。

## 埋め込み

```yulang
my name = "yu"
"hello %{name}"
"n = %{12}"
"ok = %{true}"
```

`%{...}` は値を `Display` role で文字列化します。標準 prelude は `int`、
`float`、`bool`、`str` の `Display` 実装を提供します。

整数の hex 表示には lower / upper hex role を使います。

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

`str` は `Index str int` と `Index str range` を実装します。index は byte offset
ではなく文字位置です。

## Splice

```yulang
"aあ🙂z".splice (range 1 3) "bc"  // "abcz"
```

`std::str::splice` と `.splice` method は、文字範囲を別の文字列で置き換えます。

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

`//` と `/* ... */` は通常コメントです。`--` と `--- ... ---` は documentation
comment で、tooling が参照する可能性があります。
