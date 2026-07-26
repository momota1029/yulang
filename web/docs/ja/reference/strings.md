# 文字列

Yulang の文字列型は `str` である。
文字列は UTF-8 のテキストとして扱う。
標準ライブラリの index / slice は、raw byte offset ではなく Unicode scalar 値の位置を使う。

## リテラル

```yulang
"hello"
"a\nb\u{21}"
"""
line1
line2
"""
```

文字列リテラルでは、`\n` のような escape と `\u{1F600}` のような Unicode escape を使える。
triple quote の文字列は複数行にできる。

## 埋め込み

```yulang
my name = "yu"
"hello %{name}"
"n = %{12}"
"ok = %{true}"
```

`%{...}` は値を `Display` role で文字列化する。
標準 prelude は primitive、`list`、`opt`、`result`、よく使う tuple arity に `Display` 実装を提供する。
container の payload にも `Display` 実装が必要である。

整数の 16 進表示には lower / upper hex role を使う。

```yulang
"hex = %x{255}"
"HEX = %X{255}"
```

## 書式指定

書式指定は `%` と埋め込みの `body` の間に置く。

```text
%[[fill]align][sign][#][0][width][.precision][kind]{expression}
```

各部分は、この順序で書かなければならない。
利用できる marker は次のとおりである。

| 部分 | 形式 | 効果 |
|------|------|------|
| `align` | `<`、`>`、`^` | 左寄せ、右寄せ、中央寄せ |
| `sign` | `+`、`-` | 正数にも符号を付けるか、負数だけに符号を残す |
| `#` | `#` | alternate form。16 進数には `0x` または `0X` が付く |
| `0` | `0` | 数値を `0` で埋める |
| `width` | 10 進数 | 結果の最小幅 |
| `precision` | `.` と 10 進数 | 表示する `body` の最大長 |
| `kind` | `?`、`x`、`X` | debug、lower hex、upper hex の表示 |

align marker の直前にある 1 文字は fill 文字になる。
precision は表示した `body` を切り詰め、その後で width と align が padding を加える。

```yulang
my text = "abcdef"
my side = "right"
my quoted = "text"

(
    "%8.3{text}",       // "     abc"
    "%*>8{side}",       // "***right"
    "%#x{255}",         // "0xff"
    "%+#08x{255}",      // "+0x000ff"
    "%?{quoted}"        // "\"text\""
)
```

`kind` を省略すると `Display` を使う。
`?` は `Debug`、`x` と `X` は lower hex `role` と upper hex `role` を使う。

## Index と Slice

```yulang
my c: char = "aあ🙂"[1] // あを表す char
"aあ🙂z"[1..<3]     // "あ🙂"
"aあ🙂z"[range 1 3]
```

`str` は `Index` を `int` と `range` の両方に実装する。
整数 index は `char` を返し、range index は `str` を返す。
どちらも byte offset ではなく文字位置を使う。

## Splice

```yulang
"aあ🙂z".splice (range 1 3) "bc"  // "abcz"
```

`std::text::str::splice` と `.splice` method は、文字範囲を新しいテキストで置き換える。

## Display と `.show`

```yulang
1.show              // "1"
true.show           // "true"
"text".show         // "text"
[1, 2, 3].show      // "[1, 2, 3]"
["a", "b"].show     // "[a, b]"
(just "x").show     // "just x"
```

`.show` は `str` への正準的な変換であり、`Display` role 経由で解決される。
標準 prelude は primitive、`unit`、`list`、`opt`、`result`、よく使う tuple arity に、ユーザー向けの `Display` impl を提供する。
文字列は quote なしで表示するため、文字列を含む構造値の `.show` は lossless な調査ではなく、読みやすい出力に使う。
`Display` は `.say` も提供し、`.show` の結果を改行付きで出力する。

ユーザー定義型の `Display` には、通常の role 構文を使う。

```yulang
struct point { x: int, y: int }

impl Display point:
    our p.show = "(" + p.x.show + ", " + p.y.show + ")"
```

この実装の戻り値が、`p.show` と文字列テンプレートの `%{p}` に使われる。

## Debug と `.debug`

```yulang
[1, 2, 3].debug      // "[1, 2, 3]"
(just "x").debug     // "just \"x\""
(1, true).debug      // "(1, true)"
```

`.debug` は開発者向けの構造表示であり、`Debug` role 経由で解決される。
標準 prelude は primitive、`list`、`opt`、`result`、よく使う tuple arity に `Debug` impl を提供する。
container の payload にも `Debug` 実装が必要である。
basic runtime host は record や長い tuple の構造 fallback も表示するため、`yulang run` や playground では形ごとの impl を増やさずに構造を調べられる。
`Debug` は `.print` / `.println` も提供し、`.debug` の結果を改行なし、または改行付きで出力する。
ユーザーに見せる文字列には `.show` / `.say` を使い、構造値を調べるときには `.debug` / `.print` / `.println` を使う。

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

`//` と `/* ... */` は通常コメントである。
`--` と `--- ... ---` は documentation コメントで、tooling が参照する可能性がある。
