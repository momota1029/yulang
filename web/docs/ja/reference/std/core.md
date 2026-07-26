# 標準ライブラリ中核

よく使う標準ライブラリ surface をまとめる。
API はまだ変わる可能性がある。

## `std::core::cmp`

```yulang
(1 == 1, 1 < 2, (3.0).ge 2.0)
```

`std::core::cmp` は `Eq` と `Ord` を宣言する。
`Eq` は `int`、`float`、`frac`、`bool`、`str`、`char`、`list int` に実装される。
`Ord` は `int`、`float`、`frac` に実装される。
`std::core::ops` の比較演算子は、これらの role method を呼ぶ。
role と `impl` の構文は [struct と role](../structs) を参照。
これらは通常の role 宣言と impl であり、別の role system ではない。

## `std::core::convert`

```yulang
my ratio: frac = 2
my decimal: float = ratio
(ratio, decimal)
```

`std::core::convert` は、明示的な `.cast` method を持つ `Cast` role を宣言する。
この module は、`path` から `bytes`、`int` から `frac` と `float`、`frac` から `float` への暗黙変換も登録する。
これらの `cast` 宣言は `Cast` role を実装せず、その method も呼ばない。
compiler が登録済みの暗黙変換を挿入する場所は [cast](../casts) を参照。

## `std::core::fmt`

```yulang
(42.show, "%#x{255}", (just "x").debug)
```

`std::core::fmt` は `Display` と `Debug` の role、書式指定の型、文字列埋め込みが使う書式化関数を宣言する。
primitive、主な container、tuple の標準 impl も提供する。
書式指定とユーザー定義型への role 実装は [文字列](../strings) を参照。

## `std::core::seq`

```yulang
("abc".len, [1, 2, 3].len, "".is_empty)
```

`std::core::seq` は `Len` と `IsEmpty` を宣言する。
`Len` は `str` と `list` に、`IsEmpty` は `str`、`list`、`bytes` に実装される。
関数 `len` は `.len` へ処理を渡す。
sequence 操作は [`std::data::list`](./list) と [`std::text::str`](./str) を参照。
このページでは role API を繰り返さない。

## `std::data::list`

```yulang
[1, 2, 3].append [4]
[1, 2, 3].first
[1, 2, 3][1]
[1, 2, 3][1..<3]
```

list は `int` と `range` の `Index`、`Fold`、`+` 経由の `Add` を実装している。
主な helper は `empty`、`singleton`、`cons`、`uncons`、`map`、`filter`、`fold`、`rev`、`append`、`first`、`sort` である。

mutable list ref には `.push` もある。

## `std::data::range`

```yulang
0..<10
0..10
0..
..<10
..
```

range は値であり、`Fold` を実装している。
そのため `for` や `std::control::nondet::each` に渡せる。

## `std::text::str`

```yulang
"abc".len
"abcd"[1..<3]
"abcd".splice (range 1 3) "XY"
```

文字列は `int` と `range` の `Index`、および `.len` の `Len` を実装している。

## `std::data::result`

```yulang
ok 1
err "bad"
```

`result 'ok 'err` は `map`、`and_then`、`unwrap_or` を提供する。
prelude は `result`、`ok`、`err` を reexport するため、ユーザーコードでは通常 `std::data::result::` や `result::` を付けない。
これは値として返すための型で、filesystem API の主 surface にはまだ使われていない。

## `std::io::console`

```yulang
say "hello"
42.say
print "raw"
println "line"
```

console output は host-handled effect である。
`say` / `.say` は `Display.show` の結果に改行を付けて出力する。
`print` / `println` は raw string を stdout へ書く。
`note` / `.note` / `eprint` / `eprintln` / `dd` は stderr を使う。
host-facing operation は `out`、`err`、`warn`、`die` の effect family に分かれており、通常のプログラムは wrapper と role method を使う。

## `std::io::file`

```yulang
write_text "/tmp/yulang-core-whole.txt" "draft"
read_text "/tmp/yulang-core-whole.txt"

write_text "/tmp/yulang-core-scoped.txt" "draft"
text_with "/tmp/yulang-core-scoped.txt": \content ->
    (content, content + "\nreviewed")

write_text "/tmp/yulang-core-buffer.txt" "draft"
my &buffer = text "/tmp/yulang-core-buffer.txt"
$buffer
```

filesystem surface は text 指向である。
`read_text` は UTF-8 のファイル全体を読み、`write_text` はファイルを作成または置換する。
host エラーが起きた場合、どちらも effect row を通じて `io_err` を発火する。
`text_with` は callback が返した最終テキストを保存する。
`text` は host-backed な可変テキスト参照を返し、buffer は `file` handler の終了時に flush される。

読む API 全体は [`std::io::file`](./fs) を参照。

## Prelude の role

prelude は `std::core::cmp` の `Eq` と `Ord`、`std::core::convert` の `Cast` を re-export する。
`std::core::fmt` の `Display` と `Debug`、`std::core::seq` の `Len` と `IsEmpty` も re-export する。
算術 role、`LowerHex`、`UpperHex` は `std::num` から来る。
`+` と `==` のような演算子、`.len` のような sequence method、`.show` と `.debug` のような書式化 method は、これらの role を通して解決される。
