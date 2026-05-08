# 標準ライブラリ中核

よく使う標準ライブラリ surface をまとめます。API はまだ変わる可能性があります。

## `std::list`

```yulang
[1, 2, 3].append [4]
[1, 2, 3].last
[1, 2, 3][1]
[1, 2, 3][1..<3]
```

list は `int` と `range` の `Index`、`Fold`、`+` 経由の `Add` を実装しています。
主な helper は `empty`、`singleton`、`cons`、`uncons`、`map`、`filter`、`fold`、
`rev`、`append`、`first`、`last`、`sort` です。

mutable list ref には `.push` もあります。

## `std::range`

```yulang
0..<10
0..10
0..
..<10
..
```

range は値であり、`Fold` を実装しています。そのため `for` や `std::undet::each`
に渡せます。

## `std::str`

```yulang
"abc".len
"abcd"[1..<3]
"abcd".splice (range 1 3) "XY"
```

文字列は `int` と `range` の `Index`、および `.len` の `Len` を実装しています。

## `std::result`

```yulang
ok 1
err "bad"
```

`result 'ok 'err` は `map`、`and_then`、`unwrap_or` を提供します。prelude は
`result`、`ok`、`err` を reexport するため、ユーザーコードでは通常
`std::result::` や `result::` を付けません。これは値として返すための型で、
filesystem API の主 surface にはまだ使われていません。

## `std::console`

```yulang
println "hello"
print "no newline"
```

console output は host-handled effect です。`println` は改行を追加します。

## `std::fs`

```yulang
fs::read_text "data.txt"
fs::write_text ("data.txt", "text")
fs::exists "data.txt"
```

filesystem surface は意図的に最小限で、まだ最終形ではありません。`read_text` は
`opt str` を返します。移行用の `read_text_or_throw` は `nil` を
`fs_err::not_found` へ写します。browser / wasm host では filesystem request が
unresolved のまま残る場合があります。

## Prelude の Role

主な prelude role は次の通りです。

- `Eq`, `Ord`
- `Add`, `Sub`, `Mul`, `Div`
- `Len`
- `Display`
- `Cast`
- `LowerHex`, `UpperHex`

`+`、`==`、`.len`、文字列埋め込み、implicit cast などは、これらの role を通して
解決されます。
